/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlockExact -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.DefsSat
import LibsignalBinary.Proofs.CodeLayout

/-!
# `HookSatExactMemcpy` and `HookSatCompress256` siblings for `CompressAndDigest` (Block `73`)

Steps Block `73`'s two direct `compress256` calls (`seg2b_placed_runsTo_sat`,
`seg3b_placed_runsTo_sat`) via `s2_compress256_step_placed_of_hookSat` under
`HookSatCompress256 H lsCompress256Sym F`, and composes `hmac_tail_placed_runsTo_sat` and
`hmac_placed_runsTo_exact` (`1200`-byte stack).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigestExact

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState hmacWith)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalHooks LibsignalPlacement blkPl_73 lsProg_73 lsmpl
)
open CryptoVerification.LibsignalAesCbc (memsetHook)
open CryptoVerification.LibsignalHmac (shaStateBytes)
open CryptoVerification.LibsignalSession.CryptoHmacSha256 (
  CalleeSaved Frame HmacPlacedPre RW RunsTo RunsToFrom StateH2Placed StateH2cPlaced StateH3Placed
  StateH3cPlaced StateH4Placed digestBytes digestBytes_length hsp hsp_align innerDigest
  innerLastBlock innerState lsCompress256Sym lsMemcpySym lsMemsetSym outerBlock outerDigest
  outerState read32_of_readBytes_shaStateBytes seg1a_placed_runsTo seg2a_placed_runsTo
  seg3a_placed_runsTo seg4_placed_runsTo toBEBytes_8_eq_list
)
open CryptoVerification.LibsignalTripleRatchet.Extract (
  CallingConventionPreserved.x19 CallingConventionPreserved.x20 CallingConventionPreserved.x21
  CallingConventionPreserved.x22 CallingConventionPreserved.x27 CallingConventionPreserved.x29
  S2Frame
)
open LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.DefsSat (
  s2Frame_of_hmacFrame s2Frame_readBytes_eq_of_readable s2Frame_readable_of_readable
)
open LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlockExact (
  HmacPlacedPreSat hmacSaved_of_s2Frame seg0_placed_runsTo_exact seg1b_placed_runsTo_exact
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (HookSatExactMemcpy)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (
  CallingConventionPreserved.x23 HookSatCompress256 s2_compress256_step_placed_of_hookSat
)

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

private theorem hmacPlacedPre_of_s2Frame [LibsignalPlacement] {F : ShaCompress}
    {key inp : List (BitVec 8)} {s₀ : State} {m : Memory}
    (h : HmacPlacedPre F key inp s₀)
    (hread_key : s₀.mem.Readable (s₀.readReg64 .x1) 32)
    (hf : S2Frame s₀.mem m [(s₀.sp - 1024#64, 1024)]) :
    HmacPlacedPre F key inp (s₀.setMem m) ∧
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

/-- `HookSatCompress256` sibling of `seg2b_placed_runsTo` (`CompressAndDigest.lean:905`). -/
theorem seg2b_placed_runsTo_sat [LibsignalPlacement] {F : ShaCompress}
    {H : LibsignalHooks} (h_compress : HookSatCompress256 H lsCompress256Sym F)
    {key : List (BitVec 8)} {byte : BitVec 8} {s₀ s : State}
    (hpre : HmacPlacedPre F key [byte] s₀) (hs : StateH2cPlaced F key byte s₀ s) :
    RunsTo (lsProg_73 H) s (fun s₃ =>
      StateH3Placed F key byte (s₀.setMem s₃.mem) s₃ ∧
      S2Frame s₀.mem s₃.mem [(s₀.sp - 1024#64, 1024)]) := by
  rcases hs with ⟨hpc, ⟨hstat, hsp_eq, hx29, hx27, hsaved, hframe⟩,
    hx0, hx1, hx2, hlr, hx19, hx20, hx21, hx22, hx23, hist, hiblk, host, hobl⟩
  have hrw_stack1024 : RW s.mem (s₀.sp - 1024#64) 1024 :=
    (hframe.rw_iff _ _).mpr hpre.rw_stack
  have hrw_hsp : RW s.mem (hsp s₀) 480 :=
    hrw_stack1024.sub (by unfold hsp; clear * -; bv_omega)
  have hsp_sub176 : hsp s₀ - 176#64 = s₀.sp - 656#64 := by unfold hsp; bv_omega
  have hrw_slack : RW s.mem (s₀.sp - 656#64) 176 :=
    hrw_stack1024.sub (by clear * -; bv_omega)
  have hsp_al : (s.sp &&& 15#64) = 0#64 := by
    rw [hsp_eq]; exact hsp_align hpre.sp_aligned
  have hiblk_len : (innerLastBlock [byte]).length = 64 := by
    unfold innerLastBlock; rw [toBEBytes_8_eq_list]; simp
  refine hmacRunsToFrom_of_hkdf (s2_compress256_step_placed_of_hookSat h_compress.toHookSat
    (stPtr := hsp s₀ + 208#64) (blkPtr := hsp s₀ + 304#64) (lr := (blkPl_73).base + 492#64)
    (st := innerState F key) (blk := innerLastBlock [byte])
    (hrun := hstat) (hpc := hpc) (hx0 := hx0) (hx1 := hx1) (hx2 := hx2) (hlr := hlr)
    (hsp_al := hsp_al) (hst := hist) (hblk := hiblk) (hlen := hiblk_len)
    (hrw_st := hrw_hsp.sub (by clear * -; bv_omega))
    (hrw_stk := by rw [hsp_eq, hsp_sub176]; exact hrw_slack)
    (hread_blk := readable_of_rw (hrw_hsp.sub (by clear * -; bv_omega)))
    (hdisj_st_stk := by rw [hsp_eq, hsp_sub176]; clear * -; unfold hsp DisjointRegions; bv_omega)
    (hdisj_st_blk := by clear * -; unfold DisjointRegions; bv_omega)
    (hdisj_stk_blk := by rw [hsp_eq, hsp_sub176]; clear * -; unfold hsp DisjointRegions; bv_omega)
    (htr_s := ⟨rfl, rfl⟩)
    fun s₃ htr₃ hpc₃ hstat₃ hcc₃ _ _ _ hst₃ hs2 _ => ?_)
  intro hL₃
  have hs2' : S2Frame s.mem s₃.mem [(hsp s₀ + 208#64, 32), (s₀.sp - 656#64, 176)] := by
    simpa only [hsp_eq, hsp_sub176] using hs2
  have hs2_1024 : S2Frame s₀.mem s₃.mem [(s₀.sp - 1024#64, 1024)] := by
    refine (s2Frame_of_hmacFrame hframe).trans (hs2'.mono fun a ha r hr => ?_)
    have hstk := ha (s₀.sp - 1024#64, 1024) (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      (dsimp only [OutsideRegion, hsp] at hstk ⊢; clear * - hstk; bv_omega)
  have hget (i : Fin 8) (off : BitVec 64)
      (hoff : hsp s₀ + off = (hsp s₀ + 208#64) + BitVec.ofNat 64 (4 * i.val)) :
      s₃.mem.read32 (hsp s₀ + off) = (innerDigest F key byte).get i := by
    rw [hoff]; exact read32_of_readBytes_shaStateBytes hst₃ i
  have host₃ : s₃.mem.readBytes (hsp s₀ + 248#64) 32 = shaStateBytes (outerState F key) := by
    refine (hs2'.readBytes_eq (hrw_hsp.sub (by clear * -; bv_omega)) ?_ (by decide)).trans host
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (clear * -; unfold hsp DisjointRegions; bv_omega)
  have hobl₃ : s₃.mem.read64 (hsp s₀ + 280#64) = 1#64 := by
    refine (hs2'.read64_eq (hrw_hsp.sub (by clear * -; bv_omega)) ?_).trans hobl
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (clear * -; unfold hsp DisjointRegions; bv_omega)
  exact ⟨s₃, .refl s₃, htr₃,
    ⟨{ pc_eq := hpc₃
       common :=
         { status := hstat₃
           sp_eq := (CallingConventionPreserved.sp_eq hcc₃).trans hsp_eq
           x29_eq := (CallingConventionPreserved.x29 hcc₃).trans hx29
           x27_eq := (CallingConventionPreserved.x27 hcc₃).trans hx27
           saved := hmacSaved_of_s2Frame
             (hrw_hsp.sub (by clear * -; unfold hsp; simp only [State.sp_setMem]; bv_omega)) hsaved hs2' (by
             intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
             rcases hr with rfl | rfl <;>
               (try dsimp only; clear * -; unfold hsp; simp only [State.sp_setMem]; unfold DisjointRegions; bv_omega))
           frame := Frame.refl s₃.mem _ }
       x19_eq := (CallingConventionPreserved.x19 hcc₃).trans hx19
       x20_eq := (CallingConventionPreserved.x20 hcc₃).trans hx20
       x21_eq := (CallingConventionPreserved.x21 hcc₃).trans hx21
       x22_eq := (CallingConventionPreserved.x22 hcc₃).trans hx22
       x23_eq := (CallingConventionPreserved.x23 hcc₃).trans hx23
       hi0 := hget 0 208#64 (by clear * -; bv_omega)
       hi1 := hget 1 212#64 (by clear * -; bv_omega)
       hi2 := hget 2 216#64 (by clear * -; bv_omega)
       hi3 := hget 3 220#64 (by clear * -; bv_omega)
       hi4 := hget 4 224#64 (by clear * -; bv_omega)
       hi5 := hget 5 228#64 (by clear * -; bv_omega)
       hi6 := hget 6 232#64 (by clear * -; bv_omega)
       hi7 := hget 7 236#64 (by clear * -; bv_omega)
       ost_eq := host₃
       obl_eq := hobl₃ },
     hs2_1024⟩, hL₃⟩

/-- `HookSatCompress256` sibling of `seg3b_placed_runsTo` (`CompressAndDigest.lean:1015`). -/
theorem seg3b_placed_runsTo_sat [LibsignalPlacement] {F : ShaCompress}
    {H : LibsignalHooks} (h_compress : HookSatCompress256 H lsCompress256Sym F)
    {key : List (BitVec 8)} {byte : BitVec 8} {s₀ s : State}
    (hpre : HmacPlacedPre F key [byte] s₀) (hs : StateH3cPlaced F key byte s₀ s) :
    RunsTo (lsProg_73 H) s (fun s₄ =>
      StateH4Placed F key byte (s₀.setMem s₄.mem) s₄ ∧
      S2Frame s₀.mem s₄.mem [(s₀.sp - 1024#64, 1024)]) := by
  rcases hs with ⟨hpc, ⟨hstat, hsp_eq, hx29, hx27, hsaved, hframe⟩,
    hx0, hx1, hx2, hlr, hx19, hx20, host, hoblk⟩
  have hrw_stack1024 : RW s.mem (s₀.sp - 1024#64) 1024 :=
    (hframe.rw_iff _ _).mpr hpre.rw_stack
  have hrw_hsp : RW s.mem (hsp s₀) 480 :=
    hrw_stack1024.sub (by unfold hsp; clear * -; bv_omega)
  have hsp_sub176 : hsp s₀ - 176#64 = s₀.sp - 656#64 := by unfold hsp; bv_omega
  have hrw_slack : RW s.mem (s₀.sp - 656#64) 176 :=
    hrw_stack1024.sub (by clear * -; bv_omega)
  have hsp_al : (s.sp &&& 15#64) = 0#64 := by
    rw [hsp_eq]; exact hsp_align hpre.sp_aligned
  have hoblk_len : (outerBlock (digestBytes (innerDigest F key byte))).length = 64 := by
    unfold outerBlock; simp [digestBytes_length, toBEBytes_8_eq_list]
  refine hmacRunsToFrom_of_hkdf (s2_compress256_step_placed_of_hookSat h_compress.toHookSat
    (stPtr := hsp s₀ + 248#64) (blkPtr := hsp s₀ + 304#64) (lr := (blkPl_73).base + 620#64)
    (st := outerState F key) (blk := outerBlock (digestBytes (innerDigest F key byte)))
    (hrun := hstat) (hpc := hpc) (hx0 := hx0) (hx1 := hx1) (hx2 := hx2) (hlr := hlr)
    (hsp_al := hsp_al) (hst := host) (hblk := hoblk) (hlen := hoblk_len)
    (hrw_st := hrw_hsp.sub (by clear * -; bv_omega))
    (hrw_stk := by rw [hsp_eq, hsp_sub176]; exact hrw_slack)
    (hread_blk := readable_of_rw (hrw_hsp.sub (by clear * -; bv_omega)))
    (hdisj_st_stk := by rw [hsp_eq, hsp_sub176]; clear * -; unfold hsp DisjointRegions; bv_omega)
    (hdisj_st_blk := by clear * -; unfold DisjointRegions; bv_omega)
    (hdisj_stk_blk := by rw [hsp_eq, hsp_sub176]; clear * -; unfold hsp DisjointRegions; bv_omega)
    (htr_s := ⟨rfl, rfl⟩)
    fun s₄ htr₄ hpc₄ hstat₄ hcc₄ _ _ _ hst₄ hs2 _ => ?_)
  intro hL₄
  have hs2' : S2Frame s.mem s₄.mem [(hsp s₀ + 248#64, 32), (s₀.sp - 656#64, 176)] := by
    simpa only [hsp_eq, hsp_sub176] using hs2
  have hs2_1024 : S2Frame s₀.mem s₄.mem [(s₀.sp - 1024#64, 1024)] := by
    refine (s2Frame_of_hmacFrame hframe).trans (hs2'.mono fun a ha r hr => ?_)
    have hstk := ha (s₀.sp - 1024#64, 1024) (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      (dsimp only [OutsideRegion, hsp] at hstk ⊢; clear * - hstk; bv_omega)
  have hget (i : Fin 8) (off : BitVec 64)
      (hoff : hsp s₀ + off = (hsp s₀ + 248#64) + BitVec.ofNat 64 (4 * i.val)) :
      s₄.mem.read32 (hsp s₀ + off) = (outerDigest F key byte).get i := by
    rw [hoff]; exact read32_of_readBytes_shaStateBytes hst₄ i
  exact ⟨s₄, .refl s₄, htr₄,
    ⟨{ pc_eq := hpc₄
       common :=
         { status := hstat₄
           sp_eq := (CallingConventionPreserved.sp_eq hcc₄).trans hsp_eq
           x29_eq := (CallingConventionPreserved.x29 hcc₄).trans hx29
           x27_eq := (CallingConventionPreserved.x27 hcc₄).trans hx27
           saved := hmacSaved_of_s2Frame
             (hrw_hsp.sub (by clear * -; unfold hsp; simp only [State.sp_setMem]; bv_omega)) hsaved hs2' (by
             intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
             rcases hr with rfl | rfl <;>
               (try dsimp only; clear * -; unfold hsp; simp only [State.sp_setMem]; unfold DisjointRegions; bv_omega))
           frame := Frame.refl s₄.mem _ }
       x19_eq := (CallingConventionPreserved.x19 hcc₄).trans hx19
       x20_eq := (CallingConventionPreserved.x20 hcc₄).trans hx20
       ho0 := hget 0 248#64 (by clear * -; bv_omega)
       ho1 := hget 1 252#64 (by clear * -; bv_omega)
       ho2 := hget 2 256#64 (by clear * -; bv_omega)
       ho3 := hget 3 260#64 (by clear * -; bv_omega)
       ho4 := hget 4 264#64 (by clear * -; bv_omega)
       ho5 := hget 5 268#64 (by clear * -; bv_omega)
       ho6 := hget 6 272#64 (by clear * -; bv_omega)
       ho7 := hget 7 276#64 (by clear * -; bv_omega) },
     hs2_1024⟩, hL₄⟩

/-- Composes `seg2` + `seg3` + `seg4` from `StateH2Placed` under `HookSatCompress256`. -/
theorem hmac_tail_placed_runsTo_sat [LibsignalPlacement] {F : ShaCompress}
    {H : LibsignalHooks} (h_compress : HookSatCompress256 H lsCompress256Sym F)
    {key : List (BitVec 8)} {byte : BitVec 8} {s₀ s : State}
    (hpre : HmacPlacedPre F key [byte] s₀)
    (hread_key : s₀.mem.Readable (s₀.readReg64 .x1) 32)
    (hs : StateH2Placed F key byte s₀ s) :
    RunsTo (lsProg_73 H) s (fun s₅ =>
      s₅.pc = s₀.readReg64 .lr ∧
      s₅.status = .Running ∧
      CalleeSaved s₀ s₅ ∧
      s₅.mem.readBytes (s₀.readReg64 .x0) 32 = hmacWith F key [byte] ∧
      S2Frame s₀.mem s₅.mem [(s₀.readReg64 .x0, 32), (s₀.sp - 1024#64, 1024)]) := by
  refine (seg2a_placed_runsTo hpre hs).trans fun s₂c h2c => ?_
  refine (seg2b_placed_runsTo_sat h_compress hpre h2c).trans fun s₃ ⟨h3, hf03⟩ => ?_
  obtain ⟨hpre₃, hread_key₃⟩ := hmacPlacedPre_of_s2Frame hpre hread_key hf03
  refine (seg3a_placed_runsTo hpre₃ h3).trans fun s₃c h3c => ?_
  refine (seg3b_placed_runsTo_sat h_compress hpre₃ h3c).trans fun s₄ ⟨h4, hf34⟩ => ?_
  have hf04 := hf03.trans hf34
  obtain ⟨hpre₄, _⟩ := hmacPlacedPre_of_s2Frame hpre hread_key hf04
  refine (seg4_placed_runsTo hpre₄ h4).mono fun s₅ h5 => ?_
  rcases h5 with ⟨hpc₅, hstat₅, hcs₅, hout₅, hfr₅⟩
  have hf04_widen : S2Frame s₀.mem s₄.mem [(s₀.readReg64 .x0, 32), (s₀.sp - 1024#64, 1024)] :=
    hf04.mono fun a ha r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact ha _ (by simp)
  exact ⟨hpc₅, hstat₅, hcs₅, hout₅, hf04_widen.trans (s2Frame_of_hmacFrame hfr₅)⟩

end LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigestExact
