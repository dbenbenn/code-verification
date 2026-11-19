/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.Loop -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.Alloc
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes`: Top-Level Proof

**Checked by Lean.**

Proves `encode_bytes_ok_ext`, `encode_bytes_ok_x`, and their `[LibsignalPlacement]` counterparts on
Block `417`.
-/

public section

namespace CryptoVerification.SpqrV1.Poly.EncodeBytes

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit bv_add_add_lit BitVec.toNat_zero bv384_toNat
  sp_sub_96_sub_464 sp_sub_560_add_464 sp_sub_96_add_8 sp_sub_96_add_16 sp_sub_96_add_24
  sp_sub_96_add_32 sp_sub_96_add_40 sp_sub_96_add_48 sp_sub_96_add_56 sp_sub_96_add_64
  sp_sub_96_add_72 sp_sub_96_add_80 sp_sub_96_add_88 sp_sub_96_add_96 sp_sub_88_add_8
  sp_sub_80_add_8 sp_sub_72_add_8 sp_sub_64_add_8 sp_sub_56_add_8 sp_sub_48_add_8
  sp_sub_40_add_8 sp_sub_32_add_8 sp_sub_24_add_8 sp_sub_16_add_8
section Placed
open CryptoVerification.SpqrV1.Alloc
variable [LibsignalPlacement]

theorem encode_bytes_finish_ok_placed {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpySpec)
    (s0 s : State) (fsp out : BitVec 64)
    (hfsp : fsp = s0.sp - 560#64) (pins : List VecPin) (pts : List Point)
    (hpins_len : pins.length = 16) (hpts_len : pts.length = 16)
    (hpts_bound : ∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)
    (Frame : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_417).base + 668#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (pointListPinAt A (fsp + 72#64) pins pts ∗ memRegion out polyEncoderSize ∗
        cells fsp 9 ∗ memRegion (fsp + 456#64) 8 ∗ savedCells s0 ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sf Pf =>
        (Pf ⊢ resultPolyEncoderAt A out (.ok { idx := 0#32, s := .points pts }) ∗
          Frame ∗ stackAt s0.sp encodeBytesStack) ∧
        CalleeSavedPreserved s0 sf ∧ sf.sp = s0.sp ∧ sf.trace = s0.trace) := by
  subst hfsp
  have hlen_eq : pins.length = pts.length := by rw [hpins_len, hpts_len]
  have hbs_len : (pointHeadersBytes pins pts).length = 384 := by
    rw [length_pointHeadersBytes pins pts hlen_eq, hpts_len]
  have hfsp_align : ((s0.sp - 560#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 560#64 hsp0_align
  rw [pointListPinAt_eq_bytes_bufs A ((s0.sp - 560#64) + 72#64) pins pts hlen_eq]
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left (memRegion_out_ok_open out))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro d0; apply SepWP.exists_left; intro d392
  rw [← hbs_len]
  refine seq_clean (mid := (blkPl_417).base + 692#64)
    (P_mid := savedCells s0 ∗ stackAt (s0.sp - 96#64) (allocHookStack + 464) ∗
      (resultPolyEncoderAt A out (.ok { idx := 0#32, s := .points pts }) ∗ Frame))
    (Q := fun sm => sm.sp = s0.sp - 560#64 ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · have hmemcpy : subroutine_ok ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
        (lsρ "memcpy") sessionMemcpySpec :=
      spqr_hook_ok_of_mem hmemcpy_sat
    simp only [sessionMemcpySpec, libcMemcpySpec] at hmemcpy
    wp_steps; wp_apply; wp_steps
    refine align_pre ?_ ?_
    · have hres :
          (out ↦₆₄ 0#64) ∗ (((out + 8#64) ↦ₛ pointHeadersBytes pins pts) ∗ pointBufList A pins pts) ∗
            ((out + 392#64) ↦₃₂ 0#32) ∗ memRegion (out + 396#64) 4 ⊢
          resultPolyEncoderAt A out (.ok { idx := 0#32, s := .points pts }) := by
        rw [← pointListPinAt_eq_bytes_bufs A (out + 8#64) pins pts hlen_eq]
        refine Entails.trans ?_
          (resultPolyEncoderPinnedAt_entails_resultPolyEncoderAt A ⟨pins⟩ out
            (.ok { idx := 0#32, s := .points pts }))
        dsimp only [resultPolyEncoderPinnedAt, polyEncoderPinnedAt, encoderStatePinnedAt,
          polyEncoderPointsTag, polyEncoderVecsOff, polyEncoderIdxOff, polyEncoderPadOff,
          polyEncoderPadSize, NUM_POLYS]
        have hpure : (out ↦₆₄ 0#64) ⊢ ⌜pts.length = 16 ∧ pins.length = 16 ∧
            (∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)⌝ ∗ (out ↦₆₄ 0#64) :=
          Entails.pure_right ⟨hpts_len, hpins_len, hpts_bound⟩ (Entails.refl _)
        exact Entails.trans (sepConj_mono_left hpure) (Entails.of_eq (by ac_rfl))
      have hstk :
          stackAt s.sp 4096 ∗ cells (s0.sp - 560#64) 9 ∗
            ((s0.sp - 488#64) ↦ₛ pointHeadersBytes pins pts) ∗ memRegion (s0.sp - 104#64) 8 ⊢
          stackAt (s0.sp - 96#64) (allocHookStack + 464) := by
        have h1 : ((s0.sp - 488#64) ↦ₛ pointHeadersBytes pins pts) ⊢ memRegion (s0.sp - 488#64) 384 := by
          rw [← hbs_len]; exact pointsToBytes_entails_memRegion _ _
        rw [stackAt_96_split_464 s0.sp, memRegion_464_split_560 s0.sp, ← hsp]
        exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h1))
      exact Entails.trans (Entails.of_eq (by ac_rfl))
        (sepConj_mono_right (sepConj_mono hstk (sepConj_mono_left hres)))
    · wp_done
  · intro s1 hpc1 hrun1 ⟨hsp1, htrace1, hvregs1⟩
    simpa only [sepConj_assoc] using
      encode_bytes_epilogue_placed (ext := ext) s0 s1
        (resultPolyEncoderAt A out (.ok { idx := 0#32, s := .points pts }) ∗ Frame)
        hsp0_align hpc1 hrun1 hsp1 htrace1 hvregs1

theorem encode_bytes_prologue_placed {ext : String → Option (State → State)}
    (s0 : State) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = (blkPl_417).base) (hrun : s0.status = .Running) :
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      ((blkPl_417).base + 40#64) s0
      (stackAt s0.sp encodeBytesStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ savedCells s0 ∗ stackAt (s0.sp - 96#64) (allocHookStack + 464) ∗ Frame) ∧
        sm.sp = s0.sp - 560#64 ∧ sm.readReg64 .x0 = s0.readReg64 .x0 ∧
        sm.readReg64 .x19 = s0.readReg64 .x8 ∧ sm.readReg64 .x21 = s0.readReg64 .x1 ∧
        sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align
  rw [stackAt_encodeBytes_split_96 s0.sp]
  conv => arg 4; rw [sepConj_assoc, sepConj_comm (cells (s0.sp - 96#64) 12) Frame, ← sepConj_assoc,
    sepConj_comm (stackAt (s0.sp - 96#64) (allocHookStack + 464) ∗ Frame) (cells (s0.sp - 96#64) 12)]
  iterate 12 (apply sepWP_cells_succ; intro)
  apply sepWP_cells_zero
  conv => arg 4; simp only [sp_sub_96_add_8, sp_sub_88_add_8, sp_sub_80_add_8, sp_sub_72_add_8,
    sp_sub_64_add_8, sp_sub_56_add_8, sp_sub_48_add_8, sp_sub_40_add_8, sp_sub_32_add_8,
    sp_sub_24_add_8, sp_sub_16_add_8, sepConj_assoc]
  wp_steps
  refine align_pre (by unfold savedCells; exact Entails.of_eq (by ac_rfl)) ?_
  wp_done

theorem encode_bytes_nonempty_body_placed {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpySpec)
    (msg : List (BitVec 8))
    (s0 s : State) (fsp out msgA : BitVec 64) (hfsp : fsp = s0.sp - 560#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (msgRO : Bool)
    (heven : msg.length % 2 = 0) (hpos : 2 ≤ msg.length) (hle : msg.length ≤ 1048576)
    (R : SepProp) (hpc : s.pc = (blkPl_417).base + 96#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = msgA)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 msg.length)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hout : out = s0.readReg64 .x8) :
    SepWPp ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (cells fsp 9 ∗ memRegion (fsp + 72#64) 384 ∗ memRegion (fsp + 456#64) 8 ∗
        savedCells s0 ∗ stackAt fsp allocHookStack ∗ memRegion out polyEncoderSize ∗
        bytesAt msgRO msgA msg ∗ A.pool)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (⌜sf.trace = s0.trace⌝ ∗
              resultPolyEncoderAt A out
                (.ok { idx := 0#32, s := .points (distributeMsgChunksTotal 0 msg (List.replicate 16 { value := [] })) }) ∗
              bytesAt msgRO msgA msg ∗ A.pool ∗ stackAt s0.sp encodeBytesStack) ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeBytesOnPanic s0 sf ∗ R)) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    rw [hfsp]; exact ProofLib.spAligned_sub s0.sp 560#64 hsp0_align
  iterate 9 (apply sepWPp_cells_succ; intro)
  apply sepWPp_cells_zero
  rename_i v0 v1 v2 v3 v4 v5 v6 v7 v8
  conv => arg 4; simp only [bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_assoc]
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (encode_bytes_alloc_0_3_placed h_panic hshim_sat halloc_sat s0 s fsp hfsp_align msg.length hpos hle v5 v6 v7 v8
      ((fsp ↦₆₄ v0) ∗ ((fsp + 8#64) ↦₆₄ v1) ∗ ((fsp + 16#64) ↦₆₄ v2) ∗ ((fsp + 24#64) ↦₆₄ v3) ∗ ((fsp + 32#64) ↦₆₄ v4) ∗
       memRegion (fsp + 72#64) 384 ∗ memRegion (fsp + 456#64) 8 ∗
       savedCells s0 ∗ memRegion out polyEncoderSize ∗ bytesAt msgRO msgA msg)
      R hpc hrun hsp hx21 htrace hvregs ?_)
  intro s1 p0 p1 p2 p3 hp0 hp1 hp2 hp3 hpc1 hrun1 hsp1 hx19_1 hx20_1 hx21_1 htr1 hvr1
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (encode_bytes_alloc_4_7_placed h_panic hshim_sat halloc_sat s0 s1 fsp hfsp_align msg.length hpos hle v1 v2 v3 v4
      ((fsp ↦₆₄ v0) ∗ ((fsp + 40#64) ↦₆₄ p3) ∗ ((fsp + 48#64) ↦₆₄ p2) ∗ ((fsp + 56#64) ↦₆₄ p1) ∗ ((fsp + 64#64) ↦₆₄ p0) ∗
       (A.live p0 msg.length 2 ∗ memRegion p0 msg.length) ∗ (A.live p1 msg.length 2 ∗ memRegion p1 msg.length) ∗
       (A.live p2 msg.length 2 ∗ memRegion p2 msg.length) ∗ (A.live p3 msg.length 2 ∗ memRegion p3 msg.length) ∗
       memRegion (fsp + 72#64) 384 ∗ memRegion (fsp + 456#64) 8 ∗
       savedCells s0 ∗ memRegion out polyEncoderSize ∗ bytesAt msgRO msgA msg)
      R hpc1 hrun1 hsp1 hx21_1 htr1 hvr1 ?_)
  intro s2 p4 p5 p6 p7 hp4 hp5 hp6 hp7 hpc2 hrun2 hsp2 hx19_2 hx20_2 hx21_2 htr2 hvr2
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (encode_bytes_alloc_8_11_placed h_panic hshim_sat halloc_sat s0 s2 fsp hfsp_align msg.length hpos hle
      ((fsp ↦₆₄ v0) ∗ ((fsp + 8#64) ↦₆₄ p7) ∗ ((fsp + 16#64) ↦₆₄ p6) ∗ ((fsp + 24#64) ↦₆₄ p5) ∗ ((fsp + 32#64) ↦₆₄ p4) ∗
       ((fsp + 40#64) ↦₆₄ p3) ∗ ((fsp + 48#64) ↦₆₄ p2) ∗ ((fsp + 56#64) ↦₆₄ p1) ∗ ((fsp + 64#64) ↦₆₄ p0) ∗
       (A.live p0 msg.length 2 ∗ memRegion p0 msg.length) ∗ (A.live p1 msg.length 2 ∗ memRegion p1 msg.length) ∗
       (A.live p2 msg.length 2 ∗ memRegion p2 msg.length) ∗ (A.live p3 msg.length 2 ∗ memRegion p3 msg.length) ∗
       (A.live p4 msg.length 2 ∗ memRegion p4 msg.length) ∗ (A.live p5 msg.length 2 ∗ memRegion p5 msg.length) ∗
       (A.live p6 msg.length 2 ∗ memRegion p6 msg.length) ∗ (A.live p7 msg.length 2 ∗ memRegion p7 msg.length) ∗
       memRegion (fsp + 72#64) 384 ∗ memRegion (fsp + 456#64) 8 ∗
       savedCells s0 ∗ memRegion out polyEncoderSize ∗ bytesAt msgRO msgA msg)
      R hpc2 hrun2 hsp2 hx21_2 htr2 hvr2 ?_)
  intro s3 p8 p9 p10 p11 hp8 hp9 hp10 hp11 hpc3 hrun3 hsp3 hx19_3 hx20_3 hx21_3 hx23_3 hx24_3 hx25_3 hx26_3 htr3 hvr3
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (encode_bytes_alloc_12_15_placed h_panic hshim_sat halloc_sat s0 s3 fsp hfsp_align msg.length hpos hle
      ((fsp ↦₆₄ v0) ∗ ((fsp + 8#64) ↦₆₄ p7) ∗ ((fsp + 16#64) ↦₆₄ p6) ∗ ((fsp + 24#64) ↦₆₄ p5) ∗ ((fsp + 32#64) ↦₆₄ p4) ∗
       ((fsp + 40#64) ↦₆₄ p3) ∗ ((fsp + 48#64) ↦₆₄ p2) ∗ ((fsp + 56#64) ↦₆₄ p1) ∗ ((fsp + 64#64) ↦₆₄ p0) ∗
       (A.live p0 msg.length 2 ∗ memRegion p0 msg.length) ∗ (A.live p1 msg.length 2 ∗ memRegion p1 msg.length) ∗
       (A.live p2 msg.length 2 ∗ memRegion p2 msg.length) ∗ (A.live p3 msg.length 2 ∗ memRegion p3 msg.length) ∗
       (A.live p4 msg.length 2 ∗ memRegion p4 msg.length) ∗ (A.live p5 msg.length 2 ∗ memRegion p5 msg.length) ∗
       (A.live p6 msg.length 2 ∗ memRegion p6 msg.length) ∗ (A.live p7 msg.length 2 ∗ memRegion p7 msg.length) ∗
       (A.live p8 msg.length 2 ∗ memRegion p8 msg.length) ∗ (A.live p9 msg.length 2 ∗ memRegion p9 msg.length) ∗
       (A.live p10 msg.length 2 ∗ memRegion p10 msg.length) ∗ (A.live p11 msg.length 2 ∗ memRegion p11 msg.length) ∗
       memRegion (fsp + 72#64) 384 ∗ memRegion (fsp + 456#64) 8 ∗
       savedCells s0 ∗ memRegion out polyEncoderSize ∗ bytesAt msgRO msgA msg)
      R hpc3 hrun3 hsp3 hx21_3 htr3 hvr3 ?_)
  intro s4 p12 p13 p14 p15 hp12 hp13 hp14 hp15 hpc4 hrun4 hsp4
    hx19_4 hx20_4 hx21_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx22_4 hx0_4 htr4 hvr4
  let cap := BitVec.ofNat 64 (msg.length / 2)
  let pins : List VecPin :=
    [⟨cap, p0⟩, ⟨cap, p1⟩, ⟨cap, p2⟩, ⟨cap, p3⟩, ⟨cap, p4⟩, ⟨cap, p5⟩, ⟨cap, p6⟩, ⟨cap, p7⟩,
     ⟨cap, p8⟩, ⟨cap, p9⟩, ⟨cap, p10⟩, ⟨cap, p11⟩, ⟨cap, p12⟩, ⟨cap, p13⟩, ⟨cap, p14⟩, ⟨cap, p15⟩]
  have hpins_len : pins.length = 16 := rfl
  have hpins_cap : ∀ pin ∈ pins, pin.cap = cap := by
    intro pin hpin; simp only [pins, List.mem_cons, List.not_mem_nil, or_false] at hpin
    rcases hpin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have hhdr := encode_bytes_store_headers_nonempty_placed (A := A) (ext := ext) s0 s4 fsp hfsp_align
    msg.length heven hpos hle v0 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
    hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15
    (memRegion (fsp + 456#64) 8 ∗ savedCells s0 ∗ stackAt fsp allocHookStack ∗
      memRegion out polyEncoderSize ∗ bytesAt msgRO msgA msg ∗ A.pool)
    hpc4 hrun4 hsp4 hx21_4
    (by rw [hx23_4, hx23_3]) (by rw [hx24_4, hx24_3]) (by rw [hx25_4, hx25_3]) (by rw [hx26_4, hx26_3])
    hx27_4 hx28_4 hx22_4 hx0_4 htr4 hvr4
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (sepWPp_seq_clean hhdr ?_)
  intro s5 hpc5 hrun5 ⟨hsp5, hx8_5, hx19_5, hx20_5, htr5, hvr5⟩
  have hx19_s5 : s5.readReg64 .x19 = s0.readReg64 .x8 := by
    rw [hx19_5, hx19_4, hx19_3, hx19_2, hx19_1, hx19, hout]
  have hx20_s5 : s5.readReg64 .x20 = msgA := by
    rw [hx20_5, hx20_4, hx20_3, hx20_2, hx20_1, hx20]
  have hinit_len : (List.replicate 16 ({ value := [] } : Point)).length = 16 := by simp
  have hinit_bound : ∀ pt ∈ (List.replicate 16 ({ value := [] } : Point)), pt.value.length ≤ 0 := by
    intro pt hpt; rw [List.mem_replicate] at hpt; rcases hpt with ⟨_, rfl⟩; simp
  have hloop := encode_bytes_dist_entry_placed (A := A) (ext := ext) msg s0 s5 fsp msgA hfsp_align msgRO
    heven (by omega) (by omega) pins (List.replicate 16 { value := [] })
    hpins_len hinit_len hpins_cap hinit_bound
    (cells fsp 9 ∗ memRegion (fsp + 456#64) 8 ∗ savedCells s0 ∗ stackAt fsp allocHookStack ∗
      memRegion out polyEncoderSize ∗ A.pool)
    hpc5 hrun5 hsp5 hx8_5 hx19_s5 hx20_s5 htr5 hvr5
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (sepWPp_seq_clean hloop ?_)
  intro s6 hpc6 hrun6 ⟨hsp6, hx19_6, htr6, hvr6⟩
  have hpts_len : (distributeMsgChunksTotal 0 msg (List.replicate 16 { value := [] })).length = 16 :=
    (distributeMsgChunks_eq_ok msg 0 (List.replicate 16 { value := [] }) heven hinit_len).2
  have hpts_bound : ∀ pt ∈ distributeMsgChunksTotal 0 msg (List.replicate 16 { value := [] }),
      pt.value.length ≤ 0x0555555555555555 := by
    intro pt hpt
    have h1 := distributeMsgChunksTotal_value_length_le msg 0
      (List.replicate 16 { value := [] }) heven hinit_len hinit_bound pt hpt
    omega
  have hfin := encode_bytes_finish_ok_placed (A := A) hmemcpy_sat s0 s6 fsp out hfsp
    pins (distributeMsgChunksTotal 0 msg (List.replicate 16 { value := [] }))
    hpins_len hpts_len hpts_bound (bytesAt msgRO msgA msg ∗ A.pool)
    hsp0_align hpc6 hrun6 hsp6 (by rw [hx19_6, hout]) htr6 hvr6
  refine SepWPp.of_sepWP (SepWP.mono (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hfin)
    fun sf Pf hpcf hrunf ⟨hPf, hcs, hspf, htrf⟩ => ?_)
  refine SepWPp.done hpcf hrunf ⟨fun hmem_f => Satisfies.mono (sepConj_mono_left ?_) hmem_f, hspf, hcs⟩
  exact Entails.trans hPf (Entails.pure_right htrf (Entails.of_eq (by ac_rfl)))

theorem encode_bytes_empty_body_placed {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpySpec)
    (s0 s : State) (fsp out : BitVec 64)
    (hfsp : fsp = s0.sp - 560#64) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (Frame : SepProp) (hpc : s.pc = (blkPl_417).base + 496#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = 0#64)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (cells fsp 9 ∗ memRegion (fsp + 72#64) 384 ∗ memRegion (fsp + 456#64) 8 ∗
        savedCells s0 ∗ stackAt fsp allocHookStack ∗ memRegion out polyEncoderSize ∗ Frame)
      (fun sf Pf =>
        (Pf ⊢ resultPolyEncoderAt A out
          (.ok { idx := 0#32, s := .points (List.replicate 16 { value := [] }) }) ∗
          Frame ∗ stackAt s0.sp encodeBytesStack) ∧
        CalleeSavedPreserved s0 sf ∧ sf.sp = s0.sp ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by
    rw [hfsp]; exact ProofLib.spAligned_sub s0.sp 560#64 hsp0_align
  have hhdr := encode_bytes_store_headers_empty_placed (A := A) (ext := ext) s0 s fsp hfsp_align
    (cells fsp 9 ∗ memRegion (fsp + 456#64) 8 ∗ savedCells s0 ∗
      stackAt fsp allocHookStack ∗ memRegion out polyEncoderSize ∗ Frame)
    hpc hrun hsp hx21 htrace hvregs
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (seq_clean hhdr ?_)
  intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, htr1, hvr1⟩
  have hpins_len : (List.replicate 16 (⟨0#64, 2#64⟩ : VecPin)).length = 16 := by simp
  have hpts_len : (List.replicate 16 ({ value := [] } : Point)).length = 16 := by simp
  have hpts_bound : ∀ pt ∈ (List.replicate 16 ({ value := [] } : Point)),
      pt.value.length ≤ 0x0555555555555555 := by
    intro pt hpt; rw [List.mem_replicate] at hpt; rcases hpt with ⟨_, rfl⟩; simp
  have hfin := encode_bytes_finish_ok_placed (A := A) hmemcpy_sat s0 s1 fsp out hfsp
    (List.replicate 16 ⟨0#64, 2#64⟩) (List.replicate 16 { value := [] })
    hpins_len hpts_len hpts_bound Frame hsp0_align hpc1 hrun1 hsp1 (by rw [hx19_1, hx19]) htr1 hvr1
  exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hfin

theorem encode_bytes_dispatch_odd_placed {ext : String → Option (State → State)}
    (s : State) (n : Nat) (hodd : n % 2 != 0) (P : SepProp)
    (hpc : s.pc = (blkPl_417).base + 40#64) (hrun : s.status = .Running)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 n) :
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      ((blkPl_417).base + 72#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧ sm.sp = s.sp ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) := by
  have hb32 := tbnz_bit0_of_odd n hodd; have hb64 := tbnz64_bit0_of_odd n hodd
  wp_steps; wp_done

theorem encode_bytes_dispatch_too_long_placed {ext : String → Option (State → State)}
    (s : State) (n : Nat) (heven : n % 2 = 0) (hgt : 1048576 < n) (hlt : n < 2 ^ 64)
    (P : SepProp)
    (hpc : s.pc = (blkPl_417).base + 40#64) (hrun : s.status = .Running)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 n) :
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      ((blkPl_417).base + 52#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧ sm.sp = s.sp ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) := by
  have hb32 := tbnz_bit0_of_even n heven; have hb64 := tbnz64_bit0_of_even n heven
  have hule := bv_ule_1048576_of_gt n hgt hlt
  wp_steps; wp_done

theorem encode_bytes_dispatch_empty_placed {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (blkPl_417).base + 40#64) (hrun : s.status = .Running)
    (hx21 : s.readReg64 .x21 = 0#64) :
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      ((blkPl_417).base + 496#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧ sm.sp = s.sp ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x21 = 0#64 ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) := by
  wp_steps; wp_done

theorem encode_bytes_dispatch_nonempty_placed {ext : String → Option (State → State)}
    (s : State) (n : Nat) (heven : n % 2 = 0) (hpos : 2 ≤ n) (hle : n ≤ 1048576)
    (P : SepProp)
    (hpc : s.pc = (blkPl_417).base + 40#64) (hrun : s.status = .Running)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 n) :
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      ((blkPl_417).base + 96#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧ sm.sp = s.sp ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x0 ∧ sm.readReg64 .x21 = BitVec.ofNat 64 n ∧
        sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) := by
  have hb32 := tbnz_bit0_of_even n heven; have hb64 := tbnz64_bit0_of_even n heven
  have hule := bv_ule_1048576_of_le n hle
  have hne0 := bv_ne_zero_of_pos n (by omega) (by omega)
  wp_steps; wp_done

theorem encode_bytes_placed_ok_ext {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpySpec) :
    EncodeBytesPlacedOkExt A ext := by
  unfold EncodeBytesPlacedOkExt
  apply subroutine_ok_of_sepWPp
  intro ⟨out, msgRO, msgA, msg⟩ R s0 hpc hrun hpre hsp0
  simp only [encodeBytesSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hx1, hlen_lt⟩, hmem⟩
  refine ⟨stackAt s0.sp encodeBytesStack ∗
      (memRegion out polyEncoderSize ∗ bytesAt msgRO msgA msg ∗ A.pool),
    R, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem, ?_⟩
  dsimp only [encodeBytesSpec]
  have hpro := encode_bytes_prologue_placed (ext := ext) s0
    (memRegion out polyEncoderSize ∗ bytesAt msgRO msgA msg ∗ A.pool)
    hsp0 hpc hrun
  refine sepWPp_seq_clean hpro ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx19_1, hx21_1, htr1, hvr1⟩
  have hx19_s1 : s1.readReg64 .x19 = out := by rw [hx19_1, hx8]
  have hx0_s1 : s1.readReg64 .x0 = msgA := by rw [hx0_1, hx0]
  have hx21_s1 : s1.readReg64 .x21 = BitVec.ofNat 64 msg.length := by rw [hx21_1, hx1]
  by_cases hodd : (msg.length % 2 != 0) = true
  · have hres : encodeBytesResult msg = .error (.polynomialError .messageLengthEven) := by
      simp [encodeBytesResult, hodd]
    rw [hres]
    have hdisp := encode_bytes_dispatch_odd_placed (ext := ext) s1 msg.length hodd
      (savedCells s0 ∗ stackAt (s0.sp - 96#64) (allocHookStack + 464) ∗
        (memRegion out polyEncoderSize ∗ bytesAt msgRO msgA msg ∗ A.pool))
      hpc1 hrun1 hx21_s1
    refine sepWPp_seq_clean hdisp ?_
    intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, htr2, hvr2⟩
    have herr := encode_bytes_err_odd_placed (A := A) (ext := ext) s0 s2 out
      (bytesAt msgRO msgA msg ∗ A.pool)
      hsp0 hpc2 hrun2 (by rw [hsp2, hsp1]) (by rw [hx19_2, hx19_s1]) (by rw [htr2, htr1]) (by rw [hvr2, hvr1])
    refine SepWPp.of_sepWP (SepWP.mono (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) herr)
      fun sf Pf hpcf hrunf ⟨hPf, hcs, hspf, htrf⟩ => ?_)
    refine SepWPp.done hpcf hrunf ⟨fun hmem_f => Satisfies.mono (sepConj_mono_left ?_) hmem_f, hspf, hcs⟩
    exact Entails.trans hPf (Entails.pure_right htrf (Entails.of_eq (by ac_rfl)))
  · have heven : msg.length % 2 = 0 := by
      simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hodd; exact hodd
    have hodd_false : (msg.length % 2 != 0) = false := bne_eq_false_iff_eq.mpr heven
    by_cases hlong : msg.length > 1048576
    · have hres : encodeBytesResult msg = .error (.polynomialError .messageLengthTooLong) := by
        simp [encodeBytesResult, hodd_false, NUM_POLYS, CHUNK_SIZE]; omega
      rw [hres]
      have hdisp := encode_bytes_dispatch_too_long_placed (ext := ext) s1 msg.length heven hlong hlen_lt
        (savedCells s0 ∗ stackAt (s0.sp - 96#64) (allocHookStack + 464) ∗
          (memRegion out polyEncoderSize ∗ bytesAt msgRO msgA msg ∗ A.pool))
        hpc1 hrun1 hx21_s1
      refine sepWPp_seq_clean hdisp ?_
      intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, htr2, hvr2⟩
      have herr := encode_bytes_err_too_long_placed (A := A) (ext := ext) s0 s2 out
        (bytesAt msgRO msgA msg ∗ A.pool)
        hsp0 hpc2 hrun2 (by rw [hsp2, hsp1]) (by rw [hx19_2, hx19_s1]) (by rw [htr2, htr1]) (by rw [hvr2, hvr1])
      refine SepWPp.of_sepWP (SepWP.mono (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) herr)
        fun sf Pf hpcf hrunf ⟨hPf, hcs, hspf, htrf⟩ => ?_)
      refine SepWPp.done hpcf hrunf ⟨fun hmem_f => Satisfies.mono (sepConj_mono_left ?_) hmem_f, hspf, hcs⟩
      exact Entails.trans hPf (Entails.pure_right htrf (Entails.of_eq (by ac_rfl)))
    · have hle : msg.length ≤ 1048576 := by omega
      have hres : encodeBytesResult msg =
          .ok { idx := 0#32, s := .points (distributeMsgChunksTotal 0 msg (List.replicate 16 { value := [] })) } := by
        simp [encodeBytesResult, hodd_false, NUM_POLYS, CHUNK_SIZE, hle]
      rw [hres]
      let fsp := s0.sp - 560#64
      have hfsp : fsp = s0.sp - 560#64 := rfl
      have hstk : stackAt (s0.sp - 96#64) (allocHookStack + 464) =
          stackAt fsp allocHookStack ∗ cells fsp 9 ∗ memRegion (fsp + 72#64) 384 ∗ memRegion (fsp + 456#64) 8 := by
        rw [stackAt_96_split_464 s0.sp, ← hfsp, memRegion_464_split fsp]
      rw [hstk]
      by_cases hemp : msg.length = 0
      · have hmsg_nil : msg = [] := List.eq_nil_of_length_eq_zero hemp
        subst hmsg_nil
        simp only [distributeMsgChunksTotal]
        have hx21_zero : s1.readReg64 .x21 = 0#64 := by simpa using hx21_s1
        have hdisp := encode_bytes_dispatch_empty_placed (ext := ext) s1
          (savedCells s0 ∗
            (stackAt fsp allocHookStack ∗ cells fsp 9 ∗ memRegion (fsp + 72#64) 384 ∗ memRegion (fsp + 456#64) 8) ∗
            (memRegion out polyEncoderSize ∗ bytesAt msgRO msgA [] ∗ A.pool))
          hpc1 hrun1 hx21_zero
        refine sepWPp_seq_clean hdisp ?_
        intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx21_2, htr2, hvr2⟩
        have hbody := encode_bytes_empty_body_placed (A := A) hmemcpy_sat s0 s2 fsp out hfsp hsp0
          (bytesAt msgRO msgA [] ∗ A.pool)
          hpc2 hrun2 (by rw [hsp2, hsp1]) (by rw [hx19_2, hx19_s1]) hx21_2 (by rw [htr2, htr1]) (by rw [hvr2, hvr1])
        refine SepWPp.of_sepWP (SepWP.mono (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hbody)
          fun sf Pf hpcf hrunf ⟨hPf, hcs, hspf, htrf⟩ => ?_)
        refine SepWPp.done hpcf hrunf ⟨fun hmem_f => Satisfies.mono (sepConj_mono_left ?_) hmem_f, hspf, hcs⟩
        exact Entails.trans hPf (Entails.pure_right htrf (Entails.of_eq (by ac_rfl)))
      · have hpos : 2 ≤ msg.length := by omega
        have hdisp := encode_bytes_dispatch_nonempty_placed (ext := ext) s1 msg.length heven hpos hle
          (savedCells s0 ∗
            (stackAt fsp allocHookStack ∗ cells fsp 9 ∗ memRegion (fsp + 72#64) 384 ∗ memRegion (fsp + 456#64) 8) ∗
            (memRegion out polyEncoderSize ∗ bytesAt msgRO msgA msg ∗ A.pool))
          hpc1 hrun1 hx21_s1
        refine sepWPp_seq_clean hdisp ?_
        intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx20_2, hx21_2, htr2, hvr2⟩
        have hbody := encode_bytes_nonempty_body_placed h_panic hshim_sat halloc_sat hmemcpy_sat msg s0 s2 fsp out msgA hfsp hsp0 msgRO
          heven hpos hle R hpc2 hrun2 (by rw [hsp2, hsp1])
          (by rw [hx19_2, hx19_s1]) (by rw [hx20_2, hx0_s1]) hx21_2
          (by rw [htr2, htr1]) (by rw [hvr2, hvr1]) hx8.symm
        exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) hbody

theorem encode_bytes_placed_ok_x {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpySpec) :
    EncodeBytesPlacedOkX A ext := by
  unfold EncodeBytesPlacedOkX
  exact encodeBytesSpecX_of_encodeBytesSpec
    (encode_bytes_placed_ok_ext h_panic hshim_sat halloc_sat hmemcpy_sat)

end Placed

end CryptoVerification.SpqrV1.Poly.EncodeBytes
