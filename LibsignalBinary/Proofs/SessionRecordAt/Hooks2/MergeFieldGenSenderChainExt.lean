/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsX -- proof-setup: allow-public-import
import ProofLib
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenSenderChain
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeSenderChainAux.Fetch
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

public section

set_option autoImplicit false
/-!
# `SessionStructure::merge_field` Tag 6 (`sender_chain`)

Verifies `SessionStructure::merge_field` (`0x5ca4`, Block `15`) on protobuf tag 6
(`sender_chain`) on `SP2Ext` and under relocatable `[LibsignalPlacement]`.
-/

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenSenderChain

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization (allocPanic)
open Proofs.libsignal.Hooks2

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite isCalleeSavedVReg

@[local arm64_norm, local wp_norm]
private theorem calleeSavedVRegs_setPC_pre_mf6g (s : State) (v : BitVec 64) :
    calleeSavedVRegs (s.setPC v) = calleeSavedVRegs s := rfl

@[local arm64_norm, local wp_norm]
private theorem calleeSavedVRegs_setMem_setPC_pre_mf6g (s : State) (v : BitVec 64) (m : Memory) :
    calleeSavedVRegs ((s.setPC v).setMem m) = calleeSavedVRegs s := rfl

@[local arm64_norm]
private theorem bv_add_neg240_mf6g (sp0 : BitVec 64) :
    sp0 + bv% (2 ^ 64 - 240) = sp0 - 240#64 := by
  simp only [BitVec.sub_eq_add_neg]
  rfl

-- Pre-indexed load (`ldr x8, [x1, #0x90]!` at +0x10c) applies `setPC` before reading/writing
-- registers; commute register/SP reads past `setPC` and `setMem`.
@[local arm64_norm, local wp_norm]
private theorem sp_setPC_pre_mf6g (s : State) (v : BitVec 64) : (s.setPC v).sp = s.sp := rfl

@[local arm64_norm, local wp_norm]
private theorem sp_setMem_setPC_pre_mf6g (s : State) (v : BitVec 64) (m : Memory) :
    ((s.setPC v).setMem m).sp = s.sp := rfl

@[local arm64_norm, local wp_norm]
private theorem readReg64_setPC_pre_mf6g (s : State) (v : BitVec 64) (r : Reg) :
    (s.setPC v).readReg64 r = s.readReg64 r := rfl

@[local arm64_norm, local wp_norm]
private theorem readReg64_setMem_setPC_pre_mf6g (s : State) (v : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC v).setMem m).readReg64 r = s.readReg64 r := rfl

@[local arm64_norm, local wp_norm]
private theorem readReg32_setPC_pre_mf6g (s : State) (v : BitVec 64) (r : Reg) :
    (s.setPC v).readReg32 r = s.readReg32 r := rfl

@[local arm64_norm, local wp_norm]
private theorem readReg32_setMem_setPC_pre_mf6g (s : State) (v : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC v).setMem m).readReg32 r = s.readReg32 r := rfl

@[local arm64_norm, local wp_norm]
private theorem readReg_setPC_pre_mf6g (s : State) (v : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC v).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm, local wp_norm]
private theorem readReg_setMem_setPC_pre_mf6g (s : State) (v : BitVec 64) (m : Memory)
    (w : RegWidth) (r : Reg) :
    ((s.setPC v).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

private theorem sepWPp_mono_pre_mf6g {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : P ⊢ P') (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  exact h R (Satisfies.mono (sepConj_mono_left hent) hm) hL

private theorem sepWPp_drop_left_mf6g {prog : Program} {ret : BitVec 64} {s : State}
    {P1 P2 : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P2 Q Qp) :
    SepWPp prog ret s (P1 ∗ P2) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  exact h _ (Satisfies.of_sep_right hm) hL

private theorem setWidth8_setWidth64_setWidth32_mf6g (v : BitVec 64) :
    (((v.setWidth 32).setWidth 64).setWidth 8) = v.setWidth 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  omega

private theorem genField_eq_sender_of_tag_eq_6 {fl : GenField} (h : fl.tag = 6) :
    ∃ c : ChainG, fl = .sender c := by
  cases fl <;> simp [GenField.tag] at h
  rename_i c
  exact ⟨c, rfl⟩

theorem stackAt_mergeFieldStack_split_senderChain_extW (sp0 : BitVec 64) :
    stackAt sp0 mergeFieldStackX =
      stackAt (sp0 - 80#64) 32688 ∗
        (∃∗ w80 : BitVec 64, ∃∗ w72 : BitVec 64, ∃∗ w64 : BitVec 64, ∃∗ w56 : BitVec 64,
         ∃∗ w48 : BitVec 64, ∃∗ w40 : BitVec 64, ∃∗ w32 : BitVec 64, ∃∗ w24 : BitVec 64,
         ∃∗ w16 : BitVec 64, ∃∗ w8 : BitVec 64,
          ((sp0 - 80#64) ↦₆₄ w80) ∗ ((sp0 - 72#64) ↦₆₄ w72) ∗
          ((sp0 - 64#64) ↦₆₄ w64) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
          ((sp0 - 48#64) ↦₆₄ w48) ∗ ((sp0 - 40#64) ↦₆₄ w40) ∗
          ((sp0 - 32#64) ↦₆₄ w32) ∗ ((sp0 - 24#64) ↦₆₄ w24) ∗
          ((sp0 - 16#64) ↦₆₄ w16) ∗ ((sp0 - 8#64) ↦₆₄ w8)) := by
  have heq : mergeFieldStackX = 32688 + 8 * 10 := rfl
  rw [heq, LibsignalTripleRatchet.stackAt_split_cells sp0 32688 10 (by decide)]
  simp (disch := decide) only [cells, sepConj_emp, bv_sub_add_lit, sepExists_sepConj_right]

theorem stackAt_32688_to_chainMerge_senderChain_extW (sp0 : BitVec 64) :
    stackAt (sp0 - 80#64) 32688 =
      memRegion (sp0 - 32768#64) 3856 ∗
        memRegion (sp0 - 240#64) 160 ∗
        stackAt (sp0 - 240#64) chainMergeStackX := by
  change memRegion ((sp0 - 80#64) - 32688#64) 32688 =
    memRegion (sp0 - 32768#64) 3856 ∗
      memRegion (sp0 - 240#64) 160 ∗
      memRegion ((sp0 - 240#64) - 28672#64) 28672
  have ha1 : (sp0 - 80#64) - 32688#64 = sp0 - 32768#64 := by bv_omega
  have ha2 : (sp0 - 32768#64) + 3856#64 = (sp0 - 240#64) - 28672#64 := by bv_omega
  have ha3 : ((sp0 - 240#64) - 28672#64) + 28672#64 = sp0 - 240#64 := by bv_omega
  have hsplit1 := memRegion_split (sp0 - 32768#64) 3856 28832 (by decide)
  rw [show (3856 : Nat) + 28832 = 32688 from rfl,
      show BitVec.ofNat 64 3856 = 3856#64 from rfl, ha2] at hsplit1
  have hsplit2 := memRegion_split ((sp0 - 240#64) - 28672#64) 28672 160 (by decide)
  rw [show (28672 : Nat) + 160 = 28832 from rfl,
      show BitVec.ofNat 64 28672 = 28672#64 from rfl, ha3] at hsplit2
  rw [ha1, hsplit1, hsplit2]
  ac_rfl

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

theorem L1_MergeFieldGenSenderChainExt_Placed : True := trivial

private theorem sepWPp_intro_rodata_byte5_placed_senderChain [LibsignalPlacement]
    {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWPp prog ret s (((lsmpl.ρ mergeFieldRodataSym + 5#64) ↦₈ᵣ 0x32#8) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  refine h R ?_ hL
  rw [sepConj_assoc]
  exact lsro8_intro hcrl.2 (by lsro_addr) (by decide +kernel) hm

private theorem step_mf6g_to_call_core_placed_ext [LibsignalPlacement]
    {H : LibsignalHooks}
    (ss bufRef sp0 w80 w72 w64 w56 w48 w40 w32 w24 w16 w8 : BitVec 64)
    (u1 u2 u3 u4 u5 u6 u7 u8 u9 : BitVec 64)
    {s : State} {P F : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_15).base)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0)
    (halign : sp0 &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = ss)
    (hx1 : (s.readReg64 .x1).setWidth 32 = 6#32)
    (hx2 : (s.readReg64 .x2).setWidth 8 = 2#8)
    (hx3 : s.readReg64 .x3 = bufRef)
    (hx4 : (s.readReg64 .x4).setWidth 32 = 99#32)
    (hP : P = (((lsmpl.ρ mergeFieldRodataSym + 5#64) ↦₈ᵣ 0x32#8) ∗
      (((ss + 0x90#64) ↦₆₄ noneCap) ∗
       ((ss + 152#64) ↦₆₄ u1) ∗ ((ss + 160#64) ↦₆₄ u2) ∗
       ((ss + 168#64) ↦₆₄ u3) ∗ ((ss + 176#64) ↦₆₄ u4) ∗
       ((ss + 184#64) ↦₆₄ u5) ∗ ((ss + 192#64) ↦₆₄ u6) ∗
       ((ss + 200#64) ↦₆₄ u7) ∗ ((ss + 208#64) ↦₆₄ u8) ∗
       ((ss + 216#64) ↦₆₄ u9) ∗ memRegion (ss + 224#64) 24) ∗
      (((sp0 - 80#64) ↦₆₄ w80) ∗ ((sp0 - 72#64) ↦₆₄ w72) ∗
       ((sp0 - 64#64) ↦₆₄ w64) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
       ((sp0 - 48#64) ↦₆₄ w48) ∗ ((sp0 - 40#64) ↦₆₄ w40) ∗
       ((sp0 - 32#64) ↦₆₄ w32) ∗ ((sp0 - 24#64) ↦₆₄ w24) ∗
       ((sp0 - 16#64) ↦₆₄ w16) ∗ ((sp0 - 8#64) ↦₆₄ w8)) ∗ F))
    (hnext : ∀ s1 : State,
      s1.pc = lsmpl.base 11 →
      s1.status = .Running →
      s1.sp = sp0 - 240#64 →
      s1.trace = s.trace →
      s1.readReg64 .lr = (blkPl_15).base + 328#64 →
      (s1.readReg64 .x0).setWidth 8 = 2#8 →
      s1.readReg64 .x1 = ss + 0x90#64 →
      s1.readReg64 .x2 = bufRef →
      (s1.readReg64 .x3).setWidth 32 = 99#32 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      post s1 (((lsmpl.ρ mergeFieldRodataSym + 5#64) ↦₈ᵣ 0x32#8) ∗
        prostChainGAt A0 (ss + 0x90#64) ChainG.empty ∗ savedRegs_senderChain sp0 w56 s ∗ F)) :
    SepWP (lsProg_15 H) (lsmpl.base 11) s P post := by
  subst hP
  have hx1' : s.readReg32 (Reg.gpr 1#5) = 6#32 := hx1
  have hx4' : s.readReg32 (Reg.gpr 4#5) = 99#32 := hx4
  have hnoneCap : noneCap = 0xffffffffffffffff#64 := rfl
  rw [hnoneCap]
  wp_steps
  apply SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (default_cells_entail_prostChainGAt A0 ss)))
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  refine hnext _ (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    ?_ (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
  have h0 : (((s.readReg64 (Reg.gpr 2#5)).setWidth 32).setWidth 64).setWidth 8 = 2#8 := by
    rw [setWidth8_setWidth64_setWidth32_mf6g]
    exact hx2
  simpa only [wp_norm, arm64_norm] using h0

private theorem step_mf6g_to_call_placed_extW [LibsignalPlacement]
    {H : LibsignalHooks}
    (ss bufRef sp0 : BitVec 64)
    {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_15).base)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0)
    (halign : sp0 &&& 15#64 = 0#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = ss)
    (hx1 : BitVec.setWidth 32 (s.readReg64 .x1) = 6#32)
    (hx2 : (s.readReg64 .x2).setWidth 8 = 2#8)
    (hx3 : s.readReg64 .x3 = bufRef)
    (hx4 : (s.readReg64 .x4).setWidth 32 = 99#32)
    (hP : P = ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96 ∗
      F ∗ stackAt sp0 mergeFieldStackX)
    (hnext : ∀ (s1 : State) (w56 : BitVec 64),
      s1.pc = lsmpl.base 11 →
      s1.status = .Running →
      s1.sp = sp0 - 240#64 →
      s1.trace = s.trace →
      s1.readReg64 .lr = (blkPl_15).base + 328#64 →
      (s1.readReg64 .x0).setWidth 8 = 2#8 →
      s1.readReg64 .x1 = ss + 0x90#64 →
      s1.readReg64 .x2 = bufRef →
      (s1.readReg64 .x3).setWidth 32 = 99#32 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      LibsignalCodeRoLoaded lsmpl s1.mem →
      SepWPp (lsProg_15 H) (s.readReg64 .lr) s1
        (prostChainGAt A0 (ss + 0x90#64) ChainG.empty ∗
         stackAt (sp0 - 80#64) 32688 ∗ savedRegs_senderChain sp0 w56 s ∗ F) Q Qp) :
    SepWPp (lsProg_15 H) (s.readReg64 .lr) s P Q Qp := by
  subst hP
  rw [stackAt_mergeFieldStack_split_senderChain_extW sp0, memRegion96_sender_split_senderChain ss]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun w80 => SepWPp.exists_elim fun w72 =>
    SepWPp.exists_elim fun w64 => SepWPp.exists_elim fun w56 =>
    SepWPp.exists_elim fun w48 => SepWPp.exists_elim fun w40 =>
    SepWPp.exists_elim fun w32 => SepWPp.exists_elim fun w24 =>
    SepWPp.exists_elim fun w16 => SepWPp.exists_elim fun w8 =>
    SepWPp.exists_elim fun u9 => SepWPp.exists_elim fun u8 =>
    SepWPp.exists_elim fun u7 => SepWPp.exists_elim fun u6 =>
    SepWPp.exists_elim fun u5 => SepWPp.exists_elim fun u4 =>
    SepWPp.exists_elim fun u3 => SepWPp.exists_elim fun u2 =>
    SepWPp.exists_elim fun u1 => ?_
  apply sepWPp_intro_rodata_byte5_placed_senderChain hcrl
  apply LibsignalTripleRatchet.sepWPp_seq_lscro (mid := lsmpl.base 11) hcrl
  refine step_mf6g_to_call_core_placed_ext ss bufRef sp0
    w80 w72 w64 w56 w48 w40 w32 w24 w16 w8 u1 u2 u3 u4 u5 u6 u7 u8 u9
    (F := stackAt (sp0 - 80#64) 32688 ∗ F)
    hpc hrun hsp halign hx0 hx1 hx2 hx3 hx4 (by ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hlr1 hx0_1 hx1_1 hx2_1 hx3_1 hx26_1 hx27_1 hx28_1 hvregs1 hcrl1
  apply sepWPp_drop_left_mf6g
  refine sepWPp_mono_pre_mf6g (Entails.of_eq (by ac_rfl))
    (hnext s1 w56 hpc1 hrun1 hsp1 htr1 hlr1 hx0_1 hx1_1 hx2_1 hx3_1 hx26_1 hx27_1 hx28_1 hvregs1 hcrl1)

private theorem step_mf6g_epilogue_placed_extW [LibsignalPlacement]
    {H : LibsignalHooks}
    (c : ChainG) (w56 : BitVec 64)
    {P_fld : GenField → Prop} {x : MergeFieldGenGhost} {R : SepProp}
    {s0 s : State} {P : SepProp}
    (hfl : x.fld = .sender c)
    (hpc : s.pc = (blkPl_15).base + 328#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 240#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hP : P = prostChainGAt A0 (x.ss + 0x90#64) c ∗ prostSSGRest A0 x.ss x.v ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
      stackAt (s0.sp - 80#64) 32688 ∗ savedRegs_senderChain s0.sp w56 s0) :
    SepWPp (lsProg_15 H) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (mergeFieldGenPlacedSpecW P_fld).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (mergeFieldGenPlacedSpecW P_fld).onPanic x s0 sf ∗ R)) := by
  subst hP
  unfold savedRegs_senderChain
  have hsp_align240 := sp_sub_240_aligned_senderChain halign
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have hx26' : s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := hx28
  apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine ⟨?_, by simp only [arm64_norm, *],
    ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
     by simp only [arm64_norm, *], by simp only [arm64_norm, *],
     by simp only [arm64_norm, *], by simp only [arm64_norm, *],
     by simp only [arm64_norm, *], by simp only [arm64_norm, *],
     by simp only [arm64_norm, *], by simp only [arm64_norm, *],
     by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩⟩
  intro hm
  simp only [mergeFieldGenRawSpecW, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩, ?_⟩
  rw [hfl, prostSSGAt_sender_some_eq A0 x.ss x.v c, stackAt_mergeFieldStack_split_senderChain_extW s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
  refine ⟨s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
    s0.readReg64 (Reg.gpr 25#5), w56,
    s0.readReg64 (Reg.gpr 24#5), s0.readReg64 (Reg.gpr 23#5),
    s0.readReg64 (Reg.gpr 22#5), s0.readReg64 (Reg.gpr 21#5),
    s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5), ?_⟩
  rw [← hfl]
  convert hm using 1
  ac_rfl

/-- Relocatable `SessionStructure::merge_field` (Block `15`, `lsProg_15 H`) on tag 6
(`sender_chain`) at `mergeFieldStackX`. -/
theorem mergeFieldGenSenderChain_placed_okW [LibsignalPlacement]
    (H : LibsignalHooks)
    (hC : DeserializeCalleesPlacedW H) (hCh : ChainMergeGenPlacedOkW H) :
    MergeFieldGenPlacedOkW H (fun fl => fl.tag = 6) := by
  let _ := hC
  have hCh' : subroutine_ok (lsProg_15 H) (lsmpl.base 11) chainMergeGenPlacedSpecW :=
    ls_call_ro_of_block (callerProg := lsProg_15 H) hCh
  unfold MergeFieldGenPlacedOkW
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre halign_bool
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned, beq_iff_eq] using halign_bool
  have ⟨hcrl0, hpre_raw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  refine ⟨(mergeFieldGenRawSpecW (fun fl => fl.tag = 6)).pre x s0, R, hpre_raw, ?_⟩
  conv =>
    arg 4
    simp only [mergeFieldGenRawSpecW, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx0, hx1, hx2, hx3, hx4, htag6, hok, hfresh, hlen⟩ => ?_
  obtain ⟨c, hfl⟩ := genField_eq_sender_of_tag_eq_6 htag6
  have hv_none : x.v.sender = none := by
    simpa [hfl, GenField.Fresh] using hfresh
  have hc_ok : c.Ok := by
    rw [hfl, GenField.Ok] at hok
    exact hok.1
  have htag : BitVec.ofNat 32 x.fld.tag = 6#32 := by rw [hfl]; rfl
  have hwt : BitVec.ofNat 8 x.fld.wt.toNat = 2#8 := by rw [hfl]; rfl
  rw [htag] at hx1
  rw [hwt] at hx2
  rw [prostSSGAt_sender_none_eq A0 x.ss x.v hv_none]
  refine step_mf6g_to_call_placed_extW x.ss x.bufRef s0.sp
    (F := prostSSGRest A0 x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail))
    hpc hrun rfl halign hcrl0 hx0 hx1 hx2 hx3 hx4 (by ac_rfl) ?_
  intro s1 w56 hpc1 hrun1 hsp1 htr1 hlr1 hx0_1 hx1_1 hx2_1 hx3_1 hx26_1 hx27_1 hx28_1 hvregs1 hcrl1
  have hsp1_aligned : s1.spAligned = true := by
    simp only [State.spAligned, hsp1, beq_iff_eq]
    exact sp_sub_240_aligned_senderChain halign
  have hpay : x.fld.payload ++ x.tail = c.payload ++ x.tail := by
    rw [hfl, GenField.payload]
  refine SepWPp.call_lscro
    (x := ChainMergeGenGhost.mk (x.ss + 0x90#64) c x.bufRef x.slot x.ptr x.tail)
    (F := prostSSGRest A0 x.ss x.v ∗
      memRegion (s0.sp - 32768#64) 3856 ∗
      memRegion (s0.sp - 240#64) 160 ∗
      savedRegs_senderChain s0.sp w56 s0)
    hCh' hpc1 hrun1 hsp1_aligned hcrl1 hlr1 ?_ ?_ ?_ ?_
  · intro R' hm
    rw [stackAt_32688_to_chainMerge_senderChain_extW s0.sp, hpay] at hm
    simp only [chainMergeGenRawSpecW, hsp1, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_1, hx1_1, hx2_1, hx3_1, hc_ok, hpay ▸ hlen⟩, ?_⟩
    convert hm using 1
    ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [chainMergeGenRawSpecW, allocPanic, allocFailedIn, htr1] at hm ⊢
    exact allowPanic_frame id hm
  · intro s2 hpc2 hrun2 hsp2 _hcrl2 hcs2
    rw [hsp1] at hsp2
    conv =>
      arg 4
      simp only [chainMergeGenRawSpecW, hsp1, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨htr2, hx0_2⟩ => ?_
    obtain ⟨_, _, _, _, _, _, _, hx26_2, hx27_2, hx28_2, _, hvregs2⟩ := hcs2
    refine step_mf6g_epilogue_placed_extW c w56 hfl hpc2 hrun2 hsp2 halign
      (htr2.trans htr1) (hvregs2.trans hvregs1) hx0_2 (hx26_2.trans hx26_1) (hx27_2.trans hx27_1) (hx28_2.trans hx28_1) ?_
    rw [stackAt_32688_to_chainMerge_senderChain_extW s0.sp, hpay]
    ac_rfl

end Placed

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenSenderChain
