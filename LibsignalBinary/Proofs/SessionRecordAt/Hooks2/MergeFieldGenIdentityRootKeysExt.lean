/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeIdentityRootKeys -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsX -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenIdentityRootKeys
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

public section

set_option autoImplicit false
/-!
# `SessionStructure::merge_field` Tags 2, 3, and 4 (Identity and Root Keys)

Verifies `SessionStructure::merge_field` (`0x5ca4`, Block `15`) on protobuf tags 2
(`local_identity_public`), 3 (`remote_identity_public`), and 4 (`root_key`) on `SP2Ext` and under
relocatable `[LibsignalPlacement]`.
-/

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenIdentityRootKeys

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeSeed.IdentityRootKeysStateSimp
open CryptoVerification.E2E.Record.DeserializeGeneral
open Proofs.libsignal.Hooks2

set_option maxRecDepth 200000
attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  setWidth8_setWidth64_setWidth32_identityRootKeys
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre_identityRootKeys
  sp_setMem_setPC_pre_identityRootKeys
  readReg64_setPC_pre_identityRootKeys
  readReg64_setMem_setPC_pre_identityRootKeys
  readReg32_setPC_pre_identityRootKeys
  readReg32_setMem_setPC_pre_identityRootKeys
  readReg_setPC_pre_identityRootKeys
  readReg_setMem_setPC_pre_identityRootKeys
  calleeSavedVRegs_setPC_pre_identityRootKeys
  calleeSavedVRegs_setMem_setPC_pre_identityRootKeys

/-! ## Pure tag-2/3/4 helpers and `prostSSGAt` decomposition -/

@[expose] def mfUnusedStack_identityRootKeys_extW (sp0 : BitVec 64) : SepProp :=
  memRegion (sp0 - 32768#64) 7648 ∗ memRegion (sp0 - 240#64) 160

set_option maxHeartbeats 1600000 in
theorem stackAt_mergeField_split_identityRootKeys_extW (sp0 : BitVec 64) :
    stackAt sp0 mergeFieldStackX =
      mfUnusedStack_identityRootKeys_extW sp0 ∗ stackAt (sp0 - 240#64) Prost.X.bytesMergeStackW ∗
        (∃∗ w80 : BitVec 64, ∃∗ w72 : BitVec 64, ∃∗ w64 : BitVec 64, ∃∗ w56 : BitVec 64,
         ∃∗ w48 : BitVec 64, ∃∗ w40 : BitVec 64, ∃∗ w32 : BitVec 64, ∃∗ w24 : BitVec 64,
         ∃∗ w16 : BitVec 64, ∃∗ w8 : BitVec 64,
          ((sp0 - 80#64) ↦₆₄ w80) ∗ ((sp0 - 72#64) ↦₆₄ w72) ∗
          ((sp0 - 64#64) ↦₆₄ w64) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
          ((sp0 - 48#64) ↦₆₄ w48) ∗ ((sp0 - 40#64) ↦₆₄ w40) ∗
          ((sp0 - 32#64) ↦₆₄ w32) ∗ ((sp0 - 24#64) ↦₆₄ w24) ∗
          ((sp0 - 16#64) ↦₆₄ w16) ∗ ((sp0 - 8#64) ↦₆₄ w8)) := by
  have h1 := LibsignalTripleRatchet.stackAt_split_cells sp0 32688 10 (by decide)
  change stackAt sp0 mergeFieldStackX = stackAt (sp0 - 80#64) 32688 ∗ cells (sp0 - 80#64) 10 at h1
  have h2 : stackAt (sp0 - 80#64) 32688 =
      mfUnusedStack_identityRootKeys_extW sp0 ∗ stackAt (sp0 - 240#64) Prost.X.bytesMergeStackW := by
    unfold stackAt mfUnusedStack_identityRootKeys_extW
    change memRegion (sp0 - 80#64 - 32688#64) 32688 =
      (memRegion (sp0 - 32768#64) 7648 ∗ memRegion (sp0 - 240#64) 160) ∗
        memRegion (sp0 - 240#64 - 24880#64) 24880
    have hsplit1 := memRegion_split (sp0 - 80#64 - 32688#64) 7648 25040 (by decide)
    have hsplit2 := memRegion_split (sp0 - 80#64 - 32688#64 + 7648#64) 24880 160 (by decide)
    have ha1 : sp0 - 80#64 - 32688#64 = sp0 - 32768#64 := by bv_omega
    have ha2 : sp0 - 80#64 - 32688#64 + 7648#64 = sp0 - 240#64 - 24880#64 := by bv_omega
    have ha3 : sp0 - 240#64 - 24880#64 + 24880#64 = sp0 - 240#64 := by bv_omega
    rw [show (32688 : Nat) = 7648 + 25040 by rfl, hsplit1,
      show (25040 : Nat) = 24880 + 160 by rfl, hsplit2, ha2, ha1, ha3]
    sep_eq
  have hc10 : cells (sp0 - 80#64) 10 =
      (∃∗ w80 : BitVec 64, ∃∗ w72 : BitVec 64, ∃∗ w64 : BitVec 64, ∃∗ w56 : BitVec 64,
       ∃∗ w48 : BitVec 64, ∃∗ w40 : BitVec 64, ∃∗ w32 : BitVec 64, ∃∗ w24 : BitVec 64,
       ∃∗ w16 : BitVec 64, ∃∗ w8 : BitVec 64,
        ((sp0 - 80#64) ↦₆₄ w80) ∗ ((sp0 - 72#64) ↦₆₄ w72) ∗
        ((sp0 - 64#64) ↦₆₄ w64) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
        ((sp0 - 48#64) ↦₆₄ w48) ∗ ((sp0 - 40#64) ↦₆₄ w40) ∗
        ((sp0 - 32#64) ↦₆₄ w32) ∗ ((sp0 - 24#64) ↦₆₄ w24) ∗
        ((sp0 - 16#64) ↦₆₄ w16) ∗ ((sp0 - 8#64) ↦₆₄ w8)) := by
    cells_unfold
  rw [h1, h2, hc10, sepConj_assoc]

set_option maxHeartbeats 1600000 in
theorem stackAt_mergeField_unsplit_identityRootKeys_extW (sp0 : BitVec 64) (s0 : State) (w56 : BitVec 64) :
    mfUnusedStack_identityRootKeys_extW sp0 ∗ stackAt (sp0 - 240#64) Prost.X.bytesMergeStackW ∗
      mfSavedRegs_identityRootKeys sp0 s0 w56 ⊢ stackAt sp0 mergeFieldStackX := by
  rw [stackAt_mergeField_split_identityRootKeys_extW sp0]
  refine sepConj_mono_right (sepConj_mono_right ?_)
  unfold mfSavedRegs_identityRootKeys
  exact Entails.sepExists_right (s0.readReg64 .x29)
    (Entails.sepExists_right (s0.readReg64 .x30)
    (Entails.sepExists_right (s0.readReg64 .x25)
    (Entails.sepExists_right w56
    (Entails.sepExists_right (s0.readReg64 .x24)
    (Entails.sepExists_right (s0.readReg64 .x23)
    (Entails.sepExists_right (s0.readReg64 .x22)
    (Entails.sepExists_right (s0.readReg64 .x21)
    (Entails.sepExists_right (s0.readReg64 .x20)
    (Entails.sepExists_right (s0.readReg64 .x19) (Entails.of_eq (by ac_rfl)))))))))))

private def prostSSGRest_identityRootKeysA (A : RustAlloc) (ss : BitVec 64) (v : SSG) : SepProp :=
  vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.recv ∗
    vecU8 A (ss + 0x60#64) [] ∗ vecU8 A (ss + 0x78#64) [] ∗
    (match v.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    (match v.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗ ((ss + 0x110#64) ↦₃₂ 0#32) ∗
         memRegion (ss + 0x114#64) 4 ∗ ((ss + 0x118#64) ↦₆₄ 0#64) ∗
         ((ss + 0x120#64) ↦₃₂ 0#32) ∗ memRegion (ss + 0x124#64) 4) ∗
    ((ss + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x130#64) 24 ∗
    ((ss + 0x148#64) ↦₃₂ v.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.prevCounter) ∗
    ((ss + 0x150#64) ↦₆₄ 0#64)

private theorem prostSSGAt_eq_split_identityRootKeysA (A : RustAlloc) (ss : BitVec 64) (v : SSG) :
    prostSSGAt A ss v =
      vecU8 A ss v.lik ∗ vecU8 A (ss + 0x18#64) v.rik ∗ vecU8 A (ss + 0x30#64) v.root ∗
        prostSSGRest_identityRootKeysA A ss v := by
  unfold prostSSGAt prostSSGRest_identityRootKeysA
  ac_rfl

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

theorem L1_MergeFieldGenIdentityRootKeysExt_Placed : True := trivial

set_option maxHeartbeats 1600000 in
theorem finish_post_placed_identityRootKeys_gen_extW [LibsignalPlacement]
    (P : GenField → Prop) (x : MergeFieldGenGhost)
    (valPtr w56 : BitVec 64) (b : List (BitVec 8))
    {s0 sf : State} {F_ss R : SepProp}
    (htrf : sf.trace = s0.trace)
    (hx0f : sf.readReg64 .x0 = 0#64)
    (hpay : x.fld.payload = [BitVec.ofNat 8 b.length] ++ b)
    (hss : vecU8 A0 valPtr b ∗ F_ss = prostSSGAt A0 x.ss (x.v.apply x.fld))
    (hmf : sf.mem ⊨
      (mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          stackAt (s0.sp - 240#64) Prost.X.bytesMergeStackW ∗
          vecU8 A0 valPtr b ∗
          Prost.sliceCursorAfter x.slot x.ptr ([BitVec.ofNat 8 b.length] ++ b ++ x.tail) x.tail ∗
          (F_ss ∗ mfUnusedStack_identityRootKeys_extW s0.sp ∗ mfRoBytes_placed_identityRootKeys))) ∗ R) :
    sf.mem ⊨ (mergeFieldGenPlacedSpecW P).post x s0 sf ∗ R := by
  have h1 : sf.mem ⊨ mfRoBytes_placed_identityRootKeys ∗
      ((mfUnusedStack_identityRootKeys_extW s0.sp ∗ stackAt (s0.sp - 240#64) Prost.X.bytesMergeStackW ∗
          mfSavedRegs_identityRootKeys s0.sp s0 w56) ∗
        ((vecU8 A0 valPtr b ∗ F_ss) ∗
          (x.bufRef ↦₆₄ x.slot) ∗
          Prost.sliceCursorAfter x.slot x.ptr ([BitVec.ofNat 8 b.length] ++ b ++ x.tail) x.tail ∗
          R)) := by
    convert hmf using 1; sep_eq
  have h2 := Satisfies.of_sep_right h1
  have h3 := Satisfies.mono (sepConj_mono_left (stackAt_mergeField_unsplit_identityRootKeys_extW s0.sp s0 w56)) h2
  rw [hss, ← hpay] at h3
  dsimp only [mergeFieldGenPlacedSpecW, LibsignalTripleRatchet.withLsCodeRoLoaded, mergeFieldGenRawSpecW]
  rw [pure_true_emp_identityRootKeys ⟨htrf, hx0f⟩, emp_sepConj]
  convert h3 using 1; sep_eq

set_option maxHeartbeats 1600000 in
theorem step_bytesMerge_call_placed_identityRootKeys_extW [LibsignalPlacement]
    {H : LibsignalHooks}
    (P : GenField → Prop)
    (hbytes : Prost.X.BytesMergePlacedOkW A0 H)
    (x : MergeFieldGenGhost) (retOff valPtr w56 : BitVec 64)
    (valBs b : List (BitVec 8))
    {s0 sm : State} {F_ss R : SepProp}
    (hret : retOff = 600#64 ∨ retOff = 556#64 ∨ retOff = 460#64)
    (hpcm : sm.pc = lsmpl.base 7)
    (hrunm : sm.status = .Running)
    (hspm : sm.sp = s0.sp - 240#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (hcrlm : LibsignalCodeRoLoaded lsmpl sm.mem)
    (htrm : sm.trace = s0.trace)
    (hlrm : sm.readReg64 .lr = (blkPl_15).base + retOff)
    (hx0m : (sm.readReg64 .x0).setWidth 8 = 2#8)
    (hx1m : sm.readReg64 .x1 = valPtr)
    (hx2m : sm.readReg64 .x2 = x.bufRef)
    (hx26m : sm.readReg64 .x26 = s0.readReg64 .x26)
    (hx27m : sm.readReg64 .x27 = s0.readReg64 .x27)
    (hx28m : sm.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs_m : calleeSavedVRegs sm = calleeSavedVRegs s0)
    (hb_lt : b.length < 128)
    (htail_lt : ([BitVec.ofNat 8 b.length] ++ b ++ x.tail).length < 2 ^ 62)
    (hpay : x.fld.payload = [BitVec.ofNat 8 b.length] ++ b)
    (hss : vecU8 A0 valPtr b ∗ F_ss = prostSSGAt A0 x.ss (x.v.apply x.fld)) :
    SepWPp (lsProg_15 H) (s0.readReg64 .lr) sm
      (vecU8 A0 valPtr valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        Prost.sliceCursorAt x.slot x.ptr ([BitVec.ofNat 8 b.length] ++ b ++ x.tail) ∗
        stackAt (s0.sp - 240#64) Prost.X.bytesMergeStackW ∗
        mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗
        (F_ss ∗ mfUnusedStack_identityRootKeys_extW s0.sp ∗ mfRoBytes_placed_identityRootKeys))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (mergeFieldGenPlacedSpecW P).post x s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic x s0 sf ∗ R)) := by
  have hcall : subroutine_ok (lsProg_15 H) (lsmpl.base 7) (Prost.X.bytesMergePlacedSpecW A0) :=
    ls_call_ro_of_block (callerProg := lsProg_15 H) hbytes
  have hspm_align : sm.spAligned = true := by
    simp only [State.spAligned, hspm, sp_sub_240_aligned_identityRootKeys halign, beq_self_eq_true]
  unfold vecU8
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim (fun cap0 => SepWPp.exists_elim (fun ptr0 => ?_))
  let g : Prost.BytesMergeGhost :=
    ⟨.lengthDelimited, valPtr, cap0, ptr0, valBs, x.bufRef, x.slot, x.ptr,
     [BitVec.ofNat 8 b.length] ++ b ++ x.tail⟩
  refine SepWPp.call_lscro (x := g)
    (F := mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗ (F_ss ∗ mfUnusedStack_identityRootKeys_extW s0.sp ∗ mfRoBytes_placed_identityRootKeys))
    hcall hpcm hrunm hspm_align hcrlm hlrm ?_ ?_ ?_ ?_
  · intro R' hm
    have hpool : A0.pool = emp := rfl
    dsimp only [Prost.X.bytesMergeRawSpecW, g]
    have hp2 : (sm.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 WireType.lengthDelimited.toNat ∧
        sm.readReg64 .x1 = valPtr ∧ sm.readReg64 .x2 = x.bufRef ∧
        ([BitVec.ofNat 8 b.length] ++ b ++ x.tail).length < 2 ^ 62 :=
      ⟨hx0m, hx1m, hx2m, htail_lt⟩
    rw [hspm, hpool, pure_true_emp_identityRootKeys hp2]
    simp only [emp_sepConj]
    convert hm using 1; sep_eq
  · intro sf code R' _ hex
    exact allowPanic_not_exited hex
  · intro sf _ hm
    dsimp only [Prost.X.bytesMergeRawSpecW, Serialization.allocPanic] at hm ⊢
    refine allowPanic_frame (fun ⟨ha, hp⟩ => ?_) hm
    rw [allocFailedIn, htrm] at ha
    rw [htrm] at hp
    exact ⟨ha, hp⟩
  · intro s2 hpc2 hrun2 hsp2 _hcrl2 hcs2
    dsimp only [Prost.X.bytesMergeRawSpecW, g]
    rw [mergeBytes_lengthDelimited_of_lt_128_identityRootKeys hb_lt]
    dsimp only
    rw [sepConj_assoc]
    refine SepWPp.pure_left (fun htr2 => ?_)
    have hpool : A0.pool = emp := rfl
    rw [hpool, hspm]
    simp only [emp_sepConj, sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_left (fun hx0_2 => ?_)
    have hvec : (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64, vecU8At A0 valPtr cap' ptr' b) =
        vecU8 A0 valPtr b := rfl
    rw [hvec]
    refine step_cbz_epilogue_placed_identityRootKeys (H := H) retOff w56
      (F := (x.bufRef ↦₆₄ x.slot) ∗
        stackAt (s0.sp - 240#64) Prost.X.bytesMergeStackW ∗
        vecU8 A0 valPtr b ∗
        Prost.sliceCursorAfter x.slot x.ptr ([BitVec.ofNat 8 b.length] ++ b ++ x.tail) x.tail ∗
        (F_ss ∗ mfUnusedStack_identityRootKeys_extW s0.sp ∗ mfRoBytes_placed_identityRootKeys))
      hret hpc2 hrun2
      (hsp2.trans hspm) halign (htr2.trans htrm) hx0_2
      (hcs2.2.2.2.2.2.2.2.1.trans hx26m)
      (hcs2.2.2.2.2.2.2.2.2.1.trans hx27m)
      (hcs2.2.2.2.2.2.2.2.2.2.1.trans hx28m)
      (hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs_m)
      (by sep_eq) ?_
    intro sf _ _ hspf htrf hx0f hcsf
    exact ⟨finish_post_placed_identityRootKeys_gen_extW P x valPtr w56 b htrf hx0f hpay hss, hspf, hcsf⟩

set_option maxHeartbeats 1600000 in
/-- Relocatable `SessionStructure::merge_field` (Block `15`, `lsProg_15 H`) on tags 2, 3, and 4
(`local_identity_public`, `remote_identity_public`, `root_key`) at `mergeFieldStackX`. -/
theorem mergeFieldGenIdentityRootKeys_placed_okW [LibsignalPlacement]
    (H : LibsignalHooks)
    (hC : DeserializeCalleesPlacedW H) :
    MergeFieldGenPlacedOkW H (fun fl => fl.tag = 2 ∨ fl.tag = 3 ∨ fl.tag = 4) := by
  let P234 : GenField → Prop := fun fl => fl.tag = 2 ∨ fl.tag = 3 ∨ fl.tag = 4
  unfold MergeFieldGenPlacedOkW
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp_align
  have ⟨hcrl0, hpre_raw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  dsimp only [mergeFieldGenRawSpecW] at hpre_raw
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_raw
  rcases hpre_raw with ⟨⟨hx0, hx1, hx2, hx3, _, hP, hok, _, hlen⟩, hmem⟩
  have hmem_ro : s0.mem ⊨
      (mfRoBytes_placed_identityRootKeys ∗ prostSSGAt A0 x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
        Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗
        stackAt s0.sp mergeFieldStackX) ∗ R := by
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
    exact rodata_placed_intro_identityRootKeys hcrl0.2 (by convert hmem using 1; sep_eq)
  refine ⟨mfRoBytes_placed_identityRootKeys ∗ prostSSGAt A0 x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
    Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗ stackAt s0.sp mergeFieldStackX,
    R, hmem_ro, ?_⟩
  rw [stackAt_mergeField_split_identityRootKeys_extW s0.sp, prostSSGAt_eq_split_identityRootKeys x.ss x.v]
  unfold mfRoBytes_placed_identityRootKeys
  simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim (fun w80 => SepWPp.exists_elim (fun w72 =>
    SepWPp.exists_elim (fun w64 => SepWPp.exists_elim (fun w56 =>
      SepWPp.exists_elim (fun w48 => SepWPp.exists_elim (fun w40 =>
        SepWPp.exists_elim (fun w32 => SepWPp.exists_elim (fun w24 =>
          SepWPp.exists_elim (fun w16 => SepWPp.exists_elim (fun w8 => ?_))))))))))
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned] using hsp_align
  have hsp_align240 := sp_sub_240_aligned_identityRootKeys halign
  rcases genField_tag_234_cases hP hok with ⟨b, hfl_eq, hb⟩ | ⟨b, hfl_eq, hb⟩ | ⟨b, hfl_eq, hb⟩
  · have hb_lt : b.length < 128 := by omega
    have hpay : x.fld.payload = [BitVec.ofNat 8 b.length] ++ b := by
      rw [hfl_eq]; dsimp only [GenField.payload]; rw [hb]; rfl
    have htag : x.fld.tag = 2 := by rw [hfl_eq]; rfl
    have hwt : x.fld.wt = .lengthDelimited := by rw [hfl_eq]; rfl
    rw [htag] at hx1
    rw [hwt] at hx2
    rw [hpay] at hlen ⊢
    simp only [arm64_norm] at hx0 hx1 hx2 hx3
    refine LibsignalTripleRatchet.sepWPp_seq_lscro (mid := lsmpl.base 7) hcrl0 ?_
    wp_steps
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    intro hcrlm
    refine SepWPp.congr_pre ?_
      (step_bytesMerge_call_placed_identityRootKeys_extW P234 hC.2.2.1 x 600#64 x.ss w56 x.v.lik b
        (F_ss := vecU8 A0 (x.ss + 0x18#64) x.v.rik ∗ vecU8 A0 (x.ss + 0x30#64) x.v.root ∗
          prostSSGRest_identityRootKeys x.ss x.v)
        (Or.inl rfl)
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        halign hcrlm (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm])
        hb_lt hlen hpay
        (by rw [hfl_eq, prostSSGAt_eq_split_identityRootKeys]; rfl))
    unfold mfSavedRegs_identityRootKeys mfRoBytes_placed_identityRootKeys
    simp only [Reg.x29, Reg.x30, Reg.x25, Reg.x24, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]
    sep_eq
  · have hb_lt : b.length < 128 := by omega
    have hpay : x.fld.payload = [BitVec.ofNat 8 b.length] ++ b := by
      rw [hfl_eq]; dsimp only [GenField.payload]; rw [hb]; rfl
    have htag : x.fld.tag = 3 := by rw [hfl_eq]; rfl
    have hwt : x.fld.wt = .lengthDelimited := by rw [hfl_eq]; rfl
    rw [htag] at hx1
    rw [hwt] at hx2
    rw [hpay] at hlen ⊢
    simp only [arm64_norm] at hx0 hx1 hx2 hx3
    refine LibsignalTripleRatchet.sepWPp_seq_lscro (mid := lsmpl.base 7) hcrl0 ?_
    wp_steps
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    intro hcrlm
    refine SepWPp.congr_pre ?_
      (step_bytesMerge_call_placed_identityRootKeys_extW P234 hC.2.2.1 x 556#64 (x.ss + 0x18#64) w56 x.v.rik b
        (F_ss := vecU8 A0 x.ss x.v.lik ∗ vecU8 A0 (x.ss + 0x30#64) x.v.root ∗
          prostSSGRest_identityRootKeys x.ss x.v)
        (Or.inr (Or.inl rfl))
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        halign hcrlm (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm])
        hb_lt hlen hpay
        (by rw [hfl_eq, prostSSGAt_eq_split_identityRootKeys]; dsimp only [SSG.apply, prostSSGRest_identityRootKeys]; sep_eq))
    unfold mfSavedRegs_identityRootKeys mfRoBytes_placed_identityRootKeys
    simp only [Reg.x29, Reg.x30, Reg.x25, Reg.x24, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]
    sep_eq
  · have hb_lt : b.length < 128 := by omega
    have hpay : x.fld.payload = [BitVec.ofNat 8 b.length] ++ b := by
      rw [hfl_eq]; dsimp only [GenField.payload]; rw [hb]; rfl
    have htag : x.fld.tag = 4 := by rw [hfl_eq]; rfl
    have hwt : x.fld.wt = .lengthDelimited := by rw [hfl_eq]; rfl
    rw [htag] at hx1
    rw [hwt] at hx2
    rw [hpay] at hlen ⊢
    simp only [arm64_norm] at hx0 hx1 hx2 hx3
    refine LibsignalTripleRatchet.sepWPp_seq_lscro (mid := lsmpl.base 7) hcrl0 ?_
    wp_steps
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    intro hcrlm
    refine SepWPp.congr_pre ?_
      (step_bytesMerge_call_placed_identityRootKeys_extW P234 hC.2.2.1 x 460#64 (x.ss + 0x30#64) w56 x.v.root b
        (F_ss := vecU8 A0 x.ss x.v.lik ∗ vecU8 A0 (x.ss + 0x18#64) x.v.rik ∗
          prostSSGRest_identityRootKeys x.ss x.v)
        (Or.inr (Or.inr rfl))
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        halign hcrlm (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm])
        hb_lt hlen hpay
        (by rw [hfl_eq, prostSSGAt_eq_split_identityRootKeys]; dsimp only [SSG.apply, prostSSGRest_identityRootKeys]; sep_eq))
    unfold mfSavedRegs_identityRootKeys mfRoBytes_placed_identityRootKeys
    simp only [Reg.x29, Reg.x30, Reg.x25, Reg.x24, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]
    sep_eq

end Placed

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenIdentityRootKeys
