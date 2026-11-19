/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4Base
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommon -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MessageEncodeCodeSym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Base Step Lemmas for `prost::encoding::varint::encode_varint::<Vec<u8>> [local#2]`

Proves `do_reserve_and_handle [local#2]` call helpers, prologue/epilogue lemmas, and
continuation-byte stages 1..3 and 9 for `encode_varint::<Vec<u8>> [local#2]` (`0x36628`).
-/

public section

namespace CryptoVerification.SpqrV1.Varint

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.SpqrV1.Alloc

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

abbrev encodeVarint2Name : String :=
  "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#2]"

private theorem vecU8At_eq (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (if cap = 0#64 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  simp only [vecU8At, vecHeader, BitVec.ofNat_eq_ofNat]; ac_rfl

theorem do_reserve2_placed_of_raw1 [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {A : RustAlloc} {hookStack : Nat}
    (h : subroutine_ok prog entry (withLsCodeLoaded lsmpl (doReserve1RawSpecWithStack A hookStack))) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl (doReserve2SpecOf ((hookStack + 48) + 64) A)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨hcode0, hpre⟩
  simp only [doReserve2SpecOf, vecU8At_eq, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hbound⟩, ⟨hlen, hcap63, hptr⟩, hmem⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (doReserve1RawSpecWithStack A hookStack)).pre x s0 ∗
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) := by
    dsimp only [withLsCodeLoaded]; rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcode0, ?_⟩; simp only [doReserve1RawSpecWithStack, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlen, hptr, hbound⟩, ?_⟩; rwa [DoReserveNorm.doReserve_pre_repack]
  refine h.mono_outcome x (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, _, hq⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [doReserve1RawSpecWithStack, doReserve2SpecOf, vecU8At_eq] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq; rcases hq with ⟨htrace, hq⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq; rcases hq with ⟨p', hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq; rcases hq with ⟨hp', hmem⟩
    have hlt : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 64 := by dsimp [reserveCap] at hbound ⊢; omega
    have htoNat : (BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)).toNat =
        reserveCap x.cap.toNat x.bs.length x.additional := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    have hlen_le : x.bs.length ≤ reserveCap x.cap.toNat x.bs.length x.additional := by dsimp [reserveCap]; omega
    have hcap_ne : BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional) ≠ 0#64 := by
      intro heq; have := congrArg BitVec.toNat heq; rw [htoNat] at this
      change reserveCap x.cap.toNat x.bs.length x.additional = 0 at this; dsimp [reserveCap] at this; omega
    rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨htrace, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]; refine ⟨p', ?_⟩
    simp only [hcap_ne, ite_false, htoNat]; rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hlen_le, by omega, hp'⟩, ?_⟩; rwa [DoReserveNorm.doReserve_post_repack]
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withLsCodeLoaded, doReserve1RawSpecWithStack, doReserve2SpecOf, doReserveSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hoom).elim

theorem do_reserve2_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_157).rebase (blkPl_157).base H) (blkPl_157).base
      (withLsCodeLoaded lsmpl (doReserve2Spec A)) :=
  do_reserve2_placed_of_raw1 (hookStack := allocHookStack)
    (do_reserve_2_raw1_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve2_placed_ok_x [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) :
    subroutine_ok ((blkPC_157).rebase (blkPl_157).base H) (blkPl_157).base
      (withLsCodeLoaded lsmpl (doReserve2SpecX A)) :=
  do_reserve2_placed_of_raw1 (hookStack := extHookStack)
    (do_reserve_2_raw1_placed_ok_x h_panic hshim halloc hrealloc)

/-- `doReserve2Spec A` entails `doReserve2SpecX A` by framing the unused bottom stack region. -/
theorem doReserve2SpecX_of_doReserve2Spec {P : Program} {addr : BitVec 64} {A : RustAlloc}
    (h : subroutine_ok P addr (doReserve2Spec A)) : subroutine_ok P addr (doReserve2SpecX A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hle : doReserveStack ≤ doReserveStackX := by decide
  have hsplit : stackAt s0.sp doReserveStackX =
      memRegion (s0.sp - BitVec.ofNat 64 doReserveStackX) (doReserveStackX - doReserveStack) ∗
        stackAt s0.sp doReserveStack := by
    have h1 := stackAt_split_bottom s0.sp doReserveStack (doReserveStackX - doReserveStack) (by decide)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 doReserveStackX) (doReserveStackX - doReserveStack) ∗ R
  have hpre' : s0.mem ⊨ (doReserve2Spec A).pre x s0 ∗ R' := by
    dsimp only [doReserve2SpecX, doReserve2Spec, R'] at hpre ⊢; rw [hsplit] at hpre; ac_nf at hpre ⊢
  refine h.mono_outcome x R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [doReserve2SpecX, doReserve2Spec, doReserveSpecX, doReserveSpec, R'] at hpost ⊢; rw [hsplit]; ac_nf at hpost ⊢
  · exact Or.inr (Or.inl ⟨hpan, allowPanic_frame id (by dsimp only [doReserve2Spec, doReserveSpec, R'] at hpost ⊢; rwa [sepConj_assoc])⟩)
  · exact (allowPanic_not_exited hex).elim
  · exact (allowPanic_not_exited hoom).elim

@[expose] def doReserve2SpecWith (resStack : Nat) (s0 : State) (A : RustAlloc) : Spec DoReserveCall where
  pre := fun x s =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜EncVarintCalleeSaved s0 s ∧
      s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧
      newCap + 1 ≤ 2 ^ 63⌝ ∗
    vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp resStack
  post := fun x s0' sf =>
    ⌜sf.trace = s0'.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      vecU8At A x.v (BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)) p' x.bs) ∗
    A.pool ∗ stackAt s0'.sp resStack
  onPanic := fun _ s0' sf => ⌜allocFailedIn s0' sf ∧ s0'.trace <+: sf.trace⌝ ∗ anyHeap

theorem step_doReserve2_call_gen {prog : Program} {resTarget : BitVec 64} {resStack : Nat} (A : RustAlloc)
    {s0 s : State}
    (hdoReserve : subroutine_ok prog resTarget (doReserve2SpecWith resStack s0 A))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hcap_eq : curCap.toNat = curBs.length) (hlen_lt : curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = resTarget) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx2 : s.readReg64 .x2 = 1#64) (hcs_s : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      EncVarintCalleeSaved s0 sm → curBs.length < newCap.toNat → curCap.toNat ≤ newCap.toNat →
      SepWPp prog ret sm
        (((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A newCap p' curBs ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_48_aligned halign
  obtain ⟨hres_bound, hnew_gt, hnew_ge⟩ := reserveCap_bounds hlen_lt
  have hx1_toNat : (s.readReg64 .x1).toNat = curBs.length := by
    rw [hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx2_toNat : (s.readReg64 .x2).toNat = 1 := by rw [hx2]; rfl
  refine SepWPp.call_cs (x := DoReserveCall.mk v curCap curPtr curBs 1) (F := F)
    hdoReserve hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [doReserve2SpecWith, vecU8At_eq_header_sep_buf, vecHeader, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hcs_s, hx0, hx1_toNat, hx2_toNat, ?_⟩, ?_⟩
    · rw [hcap_eq]; exact hres_bound
    · convert hm using 1; ac_rfl
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [doReserve2SpecWith, encodeVarintSpec, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [doReserve2SpecWith, vecU8At_eq_header_sep_buf, vecHeader, hsp, hcap_eq,
      sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun p' => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    have hnew_ge' : curCap.toNat ≤ (BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)).toNat := by
      rw [hcap_eq]; exact hnew_ge
    refine SepWPp.weaken_pre ?_ (hnext sm (BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)) p'
      hpcm hrunm hspm htrm' hcsm.1 hcsm.2.1
      (hcs_s.trans (EncVarintCalleeSaved.of_calleeSavedPreserved hcsm hinv_call))
      hnew_gt hnew_ge')
    exact Entails.of_eq (by ac_rfl)

set_option hygiene false in
local macro "encVarint2_prologue_body " entry:term:max ofCs:term:max csPred:term:max : tactic => `(tactic| (
  subst hP
  apply ($ofCs (mid := if val.ult 128#64 then $entry + 868#64 else $entry + 32#64))
  wp_steps
  apply SepWP.done (by cases val.ult 128#64 <;> simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv_step
  exact hnext _ (by cases val.ult 128#64 <;> simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [$csPred:term, arm64_norm, *, and_self])))
theorem step_encVarint2_prologue_placed [LibsignalPlacement] (H : String → Option (State → State))
    (val v cap ptr sp v48 v40 v32 v24 v16 v8 : BitVec 64) (bs : List (BitVec 8))
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_148).base) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hP : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if val.ult 128#64 then (blkPl_148).base + 868#64 else (blkPl_148).base + 32#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s.trace →
      sm.readReg64 .x0 = val → sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 bs.length → sm.readReg64 .x9 = cap →
      EncVarintCalleeSavedPlaced s sm →
      SepWPp (lsProg_148 H) ret sm
        (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
          ((sp - 32#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .x19)) ∗ F) Q Qp) :
    SepWPp (lsProg_148 H) ret s P Q Qp := by
  encVarint2_prologue_body (blkPl_148).base SepWPp.of_sepWP_cs_placed EncVarintCalleeSavedPlaced

set_option hygiene false in
local macro "encVarint2_final_body " entry:term:max callMid:term:max ofCs:term:max csPred:term:max callGen:term:max : tactic => `(tactic| (
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗
      ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗ ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
      ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗ A.pool ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · rcases hcs with ⟨h21, h22, h23, h24, h25, h26, h27, h28, hvregs, _⟩
    have hbeq := cap_beq_len_false hlt; have hlen1 := bv_len_add_one curBs (lastVal.setWidth 8)
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs (BitVec.zeroExtend 8 lastVal) hlt]
    exact hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by encodedLen_cc_close) (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply ($ofCs (mid := $callMid)); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
    refine $callGen A hdoReserve v curCap curPtr sp
      ($entry + 932#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗
        ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗ ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
      (by ac_rfl) ?_
    intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge
    rcases hcsm with ⟨h21, h22, h23, h24, h25, h26, h27, h28, hvregs, _⟩
    have hx19m' : sm.readReg64 .x19 = lastVal := by simp only [arm64_norm, *]
    have hx20m' : sm.readReg64 .x20 = v := by simp only [arm64_norm, *]
    have hbeq := cap_beq_len_false hnew_gt; have hlen1 := bv_len_add_one curBs (lastVal.setWidth 8)
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A newCap p' curBs (BitVec.zeroExtend 8 lastVal) hnew_gt]
    have hGoalEq :
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [lastVal.setWidth 8]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [lastVal.setWidth 8]) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗
          (((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗
            ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗ ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
            ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗ F) =
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [lastVal.setWidth 8]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [lastVal.setWidth 8]) ∗
          ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗
          ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗ ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
          ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F := by ac_rfl
    rw [hGoalEq]
    exact hnext _ newCap p' (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by encodedLen_cc_close) hnew_ge (fun h => absurd h hlt)))
theorem step_encVarint2_final_placed [LibsignalPlacement] {resStack : Nat} (A : RustAlloc)
    (H : String → Option (State → State)) {s0 s : State}
    (hdoReserve : subroutine_ok (lsProg_148 H) (lsmpl.base 157) (doReserve2SpecWithPlaced resStack s0 A))
    (lastVal v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_148).base + 868#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = lastVal) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗ ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sf : State) (cap' ptr' : BitVec 64),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → curCap.toNat ≤ cap'.toNat →
      (curBs.length < curCap.toNat → cap' = curCap ∧ ptr' = curPtr) →
      Q sf (((v ↦₆₄ cap') ∗ ((v + 8#64) ↦₆₄ ptr') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [lastVal.setWidth 8]).length) ∗
        vecU8Buf A cap' ptr' (curBs ++ [lastVal.setWidth 8]) ∗
        ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗
        ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗ ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)) :
    SepWPp (lsProg_148 H) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  encVarint2_final_body (blkPl_148).base (lsmpl.base 157) SepWPp.of_sepWP_cs_placed EncVarintCalleeSavedPlaced step_doReserve2_call_gen_placed

set_option hygiene false in
local macro "encVarint2_exit_close" : tactic => `(tactic| (
  intro sf cap' ptr' hpcf hrunf hspf htrf hcsf hge hpres
  have hinv' := hinv.step (byte := lastVal.setWidth 8) hge hpres
  rw [hbs] at hinv'; have ⟨hcap_le, hcap_pres⟩ := hinv'.finish
  refine ⟨?_, hspf, hcsf⟩; intro hm_f; rw [sepConj_emp, hbs] at hm_f
  simp only [encodeVarintSpecOf, vecU8At_eq_header_sep_buf, vecHeader,
    stackAt_encodeVarint_gen_eq hres, sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨v48, v40, s0.readReg64 .fp, s0.readReg64 .lr,
    s0.readReg64 .x20, s0.readReg64 .x19, cap', ptr', htrf, ⟨hcap_le, hcap_pres⟩, ?_⟩
  convert hm_f using 1; ac_rfl))

theorem step_encVarint2_exit_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 8 * 6 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State)) {s0 s : State}
    (hdoReserve : subroutine_ok (lsProg_148 H) (lsmpl.base 157) (doReserve2SpecWithPlaced resStack s0 A))
    (x : EncodeVarintGhost) (lastVal curCap curPtr v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : VecReserveInv x.cap x.ptr curCap curPtr curBs)
    (hbs : curBs ++ [lastVal.setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62) {R P : SepProp}
    (hpc : s.pc = (blkPl_148).base + 868#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 48#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = lastVal) (hx1 : s.readReg64 .x1 = x.v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A curCap curPtr curBs ∗
      ((s0.sp - 48#64) ↦₆₄ v48) ∗ ((s0.sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (s0.sp - 48#64) resStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp (lsProg_148 H) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpecOf resStack A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  refine step_encVarint2_final_placed (F := emp) A H hdoReserve lastVal x.v curCap curPtr s0.sp v48 v40
    curBs hlen_lt hpc hrun hsp halign htr hx0 hx1 hx8 hx9 hcs (by rw [hP]; ac_rfl) ?_
  encVarint2_exit_close

/-! ## Continuation-Byte Stages 1..3 and 9 -/

set_option hygiene false in
local macro "encVarint2_s1_body " entry:term:max callMid:term:max ofCs:term:max csPred:term:max callGen:term:max : tactic => `(tactic| (
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 7).ult 128#64 = true ∨ (val >>> 7).ult 128#64 = false := by
    cases (val >>> 7).ult 128#64 <;> simp
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt; have hlen1 := bv_len_add_one curBs (varintContByte val)
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply ($ofCs (mid := $entry + 868#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte val) hlt]
      exact hnext _ curCap curPtr v48 v40 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply ($ofCs (mid := $entry + 128#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte val) hlt]
      exact hnext _ curCap curPtr v48 v40 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply ($ofCs (mid := $callMid)); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
    refine $callGen A hdoReserve v curCap curPtr sp
      ($entry + 96#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
      (by ac_rfl) ?_
    intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge
    have hlen1 := bv_len_add_one curBs (varintContByte val)
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    have hGoalEq :
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte val]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [varintContByte val]) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗
          (((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F) =
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte val]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [varintContByte val]) ∗
          ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F := by ac_rfl
    rcases hcond_or with hcond | hcond
    · apply ($ofCs (mid := $entry + 868#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step'
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte val) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hcsm.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply ($ofCs (mid := $entry + 128#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step'
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte val) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hcsm.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)))
theorem step_encVarint2_s1_placed [LibsignalPlacement] {resStack : Nat} (A : RustAlloc)
    (H : String → Option (State → State)) {s0 s : State}
    (hdoReserve : subroutine_ok (lsProg_148 H) (lsmpl.base 157) (doReserve2SpecWithPlaced resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_148).base + 32#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 7).ult 128#64 then (blkPl_148).base + 868#64 else (blkPl_148).base + 128#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 7).ult 128#64 then val >>> 7 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte val]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x10 = nextPtr → EncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat → (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (lsProg_148 H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte val]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte val]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_148 H) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  encVarint2_s1_body (blkPl_148).base (lsmpl.base 157) SepWPp.of_sepWP_cs_placed EncVarintCalleeSavedPlaced step_doReserve2_call_gen_placed

set_option hygiene false in
local macro "encVarint2_s2_body " entry:term:max callMid:term:max ofCs:term:max csPred:term:max callGen:term:max : tactic => `(tactic| (
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 14).ult 128#64 = true ∨ (val >>> 14).ult 128#64 = false := by
    cases (val >>> 14).ult 128#64 <;> simp
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt; have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 7))
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply ($ofCs (mid := $entry + 868#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 7)) hlt]
      exact hnext _ curCap curPtr v48 v40 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply ($ofCs (mid := $entry + 236#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 7)) hlt]
      exact hnext _ curCap curPtr v48 v40 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply ($ofCs (mid := $callMid)); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
    refine $callGen A hdoReserve v curCap curPtr sp
      ($entry + 200#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
      (by ac_rfl) ?_
    intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge
    have hx19m' : sm.readReg64 .x19 = v := by simp only [arm64_norm, *]
    have hx20m' : sm.readReg64 .x20 =
        BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 val) >>> 7)) |||
          4294967168#64 := by simp only [arm64_norm, zext64_trunc32_orr_mask, *]
    have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 7))
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    have hGoalEq :
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 7)]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [varintContByte (val >>> 7)]) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗
          (((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F) =
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 7)]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [varintContByte (val >>> 7)]) ∗
          ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ val) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F := by ac_rfl
    rcases hcond_or with hcond | hcond
    · apply ($ofCs (mid := $entry + 868#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step'
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 7)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v48 val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hcsm.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply ($ofCs (mid := $entry + 236#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step'
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 7)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v48 val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hcsm.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)))
theorem step_encVarint2_s2_placed [LibsignalPlacement] {resStack : Nat} (A : RustAlloc)
    (H : String → Option (State → State)) {s0 s : State}
    (hdoReserve : subroutine_ok (lsProg_148 H) (lsmpl.base 157) (doReserve2SpecWithPlaced resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_148).base + 128#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr) (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 14).ult 128#64 then (blkPl_148).base + 868#64 else (blkPl_148).base + 236#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 14).ult 128#64 then val >>> 14 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 7)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x10 = nextPtr → EncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat → (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (lsProg_148 H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 7)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 7)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_148 H) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  encVarint2_s2_body (blkPl_148).base (lsmpl.base 157) SepWPp.of_sepWP_cs_placed EncVarintCalleeSavedPlaced step_doReserve2_call_gen_placed

set_option hygiene false in
local macro "encVarint2_s3_body " entry:term:max callMid:term:max ofCs:term:max csPred:term:max callGen:term:max : tactic => `(tactic| (
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 21).ult 128#64 = true ∨ (val >>> 21).ult 128#64 = false := by
    cases (val >>> 21).ult 128#64 <;> simp
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt; have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 14))
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply ($ofCs (mid := $entry + 868#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 14)) hlt]
      exact hnext _ curCap curPtr v48 v40 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
    · apply ($ofCs (mid := $entry + 336#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 14)) hlt]
      exact hnext _ curCap curPtr v48 v40 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply ($ofCs (mid := $callMid)); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
    refine $callGen A hdoReserve v curCap curPtr sp
      ($entry + 304#64) curBs hcap_eq (hlen_lt.resolve_left hlt)
      (F := ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
      (by ac_rfl) ?_
    intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge
    have hx19m' : sm.readReg64 .x19 =
        BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 val) >>> 14)) |||
          4294967168#64 := by simp only [arm64_norm, zext64_trunc32_orr_mask, *]
    have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 14))
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    have hGoalEq :
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 14)]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [varintContByte (val >>> 14)]) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗
          (((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F) =
        ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 14)]).length) ∗
          vecU8Buf A newCap p' (curBs ++ [varintContByte (val >>> 14)]) ∗
          ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F := by ac_rfl
    rcases hcond_or with hcond | hcond
    · apply ($ofCs (mid := $entry + 868#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step'
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 14)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hcsm.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)
    · apply ($ofCs (mid := $entry + 336#64)); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step'
      rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 14)) hnew_gt, hGoalEq]
      exact hnext _ newCap p' v val (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hcsm.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
        hnew_ge (fun h => absurd h hlt)))
theorem step_encVarint2_s3_placed [LibsignalPlacement] {resStack : Nat} (A : RustAlloc)
    (H : String → Option (State → State)) {s0 s : State}
    (hdoReserve : subroutine_ok (lsProg_148 H) (lsmpl.base 157) (doReserve2SpecWithPlaced resStack s0 A))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_148).base + 236#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr) (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 21).ult 128#64 then (blkPl_148).base + 868#64 else (blkPl_148).base + 336#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 21).ult 128#64 then val >>> 21 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 14)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x12 = val >>> 28 → EncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat → (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (lsProg_148 H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 14)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 14)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗ A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_148 H) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  encVarint2_s3_body (blkPl_148).base (lsmpl.base 157) SepWPp.of_sepWP_cs_placed EncVarintCalleeSavedPlaced step_doReserve2_call_gen_placed

set_option hygiene false in
local macro "encVarint2_s9_body " entry:term:max callMid:term:max ofCs:term:max csPred:term:max callGen:term:max : tactic => `(tactic| (
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hbyte := contByte9_contByte_eq val hnot_ult
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt; have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 56))
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply ($ofCs (mid := $entry + 868#64)); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 56)) hlt]
    exact hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
      (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply ($ofCs (mid := $callMid)); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
    refine $callGen A hdoReserve v curCap curPtr sp
      ($entry + 972#64) curBs hcap_eq (hlen_lt.resolve_left hlt) (F := F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
      (by ac_rfl) ?_
    intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge
    have hx19m' : sm.readReg64 .x19 = v := by simp only [arm64_norm, *]
    have hx20m' : sm.readReg64 .x20 = val >>> 56 := by simp only [arm64_norm, *]
    have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 56))
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply ($ofCs (mid := $entry + 868#64)); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step2
    rw [vecU8Buf_snoc_eq A newCap p' curBs (varintContByte (val >>> 56)) hnew_gt]
    exact hnext _ newCap p' (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans (by simp only [$csPred:term, arm64_norm, *, and_self]))
      hnew_ge (fun h => absurd h hlt)))
theorem step_encVarint2_s9_placed [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State))
    {resStack : Nat} {s0 : State}
    (hdoReserve : subroutine_ok (lsProg_148 H) (lsmpl.base 157) (doReserve2SpecWithPlaced resStack s0 A))
    (val v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (hnot_ult : (val >>> 56).ult 128#64 = false)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {x : EncodeVarintGhost} {R : SepProp} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_148).base + 840#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = val >>> 56) (hx11 : s.readReg64 .x11 = curPtr)
    (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A curCap curPtr curBs ∗
      A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (blkPl_148).base + 868#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = 1#64 → sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 56)]).length →
      sm.readReg64 .x9 = nextCap → EncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat → (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (lsProg_148 H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 56)]).length) ∗
          vecU8Buf A nextCap nextPtr (curBs ++ [varintContByte (val >>> 56)]) ∗
          A.pool ∗ stackAt (sp - 48#64) resStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_148 H) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpec A).onPanic x s0 sf ∗ R)) := by
  encVarint2_s9_body (blkPl_148).base (lsmpl.base 157) SepWPp.of_sepWP_cs_placed EncVarintCalleeSavedPlaced step_doReserve2_call_gen_placed

end CryptoVerification.SpqrV1.Varint
