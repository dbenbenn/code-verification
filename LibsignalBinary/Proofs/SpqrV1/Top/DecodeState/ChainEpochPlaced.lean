/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochErrPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlaced -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.VersionNegotiationLoop
import ProofLib.SepLogic.WPp

/-!
# `spqr::decode_state` (Block `325`): Relocatable `ChainEpochPB` Field Merge Helpers

Relocatable `[LibsignalPlacement]` proofs of `ChainEpochPB` tag 1 (`send`), tag 2 (`recv`),
and `skip_field(depth=98)` (`+964..+1164`).
-/

public section

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Top.DecodeState.Placed

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Panic-Aware Call Wrapper for `EpochDirection::merge` -/

theorem SepWPpIPlaced.call_epochDirectionMerge [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec A)))
    (wt : WireType) (msgPtr : BitVec 64) (msg : EpochDirectionPB)
    (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8))
    {x_outer : DecodeStateGhost} {s0 s : State}
    {P F R : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 wt.toNat)
    (hx1 : s.readReg64 .x1 = msgPtr)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hlen : bs.length < 2 ^ 63)
    (hP : P = (epochDirectionPBCapOkAt A msgPtr bs.length msg ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot ptr bs ∗ A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (m' : EpochDirectionPB) (rest : List (BitVec 8)),
      (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto wt) msg bs 98).toOption = some (m', rest) →
      rest.length ≤ bs.length → IsDropSuffix bs rest →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          epochDirectionPBCapOkAt A msgPtr rest.length m' ∗
          sliceCursorAfter slot ptr bs rest) ∗ F)
        Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R))
    (herr : ∀ (sf : State) (n : Nat) (m' : EpochDirectionPB),
      (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto wt) msg bs 98).toOption = none →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 → n ≤ 1 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          decodeErrorAtStackLen A (sf.readReg64 .x0) n ∗
          epochDirectionPBAt A msgPtr m' ∗
          memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F)
        Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R)) :
    SepWPpIPlaced prog ret s P Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R) := by
  intro hinv
  let sp_cur := s0.sp - 1392#64
  let x_ed : EpochDirectionMergeGhost := ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - epochDirectionMergeStack) ∗ F
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  have hwpp : SepWPp prog ret_pc s P
      (fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧
        Pm = (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec A)).post x_ed s sm ∗ F_ext)
      (decodeStatePanicPostPlaced H_inner A x_outer s0 R) := by
    refine SepWPp.call (x := x_ed) (F := F_ext) hcall hpc hrun halign hlr ?_ ?_ ?_ ?_ ?_
    · intro R' hm
      dsimp only [withLsCodeRoLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hinv, ?_⟩
      dsimp only [epochDirectionMergeSpec, x_ed]
      rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0, hx1, hx2, hlen⟩, ?_⟩
      rw [hP] at hm
      have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (stackAt_to_callee sp_cur epochDirectionMergeStack (by decide)))))))) hm
      refine Satisfies.mono (Entails.of_eq ?_) hm1
      dsimp only [sp_cur, F_ext]; ac_rfl
    · intro sm _ R' _ hpost
      dsimp only [epochDirectionMergeSpec, withLsCodeRoLoaded] at hpost
      exact allowPanic_not_exited hpost
    · intro sm _ hm'
      dsimp only [decodeStatePanicPostPlaced, spqrDecodeStatePlacedSpec, withLsCodeRoLoaded, epochDirectionMergeSpec] at hm' ⊢
      exact allowPanic_frame (allocFailedIn_trans htr) hm'
    · intro sm hpcm hrunm hspm hcsm
      exact SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩
    · intro sm R' _ hpost
      exact False.elim (not_satisfies_false_sepConj hpost)
  intro R' hm hL
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, _, hpost, hspm, hcsm, rfl⟩ | hpan_or_oom⟩ := hwpp R' hm hL
  · rw [sepConj_assoc] at hpost
    change sm.mem ⊨ (epochDirectionMergeSpec A).post x_ed s sm ∗ (F_ext ∗ R') at hpost
    dsimp only [epochDirectionMergeSpec, x_ed] at hpost
    rw [hsp] at hpost
    rcases hed : (Proto.mergeMessage EpochDirectionPB.mergeField (codecWireTypeToProto wt) msg bs 98).toOption with _ | ⟨m', rest⟩
    · simp only [hed, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
      rcases hpost with ⟨m', n, hpost⟩
      have hpost_pure : sm.mem ⊨ ⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 ≠ 0#64⌝ ∗ (⌜n ≤ 1⌝ ∗
          (((bufRef ↦₆₄ slot) ∗ A.pool ∗
            (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
              (v1StateMergeStack - epochDirectionMergeStack) ∗
              stackAt sp_cur epochDirectionMergeStack) ∗
            decodeErrorAtStackLen A (sm.readReg64 .x0) n ∗
            epochDirectionPBAt A msgPtr m' ∗
            memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F) ∗ R')) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext]; ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨htrm, hx0_ne, hn, hpost1⟩
      rw [hsp] at hspm
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur epochDirectionMergeStack (by decide))))))) hpost1
      obtain ⟨sf, hsteps', hout'⟩ :=
        herr sm n m' hed hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_ne hn (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
    · simp only [hed] at hpost
      have hpost_pure : sm.mem ⊨ ⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 = 0#64⌝ ∗
          (((bufRef ↦₆₄ slot) ∗ A.pool ∗
            (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
              (v1StateMergeStack - epochDirectionMergeStack) ∗
              stackAt sp_cur epochDirectionMergeStack) ∗
            epochDirectionPBCapOkAt A msgPtr rest.length m' ∗
            sliceCursorAfter slot ptr bs rest) ∗ F) ∗ R') := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        dsimp only [sp_cur, F_ext]; ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨htrm, hx0_0, hpost1⟩
      rw [hsp] at hspm
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (stackAt_of_callee sp_cur epochDirectionMergeStack (by decide))))))) hpost1
      have ⟨hle, hsuf⟩ := proto_mergeMessage_suffix hed
      obtain ⟨sf, hsteps', hout'⟩ :=
        hok sm m' rest hed hle hsuf hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_0 (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr hpan_or_oom⟩

/-! ## `ChainEpochPB` Framing & Initialization Helpers -/

private theorem optEpochDirectionPB_none_split48 (a : BitVec 64) :
    memRegion (a + 8#64) 48 ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 32,
        ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
        ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₃₂ w6) ∗
        memRegion (a + 52#64) 4 := by
  have hs1 := ProofLib.memRegion_split (a + 8#64) 8 40 (by decide)
  have hs2 := ProofLib.memRegion_split ((a + 8#64) + 8#64) 8 32 (by decide)
  have hs3 := ProofLib.memRegion_split (((a + 8#64) + 8#64) + 8#64) 8 24 (by decide)
  have hs4 := ProofLib.memRegion_split ((((a + 8#64) + 8#64) + 8#64) + 8#64) 8 16 (by decide)
  have hs5 := ProofLib.memRegion_split (((((a + 8#64) + 8#64) + 8#64) + 8#64) + 8#64) 8 8 (by decide)
  have hs6 := ProofLib.memRegion_split ((((((a + 8#64) + 8#64) + 8#64) + 8#64) + 8#64) + 8#64) 4 4 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hs1 hs2 hs3 hs4 hs5 hs6
  rw [hs1, hs2, hs3, hs4, hs5, hs6,
    ProofLib.memRegion_eight (a + 8#64),
    ProofLib.memRegion_eight (a + 16#64),
    ProofLib.memRegion_eight (a + 24#64),
    ProofLib.memRegion_eight (a + 32#64),
    ProofLib.memRegion_eight (a + 40#64),
    ProofLib.memRegion_four (a + 48#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w6
  apply Entails.sepExists_elim; intro w5
  apply Entails.sepExists_elim; intro w4
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w1
  refine Entails.sepExists_right w1 (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.sepExists_right w4
      (Entails.sepExists_right w5 (Entails.sepExists_right w6 ?_)))))
  exact Entails.of_eq (by ac_rfl)

private theorem optEpochDirectionPBCapOkAt_some (A : RustAlloc) (a : BitVec 64) (remLen : Nat) (d : EpochDirectionPB) :
    optEpochDirectionPBCapOkAt A a remLen (some d) = epochDirectionPBCapOkAt A a remLen d := rfl

private theorem optEpochDirectionPBCapOkAt_none (A : RustAlloc) (a : BitVec 64) (remLen : Nat) :
    optEpochDirectionPBCapOkAt A a remLen none = (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 48 := rfl

private theorem optEpochDirectionPBAt_some_eq (A : RustAlloc) (a : BitVec 64) (d : EpochDirectionPB) :
    optEpochDirectionPBAt A a (some d) = epochDirectionPBAt A a d := rfl

private def epochDirectionPBCapOkRestAt (A : RustAlloc) (a : BitVec 64) (remLen : Nat)
    (cap1 : BitVec 64) (d : EpochDirectionPB) : SepProp :=
  (∃∗ ptr1 : BitVec 64,
    ((a + 8#64) ↦₆₄ ptr1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
    vecU8Heap A cap1 ptr1 d.next) ∗
  vecU8CapOkAt A (a + 0x18#64) remLen d.prev ∗
  ((a + 0x30#64) ↦₃₂ d.ctr) ∗
  memRegion (a + 0x34#64) 4

private theorem epochDirectionPBCapOkAt_expose_cap (A : RustAlloc) (a : BitVec 64) (remLen : Nat) (d : EpochDirectionPB) :
    epochDirectionPBCapOkAt A a remLen d ⊢
      ∃∗ cap1 : BitVec 64,
        ⌜BytesMergeCapOk cap1 remLen ∧ cap1.toNat < 2 ^ 63⌝ ∗
        (a ↦₆₄ cap1) ∗
        epochDirectionPBCapOkRestAt A a remLen cap1 d := by
  unfold epochDirectionPBCapOkAt
  rw [show vecU8CapOkAt A a remLen d.next =
    ∃∗ cap1 : BitVec 64, ∃∗ ptr1 : BitVec 64,
      ⌜BytesMergeCapOk cap1 remLen⌝ ∗ vecU8At A a cap1 ptr1 d.next from rfl]
  simp only [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro cap1
  apply Entails.sepExists_elim; intro ptr1
  refine Entails.sepExists_right cap1 ?_
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_left; intro hcap
  rw [vecU8At_eq_header_heap]
  unfold vecHeader
  simp only [sepConj_assoc]
  have hlt_ent := vecU8Heap_cap_lt A cap1 ptr1 d.next
  have hreord1 :
      (a ↦₆₄ cap1) ∗ ((a + 8#64) ↦₆₄ ptr1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
        vecU8Heap A cap1 ptr1 d.next ∗
        vecU8CapOkAt A (a + 0x18#64) remLen d.prev ∗
        ((a + 0x30#64) ↦₃₂ d.ctr) ∗ memRegion (a + 0x34#64) 4 =
      vecU8Heap A cap1 ptr1 d.next ∗
        ((a ↦₆₄ cap1) ∗ ((a + 8#64) ↦₆₄ ptr1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
          vecU8CapOkAt A (a + 0x18#64) remLen d.prev ∗
          ((a + 0x30#64) ↦₃₂ d.ctr) ∗ memRegion (a + 0x34#64) 4) := by ac_rfl
  rw [hreord1]
  refine Entails.trans (sepConj_mono_left hlt_ent) ?_
  rw [sepConj_assoc]
  apply Entails.pure_left; intro hcap_lt
  apply Entails.pure_right ⟨hcap, hcap_lt⟩
  unfold epochDirectionPBCapOkRestAt
  have hreord2 :
      vecU8Heap A cap1 ptr1 d.next ∗ ((a ↦₆₄ cap1) ∗ ((a + 8#64) ↦₆₄ ptr1) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
        vecU8CapOkAt A (a + 0x18#64) remLen d.prev ∗
        ((a + 0x30#64) ↦₃₂ d.ctr) ∗ memRegion (a + 0x34#64) 4) =
      (a ↦₆₄ cap1) ∗
        (((a + 8#64) ↦₆₄ ptr1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
          vecU8Heap A cap1 ptr1 d.next) ∗
        vecU8CapOkAt A (a + 0x18#64) remLen d.prev ∗
        ((a + 0x30#64) ↦₃₂ d.ctr) ∗ memRegion (a + 0x34#64) 4 := by ac_rfl
  rw [hreord2]
  exact sepConj_mono_right (sepConj_mono_left (Entails.sepExists_right ptr1 (Entails.refl _)))

attribute [local irreducible] skipField Proto.mergeMessage Proto.spqrDecodeState

private theorem epochDirectionPBCapOkAt_fold_cap (A : RustAlloc) (a cap1 : BitVec 64) (remLen : Nat)
    (d : EpochDirectionPB) (hcap : BytesMergeCapOk cap1 remLen) :
    (a ↦₆₄ cap1) ∗ epochDirectionPBCapOkRestAt A a remLen cap1 d ⊢
      epochDirectionPBCapOkAt A a remLen d := by
  unfold epochDirectionPBCapOkAt epochDirectionPBCapOkRestAt
  rw [show vecU8CapOkAt A a remLen d.next =
    ∃∗ cap1 : BitVec 64, ∃∗ ptr1 : BitVec 64,
      ⌜BytesMergeCapOk cap1 remLen⌝ ∗ vecU8At A a cap1 ptr1 d.next from rfl]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro ptr1
  refine Entails.sepExists_right cap1 (Entails.sepExists_right ptr1 ?_)
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_right hcap
  rw [vecU8At_eq_header_heap]
  unfold vecHeader
  exact Entails.of_eq (by ac_rfl)

theorem chainEpochPBCapOkAt_eq_placed (A : RustAlloc) (sp : BitVec 64) (remLen : Nat) (ep : ChainEpochPB) :
    chainEpochPBCapOkAt A (sp - 688#64) remLen ep =
      optEpochDirectionPBCapOkAt A (sp - 688#64) remLen ep.send ∗
      optEpochDirectionPBCapOkAt A (sp - 632#64) remLen ep.recv := by
  unfold chainEpochPBCapOkAt
  have ha : sp - 688#64 + 0x38#64 = sp - 632#64 := by bv_omega
  rw [ha]

private abbrev chainEpochPBCapOkAt_eq := @chainEpochPBCapOkAt_eq_placed

private theorem chainEpochPBAt_eq (A : RustAlloc) (sp : BitVec 64) (ep : ChainEpochPB) :
    chainEpochPBAt A (sp - 688#64) ep =
      optEpochDirectionPBAt A (sp - 688#64) ep.send ∗
      optEpochDirectionPBAt A (sp - 632#64) ep.recv := by
  unfold chainEpochPBAt
  have ha : sp - 688#64 + 0x38#64 = sp - 632#64 := by bv_omega
  rw [ha]

theorem epochLoop_cursor_to_epochErrFrame_placed [LibsignalPlacement] (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (x : DecodeStateGhost) (cur : List (BitVec 8)) (remSt remEp : Nat)
    (curSt : PqRatchetState) (curEpoch : ChainEpochPB) (s0 : State) :
    sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes cur ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) remSt curSt ∗
      chainEpochPBCapOkAt A (s0.sp - 688#64) remEp curEpoch ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A x s0 ⊢
      decodeStateEpochErrFramePlaced H_inner A x curSt curEpoch s0 := by
  dsimp only [decodeStateLoopCommonPlaced, decodeStateEpochErrFramePlaced, decodeStateEpochErrTailFramePlaced]
  have h1 := sliceCursorAfter_to_memRegion s0.sp x.st.ptr x.st.bytes cur
  have h2 := protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) remSt curSt
  have h3 := chainEpochPBCapOkAt_entails_chainEpochPBAt A (s0.sp - 688#64) remEp curEpoch
  have hst := vecArg_join_bytes A x.st
  have hlow := lower_352_fold s0.sp
  have hup := upper_240_fold s0.sp (s0.sp - 1056#64)
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono_left h3))) ?_
  have hreord :
      (memRegion (s0.sp - 1056#64) 16 ∗ (x.st.ptr ↦ₛ x.st.bytes)) ∗
        protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
        chainEpochPBAt A (s0.sp - 688#64) curEpoch ∗
        memRegion (s0.sp - 576#64) 240 ∗
        (v1StateJumpTablesPlacedAt ∗ vecArgRestAt A x.st ∗ memRegion x.outPtr 352 ∗
          A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          memRegion (s0.sp - 1392#64) 336 ∗ ((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗
          memRegion (s0.sp - 328#64) 224 ∗ memRegion (s0.sp - 104#64) 8 ∗
          decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
            (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
            (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
            (s0.readReg64 .x20) (s0.readReg64 .x19)) =
      chainEpochPBAt A (s0.sp - 688#64) curEpoch ∗
        v1StateJumpTablesPlacedAt ∗
        ((x.st.ptr ↦ₛ x.st.bytes) ∗ vecArgRestAt A x.st) ∗
        memRegion x.outPtr 352 ∗ A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
        (memRegion (s0.sp - 1392#64) 336 ∗ memRegion (s0.sp - 1056#64) 16) ∗
        protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) curSt ∗
        memRegion (s0.sp - 576#64) 240 ∗
        (((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗ memRegion (s0.sp - 328#64) 224 ∗
          memRegion (s0.sp - 104#64) 8) ∗
        decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
          (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
          (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
          (s0.readReg64 .x20) (s0.readReg64 .x19) := by ac_rfl
  rw [hreord]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono hst (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono hlow (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left hup)))))))))

theorem epochLoop_calleeErr_to_epochErrFrame_placed [LibsignalPlacement] (H_inner : V1InnerHeapPred)
    (A : RustAlloc) (x : DecodeStateGhost) {cur : List (BitVec 8)}
    (hcur_le : cur.length ≤ x.st.bytes.length) (hcur_suf : IsDropSuffix x.st.bytes cur)
    (remSt : Nat) (curSt : PqRatchetState) (curEpoch : ChainEpochPB) (s0 : State) :
    memRegion (s0.sp - 1056#64) 16 ∗
      ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur) ∗
      (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) remSt curSt ∗
      chainEpochPBAt A (s0.sp - 688#64) curEpoch ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommonPlaced A x s0 ⊢
      decodeStateEpochErrFramePlaced H_inner A x curSt curEpoch s0 := by
  dsimp only [decodeStateLoopCommonPlaced, decodeStateEpochErrFramePlaced, decodeStateEpochErrTailFramePlaced]
  have h1 := pointsToBytes_prefix_join (ptr := x.st.ptr) hcur_le hcur_suf
  have hst := Entails.trans (sepConj_mono_left h1) (vecArg_join_bytes A x.st)
  have h2 := protoPqRatchetStateCapOkAt_entails_protoPqRatchetStateAt H_inner A (s0.sp - 1040#64) remSt curSt
  have hlow := lower_352_fold s0.sp
  have hup := upper_240_fold s0.sp (s0.sp - 1056#64)
  have hreord :
      memRegion (s0.sp - 1056#64) 16 ∗
        ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur) ∗
        (x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) remSt curSt ∗
        chainEpochPBAt A (s0.sp - 688#64) curEpoch ∗
        memRegion (s0.sp - 576#64) 240 ∗
        (v1StateJumpTablesPlacedAt ∗ vecArgRestAt A x.st ∗ memRegion x.outPtr 352 ∗
          A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          memRegion (s0.sp - 1392#64) 336 ∗ ((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗
          memRegion (s0.sp - 328#64) 224 ∗ memRegion (s0.sp - 104#64) 8 ∗
          decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
            (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
            (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
            (s0.readReg64 .x20) (s0.readReg64 .x19)) =
      chainEpochPBAt A (s0.sp - 688#64) curEpoch ∗
        v1StateJumpTablesPlacedAt ∗
        (((x.st.ptr ↦ₛ x.st.bytes.take (x.st.bytes.length - cur.length)) ∗
            ((x.st.ptr + BitVec.ofNat 64 (x.st.bytes.length - cur.length)) ↦ₛ cur)) ∗
          vecArgRestAt A x.st) ∗
        memRegion x.outPtr 352 ∗ A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
        (memRegion (s0.sp - 1392#64) 336 ∗ memRegion (s0.sp - 1056#64) 16) ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) remSt curSt ∗
        memRegion (s0.sp - 576#64) 240 ∗
        (((s0.sp - 336#64) ↦₆₄ (s0.sp - 1056#64)) ∗ memRegion (s0.sp - 328#64) 224 ∗
          memRegion (s0.sp - 104#64) 8) ∗
        decodeStateSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
          (s0.readReg64 .x28) (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25)
          (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
          (s0.readReg64 .x20) (s0.readReg64 .x19) := by ac_rfl
  rw [hreord]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono hst (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono hlow (sepConj_mono h2
      (sepConj_mono_right (sepConj_mono_left hup)))))))))

theorem SepWPpIPlaced.call_growOneChainEpoch [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (growOneStrideFullSpec A 112 8))
    (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    {x_outer : DecodeStateGhost} {s0 s : State}
    {P F R : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = v)
    (hlen : bs.length = cap.toNat * 112)
    (hptr : ptr ≠ 0#64)
    (hbound : max (2 * cap.toNat) 4 * 112 + 8 ≤ 2 ^ 63)
    (hP : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      (if cap = 0#64 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
      A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (p' : BitVec 64),
      p' ≠ 0#64 → p'.toNat % 8 = 0 →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      SepWPpIPlaced prog ret sf
        (((v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
          A.live p' (max (2 * cap.toNat) 4 * 112) 8 ∗ (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length) ((max (2 * cap.toNat) 4 - cap.toNat) * 112) ∗
          A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
        Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R)) :
    SepWPpIPlaced prog ret s P Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R) := by
  intro hinv
  let sp_cur := s0.sp - 1392#64
  let x_go : GrowGhost := (v, cap, ptr, bs)
  let F_ext := memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
    (v1StateMergeStack - growOneStack) ∗ F
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  have hwpp : SepWPp prog ret_pc s P
      (fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧
        Pm = (growOneStrideFullSpec A 112 8).post x_go s sm ∗ F_ext)
      (decodeStatePanicPostPlaced H_inner A x_outer s0 R) := by
    refine SepWPp.call (x := x_go) (F := F_ext) hcall hpc hrun halign hlr ?_ ?_ ?_ ?_ ?_
    · intro R' hm
      dsimp only [growOneStrideFullSpec, x_go]
      rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0, hlen, hptr, hbound⟩, ?_⟩
      rw [hP] at hm
      have hm1 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (stackAt_to_callee sp_cur growOneStack (by decide)))))))) hm
      refine Satisfies.mono (Entails.of_eq ?_) hm1
      dsimp only [sp_cur, F_ext]; ac_rfl
    · intro sm _ R' _ hpost
      dsimp only [growOneStrideFullSpec] at hpost
      exact allowPanic_not_exited hpost
    · intro sm _ hm'
      dsimp only [decodeStatePanicPostPlaced, spqrDecodeStatePlacedSpec, growOneStrideFullSpec] at hm' ⊢
      exact allowPanic_frame (allocFailedIn_trans htr) hm'
    · intro sm hpcm hrunm hspm hcsm
      exact SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩
    · intro sm R' _ hpost
      exact False.elim (not_satisfies_false_sepConj hpost)
  intro R' hm hL
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, _, hpost, hspm, hcsm, rfl⟩ | hpan_or_oom⟩ := hwpp R' hm hL
  · rw [sepConj_assoc] at hpost
    dsimp only [growOneStrideFullSpec, x_go] at hpost
    rw [hsp] at hpost
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
    rcases hpost with ⟨p', hpost⟩
    have hpost_pure : sm.mem ⊨ ⌜sm.trace = s.trace⌝ ∗ (⌜p' ≠ 0#64 ∧ p'.toNat % 8 = 0⌝ ∗
        (((v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
          A.live p' (max (2 * cap.toNat) 4 * 112) 8 ∗ (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length) ((max (2 * cap.toNat) 4 - cap.toNat) * 112) ∗
          A.pool ∗
          (memRegion (sp_cur - BitVec.ofNat 64 v1StateMergeStack)
            (v1StateMergeStack - growOneStack) ∗
            stackAt sp_cur growOneStack)) ∗ F) ∗ R') := by
      refine Satisfies.mono (Entails.of_eq ?_) hpost
      dsimp only [sp_cur, F_ext]; ac_rfl
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
    rcases hpost_pure with ⟨htrm, ⟨hp'_ne, hp'_al⟩, hpost1⟩
    rw [hsp] at hspm
    have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right
          (stackAt_of_callee sp_cur growOneStack (by decide)))))))))) hpost1
    obtain ⟨sf, hsteps', hout'⟩ :=
      hok sm p' hp'_ne hp'_al hpcm hrunm hspm (htr.step htrm hcsm) hcsm (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr hpan_or_oom⟩

/-! ## `ChainEpochPB` Tag Body Helpers (`send`, `recv`, `skip_field`) -/

end CryptoVerification.SpqrV1.Top.DecodeState
