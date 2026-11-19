/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlaced -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergePart2CodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `spqr::decode_state` — Placed Outer `PqRatchetState::v1` (Tag 3) & Default `skip_field` Step
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

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup v1StateJumpTablesPlacedAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Panic-Aware Call Wrapper for `V1State::merge` -/

@[simp] private theorem messageMerge_codecWireTypeToProto_eq (wt : WireType) :
    Prost.MessageMerge.codecWireTypeToProto wt = codecWireTypeToProto wt := by
  cases wt <;> rfl

theorem SepWPpIPlaced.call_v1StateMerge [LibsignalPlacement] {H_inner : V1InnerHeapPred}
    {A : RustAlloc}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (Prost.MessageMerge.v1StateMergePlacedSpec A)))
    (hcap : ∀ (a : BitVec 64) (remLen : Nat) (opt : Option V1State.InnerState),
      OptInnerStatePolyBound remLen opt →
      Prost.MessageMerge.optProtoInnerStateCapAt A a remLen opt ⊢
        optProtoInnerStateCapOkAt H_inner A a remLen opt)
    (hdrop : ∀ (a : BitVec 64) (opt : Option V1State.InnerState),
      Drop.optProtoInnerStateAt A a opt ⊢ optProtoInnerStateAt H_inner A a opt)
    (wt : WireType) (msgPtr : BitVec 64) (msg : V1State)
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
    (hlen : bs.length < 2 ^ 32)
    (hP : P = (optProtoInnerStateCapOkAt H_inner A msgPtr bs.length msg.innerState ∗
      v1StateJumpTablesPlacedAt ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot ptr bs ∗ A.pool ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (m' : V1State) (rest : List (BitVec 8)),
      (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto wt) msg bs 100).toOption = some (m', rest) →
      rest.length ≤ bs.length → IsDropSuffix bs rest →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          v1StateJumpTablesPlacedAt ∗
          optProtoInnerStateCapOkAt H_inner A msgPtr rest.length m'.innerState ∗
          sliceCursorAfter slot ptr bs rest) ∗ F)
        Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R))
    (herr : ∀ (sf : State) (n : Nat) (m' : Option V1State.InnerState),
      (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto wt) msg bs 100).toOption = none →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 → n ≤ 10 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool ∗ stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          v1StateJumpTablesPlacedAt ∗
          decodeErrorAtStackLen A (sf.readReg64 .x0) n ∗
          optProtoInnerStateAt H_inner A msgPtr m' ∗
          memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F)
        Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R)) :
    SepWPpIPlaced prog ret s P Q (decodeStatePanicPostPlaced H_inner A x_outer s0 R) := by
  intro hinv R' hm hL
  let x_v1 : V1StateMergeGhost := ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩
  rw [hP] at hm
  have hm_cap := Satisfies.mono (sepConj_mono_left (sepConj_mono_left (sepConj_mono_left
    (optProtoInnerStateCapOkAt_entails_capAt H_inner A msgPtr bs.length msg.innerState)))) hm
  have hm_pb : s.mem ⊨ ⌜OptInnerStatePolyBound bs.length msg.innerState⌝ ∗
      ((Prost.MessageMerge.optProtoInnerStateCapAt A msgPtr bs.length msg.innerState ∗
        v1StateJumpTablesPlacedAt ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr bs ∗ A.pool ∗
        stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F ∗ R') := by
    refine Satisfies.mono (Entails.of_eq ?_) hm_cap
    ac_rfl
  rw [satisfies_pure_sepConj] at hm_pb
  rcases hm_pb with ⟨hpb, hm'⟩
  have hpre : s.mem ⊨ (withLsCodeRoLoaded lsmpl (Prost.MessageMerge.v1StateMergePlacedSpec A)).pre x_v1 s ∗ (F ∗ R') := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hinv, ?_⟩
    dsimp only [Prost.MessageMerge.v1StateMergePlacedSpec, x_v1]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, by omega, hpb⟩, ?_⟩
    refine Satisfies.mono (Entails.of_eq ?_) hm'
    ac_rfl
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x_v1 (F ∗ R') s hpc hrun hpre halign hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · change sm.mem ⊨ (Prost.MessageMerge.v1StateMergePlacedSpec A).post x_v1 s sm ∗ (F ∗ R') at hpost
    dsimp only [Prost.MessageMerge.v1StateMergePlacedSpec, x_v1] at hpost
    rw [hsp, messageMerge_codecWireTypeToProto_eq] at hpost
    rcases hv1 : (Proto.mergeMessage V1State.mergeField (codecWireTypeToProto wt) msg bs 100).toOption with _ | ⟨m', rest⟩
    · simp only [hv1, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
      rcases hpost with ⟨m', n, hpost⟩
      have hpost_pure : sm.mem ⊨ ⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 ≠ 0#64⌝ ∗ (⌜n ≤ 4⌝ ∗
          (((bufRef ↦₆₄ slot) ∗ A.pool ∗
            stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
            v1StateJumpTablesPlacedAt ∗
            decodeErrorAtStackLen A (sm.readReg64 .x0) n ∗
            Drop.optProtoInnerStateAt A msgPtr m' ∗
            memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F) ∗ R')) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨htrm, hx0_ne, hn, hpost1⟩
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left (hdrop msgPtr m'))))))))) hpost1
      rw [hlr] at hpcm; rw [hsp] at hspm
      obtain ⟨sf, hsteps', hout'⟩ :=
        herr sm n m' hv1 hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_ne (by omega) (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
    · simp only [hv1] at hpost
      have hpost_pure : sm.mem ⊨ ⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 = 0#64 ∧ OptInnerStatePolyBound rest.length m'.innerState⌝ ∗
          (((bufRef ↦₆₄ slot) ∗ A.pool ∗
            stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
            v1StateJumpTablesPlacedAt ∗
            Prost.MessageMerge.optProtoInnerStateCapAt A msgPtr rest.length m'.innerState ∗
            sliceCursorAfter slot ptr bs rest) ∗ F) ∗ R') := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨htrm, ⟨hx0_0, hpb'⟩, hpost1⟩
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (hcap msgPtr rest.length m'.innerState hpb')))))))) hpost1
      rw [hlr] at hpcm; rw [hsp] at hspm
      have ⟨hle, hsuf⟩ := proto_mergeMessage_suffix hv1
      obtain ⟨sf, hsteps', hout'⟩ :=
        hok sm m' rest hv1 hle hsuf hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_0 (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · change sm.mem ⊨ (Prost.MessageMerge.v1StateMergePlacedSpec A).onPanic x_v1 s sm ∗ (F ∗ R') at hpost
    rw [← sepConj_assoc] at hpost
    refine ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost, ?_⟩)⟩
    intro hm''
    dsimp only [decodeStatePanicPostPlaced, spqrDecodeStatePlacedSpec, Prost.MessageMerge.v1StateMergePlacedSpec] at hm'' ⊢
    exact allowPanic_frame (allocFailedIn_trans htr) hm''
  · dsimp only [Prost.MessageMerge.v1StateMergePlacedSpec, withLsCodeRoLoaded] at hpost
    exact (allowPanic_not_exited hpost).elim
  · exact False.elim (not_satisfies_false_sepConj hpost)

/-! ## 2. Outer `skip_field(depth=100)` (`+456` -> `+1576` / `+1668`) -/

attribute [local irreducible] Proto.mergeMessage mergeLoopBin Proto.spqrDecodeState

private theorem setWidth8_ofNat64_wt (iwt : WireType) :
    BitVec.setWidth 8 (BitVec.ofNat 64 iwt.toNat) = BitVec.ofNat 8 iwt.toNat := by
  cases iwt <;> rfl

/-! ## 3. Spatial & Framing Helpers for Outer Tag 3 (`PqRatchetState::v1`, `224`B) -/

private theorem protoPqRatchetStateCapOkAt_v1_eq (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (sp : BitVec 64) (remLen : Nat) (optVn : Option VersionNegotiationPB)
    (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner) :
    protoPqRatchetStateCapOkAt H_inner A (sp - 1040#64) remLen ⟨optVn, optCh, inner⟩ =
      optVersionNegotiationPBCapOkAt A (sp - 1040#64) remLen optVn ∗
      optChainPBCapOkAt A (sp - 992#64) remLen optCh ∗
      optProtoPqRatchetInnerCapOkAt H_inner A (sp - 912#64) remLen inner := by
  unfold protoPqRatchetStateCapOkAt
  dsimp only
  have ha1 : sp - 1040#64 + 48#64 = sp - 992#64 := by bv_omega
  have ha2 : sp - 1040#64 + 128#64 = sp - 912#64 := by bv_omega
  rw [ha1, ha2]

private theorem optProtoInnerStateCapOkAt_expose_head (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (a : BitVec 64) (remLen : Nat) (opt : Option V1State.InnerState) :
    optProtoInnerStateCapOkAt H_inner A a remLen opt ⊢
      ∃∗ q : Quads28,
        ⌜q.head ≠ none3Cap⌝ ∗
        (a ↦₆₄ q.head) ∗
        (((a + 8#64) ↦₆₄ q.1.1.2.1) ∗ ((a + 16#64) ↦₆₄ q.1.1.2.2.1) ∗
         ((a + 24#64) ↦₆₄ q.1.1.2.2.2.1) ∗ ((a + 32#64) ↦₆₄ q.1.1.2.2.2.2.1) ∗
         ((a + 40#64) ↦₆₄ q.1.1.2.2.2.2.2.1) ∗ ((a + 48#64) ↦₆₄ q.1.1.2.2.2.2.2.2) ∗
         quads7At (a + 56#64) q.1.2 ∗ quads14At (a + 112#64) q.2 ∗
         optProtoInnerStateCapOkHeap H_inner A remLen q opt) := by
  refine Entails.trans (optProtoInnerStateCapOkAt_entails_quads28 H_inner A a remLen opt) ?_
  apply Entails.sepExists_elim; intro q
  refine Entails.sepExists_right q ?_
  cases opt with
  | none =>
    unfold optProtoInnerStateCapOkHeap quads28At
    dsimp only
    rw [quads14At, quads7At_split_head a q.1.1]
    rw [sepConj_comm _ ⌜_⌝]
    apply Entails.pure_left; intro hrh
    have hne : q.head ≠ none3Cap := by rw [hrh.2]; decide
    apply Entails.pure_right hne
    have htrue : (⌜remLen < 2 ^ 56 ∧ q.head = none2Cap⌝ : SepProp) = emp := by
      simp only [hrh, and_self, pure_true]
    rw [htrue, sepConj_emp]
    unfold Quads28.head
    exact Entails.of_eq (by ac_rfl)
  | some is =>
    unfold optProtoInnerStateCapOkHeap
    dsimp only
    rw [sepConj_comm (quads28At a q), sepConj_assoc]
    apply Entails.pure_left; intro hph
    apply Entails.pure_right hph.2
    have htrue : (⌜OptInnerStatePolyBound remLen (some is) ∧ q.head ≠ none3Cap⌝ : SepProp) = emp := by
      rw [eq_true hph, pure_true]
    rw [quads28At, quads14At, quads7At_split_head a q.1.1, htrue, emp_sepConj]
    unfold Quads28.head
    exact Entails.of_eq (by ac_rfl)

private theorem optProtoInnerStateCapOkAt_fold_head (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (a : BitVec 64) (q : Quads28) (remLen : Nat) (opt : Option V1State.InnerState) :
    (a ↦₆₄ q.head) ∗
      (((a + 8#64) ↦₆₄ q.1.1.2.1) ∗ ((a + 16#64) ↦₆₄ q.1.1.2.2.1) ∗
       ((a + 24#64) ↦₆₄ q.1.1.2.2.2.1) ∗ ((a + 32#64) ↦₆₄ q.1.1.2.2.2.2.1) ∗
       ((a + 40#64) ↦₆₄ q.1.1.2.2.2.2.2.1) ∗ ((a + 48#64) ↦₆₄ q.1.1.2.2.2.2.2.2) ∗
       quads7At (a + 56#64) q.1.2 ∗ quads14At (a + 112#64) q.2 ∗
       optProtoInnerStateCapOkHeap H_inner A remLen q opt) ⊢
    optProtoInnerStateCapOkAt H_inner A a remLen opt := by
  have hq :
      (a ↦₆₄ q.head) ∗
        (((a + 8#64) ↦₆₄ q.1.1.2.1) ∗ ((a + 16#64) ↦₆₄ q.1.1.2.2.1) ∗
         ((a + 24#64) ↦₆₄ q.1.1.2.2.2.1) ∗ ((a + 32#64) ↦₆₄ q.1.1.2.2.2.2.1) ∗
         ((a + 40#64) ↦₆₄ q.1.1.2.2.2.2.2.1) ∗ ((a + 48#64) ↦₆₄ q.1.1.2.2.2.2.2.2) ∗
         quads7At (a + 56#64) q.1.2 ∗ quads14At (a + 112#64) q.2 ∗
         optProtoInnerStateCapOkHeap H_inner A remLen q opt) =
      quads28At a q ∗ optProtoInnerStateCapOkHeap H_inner A remLen q opt := by
    unfold quads28At quads14At Quads28.head
    rw [quads7At_split_head a q.1.1]
    ac_rfl
  rw [hq]
  exact quads28_entails_optProtoInnerStateCapOkAt H_inner A a remLen q opt

private theorem head_ne_none3Cap_branch {w : BitVec 64} (hne : w ≠ none3Cap) :
    (w + 3#64 != 0#64) = true ∧ (w + 3#64 == 0#64) = false := by
  have h0 : w + 3#64 ≠ 0#64 := by
    intro h
    apply hne
    change w = -3#64
    bv_omega
  exact ⟨bne_iff_ne.mpr h0, beq_eq_false_iff_ne.mpr h0⟩

private theorem memRegion_224_split_head (a : BitVec 64) :
    memRegion a 224 ⊢
      memRegion (a + 8#64) 216 ∗ (∃∗ w : BitVec 64, a ↦₆₄ w) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 216) (b' := a + 8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight a]
  exact Entails.of_eq (by ac_rfl)

private theorem optProtoInnerStateCapOkAt_default_init (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (a : BitVec 64) (remLen : Nat) (hrem : remLen < 2 ^ 56) :
    (a ↦₆₄ (-2#64)) ∗ memRegion (a + 8#64) 216 ⊢
      optProtoInnerStateCapOkAt H_inner A a remLen (default : V1State).innerState := by
  have hd : (default : V1State).innerState = none := rfl
  rw [hd]
  unfold optProtoInnerStateCapOkAt none2Cap
  exact Entails.pure_right hrem (Entails.refl _)

private theorem scratch_688_split_quads28_and_3a0 (sp w0 : BitVec 64) :
    ((sp - 688#64) ↦₆₄ w0) ∗ memRegion (sp - 680#64) 40 ∗ memRegion (sp - 640#64) 304 ⊢
      memRegion (sp - 456#64) 120 ∗
      (∃∗ w_3a0 : BitVec 64, ∃∗ q_dst : Quads28,
        quads28At (sp - 688#64) q_dst ∗ ((sp - 464#64) ↦₆₄ w_3a0)) := by
  refine Entails.trans (scratch_688_fold_48 sp w0) ?_
  rw [ProofLib.memRegion_split' (b := sp - 688#64) (n := 224) (k := 128)
      (b' := sp - 464#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 464#64) (n := 8) (k := 120)
      (b' := sp - 456#64) rfl (by bv_omega) (by decide),
    memRegion_224_eq_quads28At (sp - 688#64),
    ProofLib.memRegion_eight (sp - 464#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.of_eq (by ac_rfl)

private theorem scratch_688_restore_from_quads28 (sp w_3a0 : BitVec 64) (q : Quads28) :
    quads28At (sp - 688#64) q ∗ ((sp - 464#64) ↦₆₄ w_3a0) ∗ memRegion (sp - 456#64) 120 ⊢
      ((sp - 688#64) ↦₆₄ q.head) ∗ memRegion (sp - 680#64) 40 ∗ memRegion (sp - 640#64) 304 := by
  have h1 := quads28_entails_head_and_memRegion_216 (sp - 688#64) q
  have h2 : ((sp - 464#64) ↦₆₄ w_3a0) ⊢ memRegion (sp - 464#64) 8 :=
    ProofLib.pointsTo64_entails_memRegion _ _
  refine Entails.trans (sepConj_mono h1 (sepConj_mono_left h2)) ?_
  have ha680 : sp - 688#64 + 8#64 = sp - 680#64 := by bv_omega
  rw [ha680]
  have h344 : memRegion (sp - 680#64) 216 ∗ memRegion (sp - 464#64) 8 ∗ memRegion (sp - 456#64) 120 =
      memRegion (sp - 680#64) 40 ∗ memRegion (sp - 640#64) 304 := by
    rw [← ProofLib.memRegion_split' (b := sp - 464#64) (n := 8) (k := 120)
        (b' := sp - 456#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 680#64) (n := 216) (k := 128)
        (b' := sp - 464#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 680#64) (n := 40) (k := 304)
        (b' := sp - 640#64) rfl (by bv_omega) (by decide)]
  have hassoc :
      ((sp - 688#64) ↦₆₄ q.head ∗ memRegion (sp - 680#64) 216) ∗
        (memRegion (sp - 464#64) 8 ∗ memRegion (sp - 456#64) 120) =
      (sp - 688#64) ↦₆₄ q.head ∗
        (memRegion (sp - 680#64) 216 ∗ memRegion (sp - 464#64) 8 ∗ memRegion (sp - 456#64) 120) := by ac_rfl
  rw [hassoc, h344]
  exact Entails.refl _

private theorem scratch_688_dropped_split_48 (sp w_3a0 : BitVec 64) :
    memRegion (sp - 688#64) 224 ∗ ((sp - 464#64) ↦₆₄ w_3a0) ∗ memRegion (sp - 456#64) 120 ⊢
      memRegion (sp - 680#64) 40 ∗ memRegion (sp - 640#64) 304 ∗
      (∃∗ w0' : BitVec 64, (sp - 688#64) ↦₆₄ w0') := by
  have h352 : memRegion (sp - 688#64) 224 ∗ ((sp - 464#64) ↦₆₄ w_3a0) ∗ memRegion (sp - 456#64) 120 ⊢
      memRegion (sp - 688#64) 352 := by
    rw [ProofLib.memRegion_split' (b := sp - 688#64) (n := 224) (k := 128)
        (b' := sp - 464#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 464#64) (n := 8) (k := 120)
        (b' := sp - 456#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))
  exact Entails.trans h352 (scratch_688_split_48 sp)

/-! ## 4. Outer Tag 3 `some (.v1 v1)` In-Place Merge (`+476..+492`) -/

/-! ## 5. 224-Byte Q-Register Copies & Outer Tag 3 `none` Path (`+324..+452`, `+1484..+1572`) -/

private theorem optProtoPqRatchetInnerCapOkAt_none_entails_quads28 (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (a : BitVec 64) (remLen : Nat) :
    optProtoPqRatchetInnerCapOkAt H_inner A a remLen none ⊢ ∃∗ q_dst : Quads28, quads28At a q_dst := by
  refine Entails.trans (optProtoPqRatchetInnerCapOkAt_entails_optProtoPqRatchetInnerAt H_inner A a remLen none) ?_
  unfold optProtoPqRatchetInnerAt
  rw [← memRegion_224_eq_quads28At a,
      ProofLib.memRegion_split' (b := a) (n := 8) (k := 216) (b' := a + 8#64) rfl rfl (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)

private theorem memRegion_16_expose_second (sp : BitVec 64) :
    memRegion (sp - 1056#64) 16 ⊢
      memRegion (sp - 1056#64) 8 ∗ (∃∗ w : BitVec 64, (sp - 1048#64) ↦₆₄ w) := by
  rw [ProofLib.memRegion_split' (b := sp - 1056#64) (n := 8) (k := 8) (b' := sp - 1048#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight (sp - 1048#64)]
  exact Entails.refl _

private theorem memRegion_16_fold_second (sp : BitVec 64) (w : BitVec 64) :
    memRegion (sp - 1056#64) 8 ∗ ((sp - 1048#64) ↦₆₄ w) ⊢
      memRegion (sp - 1056#64) 16 := by
  rw [ProofLib.memRegion_split' (b := sp - 1056#64) (n := 8) (k := 8) (b' := sp - 1048#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (ProofLib.pointsTo64_entails_memRegion _ _)

/-- 224-byte Q-register copy (`+340..+428`, 22 instructions) from
    `x29 - 0xe8` (`s0.sp - 328#64`) to `sp + 0x2c0` (`s0.sp - 688#64`), also storing
    `x24` (`s0.sp - 912#64`) at `sp + 0x3a0` (`s0.sp - 464#64`). -/
theorem decodeState_v1_copy_to_scratch_535f0_placed [LibsignalPlacement] {target_pc v0 v20 v27 : BitVec 64}
    {ext : String → Option (State → State)}
    (outPtr : BitVec 64) (q_src q_dst : Quads28) (w_3a0 : BitVec 64)
    (s0 s : State) (P R_frame : SepProp) (post : State → SepProp → Prop)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 340#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = v0)
    (hx19 : s.readReg64 .x19 = outPtr)
    (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = (quads28At (s0.sp - 328#64) q_src ∗
      quads28At (s0.sp - 688#64) q_dst ∗
      ((s0.sp - 464#64) ↦₆₄ w_3a0)) ∗
      R_frame)
    (hnext : ∀ (sf : State) (P' : SepProp),
      sf.pc = decodeStatePlacedEntry + 428#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 (Reg.gpr 0#5) = v0 →
      sf.readReg64 .x19 = outPtr →
      sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = (quads28At (s0.sp - 328#64) q_src ∗
        quads28At (s0.sp - 688#64) q_src ∗
        ((s0.sp - 464#64) ↦₆₄ (s0.sp - 912#64))) ∗
        R_frame →
      SepWP (decodeStatePlacedProg ext) target_pc sf P' post) :
    SepWP (decodeStatePlacedProg ext) target_pc s P post := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  rcases q_src with ⟨⟨⟨s00, s01, s02, s03, s04, s05, s06⟩, ⟨s10, s11, s12, s13, s14, s15, s16⟩⟩,
                     ⟨⟨s20, s21, s22, s23, s24, s25, s26⟩, ⟨s30, s31, s32, s33, s34, s35, s36⟩⟩⟩
  rcases q_dst with ⟨⟨⟨d00, d01, d02, d03, d04, d05, d06⟩, ⟨d10, d11, d12, d13, d14, d15, d16⟩⟩,
                     ⟨⟨d20, d21, d22, d23, d24, d25, d26⟩, ⟨d30, d31, d32, d33, d34, d35, d36⟩⟩⟩
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry,
    quads28At, quads14At, quads7At] at hpc hnext ⊢
  wp_steps 22
  exact hnext _ _
    (by simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, htr])
    (by simp only [arm64_norm, hx0]) (by simp only [arm64_norm, hx19])
    (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21])
    (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx23])
    (by simp only [arm64_norm, hx24]) (by simp only [arm64_norm, hx25])
    (by simp only [arm64_norm, hx26]) (by simp only [arm64_norm, hx27])
    (by simp only [arm64_norm, hx28]) (by simp only [arm64_norm, hx29])
    (by dsimp only [quads28At, quads14At, quads7At])

/-- 224-byte Q-register copy (`+1484..+1576`, 23 instructions) from
    `x29 - 0xe8` (`s0.sp - 328#64`) to `x24` (`s0.sp - 912#64`), followed by `cbnz x0, 0x53bc0`
    (not taken since `x0 = 0#64`) and `ldr x20, [sp, #0x158]`. -/
theorem decodeState_v1_copy_to_state_53a68_placed [LibsignalPlacement] {target_pc v27 : BitVec 64}
    {ext : String → Option (State → State)}
    (outPtr : BitVec 64) (q_src q_dst : Quads28) (remLen : Nat)
    (s0 s : State) (P R_frame : SepProp) (post : State → SepProp → Prop)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1484#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx19 : s.readReg64 .x19 = outPtr)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = (quads28At (s0.sp - 328#64) q_src ∗
      quads28At (s0.sp - 912#64) q_dst ∗
      ((s0.sp - 1048#64) ↦₆₄ BitVec.ofNat 64 remLen)) ∗
      R_frame)
    (hnext : ∀ (sf : State) (P' : SepProp),
      sf.pc = decodeStatePlacedEntry + 1576#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 remLen →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = (quads28At (s0.sp - 328#64) q_src ∗
        quads28At (s0.sp - 912#64) q_src ∗
        ((s0.sp - 1048#64) ↦₆₄ BitVec.ofNat 64 remLen)) ∗
        R_frame →
      SepWP (decodeStatePlacedProg ext) target_pc sf P' post) :
    SepWP (decodeStatePlacedProg ext) target_pc s P post := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  rcases q_src with ⟨⟨⟨s00, s01, s02, s03, s04, s05, s06⟩, ⟨s10, s11, s12, s13, s14, s15, s16⟩⟩,
                     ⟨⟨s20, s21, s22, s23, s24, s25, s26⟩, ⟨s30, s31, s32, s33, s34, s35, s36⟩⟩⟩
  rcases q_dst with ⟨⟨⟨d00, d01, d02, d03, d04, d05, d06⟩, ⟨d10, d11, d12, d13, d14, d15, d16⟩⟩,
                     ⟨⟨d20, d21, d22, d23, d24, d25, d26⟩, ⟨d30, d31, d32, d33, d34, d35, d36⟩⟩⟩
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry,
    quads28At, quads14At, quads7At] at hpc hnext ⊢
  wp_steps 23
  exact hnext _ _
    (by simp only [arm64_norm, hx0])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, htr])
    (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
    (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
    (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
    (by simp only [arm64_norm, hx27]) (by simp only [arm64_norm, hx28])
    (by simp only [arm64_norm, hx29])
    (by dsimp only [quads28At, quads14At, quads7At])

/-! ## 6. Outer Tag 3 Entry (`+312`) -/

end CryptoVerification.SpqrV1.Top.DecodeState
