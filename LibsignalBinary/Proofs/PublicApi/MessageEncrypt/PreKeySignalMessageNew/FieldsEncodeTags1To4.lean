/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodePure -- proof-setup: allow-public-import
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Prost.ProstCodeSym -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import ProofLib.ProgramReflection.SortedFresh
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeVarint
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarint
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# `PreKeySignalMessage::new` Field Encoding: Tags 1–3

Shared register/frame invariants, `encode_varint` and `memcpy` call helpers, and symbolic execution
steps for protobuf tags 1 (`pre_key_id`), 2 (`base_key`), and 3 (`identity_key`) (`+0x25c..+0x35c`).
-/

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
open ProofLib.ProgramReflection
open EncodeVarintNorm

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

abbrev preKeyMsgNewName : String :=
  "<libsignal_protocol::protocol::PreKeySignalMessage>::new"

@[simp, arm64_norm, wp_norm]
theorem fp_sub_48_eq (sp : BitVec 64) :
    (sp + 272#64) + 18446744073709551568#64 = sp + 224#64 := by
  rw [BitVec.add_assoc]; rfl

@[simp, arm64_norm, wp_norm]
theorem fp_sub_48_sub_eq (sp : BitVec 64) :
    (sp + 272#64) - 48#64 = sp + 224#64 := by
  rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl

@[simp, arm64_norm, wp_norm]
theorem fp_sub_40_eq (sp : BitVec 64) :
    (sp + 272#64) + 18446744073709551576#64 = (sp + 224#64) + 8#64 := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; rfl

@[simp, arm64_norm, wp_norm]
theorem fp_sub_32_eq (sp : BitVec 64) :
    (sp + 272#64) + 18446744073709551584#64 = (sp + 224#64) + 16#64 := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; rfl

theorem sp0_sub_96_eq_sp_add_272 (sp0 : BitVec 64) :
    sp0 - 0x60#64 = (sp0 - 0x170#64) + 272#64 := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl

/-! ## Call and Stack Helpers for Field Encoding -/

theorem cap_sub_len_ult_false {bs : List (BitVec 8)} {n : Nat} {cap : BitVec 64}
    (hle : bs.length + n ≤ cap.toNat) :
    (cap - BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 n) = false := by
  have hcap := cap.isLt
  have hbs : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    simp only [BitVec.toNat_ofNat]; omega
  have hsub : (cap - BitVec.ofNat 64 bs.length).toNat = cap.toNat - bs.length := by
    rw [BitVec.toNat_sub_of_le]
    · exact congrArg (cap.toNat - ·) hbs
    · rw [BitVec.le_def]; omega
  simp only [BitVec.ult_eq_decide, hsub, hn, decide_eq_false_iff_not]
  omega

theorem cap_sub_len_ule_true {bs : List (BitVec 8)} {n : Nat} {cap : BitVec 64}
    (hle : bs.length + n ≤ cap.toNat) :
    (BitVec.ofNat 64 n).ule (cap - BitVec.ofNat 64 bs.length) = true := by
  have hcap := cap.isLt
  have hbs : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    simp only [BitVec.toNat_ofNat]; omega
  have hsub : (cap - BitVec.ofNat 64 bs.length).toNat = cap.toNat - bs.length := by
    rw [BitVec.toNat_sub_of_le]
    · exact congrArg (cap.toNat - ·) hbs
    · rw [BitVec.le_def]; omega
  simp only [BitVec.ule_eq_decide, hsub, hn, decide_eq_true_eq]
  omega

theorem bv_len_add_slice (bs payload : List (BitVec 8)) :
    BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length =
      BitVec.ofNat 64 (bs ++ payload).length := by
  simp [List.length_append, BitVec.ofNat_add]

theorem boxU8Buf_nonempty_eq (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8))
    (hne : bs ≠ []) :
    boxU8Buf A ptr bs =
      (ptr ↦ₛ bs) ∗ (⌜ptr ≠ 0#64 ∧ bs.length < 2 ^ 63⌝ ∗ A.live ptr bs.length 1) := by
  simp only [boxU8Buf, hne, ↓reduceIte]
  ac_rfl

/-- Callee-saved registers preserved across all eight field-encoding blocks. -/
@[expose] def PreKeyMsgTagRegs (s0 s : State) : Prop :=
  s.readReg64 .x19 = s0.readReg64 .x19 ∧
  s.readReg64 .x20 = s0.readReg64 .x20 ∧
  s.readReg64 .x21 = s0.readReg64 .x21 ∧
  s.readReg64 .x22 = s0.readReg64 .x22 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  s.readReg64 .fp = s0.readReg64 .fp ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

theorem PreKeyMsgTagRegs.trans {s0 s1 s2 : State} (h1 : PreKeyMsgTagRegs s0 s1) (h2 : PreKeyMsgTagRegs s1 s2) :
    PreKeyMsgTagRegs s0 s2 := by
  reg_chain

theorem PreKeyMsgTagRegs.of_calleeSaved {s0 s1 : State} (h : CalleeSavedPreserved s0 s1) :
    PreKeyMsgTagRegs s0 s1 := by
  reg_chain

theorem preKeyMsgCommonRegs_of_tagRegs {x : PreKeyMsgNewCall} {g : PreKeyMsgFrameGhost} {s0 s sf : State}
    (h : preKeyMsgCommonRegs x g s0 s)
    (hrun : sf.status = .Running)
    (hsp : sf.sp = s.sp)
    (htr : sf.trace = s.trace)
    (hregs : PreKeyMsgTagRegs s sf) :
    preKeyMsgCommonRegs x g s0 sf := by
  have hsf_al : sf.spAligned = true := by simpa only [State.spAligned, hsp] using h.2.2.2.1
  exact ⟨hrun, by reg_chain, h.2.2.1, hsf_al, by reg_chain⟩

theorem stackAt_preKeyMsgSubStack_eq_encodeVarint (sp : BitVec 64) :
    stackAt sp preKeyMsgSubStack =
      stackAt sp encodeVarintStack ∗
      memRegion (sp - 7824#64) 3568 := by
  unfold stackAt
  rw [memRegion_split'
    (b := sp - BitVec.ofNat 64 preKeyMsgSubStack)
    (b' := sp - BitVec.ofNat 64 encodeVarintStack)
    (n := 3568)
    (k := encodeVarintStack)
    (by decide)
    (by
      change sp - 4256#64 = sp - 7824#64 + 3568#64
      exact (bv_sub_add_lit sp 7824 3568).symm)
    (by decide)]
  exact sepConj_comm _ _

theorem stackAt_preKeyMsgSubStack_eq_allocHook (sp : BitVec 64) :
    stackAt sp preKeyMsgSubStack =
      stackAt sp allocHookStack ∗ memRegion (sp - 7824#64) 3728 := by
  unfold stackAt
  rw [memRegion_split' (b := sp - BitVec.ofNat 64 preKeyMsgSubStack)
    (b' := sp - BitVec.ofNat 64 allocHookStack) (n := 3728) (k := allocHookStack) (by decide)
    (by change sp - 4096#64 = sp - 7824#64 + 3728#64; exact (bv_sub_add_lit sp 7824 3728).symm)
    (by decide)]
  exact sepConj_comm _ _

theorem call_noPanic {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf R', sf.status = .Panicked → (sf.mem ⊨ spec.onPanic x s sf ∗ R') → False)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.call_wpp (x := x) (F := F) hcall hpc hrun hsp hlr
    (fun R hm => ?_) hexit
    (fun sf hpan ⟨R', hpost⟩ => (hpanic sf R' hpan hpost).elim)
    hnext
    (hoom := fun sf R' hoom_st hpost => (hoom sf (F ∗ R') hoom_st hpost).elim)
  rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
  exact ⟨hφ, hm⟩

theorem hookSat_memcpy_of_withPanics {ext : String → Option (State → State)}
    (hmemcpy : Rust.withPanics ext "memcpy" = some hookMemcpy) :
    HookSat ext memcpyName (sessionMemcpySpec allocHookStack) :=
  ⟨hookMemcpy, by simpa [Rust.withPanics, Rust.isPanicSymbol, memcpyName] using hmemcpy,
    hookMemcpy_trace_ok allocHookStack⟩

theorem bv_len_beq_zero_false {bs : List (BitVec 8)} (hpos : 0 < bs.length) (hlt : bs.length < 2 ^ 64) :
    (BitVec.ofNat 64 bs.length == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  omega

/-! ## Tag 2 (`base_key`, `+0x2a0..+0x300`) -/

section Placed

open CryptoVerification.LibsignalPublicApi.Placed

@[expose] def EncodePanicPost (s0 : State) : State → SepProp → Prop :=
  fun sf P_f => ∀ R, (sf.mem ⊨ P_f ∗ R) →
    (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)

theorem SepWPp.of_sepWP_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h : SepWP prog mid s P (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen (fun _ _ hcl' hkf => hcl'.of_keepsFrozen hkf) hcl h

private theorem subroutine_ok_withLsCl_of_plain [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsCl lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCl] at hpre
  rw [sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl s0.mem⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre'⟩ := hpre
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hsteps, hout, _⟩ := h.no_fault_before_outcome x R s0 hpc hrun hpre' hsp hL
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCl]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcl0.of_keepsFrozen hsteps.keepsFrozen, hpost⟩
  · exact Or.inr hrest

@[expose] def encodeVarintNoGrowPlacedSpec (A : RustAlloc) : Spec EncodeVarintGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.val ∧ s.readReg64 .x1 = x.v ∧
      x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat ∧ x.cap.toNat < 2 ^ 61⌝ ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp encodeVarintStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      vecU8At A x.v x.cap x.ptr (x.bs ++ encodeVarint x.val) ∗
      A.pool ∗ stackAt s0.sp encodeVarintStack
  onPanic := (encodeVarintSpec A).onPanic

theorem encodeVarintNoGrow_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintNoGrowPlacedSpec A)) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  dsimp only [encodeVarintNoGrowPlacedSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hle, hcap⟩, hpre⟩
  have hpre_ev : s0.mem ⊨ (withLsCodeLoaded lsmpl (encodeVarintSpec A)).pre x s0 ∗ R := by
    dsimp only [withLsCodeLoaded, encodeVarintSpec]
    rw [sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl s0.mem⌝, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcl0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, Or.inr (by omega)⟩, hpre⟩
  refine (CryptoVerification.LibsignalTripleRatchet.Prost.encode_varint_placed_ok
    hshim halloc hrealloc hpanic).mono_outcome x R s0 hpc hrun hpre_ev hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, encodeVarintSpec] at hpost
    dsimp only [withLsCodeLoaded, encodeVarintNoGrowPlacedSpec]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
    rcases hpost with ⟨cap', ptr', hpost⟩
    have hpull :
        ((⌜sf.trace = s0.trace⌝ ∗
          (⌜x.cap.toNat ≤ cap'.toNat ∧
            (x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat →
              cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
            vecU8At A x.v cap' ptr' (x.bs ++ encodeVarint x.val)) ∗
          A.pool ∗ stackAt s0.sp encodeVarintStack) ∗ R) =
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          ((⌜sf.trace = s0.trace⌝ ∗
            vecU8At A x.v cap' ptr' (x.bs ++ encodeVarint x.val) ∗
            A.pool ∗ stackAt s0.sp encodeVarintStack) ∗ R) := by ac_rfl
    rw [hpull, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨_, hno⟩, hpost⟩
    obtain ⟨rfl, rfl⟩ := hno hle
    exact hpost
  · exact Or.inr hrest

theorem step_call_encVarint_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (val v cap ptr sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    (s_base s_init : State)
    (hle : bs.length + (encodeVarint val).length ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 61)
    {ret : BitVec 64} {s0 : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hpc : s0.pc = (blkPl_10).base) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp) (halign : s0.spAligned = true) (hlr : s0.readReg64 .lr = ret_pc)
    (htr : s0.trace = s_base.trace) (hregs : PreKeyMsgTagRegs s_init s0)
    (hx0 : s0.readReg64 .x0 = val) (hx1 : s0.readReg64 .x1 = v)
    (hP : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A cap ptr bs ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp →
      sf.trace = s_base.trace → LibsignalCodeLoaded lsmpl sf.mem → PreKeyMsgTagRegs s_init sf →
      SepWPp (lsProg_41 H) ret sf
        (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bs ++ encodeVarint val).length) ∗
          vecU8Buf A cap ptr (bs ++ encodeVarint val) ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q (EncodePanicPost s_base)) :
    SepWPp (lsProg_41 H) ret s0 P Q (EncodePanicPost s_base) := by
  subst hsp
  have henc := ls_subroutine_ok_cl_of_block (callerProg := lsProg_41 H)
    (encodeVarintNoGrow_placed_ok hshim halloc hrealloc hpanic)
  refine SepWPp.call (x := ⟨val, v, cap, ptr, bs⟩)
    (F := memRegion (s0.sp - 7824#64) 3568 ∗ F)
    henc hpc hrun halign hlr ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => by
      simpa only [withLsCl, encodeVarintNoGrowPlacedSpec, encodeVarintSpec, htr, allocFailedIn]
        using allowPanic_frame id hm) ?_
  · intro R' hm
    dsimp only [withLsCl, encodeVarintNoGrowPlacedSpec]
    rw [sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl s0.mem⌝, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hle, hcap⟩, ?_⟩
    have heq0 : P ∗ R' = (vecU8At A v cap ptr bs ∗ A.pool ∗ stackAt s0.sp encodeVarintStack) ∗
        ((memRegion (s0.sp - 7824#64) 3568 ∗ F) ∗ R') := by
      rw [hP, stackAt_preKeyMsgSubStack_eq_encodeVarint s0.sp, vecU8At_eq_header_sep_buf, vecHeader]
      ac_rfl
    exact heq0 ▸ hm
  intro sf hpcf hrunf hspf hcsf
  dsimp only [withLsCl, encodeVarintNoGrowPlacedSpec]; simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hclf => ?_
  refine SepWPp.pure_elim fun htrf => ?_
  have heq1 :
      vecU8At A v cap ptr (bs ++ encodeVarint val) ∗ A.pool ∗ stackAt s0.sp encodeVarintStack ∗
        memRegion (s0.sp - 7824#64) 3568 ∗ F =
      (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bs ++ encodeVarint val).length) ∗
        vecU8Buf A cap ptr (bs ++ encodeVarint val) ∗ A.pool ∗ stackAt s0.sp preKeyMsgSubStack) ∗ F) := by
    rw [stackAt_preKeyMsgSubStack_eq_encodeVarint s0.sp, vecU8At_eq_header_sep_buf, vecHeader]
    ac_rfl
  rw [heq1]
  exact hnext sf hpcf hrunf hspf (htrf.trans htr) hclf (by reg_chain)

theorem step_call_memcpy_placed [LibsignalPlacement] {H : LibsignalHooks}
    (hmemcpy : HookSat H "memcpy" framelessMemcpySpec)
    (dst src sp ret_pc v23 v26 : BitVec 64) (payload : List (BitVec 8))
    (tr : List TraceEvent) (s_init : State)
    {ret : BitVec 64} {s0 : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hpc : s0.pc = lsρ "memcpy") (hrun : s0.status = .Running)
    (hsp : s0.sp = sp) (halign : s0.spAligned = true) (hlr : s0.readReg64 .lr = ret_pc)
    (htr : s0.trace = tr) (hregs : PreKeyMsgTagRegs s_init s0)
    (hx23 : s0.readReg64 .x23 = v23) (hx26 : s0.readReg64 .x26 = v26)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = src)
    (hx2 : (s0.readReg64 .x2).toNat = payload.length)
    (hP : P = (memRegion dst payload.length ∗ (src ↦ₛ payload)) ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp →
      sf.trace = tr → LibsignalCodeLoaded lsmpl sf.mem → PreKeyMsgTagRegs s_init sf →
      sf.readReg64 .x23 = v23 → sf.readReg64 .x26 = v26 →
      SepWPp (lsProg_41 H) ret sf (((dst ↦ₛ payload) ∗ (src ↦ₛ payload)) ∗ F) Q Qp) :
    SepWPp (lsProg_41 H) ret s0 P Q Qp := by
  subst hsp
  have hmc := ls_hook_ok_of_mem (prog := lsProg_41 H) (sym := "memcpy") hmemcpy
  intro R hm hL
  have hpre : s0.mem ⊨ framelessMemcpySpec.pre (dst, src, payload) s0 ∗ (F ∗ R) := by
    dsimp only [framelessMemcpySpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    rw [hP, sepConj_assoc] at hm; exact hm
  obtain ⟨sf, hsteps, hout, _⟩ :=
    hmc.no_fault_before_outcome (dst, src, payload) (F ∗ R) s0 hpc hrun hpre halign hL
  rcases hout with ⟨⟨hpcf, _, hrunf⟩, ⟨hspf, hcsf⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · dsimp only [framelessMemcpySpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨_, htrf⟩, hpost⟩
    rw [hlr] at hpcf
    have hpost' : sf.mem ⊨ (((dst ↦ₛ payload) ∗ (src ↦ₛ payload)) ∗ F) ∗ R := by
      simpa only [sepConj_assoc] using hpost
    obtain ⟨sf', hsteps', hout'⟩ :=
      hnext sf hpcf hrunf hspf (htrf.trans htr) (hcl.of_keepsFrozen hsteps.keepsFrozen)
        (by reg_chain) (by reg_chain) (by reg_chain) R hpost' (hsteps.codeLoaded hL)
    exact ⟨sf', hsteps.trans hsteps', hout'⟩
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

theorem step_preKeyMsg_tag1_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64) (s_base : State)
    (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 604#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = s_base.trace)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx20 : (s.readReg64 .x20).setWidth 32 = (if x.preKeyId.isSome then 1#32 else 0#32))
    (hx25 : (s.readReg64 .x25).setWidth 32 = g.preKeyVal32)
    (hP : P = (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix0 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix0 x) ∗
      A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 672#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = s_base.trace → LibsignalCodeLoaded lsmpl sm.mem →
      sm.readReg64 .x1 = BitVec.ofNat 64 (serPrefix1 x).length → PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix1 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix1 x) ∗
          A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) Q (EncodePanicPost s_base)) :
    SepWPp (lsProg_41 H) ret s P Q (EncodePanicPost s_base) := by
  rcases hwf with ⟨hser_lt, _, hpk_val, _⟩
  have hcap_toNat : (BitVec.ofNat 64 x.model.serialized.length).toNat = x.model.serialized.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have ⟨h0_len, h01_le, h12_le, h23_le, h34_le, h45_le, h56_le, h67_le, h78_le, h8_len⟩ :=
    serPrefix_lengths_le x
  subst hP
  cases hpk : x.preKeyId with
  | none =>
    simp only [hpk, Option.isSome, Bool.false_eq_true, ↓reduceIte] at hx20
    have hw20 : s.readReg32 .x20 = 0#32 := by simpa [State.readReg32] using hx20
    have hser1 : serPrefix1 x = serPrefix0 x := by simp [serPrefix1, hpk, LibsignalSessionApi.Prost.uint32Field]
    have h1_len_bv : BitVec.ofNat 64 (serPrefix1 x).length = 1#64 := by simp [hser1, h0_len]
    apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_41).base + 672#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl1; rw [← hser1]
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
      (by rw [h1_len_bv]; simp only [arm64_norm, *])
      (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self])
  | some pid =>
    simp only [hpk, Option.isSome, ↓reduceIte] at hx20
    rw [hpk_val pid hpk] at hx25
    have hw20 : s.readReg32 .x20 = 1#32 := by simpa [State.readReg32] using hx20
    have hw25 : s.readReg32 .x25 = pid := by simpa [State.readReg32] using hx25
    have hser1 : (serPrefix0 x ++ [0x08#8]) ++ encodeVarint (pid.zeroExtend 64) = serPrefix1 x := by
      simp [serPrefix1, hpk, prost_uint32Field_some, prost_key_1_0, List.append_assoc]
    have h1_len : (serPrefix1 x).length = 2 + (encodeVarint (pid.zeroExtend 64)).length := by
      rw [← hser1, List.length_append, List.length_append, h0_len, List.length_singleton]
    have hvar_pos : 1 ≤ (encodeVarint (pid.zeroExtend 64)).length := by
      unfold encodeVarint encodeVarintAux; split <;> simp
    have hlt0 : (serPrefix0 x).length < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
    have hbeq0 := cap_beq_len_false hlt0
    have h0_len_bv : BitVec.ofNat 64 (serPrefix0 x).length = 1#64 := by simp [h0_len]
    rw [h0_len_bv] at hbeq0
    have hle_var : (serPrefix0 x ++ [0x08#8]).length + (encodeVarint (pid.zeroExtend 64)).length ≤
        (BitVec.ofNat 64 x.model.serialized.length).toNat := by
      rw [List.length_append, h0_len, List.length_singleton]; omega
    rw [vecU8Buf_eq_open_one A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix0 x) hlt0, h0_len_bv]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_10).base); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *])
    intro hcl0
    have hsnoc := vecU8Buf_snoc_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix0 x) 8#8 hlt0
    rw [h0_len_bv] at hsnoc; rw [hsnoc]
    refine step_call_encVarint_placed hshim halloc hrealloc hpanic
      (pid.zeroExtend 64) (sp + 224#64) (BitVec.ofNat 64 x.model.serialized.length) g.serPtr sp
      ((blkPl_41).base + 660#64) (serPrefix0 x ++ [8#8]) s_base s hle_var (by omega)
      (F := F) hcl0
      (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simpa only [State.spAligned, arm64_norm, *] using halign)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp [h0_len])
      fun sf1 hpcf1 hrunf1 hspf1 htrf1 hclf1 hregs1 => ?_
    have hfp1 : sf1.readReg64 .fp = sp + 272#64 := by reg_chain
    rw [hser1]
    apply SepWPp.of_sepWP_lscl hclf1 (mid := (blkPl_41).base + 672#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl2
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl2
      (by simp only [arm64_norm, *])
      (PreKeyMsgTagRegs.trans hregs1 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))

theorem step_preKeyMsg_tag2_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hmemcpy : HookSat H "memcpy" framelessMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64) (s_base : State)
    (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 672#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = s_base.trace)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (serPrefix1 x).length)
    (hx24 : s.readReg64 .x24 = 33#64) (hx28 : s.readReg64 .x28 = g.bkSerPtr)
    (hP : P = (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix1 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix1 x) ∗
      boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 768#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = s_base.trace → LibsignalCodeLoaded lsmpl sm.mem →
      sm.readReg64 .x23 = BitVec.ofNat 64 (serPrefix2 x).length →
      sm.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix2 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix2 x) ∗
          boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q (EncodePanicPost s_base)) :
    SepWPp (lsProg_41 H) ret s P Q (EncodePanicPost s_base) := by
  rcases hwf with ⟨hser_lt, _⟩
  have hbk_len : x.baseKey.serialize.length = 33 := by simp [PublicKey.serialize]
  have hcap_toNat : (BitVec.ofNat 64 x.model.serialized.length).toNat = x.model.serialized.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have ⟨h0_len, h01_le, h12_le, h23_le, h34_le, h45_le, h56_le, h67_le, h78_le, h8_len⟩ :=
    serPrefix_lengths_le x
  have hcap_pos : 0 < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hbk_bv : BitVec.ofNat 64 x.baseKey.serialize.length = 33#64 := by simp [hbk_len]
  have hser2 : (serPrefix1 x ++ 18#8 :: encodeVarint 33#64) ++ x.baseKey.serialize = serPrefix2 x := by
    rw [serPrefix2, prost_bytesField_some 2 x.baseKey.serialize (by omega), prost_key_2_2, hbk_bv]
    simp only [← List.append_assoc, List.singleton_append]
  have hvar33_len : (encodeVarint 33#64).length = 1 := by rw [encodeVarint_33]; rfl
  have h2_len : (serPrefix2 x).length = (serPrefix1 x).length + 1 + 1 + 33 := by
    rw [← hser2, List.length_append, List.length_append, List.length_cons, hvar33_len, hbk_len]
  have hlt1 : (serPrefix1 x).length < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hbeq1 := cap_beq_len_false hlt1
  have hle_var : (serPrefix1 x ++ [0x12#8]).length + (encodeVarint 33#64).length ≤
      (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_singleton, hvar33_len]; omega
  have hle_slice : (serPrefix1 x ++ 18#8 :: encodeVarint 33#64).length +
      x.baseKey.serialize.length ≤ (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_cons, hvar33_len, hbk_len]; omega
  subst hP
  rw [vecU8Buf_eq_open_one A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix1 x) hlt1]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_10).base); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *])
  intro hcl0
  rw [vecU8Buf_snoc_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix1 x) 18#8 hlt1,
    bv_len_add_one (serPrefix1 x) 18#8]
  refine step_call_encVarint_placed hshim halloc hrealloc hpanic
    33#64 (sp + 224#64) (BitVec.ofNat 64 x.model.serialized.length) g.serPtr sp
    ((blkPl_41).base + 716#64) (serPrefix1 x ++ [18#8]) s_base s hle_var (by omega)
    (F := boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗ F) hcl0
    (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simpa only [State.spAligned, arm64_norm, *] using halign)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by ac_rfl)
    fun sf1 hpcf1 hrunf1 hspf1 htrf1 hclf1 hregs1 => ?_
  simp only [List.append_assoc, List.singleton_append]
  have hfp1 : sf1.readReg64 .fp = sp + 272#64 := by reg_chain
  have hx24_1 : sf1.readReg64 .x24 = 33#64 := by reg_chain
  have hx28_1 : sf1.readReg64 .x28 = g.bkSerPtr := by reg_chain
  have hult1 := cap_sub_len_ult_false hle_slice
  have hule1 := cap_sub_len_ule_true hle_slice
  rw [hbk_bv] at hult1 hule1
  have hbk_ne : x.baseKey.serialize ≠ [] := by intro h; simp [h] at hbk_len
  rw [vecU8Buf_eq_open_slice A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
    (serPrefix1 x ++ 18#8 :: encodeVarint 33#64) x.baseKey.serialize.length hle_slice hcap_pos,
    boxU8Buf_nonempty_eq A g.bkSerPtr x.baseKey.serialize hbk_ne]
  apply SepWPp.of_sepWP_lscl hclf1 (mid := lsρ "memcpy"); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hclf1'
  refine step_call_memcpy_placed hmemcpy
    (g.serPtr + BitVec.ofNat 64 (serPrefix1 x ++ 18#8 :: encodeVarint 33#64).length)
    g.bkSerPtr sp ((blkPl_41).base + 760#64)
    (BitVec.ofNat 64 (serPrefix1 x ++ 18#8 :: encodeVarint 33#64).length)
    (BitVec.ofNat 64 x.model.serialized.length)
    x.baseKey.serialize s_base.trace s
    (F := ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix1 x ++ 18#8 :: encodeVarint 33#64).length) ∗
      vecSliceRest A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
        (serPrefix1 x ++ 18#8 :: encodeVarint 33#64) x.baseKey.serialize.length ∗
      A.pool ∗ stackAt sp preKeyMsgSubStack ∗
      (⌜g.bkSerPtr ≠ 0#64 ∧ x.baseKey.serialize.length < 2 ^ 63⌝ ∗ A.live g.bkSerPtr x.baseKey.serialize.length 1) ∗ F)
    hclf1' (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simpa only [State.spAligned, arm64_norm, *] using halign)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (PreKeyMsgTagRegs.trans hregs1 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by ac_rfl)
    fun sf2 hpcf2 hrunf2 hspf2 htrf2 hclf2 hregs2 hx23_2 hx26_2 => ?_
  have hfp2 : sf2.readReg64 .fp = sp + 272#64 := by reg_chain
  have hx24_2 : sf2.readReg64 .x24 = 33#64 := by reg_chain
  simp only [arm64_norm] at hx23_2 hx24_2
  have hadd_len : BitVec.ofNat 64 (serPrefix1 x ++ 18#8 :: encodeVarint 33#64).length + 33#64 =
      BitVec.ofNat 64 (serPrefix2 x).length := by
    simp only [h2_len, List.length_append, List.length_cons, hvar33_len, BitVec.ofNat_add]; ac_rfl
  clear h2_len
  have hpost_eq :
      (((g.serPtr + BitVec.ofNat 64 (serPrefix1 x ++ 18#8 :: encodeVarint 33#64).length) ↦ₛ x.baseKey.serialize) ∗
        (g.bkSerPtr ↦ₛ x.baseKey.serialize)) ∗
      (((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
        (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
        (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix1 x ++ 18#8 :: encodeVarint 33#64).length) ∗
        vecSliceRest A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
          (serPrefix1 x ++ 18#8 :: encodeVarint 33#64) x.baseKey.serialize.length ∗
        A.pool ∗ stackAt sp preKeyMsgSubStack ∗
        (⌜g.bkSerPtr ≠ 0#64 ∧ x.baseKey.serialize.length < 2 ^ 63⌝ ∗
          A.live g.bkSerPtr x.baseKey.serialize.length 1) ∗ F) =
      ((((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
        (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
        (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix1 x ++ 18#8 :: encodeVarint 33#64).length) ∗
        vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix2 x) ∗
        boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) := by
    rw [← hser2,
      ← vecU8Buf_append_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
        (serPrefix1 x ++ 18#8 :: encodeVarint 33#64) x.baseKey.serialize hcap_pos,
      boxU8Buf_nonempty_eq A g.bkSerPtr x.baseKey.serialize hbk_ne]; ac_rfl
  rw [hpost_eq]
  apply SepWPp.of_sepWP_lscl hclf2 (mid := (blkPl_41).base + 768#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hcl3
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl3
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (PreKeyMsgTagRegs.trans hregs2 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))

theorem step_preKeyMsg_tag3_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hmemcpy : HookSat H "memcpy" framelessMemcpySpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp : BitVec 64) (s_base : State)
    (hwf : PreKeyMsgGhostWf x g)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 768#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : s.spAligned = true) (htr : s.trace = s_base.trace)
    (hfp : s.readReg64 .fp = sp + 272#64)
    (hx22 : s.readReg64 .x22 = 33#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (serPrefix2 x).length)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length)
    (hP : P = (((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix2 x).length) ∗
      vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix2 x) ∗
      boxU8Buf A g.ikSerPtr x.ik.serialize ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = (blkPl_41).base + 860#64 → sm.status = .Running →
      sm.sp = sp → sm.trace = s_base.trace → LibsignalCodeLoaded lsmpl sm.mem →
      sm.readReg64 .x23 = BitVec.ofNat 64 (serPrefix3 x).length →
      sm.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length →
      PreKeyMsgTagRegs s sm →
      SepWPp (lsProg_41 H) ret sm
        ((((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
          ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
          (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix3 x).length) ∗
          vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix3 x) ∗
          boxU8Buf A g.ikSerPtr x.ik.serialize ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F)
        Q (EncodePanicPost s_base)) :
    SepWPp (lsProg_41 H) ret s P Q (EncodePanicPost s_base) := by
  rcases hwf with ⟨hser_lt, _⟩
  have hik_len : x.ik.serialize.length = 33 := by simp [IdentityKey.serialize, PublicKey.serialize]
  have hcap_toNat : (BitVec.ofNat 64 x.model.serialized.length).toNat = x.model.serialized.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have ⟨h0_len, h01_le, h12_le, h23_le, h34_le, h45_le, h56_le, h67_le, h78_le, h8_len⟩ :=
    serPrefix_lengths_le x
  have hcap_pos : 0 < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hik_bv : BitVec.ofNat 64 x.ik.serialize.length = 33#64 := by simp [hik_len]
  have hser3 : (serPrefix2 x ++ 26#8 :: encodeVarint 33#64) ++ x.ik.serialize = serPrefix3 x := by
    rw [serPrefix3, prost_bytesField_some 3 x.ik.serialize (by omega), prost_key_3_2, hik_bv]
    simp only [← List.append_assoc, List.singleton_append]
  have hvar33_len : (encodeVarint 33#64).length = 1 := by rw [encodeVarint_33]; rfl
  have h3_len : (serPrefix3 x).length = (serPrefix2 x).length + 1 + 1 + 33 := by
    rw [← hser3, List.length_append, List.length_append, List.length_cons, hvar33_len, hik_len]
  have hlt2 : (serPrefix2 x).length < (BitVec.ofNat 64 x.model.serialized.length).toNat := by omega
  have hbeq2 := cap_beq_len_false hlt2
  have hle_var : (serPrefix2 x ++ [26#8]).length + (encodeVarint 33#64).length ≤
      (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_singleton, hvar33_len]; omega
  have hle_slice : (serPrefix2 x ++ 26#8 :: encodeVarint 33#64).length +
      x.ik.serialize.length ≤ (BitVec.ofNat 64 x.model.serialized.length).toNat := by
    rw [List.length_append, List.length_cons, hvar33_len, hik_len]; omega
  subst hP
  rw [vecU8Buf_eq_open_one A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix2 x) hlt2]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_10).base); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *])
  intro hcl0
  rw [vecU8Buf_snoc_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix2 x) 26#8 hlt2,
    bv_len_add_one (serPrefix2 x) 26#8]
  refine step_call_encVarint_placed hshim halloc hrealloc hpanic
    33#64 (sp + 224#64) (BitVec.ofNat 64 x.model.serialized.length) g.serPtr sp
    ((blkPl_41).base + 808#64) (serPrefix2 x ++ [26#8]) s_base s hle_var (by omega)
    (F := ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗ boxU8Buf A g.ikSerPtr x.ik.serialize ∗ F) hcl0
    (by simp only [arm64_norm, *]; rfl) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simpa only [State.spAligned, arm64_norm, *] using halign)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by ac_rfl)
    fun sf1 hpcf1 hrunf1 hspf1 htrf1 hclf1 hregs1 => ?_
  simp only [List.append_assoc, List.singleton_append]
  have halign1 : sf1.spAligned = true := by simpa only [State.spAligned, hspf1, hsp] using halign
  have hfp1 : sf1.readReg64 .fp = sp + 272#64 := by reg_chain
  have hx22_1 : sf1.readReg64 .x22 = 33#64 := by reg_chain
  have hult1 := cap_sub_len_ult_false hle_slice
  have hule1 := cap_sub_len_ule_true hle_slice
  rw [hik_bv] at hult1 hule1
  have hik_ne : x.ik.serialize ≠ [] := by intro h; simp [h] at hik_len
  rw [vecU8Buf_eq_open_slice A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
    (serPrefix2 x ++ 26#8 :: encodeVarint 33#64) x.ik.serialize.length hle_slice hcap_pos,
    boxU8Buf_nonempty_eq A g.ikSerPtr x.ik.serialize hik_ne]
  apply SepWPp.of_sepWP_lscl hclf1 (mid := lsρ "memcpy"); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hclf1'
  refine step_call_memcpy_placed hmemcpy
    (g.serPtr + BitVec.ofNat 64 (serPrefix2 x ++ 26#8 :: encodeVarint 33#64).length)
    g.ikSerPtr sp ((blkPl_41).base + 852#64)
    (BitVec.ofNat 64 (serPrefix2 x ++ 26#8 :: encodeVarint 33#64).length)
    (BitVec.ofNat 64 x.model.serialized.length)
    x.ik.serialize s_base.trace s
    (F := ((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
      ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
      (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
      (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix2 x ++ 26#8 :: encodeVarint 33#64).length) ∗
      vecSliceRest A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
        (serPrefix2 x ++ 26#8 :: encodeVarint 33#64) x.ik.serialize.length ∗
      A.pool ∗ stackAt sp preKeyMsgSubStack ∗
      (⌜g.ikSerPtr ≠ 0#64 ∧ x.ik.serialize.length < 2 ^ 63⌝ ∗ A.live g.ikSerPtr x.ik.serialize.length 1) ∗ F)
    hclf1' (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simpa only [State.spAligned, arm64_norm, *] using halign1)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (PreKeyMsgTagRegs.trans hregs1 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by ac_rfl)
    fun sf2 hpcf2 hrunf2 hspf2 htrf2 hclf2 hregs2 hx23_2 hx26_2 => ?_
  have hfp2 : sf2.readReg64 .fp = sp + 272#64 := by reg_chain
  have hx22_2 : sf2.readReg64 .x22 = 33#64 := by reg_chain
  simp only [arm64_norm] at hx23_2 hx22_2
  have hadd_len : BitVec.ofNat 64 (serPrefix2 x ++ 26#8 :: encodeVarint 33#64).length + 33#64 =
      BitVec.ofNat 64 (serPrefix3 x).length := by
    simp only [h3_len, List.length_append, List.length_cons, hvar33_len, BitVec.ofNat_add]; ac_rfl
  clear h3_len
  have hpost_eq :
      (((g.serPtr + BitVec.ofNat 64 (serPrefix2 x ++ 26#8 :: encodeVarint 33#64).length) ↦ₛ x.ik.serialize) ∗
        (g.ikSerPtr ↦ₛ x.ik.serialize)) ∗
      (((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
        ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
        (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
        (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix2 x ++ 26#8 :: encodeVarint 33#64).length) ∗
        vecSliceRest A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
          (serPrefix2 x ++ 26#8 :: encodeVarint 33#64) x.ik.serialize.length ∗
        A.pool ∗ stackAt sp preKeyMsgSubStack ∗
        (⌜g.ikSerPtr ≠ 0#64 ∧ x.ik.serialize.length < 2 ^ 63⌝ ∗
          A.live g.ikSerPtr x.ik.serialize.length 1) ∗ F) =
      ((((sp + 16#64) ↦₆₄ g.ikSerPtr) ∗
        ((sp + 224#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
        (((sp + 224#64) + 8#64) ↦₆₄ g.serPtr) ∗
        (((sp + 224#64) + 16#64) ↦₆₄ BitVec.ofNat 64 (serPrefix2 x ++ 26#8 :: encodeVarint 33#64).length) ∗
        vecU8Buf A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr (serPrefix3 x) ∗
        boxU8Buf A g.ikSerPtr x.ik.serialize ∗ A.pool ∗ stackAt sp preKeyMsgSubStack) ∗ F) := by
    rw [← hser3,
      ← vecU8Buf_append_eq A (BitVec.ofNat 64 x.model.serialized.length) g.serPtr
        (serPrefix2 x ++ 26#8 :: encodeVarint 33#64) x.ik.serialize hcap_pos,
      boxU8Buf_nonempty_eq A g.ikSerPtr x.ik.serialize hik_ne]; ac_rfl
  rw [hpost_eq]
  apply SepWPp.of_sepWP_lscl hclf2 (mid := (blkPl_41).base + 860#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hcl3
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl3
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (PreKeyMsgTagRegs.trans hregs2 (by simp only [PreKeyMsgTagRegs, arm64_norm, and_self]))

end Placed

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode
