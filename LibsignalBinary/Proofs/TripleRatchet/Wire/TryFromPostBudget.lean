/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanupBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDeserBudget
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSomeBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxesBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost
import ProofLib.Sep
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSome -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
public import ProofLib.Placed.OpcodeExclusion
import LibsignalBinary.Proofs.Placed.BudgetPoolSync

/-!
# Budget-Threaded Post-Loop Composition for `<SignalMessage>::try_from`

Defines output-indexed post-loop allocator event envelopes (`TryFromPostPreEnv`, `TryFromPostEnv`),
proves `FreeOnlyEvs` transport lemmas, and composes the relocatable `[LibsignalPlacement]`
budget-threaded post-loop theorem `tryFrom_post_wp_placed` on Block `85`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession
  (ProtoSignalMessage PublicKey SignalMessage SignalProtocolError)
open CryptoVerification (LibsignalPlacement LibsignalHooks)
open CryptoVerification.RustHeap (RustAlloc vecHeader)
open CryptoVerification.LibsignalProtoCodec (decode protoSignalCodec)
open CryptoVerification.LibsignalTripleRatchet
  (TryFromGhost blkPl_85 logOff decodeErrorAt boxU8Buf)
open CryptoVerification.LibsignalTripleRatchetRepr
  (signalMessageResultAt speWord noneCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (skipFieldStackX wireSignalMessageOf)
open CryptoVerification.LibsignalTripleRatchet.Wire renaming SepWPp → WSepWPp
open CryptoVerification.LibsignalTripleRatchet.Wire
  (tryFromPlacedProg tryFromPlacedImg
   PostEpilogueStatePlaced LoopExitStatePlaced
   deallocSlot vecU8Buf optVecU8Buf optVecU8Buf_entails_deallocSlot optU32TagVal
   optBoxU8Pending deserializeResult33At
   pkBytesOf pkLayoutAt pkLayoutAt_eq_pointsToBytes exists_pkBytesOf sevenBytesHeadAt
   pointsTo32_pair_eq_pointsTo64 memRegion120_split16
   tryFrom_eq_of_gt9 msg_bounds_of_decode
   spUnused0 spUnused104 memRegion72_104_unpack
   memRegion104_0_unpack pcVal_if_eq_getD
   wireSignalMessageOf_rk_some_entails
   zext32_zext64_8
   memRegion176_split_88_16_72 memRegion176_split_104_72
   pure_true_emp entails_of_eq)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget SeqEnv
   fitsEvents_append)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefsBudget
  (TripleRatchetHooksWPlaced DropDecodeErrorOkWPlaced DropSpeOkWPlaced
   IntoBoxedSliceOkPlaced TryCloneFromRefOkPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanupBudget
  (postNoPanicQp wpp_mono_post_noPanic wpp_frame_noPanic post_none_wp_placed)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDeserBudget
  (post_rk_none_wp_placed post_deser_err_wp_placed post_deser_ok_head_wp_placed
   post_counter_none_wp_placed post_counter_some_head_wp_placed post_ct_none_wp_placed)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSomeBudget
  (post_rk_some_head_wp_placed)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxesBudget
  (IntoBoxedCapEnv IntoBoxedOptCapEnv PostCtBoxesEnv PostCtBoxesPost
   TryCloneBytesEnv PostClonePackEnv
   post_ct_some_boxes_wp_placed post_clone_and_pack_wp_placed)

/-! ## Post-loop allocator event envelopes and transport lemmas -/

/-- Capacity-bounded allocator event envelope of `<Vec<u8>>::into_boxed_slice`:
quantifies over all valid `Vec<u8>` capacities `bs.length ≤ cap.toNat < 2 ^ 63`. -/
@[expose] def IntoBoxedBoundedEnv (bs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  ∃ cap : BitVec 64, bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ IntoBoxedCapEnv cap bs evs

/-- Optional capacity-bounded allocator event envelope for `m'.addresses`. -/
@[expose] def IntoBoxedOptBoundedEnv : Option (List (BitVec 8)) → List AllocEvent → Prop
  | none => (· = [])
  | some ad => IntoBoxedBoundedEnv ad

/-- Allocation-phase envelope on the `.ok msg` path of `<SignalMessage>::try_from` post-loop:
`into_boxed_slice` on `ciphertext`, optional `into_boxed_slice` on `addresses`, and
`try_clone_from_ref_in` on `serialized`. -/
@[expose] def TryFromPostOkAllocEnv (bs ct : List (BitVec 8))
    (adOpt : Option (List (BitVec 8))) : List AllocEvent → Prop :=
  SeqEnv (IntoBoxedBoundedEnv ct) (SeqEnv (IntoBoxedOptBoundedEnv adOpt) (TryCloneBytesEnv bs))

/-- Output-indexed precondition budget envelope of `<SignalMessage>::try_from` post-loop:
empty (`evs = []`, requiring zero budget) on `.error _`, and `SeqEnv FreeOnlyEvs TryFromPostOkAllocEnv`
on `.ok msg`. -/
@[expose] def TryFromPostOutPreEnv : Except SignalProtocolError SignalMessage → List AllocEvent → Prop
  | .error _ => (· = [])
  | .ok msg =>
    SeqEnv FreeOnlyEvs (TryFromPostOkAllocEnv msg.serialized msg.ciphertext msg.addresses)

/-- Output-indexed postcondition event envelope of `<SignalMessage>::try_from` post-loop:
`TryFromPostOutPreEnv out` followed by trailing `FreeOnlyEvs` cleanup deallocations. -/
@[expose] def TryFromPostOutEnv (out : Except SignalProtocolError SignalMessage) :
    List AllocEvent → Prop :=
  SeqEnv (TryFromPostOutPreEnv out) FreeOnlyEvs

/-- Input-bytes precondition budget envelope of `tryFrom_post_wp_placed`. -/
@[expose] def TryFromPostPreEnv (bs : List (BitVec 8)) : List AllocEvent → Prop :=
  TryFromPostOutPreEnv (SignalMessage.tryFrom protoSignalCodec bs)

/-- Input-bytes postcondition event envelope of `tryFrom_post_wp_placed`. -/
@[expose] def TryFromPostEnv (bs : List (BitVec 8)) : List AllocEvent → Prop :=
  TryFromPostOutEnv (SignalMessage.tryFrom protoSignalCodec bs)

theorem tryFromPostOutEnv_of_error_freeOnly {e : SignalProtocolError} {evs : List AllocEvent}
    (hf : FreeOnlyEvs evs) : TryFromPostOutEnv (.error e) evs :=
  SeqEnv.append (evs₁ := []) (evs₂ := evs) rfl hf

private theorem tryFromPostOutEnv_of_eq_error {out : Except SignalProtocolError SignalMessage}
    {e : SignalProtocolError} {evs : List AllocEvent}
    (hout : out = .error e) (hf : FreeOnlyEvs evs) : TryFromPostOutEnv out evs :=
  hout ▸ tryFromPostOutEnv_of_error_freeOnly hf

theorem freeOnly_of_tryFromPostOutEnv_error {e : SignalProtocolError} {evs : List AllocEvent}
    (h : TryFromPostOutEnv (.error e) evs) : FreeOnlyEvs evs := by
  rcases h with rfl | ⟨a, b, rfl, rfl, hfb⟩
  · exact .nil
  · exact hfb

theorem fitsEnv_tryFromPostOutPre_step_freeOnly {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {out : Except SignalProtocolError SignalMessage} {evs₀ : List AllocEvent}
    (hf : FreeOnlyEvs evs₀) (h : FitsEnv M lim st (TryFromPostOutPreEnv out)) :
    FitsEnv M lim (M.stepEvents evs₀ st) (TryFromPostOutPreEnv out) := by
  cases out with
  | error e =>
    intro evs hevs
    subst hevs
    trivial
  | ok msg =>
    intro evs hevs
    have hcomb : TryFromPostOutPreEnv (.ok msg) (evs₀ ++ evs) := by
      rcases hevs with h1 | ⟨e1, e2, rfl, h1, h2⟩
      · exact Or.inl (hf.append h1)
      · rw [← List.append_assoc]
        exact SeqEnv.append (hf.append h1) h2
    exact ((fitsEvents_append M lim evs₀ evs st).mp (h _ hcomb)).2

theorem tryFromPostOutEnv_prepend_freeOnly {out : Except SignalProtocolError SignalMessage}
    {evs₀ evs₁ : List AllocEvent}
    (hf : FreeOnlyEvs evs₀) (h : TryFromPostOutEnv out evs₁) :
    TryFromPostOutEnv out (evs₀ ++ evs₁) := by
  cases out with
  | error e =>
    exact tryFromPostOutEnv_of_error_freeOnly (hf.append (freeOnly_of_tryFromPostOutEnv_error h))
  | ok msg =>
    rcases h with hpre | ⟨e1, e2, rfl, hpre, hf2⟩
    · refine Or.inl ?_
      rcases hpre with h1 | ⟨a, b, rfl, h1, h2⟩
      · exact Or.inl (hf.append h1)
      · rw [← List.append_assoc]
        exact SeqEnv.append (hf.append h1) h2
    · rw [← List.append_assoc]
      refine SeqEnv.append ?_ hf2
      rcases hpre with h1 | ⟨a, b, rfl, h1, h2⟩
      · exact Or.inl (hf.append h1)
      · rw [← List.append_assoc]
        exact SeqEnv.append (hf.append h1) h2

private theorem intoBoxedOptBounded_of_cap {adCap : BitVec 64}
    {adOpt : Option (List (BitVec 8))} {evs : List AllocEvent}
    (had_bnd : ∀ ad, adOpt = some ad → ad.length ≤ adCap.toNat ∧ adCap.toNat < 2 ^ 63)
    (h : IntoBoxedOptCapEnv adCap adOpt evs) :
    IntoBoxedOptBoundedEnv adOpt evs := by
  cases adOpt with
  | none => exact h
  | some ad =>
    have hb := had_bnd ad rfl
    exact ⟨adCap, hb.1, hb.2, h⟩

private theorem fitsEnv_postCtBoxes_of_ok {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {msg : SignalMessage} {ctCap adCap : BitVec 64}
    (hct_le : msg.ciphertext.length ≤ ctCap.toNat) (hct_lt : ctCap.toNat < 2 ^ 63)
    (had_bnd : ∀ ad, msg.addresses = some ad → ad.length ≤ adCap.toNat ∧ adCap.toNat < 2 ^ 63)
    (hFit : FitsEnv M lim st (TryFromPostOutPreEnv (.ok msg))) :
    FitsEnv M lim st (PostCtBoxesEnv ctCap adCap msg.ciphertext msg.addresses) := by
  refine hFit.mono fun evs hevs => ?_
  rcases hevs with hf | ⟨e0, e12, rfl, hf, h12⟩
  · exact Or.inl hf
  · refine SeqEnv.append hf ?_
    rcases h12 with h1 | ⟨e1, e2, rfl, h1, h2⟩
    · exact Or.inl ⟨ctCap, hct_le, hct_lt, h1⟩
    · exact SeqEnv.append ⟨ctCap, hct_le, hct_lt, h1⟩ (Or.inl (intoBoxedOptBounded_of_cap had_bnd h2))

private theorem fitsEnv_tryClone_of_postCtBoxes {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {msg : SignalMessage} {ctCap adCap : BitVec 64} {evs_box : List AllocEvent}
    (hct_le : msg.ciphertext.length ≤ ctCap.toNat) (hct_lt : ctCap.toNat < 2 ^ 63)
    (had_bnd : ∀ ad, msg.addresses = some ad → ad.length ≤ adCap.toNat ∧ adCap.toNat < 2 ^ 63)
    (hFit : FitsEnv M lim st (TryFromPostOutPreEnv (.ok msg)))
    (hbox : PostCtBoxesPost ctCap adCap msg.ciphertext msg.addresses evs_box) :
    FitsEnv M lim (M.stepEvents evs_box st) (TryCloneBytesEnv msg.serialized) := by
  rcases hbox with ⟨evs₀, evs₁, evs₂, rfl, hf₀, h1, h2⟩
  have hFit1 := hFit.seq_right hf₀
  have hFit2 := hFit1.seq_right ⟨ctCap, hct_le, hct_lt, h1⟩
  have hFit3 := hFit2.seq_right (intoBoxedOptBounded_of_cap had_bnd h2)
  simpa only [M.stepEvents_append] using hFit3

private theorem tryFromPostOutEnv_of_boxes_clone {msg : SignalMessage}
    {ctCap adCap : BitVec 64} {evs_box evs_cp : List AllocEvent}
    (hct_le : msg.ciphertext.length ≤ ctCap.toNat) (hct_lt : ctCap.toNat < 2 ^ 63)
    (had_bnd : ∀ ad, msg.addresses = some ad → ad.length ≤ adCap.toNat ∧ adCap.toNat < 2 ^ 63)
    (hbox : PostCtBoxesPost ctCap adCap msg.ciphertext msg.addresses evs_box)
    (hcp : PostClonePackEnv msg.serialized evs_cp) :
    TryFromPostOutEnv (.ok msg) (evs_box ++ evs_cp) := by
  rcases hbox with ⟨evs₀, evs₁, evs₂, rfl, hf₀, h1, h2⟩
  have h1' : IntoBoxedBoundedEnv msg.ciphertext evs₁ := ⟨ctCap, hct_le, hct_lt, h1⟩
  have h2' : IntoBoxedOptBoundedEnv msg.addresses evs₂ := intoBoxedOptBounded_of_cap had_bnd h2
  rcases hcp with hclone | ⟨ec, ef, rfl, hclone, hff⟩
  · refine Or.inl ?_
    have heq : evs₀ ++ evs₁ ++ evs₂ ++ evs_cp = evs₀ ++ (evs₁ ++ (evs₂ ++ evs_cp)) := by
      simp [List.append_assoc]
    rw [heq]
    exact SeqEnv.append hf₀ (SeqEnv.append h1' (SeqEnv.append h2' hclone))
  · have heq : evs₀ ++ evs₁ ++ evs₂ ++ (ec ++ ef) = (evs₀ ++ (evs₁ ++ (evs₂ ++ ec))) ++ ef := by
      simp [List.append_assoc]
    rw [heq]
    exact SeqEnv.append (SeqEnv.append hf₀ (SeqEnv.append h1' (SeqEnv.append h2' hclone))) hff

/-! ## Local separation-logic entailment helpers -/

private theorem entails_of_perm {P Q : SepProp}
    (hent : P ⊢ Q := by first | sep_accu | sep_interval | bi_entail) : P ⊢ Q :=
  hent

private theorem wpp_replace_sub {prog : Program} {ret : BitVec 64} {s : State}
    {P Old New F : SepProp} {Q : State → SepProp → Prop} {qp : State → SepProp → Prop}
    (himp : Old ⊢ New)
    (hk : WSepWPp prog ret s (New ∗ F) Q qp)
    (hent : P ⊢ Old ∗ F := by first | sep_accu | bi_frame) :
    WSepWPp prog ret s P Q qp :=
  WSepWPp.mono_pre (Entails.trans hent (sepConj_mono_left himp)) hk

private theorem wpp_replace_sub_exists {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P Old F : SepProp} {New : α → SepProp} {Q : State → SepProp → Prop} {qp : State → SepProp → Prop}
    (himp : Old ⊢ ∃∗ x, New x)
    (hk : ∀ x, WSepWPp prog ret s (New x ∗ F) Q qp)
    (hent : P ⊢ Old ∗ F := by first | sep_accu | bi_frame) :
    WSepWPp prog ret s P Q qp := by
  refine wpp_replace_sub himp ?_ hent
  rw [sepExists_sepConj_left]
  exact WSepWPp.exists_pre hk

private theorem wpp_pure_anywhere (φ : Prop) {prog : Program} {ret : BitVec 64} {s : State}
    {P F : SepProp} {Q : State → SepProp → Prop} {qp : State → SepProp → Prop}
    (hk : φ → WSepWPp prog ret s F Q qp)
    (hent : P ⊢ ⌜φ⌝ ∗ F := by first | sep_accu | bi_frame) :
    WSepWPp prog ret s P Q qp :=
  WSepWPp.mono_pre hent (WSepWPp.pure_pre hk)

private theorem wpp_bind_frame_gen {prog : Program} {mid ret : BitVec 64}
    {s0 s : State} {P F : SepProp} {Q1 Q : State → SepProp → Prop}
    (h1 : WSepWPp prog mid s P Q1 (postNoPanicQp s0))
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Q1 sm Pm →
      WSepWPp prog ret sm (Pm ∗ F) Q (postNoPanicQp s0)) :
    WSepWPp prog ret s (P ∗ F) Q (postNoPanicQp s0) := by
  refine WSepWPp.bind
    (wpp_frame_noPanic (Q := fun sm PmF => ∃ Pm, Q1 sm Pm ∧ PmF = Pm ∗ F) h1
      fun sm Pm hq => ⟨Pm, hq, rfl⟩) ?_
  intro sm PmF hpcm hrunm ⟨Pm, hq, hEq⟩
  rw [hEq]
  exact h2 sm Pm hpcm hrunm hq

private theorem wpp_frame_call {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P P1 F : SepProp} {Q1 Q : State → SepProp → Prop}
    (h1 : WSepWPp prog ret s P1 Q1 (postNoPanicQp s0))
    (hpost : ∀ sf Pf, Q1 sf Pf → Q sf (Pf ∗ F))
    (hent : P ⊢ P1 ∗ F := by first | sep_accu | bi_frame) :
    WSepWPp prog ret s P Q (postNoPanicQp s0) :=
  WSepWPp.mono_pre hent (wpp_frame_noPanic h1 hpost)

private theorem wpp_bind_frame_call {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P1 F : SepProp} {Q1 Q : State → SepProp → Prop}
    (h1 : WSepWPp prog mid s P1 Q1 (postNoPanicQp s0))
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Q1 sm Pm →
      WSepWPp prog ret sm (Pm ∗ F) Q (postNoPanicQp s0))
    (hent : P ⊢ P1 ∗ F := by first | sep_accu | bi_frame) :
    WSepWPp prog ret s P Q (postNoPanicQp s0) :=
  WSepWPp.mono_pre hent (wpp_bind_frame_gen h1 h2)

private theorem memRegion120_split24 (x19 : BitVec 64) :
    memRegion x19 120 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ ((x19 + 16#64) ↦₆₄ w2) ∗
        memRegion (x19 + 24#64) 96 := by
  sep_interval

private theorem vecU8Buf_cap_bounds (A : RustAlloc) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63⌝ ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8Buf
  refine Entails.pure_left fun h => ?_
  rw [pure_true_emp ⟨h.1, h.2.1⟩, emp_sepConj, pure_true_emp h, emp_sepConj]
  exact Entails.refl _

private theorem optVecU8Buf_cap_bounds (A : RustAlloc) (cap ptr len : BitVec 64)
    (opt : Option (List (BitVec 8))) :
    optVecU8Buf A cap ptr len opt ⊢
      ⌜∀ bs, opt = some bs → bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63⌝ ∗
        optVecU8Buf A cap ptr len opt := by
  cases opt with
  | none =>
    rw [pure_true_emp (fun _ h => nomatch h), emp_sepConj]
    exact Entails.refl _
  | some bs =>
    dsimp only [optVecU8Buf, vecU8Buf]
    refine Entails.pure_left fun hlen => Entails.pure_left fun hb => ?_
    have hall : ∀ bs', (some bs : Option (List (BitVec 8))) = some bs' →
        bs'.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 := by
      intro bs' heq; cases heq; exact ⟨hb.1, hb.2.1⟩
    rw [pure_true_emp hall, emp_sepConj, pure_true_emp hlen, emp_sepConj,
      pure_true_emp hb, emp_sepConj]
    exact Entails.refl _

/-! ## Relocatable `[LibsignalPlacement]` post-loop composition theorems (Block `85`) -/

theorem post_after_578_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hDropSpe : DropSpeOkWPlaced A lim H)
    (hIntoBox : IntoBoxedSliceOkPlaced A lim H)
    (hTryClone : TryCloneFromRefOkPlaced A lim H)
    (st : M.σ) {s0 s : State}
    {sp' x19 x21 rkCap rkPtr ctCap ctPtr ctLen pqCap pqPtr pqLen adCap adPtr adLen : BitVec 64}
    {w136 w144 w152 w15 w23 : BitVec 64}
    {counter w52 pcTag pcVal w9 : BitVec 32} {w13 : BitVec 16}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8}
    (bs rk : List (BitVec 8)) (m' : ProtoSignalMessage) (pk : PublicKey)
    {out : Except SignalProtocolError SignalMessage}
    (hgt9 : 9 < bs.length) (hlt : bs.length < 2 ^ 32)
    (hdec : decode ((bs.take (bs.length - 8)).drop 1) = some m')
    (hpk : pk.bytes.toList = pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31)
    (hout : out =
      match m'.ciphertext with
      | none => .error .invalidProtobufEncoding
      | some ciphertext =>
        .ok { messageVersion := (bs.headD 0#8) >>> 4, senderRatchetKey := pk, counter,
              previousCounter := m'.previousCounter.getD 0#32, ciphertext,
              pqRatchet := m'.pqRatchet.getD [], addresses := m'.addresses,
              serialized := bs })
    (hFit : FitsEnv M lim st (TryFromPostOutPreEnv out))
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 1400#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = addsPState64 ctCap 1#64)
    (hx8 : s.readReg64 .x8 = (m'.previousCounter.getD 0#32).zeroExtend 64)
    (hx19 : s.readReg64 .x19 = x19)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 bs.length)
    (hx21 : s.readReg64 .x21 = x21)
    (hx22 : s.readReg64 .x22 = adCap)
    (hx23 : s.readReg64 .x23 = (bs.headD 0#8).zeroExtend 64)
    (hx24 : s.readReg64 .x24 = b7.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = pqCap)
    (hx26 : s.readReg64 .x26 = speWord 2)
    (hx27 : s.readReg64 .x27 = ctCap)
    (hx28 : s.readReg64 .x28 = ctPtr) :
    WSepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 1088#64) s
      (spUnused0 sp' ∗
        ((sp' + 12#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 16#64) ↦₆₄ adLen) ∗
        ((sp' + 28#64) ↦₃₂ counter) ∗ ((sp' + 32#64) ↦₆₄ ctLen) ∗
        ((sp' + 40#64) ↦₆₄ pqLen) ∗ ((sp' + 48#64) ↦₃₂ pcTag) ∗
        ((sp' + 52#64) ↦₃₂ w52) ∗ ((sp' + 60#64) ↦₃₂ pcVal) ∗
        ((sp' + 64#64) ↦₆₄ w15) ∗
        ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
        ((sp' + 88#64) ↦₆₄ adPtr) ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        spUnused104 sp' ∗
        ((sp' + 104#64) ↦₆₄ w23) ∗ ((sp' + 112#64) ↦₈ b31) ∗
        ((sp' + 120#64) ↦₃₂ w9) ∗ ((sp' + 124#64) ↦₁₆ w13) ∗
        sevenBytesHeadAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6 ∗
        vecHeader (sp' + 136#64) w136 w144 w152 ∗
        ((sp' + 176#64) ↦₆₄ speWord 2) ∗ memRegion (sp' + 184#64) 40 ∗
        memRegion (sp' + 224#64) 64 ∗
        vecU8Buf A.repAlloc rkCap rkPtr rk ∗
        optVecU8Buf A.repAlloc ctCap ctPtr ctLen m'.ciphertext ∗
        optVecU8Buf A.repAlloc pqCap pqPtr pqLen m'.pqRatchet ∗
        optVecU8Buf A.repAlloc adCap adPtr adLen m'.addresses ∗
        memRegion x19 120 ∗
        (x21 ↦ₛ bs) ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        ∃ evs : List AllocEvent, TryFromPostOutEnv out evs ∧
          (Pf ⊢ memRegion sp' 104 ∗ memRegion (sp' + 104#64) 72 ∗
            memRegion (sp' + 176#64) 112 ∗
            signalMessageResultAt A.repAlloc [] x19 out ∗
            (x21 ↦ₛ bs) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100)))
      (postNoPanicQp s0) := by
  have h48_pair := pointsTo32_pair_eq_pointsTo64 (sp' + 48#64) pcTag w52
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h48_pair
  refine wpp_replace_sub (entails_of_eq h48_pair) ?_
  cases hct : m'.ciphertext with
  | none =>
    simp only [hct] at hout
    have hct_eq : optVecU8Buf A.repAlloc ctCap ctPtr ctLen none = ⌜ctCap = noneCap⌝ := rfl
    rw [hct_eq]
    refine wpp_pure_anywhere (ctCap = noneCap) fun hct_cap => ?_
    subst hct_cap
    refine wpp_replace_sub_exists (optVecU8Buf_entails_deallocSlot A.repAlloc pqCap pqPtr pqLen m'.pqRatchet) fun pqAct => ?_
    refine wpp_replace_sub_exists (optVecU8Buf_entails_deallocSlot A.repAlloc adCap adPtr adLen m'.addresses) fun adAct => ?_
    refine wpp_replace_sub (memRegion120_split16 x19) ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine WSepWPp.exists_pre fun w1 => WSepWPp.exists_pre fun w0 => ?_
    refine wpp_frame_call
      (post_ct_none_wp_placed
        (w0 := w0) (w1 := w1) (rkCap := rkCap) (rkPtr := rkPtr)
        (pqPtr := pqPtr) (adPtr := adPtr)
        hS st rk pqAct adAct hout hst hpc hrun hpstate hx19 hx26 hx25 hx22)
      fun sf Pf ⟨hstf, evs, hfree, hent⟩ =>
        ⟨hstf, evs, tryFromPostOutEnv_of_eq_error hout hfree, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    generalize skipFieldStackX 100 = nStk,
      signalMessageResultAt A.repAlloc [] x19 out = resOut,
      A.pool lim (M.stepEvents evs st) sf = poolOut
    unfold spUnused0 spUnused104 sevenBytesHeadAt vecHeader
    sep_interval
  | some ct =>
    simp only [hct] at hout
    have hbnd := msg_bounds_of_decode hgt9 hlt hdec hct
    have hct_eq : optVecU8Buf A.repAlloc ctCap ctPtr ctLen (some ct) =
        ⌜ctLen = BitVec.ofNat 64 ct.length⌝ ∗ vecU8Buf A.repAlloc ctCap ctPtr ct := rfl
    rw [hct_eq]
    refine wpp_pure_anywhere (ctLen = BitVec.ofNat 64 ct.length) fun hct_len => ?_
    subst hct_len
    refine wpp_replace_sub (vecU8Buf_cap_bounds A.repAlloc ctCap ctPtr ct) ?_
    refine wpp_pure_anywhere (ct.length ≤ ctCap.toNat ∧ ctCap.toNat < 2 ^ 63)
      fun ⟨hct_le, hct_lt⟩ => ?_
    refine wpp_replace_sub (optVecU8Buf_cap_bounds A.repAlloc adCap adPtr adLen m'.addresses) ?_
    refine wpp_pure_anywhere (∀ ad, m'.addresses = some ad → ad.length ≤ adCap.toNat ∧ adCap.toNat < 2 ^ 63)
      fun had_bnd => ?_
    set msg : SignalMessage :=
      { messageVersion := (bs.headD 0#8) >>> 4, senderRatchetKey := pk, counter,
        previousCounter := m'.previousCounter.getD 0#32, ciphertext := ct,
        pqRatchet := m'.pqRatchet.getD [], addresses := m'.addresses,
        serialized := bs }
    have hFit_ok : FitsEnv M lim st (TryFromPostOutPreEnv (.ok msg)) := hout ▸ hFit
    have hFit_boxes := fitsEnv_postCtBoxes_of_ok (msg := msg) hct_le hct_lt had_bnd hFit_ok
    refine wpp_bind_frame_call
      (post_ct_some_boxes_wp_placed
        (pqPtr := pqPtr) (pqLen := pqLen) (adPtr := adPtr) (adLen := adLen)
        (w48 := w52 ++ pcTag) (w136 := w136) (w144 := w144) (w152 := w152) (w60 := pcVal)
        hDropSpe hIntoBox st ct m'.pqRatchet m'.addresses
        hct_lt hFit_boxes hst hpc hrun hpstate hx8 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx27 hx28) ?_
    intro s2 P2 hpc2 hrun2 ⟨pqCap', pqPtr', ctBoxPtr, adBoxPtr, w96', evs_box, hbox_post,
      hst2, _, _, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hent2⟩
    have hFit_clone := fitsEnv_tryClone_of_postCtBoxes (msg := msg) hct_le hct_lt had_bnd hFit_ok hbox_post
    refine WSepWPp.mono_pre (sepConj_mono_left hent2) ?_
    refine wpp_replace_sub (memRegion120_split16 x19) ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine WSepWPp.exists_pre fun w1 => WSepWPp.exists_pre fun w0 => ?_
    refine wpp_frame_call
      (post_clone_and_pack_wp_placed
        (pqCap' := pqCap') (pqPtr' := pqPtr') (ctBoxPtr := ctBoxPtr)
        (adBoxPtr := adBoxPtr) (w96 := w96') (rkCap := rkCap) (rkPtr := rkPtr)
        (w0 := w0) (w1 := w1) (b_ver := bs.headD 0#8)
        hS hTryClone (M.stepEvents evs_box st) rk msg hout hbnd hpk rfl
        hFit_clone hst2 hpc2 hrun2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2)
      (fun sf Pf ⟨hstf, evs_cp, hcp_env, hent⟩ =>
        ⟨hstf, evs_box ++ evs_cp,
          hout ▸ tryFromPostOutEnv_of_boxes_clone (msg := msg) hct_le hct_lt had_bnd hbox_post hcp_env,
          ?_⟩)
      (by dsimp only [msg]; sep_accu)
    rw [M.stepEvents_append]
    refine Entails.trans (sepConj_mono_left hent) ?_
    dsimp only [msg]
    generalize skipFieldStackX 100 = nStk,
      signalMessageResultAt A.repAlloc [] x19 out = resOut,
      A.pool lim (M.stepEvents evs_cp (M.stepEvents evs_box st)) sf = poolOut
    unfold spUnused0 spUnused104 sevenBytesHeadAt vecHeader
    sep_interval

theorem post_after_54c_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hDropSpe : DropSpeOkWPlaced A lim H)
    (hIntoBox : IntoBoxedSliceOkPlaced A lim H)
    (hTryClone : TryCloneFromRefOkPlaced A lim H)
    (st : M.σ) {s0 s : State}
    {sp' x19 x21 rkCap rkPtr ctCap ctPtr ctLen pqCap pqPtr pqLen adCap adPtr adLen : BitVec 64}
    {w136 w144 w152 w15 w23 : BitVec 64}
    {w12 w52 cTag cVal pcTag pcVal w68 w9 : BitVec 32} {w13 : BitVec 16}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8}
    (bs rk : List (BitVec 8)) (m' : ProtoSignalMessage) (pk : PublicKey)
    {out : Except SignalProtocolError SignalMessage}
    (hgt9 : 9 < bs.length) (hlt : bs.length < 2 ^ 32)
    (hdec : decode ((bs.take (bs.length - 8)).drop 1) = some m')
    (hpk : pk.bytes.toList = pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31)
    (hc : optU32TagVal cTag cVal m'.counter)
    (hpc_tag : optU32TagVal pcTag pcVal m'.previousCounter)
    (hout : out =
      match m'.counter with
      | none => .error .invalidProtobufEncoding
      | some counter =>
        match m'.ciphertext with
        | none => .error .invalidProtobufEncoding
        | some ciphertext =>
          .ok { messageVersion := (bs.headD 0#8) >>> 4, senderRatchetKey := pk, counter,
                previousCounter := m'.previousCounter.getD 0#32, ciphertext,
                pqRatchet := m'.pqRatchet.getD [], addresses := m'.addresses,
                serialized := bs })
    (hFit : FitsEnv M lim st (TryFromPostOutPreEnv out))
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 1356#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = subsPState32 cTag 1#32)
    (hx8 : s.readReg64 .x8 = w15)
    (hx9 : s.readReg64 .x9 = (b8.zeroExtend 32).zeroExtend 64)
    (hx19 : s.readReg64 .x19 = x19)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 bs.length)
    (hx21 : s.readReg64 .x21 = x21)
    (hx22 : s.readReg64 .x22 = adCap)
    (hx23 : s.readReg64 .x23 = (bs.headD 0#8).zeroExtend 64)
    (hx24 : s.readReg64 .x24 = (b7.zeroExtend 32).zeroExtend 64)
    (hx25 : s.readReg64 .x25 = pqCap)
    (hx26 : s.readReg64 .x26 = speWord 2)
    (hx27 : s.readReg64 .x27 = ctCap)
    (hx28 : s.readReg64 .x28 = ctPtr) :
    WSepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 1088#64) s
      (spUnused0 sp' ∗
        ((sp' + 12#64) ↦₃₂ w12) ∗ ((sp' + 16#64) ↦₆₄ adLen) ∗
        ((sp' + 28#64) ↦₃₂ cVal) ∗ ((sp' + 32#64) ↦₆₄ ctLen) ∗
        ((sp' + 40#64) ↦₆₄ pqLen) ∗ ((sp' + 48#64) ↦₃₂ pcTag) ∗
        ((sp' + 52#64) ↦₃₂ w52) ∗ ((sp' + 60#64) ↦₃₂ pcVal) ∗
        ((sp' + 64#64) ↦₆₄ (w68 ++ cTag)) ∗
        ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
        ((sp' + 88#64) ↦₆₄ adPtr) ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        spUnused104 sp' ∗
        ((sp' + 104#64) ↦₆₄ w23) ∗ ((sp' + 112#64) ↦₈ b31) ∗
        ((sp' + 120#64) ↦₃₂ w9) ∗ ((sp' + 124#64) ↦₁₆ w13) ∗
        sevenBytesHeadAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6 ∗
        vecHeader (sp' + 136#64) w136 w144 w152 ∗
        ((sp' + 176#64) ↦₆₄ speWord 2) ∗ memRegion (sp' + 184#64) 40 ∗
        memRegion (sp' + 224#64) 64 ∗
        vecU8Buf A.repAlloc rkCap rkPtr rk ∗
        optVecU8Buf A.repAlloc ctCap ctPtr ctLen m'.ciphertext ∗
        optVecU8Buf A.repAlloc pqCap pqPtr pqLen m'.pqRatchet ∗
        optVecU8Buf A.repAlloc adCap adPtr adLen m'.addresses ∗
        memRegion x19 120 ∗
        (x21 ↦ₛ bs) ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        ∃ evs : List AllocEvent, TryFromPostOutEnv out evs ∧
          (Pf ⊢ memRegion sp' 104 ∗ memRegion (sp' + 104#64) 72 ∗
            memRegion (sp' + 176#64) 112 ∗
            signalMessageResultAt A.repAlloc [] x19 out ∗
            (x21 ↦ₛ bs) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100)))
      (postNoPanicQp s0) := by
  cases hcnt : m'.counter with
  | none =>
    simp only [hcnt] at hout
    rw [hcnt] at hc
    dsimp only [optU32TagVal] at hc
    subst hc
    have h48_pair := pointsTo32_pair_eq_pointsTo64 (sp' + 48#64) pcTag w52
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h48_pair
    refine wpp_replace_sub (entails_of_eq h48_pair) ?_
    refine wpp_replace_sub_exists (optVecU8Buf_entails_deallocSlot A.repAlloc ctCap ctPtr ctLen m'.ciphertext) fun ctAct => ?_
    refine wpp_replace_sub_exists (optVecU8Buf_entails_deallocSlot A.repAlloc pqCap pqPtr pqLen m'.pqRatchet) fun pqAct => ?_
    refine wpp_replace_sub_exists (optVecU8Buf_entails_deallocSlot A.repAlloc adCap adPtr adLen m'.addresses) fun adAct => ?_
    refine wpp_replace_sub (memRegion120_split16 x19) ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine WSepWPp.exists_pre fun w1 => WSepWPp.exists_pre fun w0 => ?_
    refine wpp_frame_call
      (post_counter_none_wp_placed
        (w0 := w0) (w1 := w1) (rkCap := rkCap) (rkPtr := rkPtr)
        (pqPtr := pqPtr) (adPtr := adPtr)
        hS st rk ctAct pqAct adAct hout
        hst hpc hrun hpstate hx19 hx26 hx27 hx28 hx25 hx22)
      fun sf Pf ⟨hstf, evs, hfree, hent⟩ =>
        ⟨hstf, evs, tryFromPostOutEnv_of_eq_error hout hfree, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    generalize skipFieldStackX 100 = nStk,
      signalMessageResultAt A.repAlloc [] x19 out = resOut,
      A.pool lim (M.stepEvents evs st) sf = poolOut
    unfold spUnused0 spUnused104 sevenBytesHeadAt vecHeader
    sep_interval
  | some counter =>
    simp only [hcnt] at hout
    rw [hcnt] at hc
    rcases hc with ⟨rfl, hcVal⟩
    subst cVal
    refine wpp_bind_frame_call
      (post_counter_some_head_wp_placed
        (w64 := w68 ++ 1#32) (w12 := w12) (pcTag := pcTag) (pcVal := pcVal)
        hDropSpe st hst hpc hrun hpstate hx8 hx9 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28) ?_
    intro s1 P1 hpc1 hrun1 ⟨hst1, _, _, hpstate1, hx8_1, hx19_1, hx20_1, hx21_1, hx22_1,
      hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, evs₀, hfree₀, hent1⟩
    rw [pcVal_if_eq_getD hpc_tag] at hx8_1
    rw [zext32_zext64_8 b7] at hx24_1
    have hFit1 := fitsEnv_tryFromPostOutPre_step_freeOnly hfree₀ hFit
    refine WSepWPp.mono_pre (sepConj_mono_left hent1) ?_
    have hcall := post_after_578_wp_placed
      (rkCap := rkCap) (rkPtr := rkPtr) (ctLen := ctLen)
      (pqPtr := pqPtr) (pqLen := pqLen) (adPtr := adPtr) (adLen := adLen)
      (w136 := w136) (w144 := w144) (w152 := w152)
      (w52 := w52) (pcTag := pcTag) (pcVal := pcVal)
      hS hDropSpe hIntoBox hTryClone (M.stepEvents evs₀ st)
      bs rk m' pk hgt9 hlt hdec hpk hout hFit1
      hst1 hpc1 hrun1 hpstate1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
      hx25_1 hx26_1 hx27_1 hx28_1
    refine WSepWPp.mono_pre ?_ (wpp_mono_post_noPanic ?_ hcall)
    · exact entails_of_perm
    · intro sf Pf ⟨hstf, evs₁, henv₁, hentf⟩
      refine ⟨hstf, evs₀ ++ evs₁, tryFromPostOutEnv_prepend_freeOnly hfree₀ henv₁, ?_⟩
      rw [M.stepEvents_append]
      exact hentf

theorem post_after_deser_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hDropSpe : DropSpeOkWPlaced A lim H)
    (hIntoBox : IntoBoxedSliceOkPlaced A lim H)
    (hTryClone : TryCloneFromRefOkPlaced A lim H)
    (st : M.σ) {s0 s : State}
    {sp' x19 x21 rkCap rkPtr ctCap ctPtr ctLen pqCap pqPtr pqLen adCap adPtr adLen : BitVec 64}
    {w12 w52 cTag cVal pcTag pcVal w68 : BitVec 32}
    (bs rk : List (BitVec 8)) (m' : ProtoSignalMessage)
    {out : Except SignalProtocolError SignalMessage}
    (hgt9 : 9 < bs.length) (hlt : bs.length < 2 ^ 32)
    (hdec : decode ((bs.take (bs.length - 8)).drop 1) = some m')
    (hc : optU32TagVal cTag cVal m'.counter)
    (hpc_tag : optU32TagVal pcTag pcVal m'.previousCounter)
    (hout : out =
      match PublicKey.deserialize rk with
      | .error e => .error e
      | .ok senderRatchetKey =>
        match m'.counter with
        | none => .error .invalidProtobufEncoding
        | some counter =>
          match m'.ciphertext with
          | none => .error .invalidProtobufEncoding
          | some ciphertext =>
            .ok { messageVersion := (bs.headD 0#8) >>> 4, senderRatchetKey, counter,
                  previousCounter := m'.previousCounter.getD 0#32, ciphertext,
                  pqRatchet := m'.pqRatchet.getD [], addresses := m'.addresses,
                  serialized := bs })
    (hFit : FitsEnv M lim st (TryFromPostOutPreEnv out))
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 1220#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x19)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 bs.length)
    (hx21 : s.readReg64 .x21 = x21)
    (hx22 : s.readReg64 .x22 = adCap)
    (hx23 : s.readReg64 .x23 = (bs.headD 0#8).zeroExtend 64)
    (hx25 : s.readReg64 .x25 = pqCap)
    (hx27 : s.readReg64 .x27 = ctCap)
    (hx28 : s.readReg64 .x28 = ctPtr) :
    WSepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 1088#64) s
      (spUnused0 sp' ∗
        ((sp' + 12#64) ↦₃₂ w12) ∗ ((sp' + 16#64) ↦₆₄ adLen) ∗
        ((sp' + 28#64) ↦₃₂ cVal) ∗ ((sp' + 32#64) ↦₆₄ ctLen) ∗
        ((sp' + 40#64) ↦₆₄ pqLen) ∗ ((sp' + 48#64) ↦₃₂ pcTag) ∗
        ((sp' + 52#64) ↦₃₂ w52) ∗ ((sp' + 60#64) ↦₃₂ pcVal) ∗
        ((sp' + 64#64) ↦₃₂ cTag) ∗ ((sp' + 68#64) ↦₃₂ w68) ∗
        ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
        ((sp' + 88#64) ↦₆₄ adPtr) ∗ ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        memRegion (sp' + 104#64) 72 ∗
        deserializeResult33At (sp' + 176#64) (PublicKey.deserialize rk) ∗
        memRegion (sp' + 209#64) 15 ∗
        memRegion (sp' + 224#64) 64 ∗
        vecU8Buf A.repAlloc rkCap rkPtr rk ∗
        optVecU8Buf A.repAlloc ctCap ctPtr ctLen m'.ciphertext ∗
        optVecU8Buf A.repAlloc pqCap pqPtr pqLen m'.pqRatchet ∗
        optVecU8Buf A.repAlloc adCap adPtr adLen m'.addresses ∗
        memRegion x19 120 ∗
        (x21 ↦ₛ bs) ∗
        A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        ∃ evs : List AllocEvent, TryFromPostOutEnv out evs ∧
          (Pf ⊢ memRegion sp' 104 ∗ memRegion (sp' + 104#64) 72 ∗
            memRegion (sp' + 176#64) 112 ∗
            signalMessageResultAt A.repAlloc [] x19 out ∗
            (x21 ↦ₛ bs) ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' (skipFieldStackX 100)))
      (postNoPanicQp s0) := by
  cases hdeser : PublicKey.deserialize rk with
  | error e =>
    simp only [hdeser] at hout
    refine wpp_replace_sub_exists (optVecU8Buf_entails_deallocSlot A.repAlloc ctCap ctPtr ctLen m'.ciphertext) fun ctAct => ?_
    refine wpp_replace_sub_exists (optVecU8Buf_entails_deallocSlot A.repAlloc pqCap pqPtr pqLen m'.pqRatchet) fun pqAct => ?_
    refine wpp_replace_sub_exists (optVecU8Buf_entails_deallocSlot A.repAlloc adCap adPtr adLen m'.addresses) fun adAct => ?_
    refine wpp_replace_sub (memRegion120_split24 x19) ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine WSepWPp.exists_pre fun w0 => WSepWPp.exists_pre fun w1 =>
      WSepWPp.exists_pre fun w2 => ?_
    refine wpp_frame_call
      (post_deser_err_wp_placed
        (w0 := w0) (w1 := w1) (w2 := w2) (rkCap := rkCap) (rkPtr := rkPtr)
        (pqPtr := pqPtr) (adPtr := adPtr)
        hS st rk ctAct pqAct adAct e hdeser hout
        hst hpc hrun hx19 hx27 hx28 hx25 hx22)
      fun sf Pf ⟨hstf, evs, hfree, hent⟩ =>
        ⟨hstf, evs, tryFromPostOutEnv_of_eq_error hout hfree, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    generalize skipFieldStackX 100 = nStk,
      signalMessageResultAt A.repAlloc [] x19 out = resOut,
      A.pool lim (M.stepEvents evs st) sf = poolOut
    unfold spUnused0
    sep_interval
  | ok pk =>
    simp only [hdeser] at hout
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, w9, w13, w15, w23, b31, hpk⟩ :=
      exists_pkBytesOf pk.bytes.toList pk.bytes.2
    have hdeser_eq : deserializeResult33At (sp' + 176#64) (.ok pk) =
        ((sp' + 176#64) ↦₈ 0#8) ∗
        pkLayoutAt (sp' + 177#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 := by
      dsimp only [deserializeResult33At]
      rw [hpk, ← pkLayoutAt_eq_pointsToBytes]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [hdeser_eq]
    refine wpp_replace_sub (memRegion72_104_unpack sp') ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine WSepWPp.exists_pre fun w104 => WSepWPp.exists_pre fun b112 =>
      WSepWPp.exists_pre fun w120 => WSepWPp.exists_pre fun w124 =>
      WSepWPp.exists_pre fun c0 => WSepWPp.exists_pre fun c1 =>
      WSepWPp.exists_pre fun c2 => WSepWPp.exists_pre fun c3 =>
      WSepWPp.exists_pre fun c4 => WSepWPp.exists_pre fun c5 =>
      WSepWPp.exists_pre fun c6 => WSepWPp.exists_pre fun w136 =>
      WSepWPp.exists_pre fun w144 => WSepWPp.exists_pre fun w152 => ?_
    refine wpp_bind_frame_call
      (post_deser_ok_head_wp_placed
        (w104 := w104) (w15 := w15) (w23 := w23)
        (cTag := cTag) (w68 := w68) (w9 := w9) (w120 := w120)
        (w13 := w13) (w124 := w124)
        (b0 := b0) (b1 := b1) (b2 := b2) (b3 := b3) (b4 := b4)
        (b5 := b5) (b6 := b6) (b7 := b7) (b8 := b8) (b31 := b31) (b112 := b112)
        (c0 := c0) (c1 := c1) (c2 := c2) (c3 := c3) (c4 := c4) (c5 := c5) (c6 := c6)
        st hst hpc hrun) ?_
    intro s1 P1 hpc1 hrun1 ⟨hst1, _, _, hpstate1, hx8_1, hx9_1, hx24_1, hx26_1, hother1, hent1⟩
    have hx19_1 : s1.readReg64 .x19 = x19 := by
      rw [hother1 .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx19]
    have hx20_1 : s1.readReg64 .x20 = BitVec.ofNat 64 bs.length := by
      rw [hother1 .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx20]
    have hx21_1 : s1.readReg64 .x21 = x21 := by
      rw [hother1 .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx21]
    have hx22_1 : s1.readReg64 .x22 = adCap := by
      rw [hother1 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx22]
    have hx23_1 : s1.readReg64 .x23 = (bs.headD 0#8).zeroExtend 64 := by
      rw [hother1 .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx23]
    have hx25_1 : s1.readReg64 .x25 = pqCap := by
      rw [hother1 .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx25]
    have hx27_1 : s1.readReg64 .x27 = ctCap := by
      rw [hother1 .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx27]
    have hx28_1 : s1.readReg64 .x28 = ctPtr := by
      rw [hother1 .x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx28]
    refine WSepWPp.mono_pre (sepConj_mono_left hent1) ?_
    have hcall := post_after_54c_wp_placed
      (rkCap := rkCap) (rkPtr := rkPtr) (ctLen := ctLen)
      (pqPtr := pqPtr) (pqLen := pqLen) (adPtr := adPtr) (adLen := adLen)
      (w136 := w136) (w144 := w144) (w152 := w152)
      (w12 := w12) (w52 := w52) (w68 := w68)
      hS hDropSpe hIntoBox hTryClone st
      bs rk m' pk hgt9 hlt hdec hpk hc hpc_tag hout hFit
      hst1 hpc1 hrun1 hpstate1 hx8_1 hx9_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
      hx25_1 hx26_1 hx27_1 hx28_1
    exact WSepWPp.mono_pre entails_of_perm hcall

theorem tryFrom_post_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hDropErr : DropDecodeErrorOkWPlaced A lim H)
    (hDropSpe : DropSpeOkWPlaced A lim H)
    (hIntoBox : IntoBoxedSliceOkPlaced A lim H)
    (hTryClone : TryCloneFromRefOkPlaced A lim H)
    (st : M.σ) {x : TryFromGhost} {s0 s : State}
    (hgt9 : 9 < x.bytes.length)
    (hlt : x.bytes.length < 2 ^ 32)
    (hge3 : ¬ ((x.bytes.headD 0#8) >>> 4) < 3#8)
    (hle4 : ¬ 4#8 < ((x.bytes.headD 0#8) >>> 4))
    (hFit : FitsEnv M lim st (TryFromPostPreEnv x.bytes))
    (hpc : s.pc = (blkPl_85).base + 944#64)
    (hrun : s.status = .Running)
    (hst : LoopExitStatePlaced s0 (s0.sp - 448#64) x.ret
      (BitVec.ofNat 64 x.bytes.length) x.bytesA ((x.bytes.headD 0#8).zeroExtend 64) s) :
    WSepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 1088#64) s
      (memRegion (s0.sp - 448#64) 176 ∗
        memRegion (s0.sp - 448#64 + 288#64) 64 ∗
        (x.bytesA ↦ₛ x.bytes) ∗
        A.pool lim st s ∗ stackAt (s0.sp - 448#64) (skipFieldStackX 100) ∗
        (match decode ((x.bytes.take (x.bytes.length - 8)).drop 1) with
         | some m' =>
           ⌜s.readReg64 .x24 = 0#64⌝ ∗ wireSignalMessageOf A.repAlloc (s0.sp - 448#64 + 176#64) m'
         | none =>
           ⌜s.readReg64 .x24 ≠ 0#64⌝ ∗ decodeErrorAt A.repAlloc (s.readReg64 .x24) ∗
             (∃∗ mErr, wireSignalMessageOf A.repAlloc (s0.sp - 448#64 + 176#64) mErr)) ∗
        memRegion x.ret 120 ∗ logOff tryFromPlacedImg)
      (fun sf Pf =>
        PostEpilogueStatePlaced s0 (s0.sp - 448#64) sf ∧
        ∃ evs : List AllocEvent, TryFromPostEnv x.bytes evs ∧
          (Pf ⊢ memRegion (s0.sp - 448#64) 352 ∗
            signalMessageResultAt A.repAlloc [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
            (x.bytesA ↦ₛ x.bytes) ∗ logOff tryFromPlacedImg ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt (s0.sp - 448#64) (skipFieldStackX 100)))
      (postNoPanicQp s0) := by
  set sp' := s0.sp - 448#64
  set out := SignalMessage.tryFrom protoSignalCodec x.bytes
  have hFit_out : FitsEnv M lim st (TryFromPostOutPreEnv out) := hFit
  have hout := tryFrom_eq_of_gt9 hgt9 hge3 hle4
  cases hdec : decode ((x.bytes.take (x.bytes.length - 8)).drop 1) with
  | none =>
    have hdec' : CryptoVerification.LibsignalProtoCodec.decode
        ((x.bytes.take (x.bytes.length - 8)).drop 1) = none := hdec
    simp only [hdec'] at hout
    rw [memRegion176_split_88_16_72 sp']
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine WSepWPp.exists_pre fun mErr => ?_
    refine wpp_pure_anywhere (s.readReg64 .x24 ≠ 0#64) fun hx24_ne => ?_
    refine wpp_frame_call
      (post_none_wp_placed hS hDropErr st hout hst hpc hrun rfl hx24_ne mErr)
      fun sf Pf ⟨hstf, evs, hfree, hent⟩ =>
        ⟨hstf, evs, tryFromPostOutEnv_of_eq_error hout hfree, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    dsimp only [sp', out]
    generalize skipFieldStackX 100 = nStk,
      signalMessageResultAt A.repAlloc [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) = resOut,
      A.pool lim (M.stepEvents evs st) sf = poolOut
    sep_interval
  | some m' =>
    have hdec' : CryptoVerification.LibsignalProtoCodec.decode
        ((x.bytes.take (x.bytes.length - 8)).drop 1) = some m' := hdec
    simp only [hdec'] at hout
    cases hrk : m'.ratchetKey with
    | none =>
      simp only [hrk] at hout
      rw [memRegion176_split_88_16_72 sp']
      simp only [sepConj_assoc]
      refine wpp_pure_anywhere (s.readReg64 .x24 = 0#64) fun hx24 => ?_
      refine wpp_frame_call
        (post_rk_none_wp_placed hS st hrk hout hst hpc hrun hx24)
        fun sf Pf ⟨hstf, evs, hfree, hent⟩ =>
          ⟨hstf, evs, tryFromPostOutEnv_of_eq_error hout hfree, ?_⟩
      refine Entails.trans (sepConj_mono_left hent) ?_
      dsimp only [sp', out]
      generalize skipFieldStackX 100 = nStk,
        signalMessageResultAt A.repAlloc [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) = resOut,
        A.pool lim (M.stepEvents evs st) sf = poolOut
      sep_interval
    | some rk =>
      simp only [hrk] at hout
      rw [memRegion176_split_104_72 sp']
      simp only [sepConj_assoc]
      refine wpp_pure_anywhere (s.readReg64 .x24 = 0#64) fun hx24 => ?_
      refine wpp_replace_sub (memRegion104_0_unpack sp') ?_
      simp only [sepExists_sepConj_left, sepConj_assoc]
      refine WSepWPp.exists_pre fun w12 => WSepWPp.exists_pre fun w16 =>
        WSepWPp.exists_pre fun w28 => WSepWPp.exists_pre fun w32 =>
        WSepWPp.exists_pre fun w40 => WSepWPp.exists_pre fun w48 =>
        WSepWPp.exists_pre fun w52 => WSepWPp.exists_pre fun w60 =>
        WSepWPp.exists_pre fun w64 => WSepWPp.exists_pre fun w68 =>
        WSepWPp.exists_pre fun w72 => WSepWPp.exists_pre fun w80 =>
        WSepWPp.exists_pre fun w88 => WSepWPp.exists_pre fun w96 => ?_
      refine wpp_replace_sub (wireSignalMessageOf_rk_some_entails A.repAlloc sp' hrk) ?_
      simp only [sepExists_sepConj_left, sepConj_assoc]
      refine WSepWPp.exists_pre fun rkCap => WSepWPp.exists_pre fun rkPtr =>
        WSepWPp.exists_pre fun ctCap => WSepWPp.exists_pre fun ctPtr =>
        WSepWPp.exists_pre fun ctLen => WSepWPp.exists_pre fun pqCap =>
        WSepWPp.exists_pre fun pqPtr => WSepWPp.exists_pre fun pqLen =>
        WSepWPp.exists_pre fun adCap => WSepWPp.exists_pre fun adPtr =>
        WSepWPp.exists_pre fun adLen => WSepWPp.exists_pre fun cTag =>
        WSepWPp.exists_pre fun cVal => WSepWPp.exists_pre fun pcTag =>
        WSepWPp.exists_pre fun pcVal => ?_
      refine wpp_pure_anywhere (optU32TagVal cTag cVal m'.counter) fun hc => ?_
      refine wpp_pure_anywhere (optU32TagVal pcTag pcVal m'.previousCounter) fun hpc_tag => ?_
      refine wpp_bind_frame_call
        (post_rk_some_head_wp_placed
          (w16 := w16) (w32 := w32) (w40 := w40) (w72 := w72)
          (w80 := w80) (w88 := w88) (w96 := w96)
          (rkCap := rkCap) (rkPtr := rkPtr)
          (ctCap := ctCap) (ctPtr := ctPtr) (ctLen := ctLen)
          (pqCap := pqCap) (pqPtr := pqPtr) (pqLen := pqLen)
          (adCap := adCap) (adPtr := adPtr) (adLen := adLen)
          (w28 := w28) (w48 := w48) (w60 := w60) (w64 := w64)
          (cTag := cTag) (cVal := cVal) (pcTag := pcTag) (pcVal := pcVal)
          hDropSpe st rk hst hpc hrun hx24) ?_
      intro s1 P1 hpc1 hrun1 ⟨hst1, _, _, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, _,
        hx25_1, _, hx27_1, hx28_1, evs₀, hfree₀, hent1⟩
      have hFit1 := fitsEnv_tryFromPostOutPre_step_freeOnly hfree₀ hFit_out
      refine WSepWPp.mono_pre (sepConj_mono_left hent1) ?_
      refine wpp_frame_call
        (post_after_deser_wp_placed
          (rkCap := rkCap) (rkPtr := rkPtr) (ctLen := ctLen)
          (pqPtr := pqPtr) (pqLen := pqLen) (adPtr := adPtr) (adLen := adLen)
          (w12 := w12) (w52 := w52) (w68 := w68)
          hS hDropSpe hIntoBox hTryClone (M.stepEvents evs₀ st)
          x.bytes rk m' hgt9 hlt hdec hc hpc_tag hout hFit1
          hst1 hpc1 hrun1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx27_1 hx28_1)
        fun sf Pf ⟨hstf, evs₁, henv₁, hent⟩ =>
          ⟨hstf, evs₀ ++ evs₁, tryFromPostOutEnv_prepend_freeOnly hfree₀ henv₁, ?_⟩
      rw [M.stepEvents_append]
      refine Entails.trans (sepConj_mono_left hent) ?_
      dsimp only [sp', out]
      generalize skipFieldStackX 100 = nStk,
        signalMessageResultAt A.repAlloc [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) = resOut,
        A.pool lim (M.stepEvents evs₁ (M.stepEvents evs₀ st)) sf = poolOut
      sep_interval

end LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBudget
