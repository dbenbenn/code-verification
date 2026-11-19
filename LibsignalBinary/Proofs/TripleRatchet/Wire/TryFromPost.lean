/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSome -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxes
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.Sep
import ProofLib.SepLogic.WPp

public section

namespace CryptoVerification.LibsignalTripleRatchet.Wire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero slt_noneCap_one
attribute [local simp, local wp_norm] cap_sub1_add3_hi_noneCap cap_sub1_add3_hi_zero slt_noneCap_one

private theorem entails_of_perm {P Q : SepProp}
    (hent : P ⊢ Q := by first | sep_accu | sep_interval | bi_entail) : P ⊢ Q :=
  hent

private theorem replace_sub {prog : Program} {ret : BitVec 64} {s : State}
    {P Old New F : SepProp} {Q : State → SepProp → Prop} {qp : State → SepProp → Prop}
    (himp : Old ⊢ New)
    (hk : SepWPp prog ret s (New ∗ F) Q qp)
    (hent : P ⊢ Old ∗ F := by first | sep_accu | bi_frame) :
    SepWPp prog ret s P Q qp :=
  SepWPp.mono_pre (Entails.trans hent (sepConj_mono_left himp)) hk

private theorem replace_sub_exists {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P Old F : SepProp} {New : α → SepProp} {Q : State → SepProp → Prop} {qp : State → SepProp → Prop}
    (himp : Old ⊢ ∃∗ x, New x)
    (hk : ∀ x, SepWPp prog ret s (New x ∗ F) Q qp)
    (hent : P ⊢ Old ∗ F := by first | sep_accu | bi_frame) :
    SepWPp prog ret s P Q qp := by
  refine replace_sub himp ?_ hent
  rw [sepExists_sepConj_left]
  exact SepWPp.exists_pre hk

private theorem pure_anywhere (φ : Prop) {prog : Program} {ret : BitVec 64} {s : State}
    {P F : SepProp} {Q : State → SepProp → Prop} {qp : State → SepProp → Prop}
    (hk : φ → SepWPp prog ret s F Q qp)
    (hent : P ⊢ ⌜φ⌝ ∗ F := by first | sep_accu | bi_frame) :
    SepWPp prog ret s P Q qp :=
  SepWPp.mono_pre hent (SepWPp.pure_pre hk)

private theorem memRegion120_split24 (x19 : BitVec 64) :
    memRegion x19 120 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ ((x19 + 16#64) ↦₆₄ w2) ∗
        memRegion (x19 + 24#64) 96 := by
  sep_interval

theorem wireSignalMessageOf_rk_some_entails (A : RustAlloc) (sp' : BitVec 64)
    {m' : ProtoSignalMessage} {rk : List (BitVec 8)} (hrk : m'.ratchetKey = some rk) :
    wireSignalMessageOf A (sp' + 176#64) m' ⊢
      ∃∗ rkCap : BitVec 64, ∃∗ rkPtr : BitVec 64,
      ∃∗ ctCap : BitVec 64, ∃∗ ctPtr : BitVec 64, ∃∗ ctLen : BitVec 64,
      ∃∗ pqCap : BitVec 64, ∃∗ pqPtr : BitVec 64, ∃∗ pqLen : BitVec 64,
      ∃∗ adCap : BitVec 64, ∃∗ adPtr : BitVec 64, ∃∗ adLen : BitVec 64,
      ∃∗ cTag : BitVec 32, ∃∗ cVal : BitVec 32,
      ∃∗ pcTag : BitVec 32, ∃∗ pcVal : BitVec 32,
        ⌜optU32TagVal cTag cVal m'.counter⌝ ∗
        ⌜optU32TagVal pcTag pcVal m'.previousCounter⌝ ∗
        vecHeader (sp' + 176#64) rkCap rkPtr (BitVec.ofNat 64 rk.length) ∗
        vecU8Buf A rkCap rkPtr rk ∗
        vecHeader (sp' + 200#64) ctCap ctPtr ctLen ∗
        optVecU8Buf A ctCap ctPtr ctLen m'.ciphertext ∗
        vecHeader (sp' + 224#64) pqCap pqPtr pqLen ∗
        optVecU8Buf A pqCap pqPtr pqLen m'.pqRatchet ∗
        vecHeader (sp' + 248#64) adCap adPtr adLen ∗
        optVecU8Buf A adCap adPtr adLen m'.addresses ∗
        ((sp' + 272#64) ↦₃₂ cTag) ∗ ((sp' + 276#64) ↦₃₂ cVal) ∗
        ((sp' + 280#64) ↦₃₂ pcTag) ∗ ((sp' + 284#64) ↦₃₂ pcVal) := by
  unfold wireSignalMessageOf
  refine Entails.sepExists_elim fun g => ?_
  unfold wireSignalMessageAt
  rw [hrk]
  have hrk_eq : optVecU8At A g.rk (sp' + 176#64) (some rk) =
      vecHeader (sp' + 176#64) g.rk.1 g.rk.2 (BitVec.ofNat 64 rk.length) ∗
      vecU8Buf A g.rk.1 g.rk.2 rk := by
    unfold optVecU8At
    exact vecU8At_eq_header_buf A (sp' + 176#64) g.rk.1 g.rk.2 rk
  rw [hrk_eq, sepConj_assoc]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (optVecU8At_entails_header_buf A g.ct (sp' + 200#64) m'.ciphertext)
        (sepConj_mono (optVecU8At_entails_header_buf A g.pq (sp' + 224#64) m'.pqRatchet)
          (sepConj_mono (optVecU8At_entails_header_buf A g.addr (sp' + 248#64) m'.addresses)
            (sepConj_mono
              (by simpa [BitVec.add_assoc, BitVec.reduceAdd] using optU32At_entails_tag_val (sp' + 272#64) m'.counter)
              (by simpa [BitVec.add_assoc, BitVec.reduceAdd] using optU32At_entails_tag_val (sp' + 280#64) m'.previousCounter))))))) ?_
  simp only [sepExists_sepConj_left]
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun ctCap => Entails.sepExists_elim fun ctPtr =>
    Entails.sepExists_elim fun ctLen => Entails.sepExists_elim fun pqCap =>
    Entails.sepExists_elim fun pqPtr => Entails.sepExists_elim fun pqLen =>
    Entails.sepExists_elim fun adCap => Entails.sepExists_elim fun adPtr =>
    Entails.sepExists_elim fun adLen => Entails.sepExists_elim fun cTag =>
    Entails.sepExists_elim fun cVal => Entails.sepExists_elim fun pcTag =>
    Entails.sepExists_elim fun pcVal => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro g.rk.1)
  refine Entails.trans ?_ (Entails.sepExists_intro g.rk.2)
  refine Entails.trans ?_ (Entails.sepExists_intro ctCap)
  refine Entails.trans ?_ (Entails.sepExists_intro ctPtr)
  refine Entails.trans ?_ (Entails.sepExists_intro ctLen)
  refine Entails.trans ?_ (Entails.sepExists_intro pqCap)
  refine Entails.trans ?_ (Entails.sepExists_intro pqPtr)
  refine Entails.trans ?_ (Entails.sepExists_intro pqLen)
  refine Entails.trans ?_ (Entails.sepExists_intro adCap)
  refine Entails.trans ?_ (Entails.sepExists_intro adPtr)
  refine Entails.trans ?_ (Entails.sepExists_intro adLen)
  refine Entails.trans ?_ (Entails.sepExists_intro cTag)
  refine Entails.trans ?_ (Entails.sepExists_intro cVal)
  refine Entails.trans ?_ (Entails.sepExists_intro pcTag)
  refine Entails.trans ?_ (Entails.sepExists_intro pcVal)
  exact entails_of_perm

theorem memRegion112_of_48_64 (sp' : BitVec 64) :
    memRegion (sp' + 176#64) 48 ∗ memRegion (sp' + 224#64) 64 ⊢
      memRegion (sp' + 176#64) 112 := by
  sep_interval

theorem memRegion112_of_33_15_64 (sp' : BitVec 64) :
    memRegion (sp' + 176#64) 33 ∗ memRegion (sp' + 209#64) 15 ∗ memRegion (sp' + 224#64) 64 ⊢
      memRegion (sp' + 176#64) 112 := by
  sep_interval

theorem memRegion112_of_8_40_64 (sp' w176 : BitVec 64) :
    ((sp' + 176#64) ↦₆₄ w176) ∗ memRegion (sp' + 184#64) 40 ∗ memRegion (sp' + 224#64) 64 ⊢
      memRegion (sp' + 176#64) 112 := by
  sep_interval

theorem memRegion104_0_pack64 (sp' : BitVec 64)
    (w12 w28 w60 : BitVec 32)
    (w16 w32 w40 w48 w64 w72 w80 w88 w96 : BitVec 64) :
    spUnused0 sp' ∗
      ((sp' + 12#64) ↦₃₂ w12) ∗ ((sp' + 16#64) ↦₆₄ w16) ∗
      ((sp' + 28#64) ↦₃₂ w28) ∗ ((sp' + 32#64) ↦₆₄ w32) ∗
      ((sp' + 40#64) ↦₆₄ w40) ∗ ((sp' + 48#64) ↦₆₄ w48) ∗
      ((sp' + 60#64) ↦₃₂ w60) ∗ ((sp' + 64#64) ↦₆₄ w64) ∗
      ((sp' + 72#64) ↦₆₄ w72) ∗ ((sp' + 80#64) ↦₆₄ w80) ∗
      ((sp' + 88#64) ↦₆₄ w88) ∗ ((sp' + 96#64) ↦₆₄ w96) ⊢
      memRegion sp' 104 := by
  unfold spUnused0; sep_interval

theorem vecU8Buf_cap_lt (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8Buf
  refine Entails.pure_left fun h => ?_
  rw [pure_true_emp h.2.1, emp_sepConj, pure_true_emp h, emp_sepConj]
  exact Entails.refl _

theorem zext32_zext64_8 (b : BitVec 8) :
    (b.zeroExtend 32).zeroExtend 64 = b.zeroExtend 64 := by bv_kernel

theorem SepWPp.bind_frame_tryFrom {prog : Program} {mid ret : BitVec 64} {s0 s : Arm64.State}
    {P F : SepProp} {Q' Q : Arm64.State → SepProp → Prop}
    (h1 : SepWPp prog mid s P Q' (tryFromQp s0))
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Q' sm Pm →
      SepWPp prog ret sm (Pm ∗ F) Q (tryFromQp s0)) :
    SepWPp prog ret s (P ∗ F) Q (tryFromQp s0) := by
  refine SepWPp.bind (SepWPp.frame_tryFrom (Q := fun sm Pmf => ∃ Pm, Pmf = Pm ∗ F ∧ Q' sm Pm)
    h1 (fun _ Pm hqm => ⟨Pm, rfl, hqm⟩)) ?_
  intro sm Pmf hpc hrun ⟨Pm, hPmf, hqm⟩
  subst hPmf
  exact h2 sm Pm hpc hrun hqm

private theorem frame_call {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P P1 F : SepProp} {Q' Q : State → SepProp → Prop}
    (h1 : SepWPp prog ret s P1 Q' (tryFromQp s0))
    (hpost : ∀ sf Pf, Q' sf Pf → Q sf (Pf ∗ F))
    (hent : P ⊢ P1 ∗ F := by first | sep_accu | bi_frame) :
    SepWPp prog ret s P Q (tryFromQp s0) :=
  SepWPp.mono_pre hent (SepWPp.frame_tryFrom h1 hpost)

private theorem bind_frame_call {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P1 F : SepProp} {Q' Q : State → SepProp → Prop}
    (h1 : SepWPp prog mid s P1 Q' (tryFromQp s0))
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Q' sm Pm →
      SepWPp prog ret sm (Pm ∗ F) Q (tryFromQp s0))
    (hent : P ⊢ P1 ∗ F := by first | sep_accu | bi_frame) :
    SepWPp prog ret s P Q (tryFromQp s0) :=
  SepWPp.mono_pre hent (SepWPp.bind_frame_tryFrom h1 h2)

theorem memRegion176_split_88_16_72 (sp' : BitVec 64) :
    memRegion sp' 176 =
      memRegion sp' 88 ∗ memRegion (sp' + 88#64) 16 ∗ memRegion (sp' + 104#64) 72 := by
  sep_interval_eq

theorem memRegion176_split_104_72 (sp' : BitVec 64) :
    memRegion sp' 176 = memRegion sp' 104 ∗ memRegion (sp' + 104#64) 72 := by
  sep_interval_eq

theorem memRegion352_of_104_72_112_64 (sp' : BitVec 64) :
    memRegion sp' 104 ∗ memRegion (sp' + 104#64) 72 ∗
      memRegion (sp' + 176#64) 112 ∗ memRegion (sp' + 288#64) 64 ⊢
      memRegion sp' 352 := by
  sep_interval

theorem memRegion352_of_88_16_72_112_64 (sp' : BitVec 64) :
    memRegion sp' 88 ∗ memRegion (sp' + 88#64) 16 ∗ memRegion (sp' + 104#64) 72 ∗
      memRegion (sp' + 176#64) 112 ∗ memRegion (sp' + 288#64) 64 ⊢
      memRegion sp' 352 := by
  sep_interval

/-!
# `<SignalMessage>::try_from` Post-Loop Composition (`+0x3b0 .. +0x764`)

Assembles the post-loop validation, `PublicKey::deserialize`, slice boxing/cloning, `SignalMessage`
packing, and error cleanup tails into `tryFrom_post_wp` and its relocatable `[LibsignalPlacement]`
counterpart `tryFrom_post_wp_placed` (Block `85`).
-/

theorem post_after_578_wp_placed [lsmpl : LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hDropSpe : DropSpeOkWPlaced A H)
    (hIntoBox : IntoBoxedSliceOkPlaced A H)
    (hTryClone : TryCloneFromRefOkPlaced A H)
    {s0 s : State}
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
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 0x578#64)
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
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s
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
        vecU8Buf A rkCap rkPtr rk ∗
        optVecU8Buf A ctCap ctPtr ctLen m'.ciphertext ∗
        optVecU8Buf A pqCap pqPtr pqLen m'.pqRatchet ∗
        optVecU8Buf A adCap adPtr adLen m'.addresses ∗
        memRegion x19 120 ∗
        (x21 ↦ₛ bs) ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ memRegion sp' 104 ∗ memRegion (sp' + 104#64) 72 ∗
          memRegion (sp' + 176#64) 112 ∗
          signalMessageResultAt A [] x19 out ∗
          (x21 ↦ₛ bs) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  have h48_pair := pointsTo32_pair_eq_pointsTo64 (sp' + 48#64) pcTag w52
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h48_pair
  refine replace_sub (entails_of_eq h48_pair) ?_
  cases hct : m'.ciphertext with
  | none =>
    simp only [hct] at hout
    have hct_eq : optVecU8Buf A ctCap ctPtr ctLen none = ⌜ctCap = noneCap⌝ := rfl
    rw [hct_eq]
    refine pure_anywhere (ctCap = noneCap) fun hct_cap => ?_
    subst hct_cap
    refine replace_sub_exists (optVecU8Buf_entails_deallocSlot A pqCap pqPtr pqLen m'.pqRatchet) fun pqAct => ?_
    refine replace_sub_exists (optVecU8Buf_entails_deallocSlot A adCap adPtr adLen m'.addresses) fun adAct => ?_
    refine replace_sub (memRegion120_split16 x19) ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_pre fun w1 => SepWPp.exists_pre fun w0 => ?_
    refine frame_call
      (post_ct_none_wp_placed
        (w0 := w0) (w1 := w1) (rkCap := rkCap) (rkPtr := rkPtr)
        (pqPtr := pqPtr) (adPtr := adPtr)
        hS rk pqAct adAct hout hst hpc hrun hpstate hx19 hx26 hx25 hx22)
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    generalize skipFieldStackX 100 = nStk, signalMessageResultAt A [] x19 out = resOut
    unfold spUnused0 spUnused104 sevenBytesHeadAt vecHeader
    sep_interval
  | some ct =>
    simp only [hct] at hout
    have hbnd := msg_bounds_of_decode hgt9 hlt hdec hct
    have hct_eq : optVecU8Buf A ctCap ctPtr ctLen (some ct) =
        ⌜ctLen = BitVec.ofNat 64 ct.length⌝ ∗ vecU8Buf A ctCap ctPtr ct := rfl
    rw [hct_eq]
    refine pure_anywhere (ctLen = BitVec.ofNat 64 ct.length) fun hct_len => ?_
    subst hct_len
    refine replace_sub (vecU8Buf_cap_lt A ctCap ctPtr ct) ?_
    refine pure_anywhere (ctCap.toNat < 2 ^ 63) fun hct_lt => ?_
    refine bind_frame_call
      (post_ct_some_boxes_wp_placed
        (pqPtr := pqPtr) (pqLen := pqLen) (adPtr := adPtr) (adLen := adLen)
        (w48 := w52 ++ pcTag) (w136 := w136) (w144 := w144) (w152 := w152) (w60 := pcVal)
        hDropSpe hIntoBox ct m'.pqRatchet m'.addresses
        hct_lt hst hpc hrun hpstate hx8 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx27 hx28) ?_
    intro s2 P2 hpc2 hrun2 ⟨pqCap', pqPtr', ctBoxPtr, adBoxPtr, w96',
      hst2, _, _, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hent2⟩
    refine SepWPp.mono_pre (sepConj_mono_left hent2) ?_
    refine replace_sub (memRegion120_split16 x19) ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_pre fun w1 => SepWPp.exists_pre fun w0 => ?_
    set msg : SignalMessage :=
      { messageVersion := (bs.headD 0#8) >>> 4, senderRatchetKey := pk, counter,
        previousCounter := m'.previousCounter.getD 0#32, ciphertext := ct,
        pqRatchet := m'.pqRatchet.getD [], addresses := m'.addresses,
        serialized := bs }
    refine frame_call
      (post_clone_and_pack_wp_placed
        (pqCap' := pqCap') (pqPtr' := pqPtr') (ctBoxPtr := ctBoxPtr)
        (adBoxPtr := adBoxPtr) (w96 := w96') (rkCap := rkCap) (rkPtr := rkPtr)
        (w0 := w0) (w1 := w1) (b_ver := bs.headD 0#8)
        hS hTryClone rk msg hout hbnd hpk rfl
        hst2 hpc2 hrun2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2)
      (fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩)
      (by dsimp only [msg]; sep_accu)
    refine Entails.trans (sepConj_mono_left hent) ?_
    dsimp only [msg]
    generalize skipFieldStackX 100 = nStk, signalMessageResultAt A [] x19 out = resOut
    unfold spUnused0 spUnused104 sevenBytesHeadAt vecHeader
    sep_interval

theorem post_after_54c_wp_placed [lsmpl : LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hDropSpe : DropSpeOkWPlaced A H)
    (hIntoBox : IntoBoxedSliceOkPlaced A H)
    (hTryClone : TryCloneFromRefOkPlaced A H)
    {s0 s : State}
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
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 0x54c#64)
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
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s
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
        vecU8Buf A rkCap rkPtr rk ∗
        optVecU8Buf A ctCap ctPtr ctLen m'.ciphertext ∗
        optVecU8Buf A pqCap pqPtr pqLen m'.pqRatchet ∗
        optVecU8Buf A adCap adPtr adLen m'.addresses ∗
        memRegion x19 120 ∗
        (x21 ↦ₛ bs) ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ memRegion sp' 104 ∗ memRegion (sp' + 104#64) 72 ∗
          memRegion (sp' + 176#64) 112 ∗
          signalMessageResultAt A [] x19 out ∗
          (x21 ↦ₛ bs) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  cases hcnt : m'.counter with
  | none =>
    simp only [hcnt] at hout
    rw [hcnt] at hc
    dsimp only [optU32TagVal] at hc
    subst hc
    have h48_pair := pointsTo32_pair_eq_pointsTo64 (sp' + 48#64) pcTag w52
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h48_pair
    refine replace_sub (entails_of_eq h48_pair) ?_
    refine replace_sub_exists (optVecU8Buf_entails_deallocSlot A ctCap ctPtr ctLen m'.ciphertext) fun ctAct => ?_
    refine replace_sub_exists (optVecU8Buf_entails_deallocSlot A pqCap pqPtr pqLen m'.pqRatchet) fun pqAct => ?_
    refine replace_sub_exists (optVecU8Buf_entails_deallocSlot A adCap adPtr adLen m'.addresses) fun adAct => ?_
    refine replace_sub (memRegion120_split16 x19) ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_pre fun w1 => SepWPp.exists_pre fun w0 => ?_
    refine frame_call
      (post_counter_none_wp_placed
        (w0 := w0) (w1 := w1) (rkCap := rkCap) (rkPtr := rkPtr)
        (pqPtr := pqPtr) (adPtr := adPtr)
        hS rk ctAct pqAct adAct hout
        hst hpc hrun hpstate hx19 hx26 hx27 hx28 hx25 hx22)
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    generalize skipFieldStackX 100 = nStk, signalMessageResultAt A [] x19 out = resOut
    unfold spUnused0 spUnused104 sevenBytesHeadAt vecHeader
    sep_interval
  | some counter =>
    simp only [hcnt] at hout
    rw [hcnt] at hc
    rcases hc with ⟨rfl, hcVal⟩
    subst cVal
    refine bind_frame_call
      (post_counter_some_head_wp_placed
        (w64 := w68 ++ 1#32) (w12 := w12) (pcTag := pcTag) (pcVal := pcVal)
        hDropSpe hst hpc hrun hpstate hx8 hx9 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28) ?_
    intro s1 P1 hpc1 hrun1 ⟨hst1, _, _, hpstate1, hx8_1, hx19_1, hx20_1, hx21_1, hx22_1,
      hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hent1⟩
    rw [pcVal_if_eq_getD hpc_tag] at hx8_1
    rw [zext32_zext64_8 b7] at hx24_1
    refine SepWPp.mono_pre (sepConj_mono_left hent1) ?_
    have hcall := post_after_578_wp_placed
      (rkCap := rkCap) (rkPtr := rkPtr) (ctLen := ctLen)
      (pqPtr := pqPtr) (pqLen := pqLen) (adPtr := adPtr) (adLen := adLen)
      (w136 := w136) (w144 := w144) (w152 := w152)
      (w52 := w52) (pcTag := pcTag) (pcVal := pcVal)
      hS hDropSpe hIntoBox hTryClone
      bs rk m' pk hgt9 hlt hdec hpk hout
      hst1 hpc1 hrun1 hpstate1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
      hx25_1 hx26_1 hx27_1 hx28_1
    exact SepWPp.mono_pre entails_of_perm hcall

theorem post_after_deser_wp_placed [lsmpl : LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hDropSpe : DropSpeOkWPlaced A H)
    (hIntoBox : IntoBoxedSliceOkPlaced A H)
    (hTryClone : TryCloneFromRefOkPlaced A H)
    {s0 s : State}
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
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 0x4c4#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x19)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 bs.length)
    (hx21 : s.readReg64 .x21 = x21)
    (hx22 : s.readReg64 .x22 = adCap)
    (hx23 : s.readReg64 .x23 = (bs.headD 0#8).zeroExtend 64)
    (hx25 : s.readReg64 .x25 = pqCap)
    (hx27 : s.readReg64 .x27 = ctCap)
    (hx28 : s.readReg64 .x28 = ctPtr) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s
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
        vecU8Buf A rkCap rkPtr rk ∗
        optVecU8Buf A ctCap ctPtr ctLen m'.ciphertext ∗
        optVecU8Buf A pqCap pqPtr pqLen m'.pqRatchet ∗
        optVecU8Buf A adCap adPtr adLen m'.addresses ∗
        memRegion x19 120 ∗
        (x21 ↦ₛ bs) ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ memRegion sp' 104 ∗ memRegion (sp' + 104#64) 72 ∗
          memRegion (sp' + 176#64) 112 ∗
          signalMessageResultAt A [] x19 out ∗
          (x21 ↦ₛ bs) ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  cases hdeser : PublicKey.deserialize rk with
  | error e =>
    simp only [hdeser] at hout
    refine replace_sub_exists (optVecU8Buf_entails_deallocSlot A ctCap ctPtr ctLen m'.ciphertext) fun ctAct => ?_
    refine replace_sub_exists (optVecU8Buf_entails_deallocSlot A pqCap pqPtr pqLen m'.pqRatchet) fun pqAct => ?_
    refine replace_sub_exists (optVecU8Buf_entails_deallocSlot A adCap adPtr adLen m'.addresses) fun adAct => ?_
    refine replace_sub (memRegion120_split24 x19) ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_pre fun w0 => SepWPp.exists_pre fun w1 =>
      SepWPp.exists_pre fun w2 => ?_
    refine frame_call
      (post_deser_err_wp_placed
        (w0 := w0) (w1 := w1) (w2 := w2) (rkCap := rkCap) (rkPtr := rkPtr)
        (pqPtr := pqPtr) (adPtr := adPtr)
        hS rk ctAct pqAct adAct e hdeser hout
        hst hpc hrun hx19 hx27 hx28 hx25 hx22)
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    generalize skipFieldStackX 100 = nStk, signalMessageResultAt A [] x19 out = resOut
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
    refine replace_sub (memRegion72_104_unpack sp') ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_pre fun w104 => SepWPp.exists_pre fun b112 =>
      SepWPp.exists_pre fun w120 => SepWPp.exists_pre fun w124 =>
      SepWPp.exists_pre fun c0 => SepWPp.exists_pre fun c1 =>
      SepWPp.exists_pre fun c2 => SepWPp.exists_pre fun c3 =>
      SepWPp.exists_pre fun c4 => SepWPp.exists_pre fun c5 =>
      SepWPp.exists_pre fun c6 => SepWPp.exists_pre fun w136 =>
      SepWPp.exists_pre fun w144 => SepWPp.exists_pre fun w152 => ?_
    refine bind_frame_call
      (post_deser_ok_head_wp_placed
        (w104 := w104) (w15 := w15) (w23 := w23)
        (cTag := cTag) (w68 := w68) (w9 := w9) (w120 := w120)
        (w13 := w13) (w124 := w124)
        (b0 := b0) (b1 := b1) (b2 := b2) (b3 := b3) (b4 := b4)
        (b5 := b5) (b6 := b6) (b7 := b7) (b8 := b8) (b31 := b31) (b112 := b112)
        (c0 := c0) (c1 := c1) (c2 := c2) (c3 := c3) (c4 := c4) (c5 := c5) (c6 := c6)
        hst hpc hrun) ?_
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
    refine SepWPp.mono_pre (sepConj_mono_left hent1) ?_
    have hcall := post_after_54c_wp_placed
      (rkCap := rkCap) (rkPtr := rkPtr) (ctLen := ctLen)
      (pqPtr := pqPtr) (pqLen := pqLen) (adPtr := adPtr) (adLen := adLen)
      (w136 := w136) (w144 := w144) (w152 := w152)
      (w12 := w12) (w52 := w52) (w68 := w68)
      hS hDropSpe hIntoBox hTryClone
      bs rk m' pk hgt9 hlt hdec hpk hc hpc_tag hout
      hst1 hpc1 hrun1 hpstate1 hx8_1 hx9_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
      hx25_1 hx26_1 hx27_1 hx28_1
    exact SepWPp.mono_pre entails_of_perm hcall

theorem tryFrom_post_wp_placed [lsmpl : LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hDropErr : DropDecodeErrorOkWPlaced A H)
    (hDropSpe : DropSpeOkWPlaced A H)
    (hIntoBox : IntoBoxedSliceOkPlaced A H)
    (hTryClone : TryCloneFromRefOkPlaced A H)
    {x : TryFromGhost} {s0 s : State}
    (hgt9 : 9 < x.bytes.length)
    (hlt : x.bytes.length < 2 ^ 32)
    (hge3 : ¬ ((x.bytes.headD 0#8) >>> 4) < 3#8)
    (hle4 : ¬ 4#8 < ((x.bytes.headD 0#8) >>> 4))
    (hpc : s.pc = (blkPl_85).base + 0x3b0#64)
    (hrun : s.status = .Running)
    (hst : LoopExitStatePlaced s0 (s0.sp - 448#64) x.ret
      (BitVec.ofNat 64 x.bytes.length) x.bytesA ((x.bytes.headD 0#8).zeroExtend 64) s) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s
      (memRegion (s0.sp - 448#64) 176 ∗
        memRegion (s0.sp - 448#64 + 288#64) 64 ∗
        (x.bytesA ↦ₛ x.bytes) ∗
        A.pool ∗ stackAt (s0.sp - 448#64) (skipFieldStackX 100) ∗
        (match decode ((x.bytes.take (x.bytes.length - 8)).drop 1) with
         | some m' =>
           ⌜s.readReg64 .x24 = 0#64⌝ ∗ wireSignalMessageOf A (s0.sp - 448#64 + 176#64) m'
         | none =>
           ⌜s.readReg64 .x24 ≠ 0#64⌝ ∗ decodeErrorAt A (s.readReg64 .x24) ∗
             (∃∗ mErr, wireSignalMessageOf A (s0.sp - 448#64 + 176#64) mErr)) ∗
        memRegion x.ret 120 ∗ logOff tryFromPlacedImg)
      (fun sf Pf =>
        PostEpilogueStatePlaced s0 (s0.sp - 448#64) sf ∧
        (Pf ⊢ memRegion (s0.sp - 448#64) 352 ∗
          signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
          (x.bytesA ↦ₛ x.bytes) ∗ logOff tryFromPlacedImg ∗ A.pool ∗
          stackAt (s0.sp - 448#64) (skipFieldStackX 100)))
      (tryFromQp s0) := by
  set sp' := s0.sp - 448#64
  set out := SignalMessage.tryFrom protoSignalCodec x.bytes
  have hout := tryFrom_eq_of_gt9 hgt9 hge3 hle4
  cases hdec : decode ((x.bytes.take (x.bytes.length - 8)).drop 1) with
  | none =>
    have hdec' : LibsignalProtoCodec.decode ((x.bytes.take (x.bytes.length - 8)).drop 1) = none := hdec
    simp only [hdec'] at hout
    rw [memRegion176_split_88_16_72 sp']
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre fun mErr => ?_
    refine pure_anywhere (s.readReg64 .x24 ≠ 0#64) fun hx24_ne => ?_
    refine frame_call
      (post_none_wp_placed hS hDropErr hout hst hpc hrun rfl hx24_ne mErr)
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    dsimp only [sp', out]
    generalize skipFieldStackX 100 = nStk,
      signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) = resOut
    sep_interval
  | some m' =>
    have hdec' : LibsignalProtoCodec.decode ((x.bytes.take (x.bytes.length - 8)).drop 1) = some m' := hdec
    simp only [hdec'] at hout
    cases hrk : m'.ratchetKey with
    | none =>
      simp only [hrk] at hout
      rw [memRegion176_split_88_16_72 sp']
      simp only [sepConj_assoc]
      refine pure_anywhere (s.readReg64 .x24 = 0#64) fun hx24 => ?_
      refine frame_call
        (post_rk_none_wp_placed hS hrk hout hst hpc hrun hx24)
        fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
      refine Entails.trans (sepConj_mono_left hent) ?_
      dsimp only [sp', out]
      generalize skipFieldStackX 100 = nStk,
        signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) = resOut
      sep_interval
    | some rk =>
      simp only [hrk] at hout
      rw [memRegion176_split_104_72 sp']
      simp only [sepConj_assoc]
      refine pure_anywhere (s.readReg64 .x24 = 0#64) fun hx24 => ?_
      refine replace_sub (memRegion104_0_unpack sp') ?_
      simp only [sepExists_sepConj_left, sepConj_assoc]
      refine SepWPp.exists_pre fun w12 => SepWPp.exists_pre fun w16 =>
        SepWPp.exists_pre fun w28 => SepWPp.exists_pre fun w32 =>
        SepWPp.exists_pre fun w40 => SepWPp.exists_pre fun w48 =>
        SepWPp.exists_pre fun w52 => SepWPp.exists_pre fun w60 =>
        SepWPp.exists_pre fun w64 => SepWPp.exists_pre fun w68 =>
        SepWPp.exists_pre fun w72 => SepWPp.exists_pre fun w80 =>
        SepWPp.exists_pre fun w88 => SepWPp.exists_pre fun w96 => ?_
      refine replace_sub (wireSignalMessageOf_rk_some_entails A sp' hrk) ?_
      simp only [sepExists_sepConj_left, sepConj_assoc]
      refine SepWPp.exists_pre fun rkCap => SepWPp.exists_pre fun rkPtr =>
        SepWPp.exists_pre fun ctCap => SepWPp.exists_pre fun ctPtr =>
        SepWPp.exists_pre fun ctLen => SepWPp.exists_pre fun pqCap =>
        SepWPp.exists_pre fun pqPtr => SepWPp.exists_pre fun pqLen =>
        SepWPp.exists_pre fun adCap => SepWPp.exists_pre fun adPtr =>
        SepWPp.exists_pre fun adLen => SepWPp.exists_pre fun cTag =>
        SepWPp.exists_pre fun cVal => SepWPp.exists_pre fun pcTag =>
        SepWPp.exists_pre fun pcVal => ?_
      refine pure_anywhere (optU32TagVal cTag cVal m'.counter) fun hc => ?_
      refine pure_anywhere (optU32TagVal pcTag pcVal m'.previousCounter) fun hpc_tag => ?_
      refine bind_frame_call
        (post_rk_some_head_wp_placed
          (w16 := w16) (w32 := w32) (w40 := w40) (w72 := w72)
          (w80 := w80) (w88 := w88) (w96 := w96)
          (rkCap := rkCap) (rkPtr := rkPtr)
          (ctCap := ctCap) (ctPtr := ctPtr) (ctLen := ctLen)
          (pqCap := pqCap) (pqPtr := pqPtr) (pqLen := pqLen)
          (adCap := adCap) (adPtr := adPtr) (adLen := adLen)
          (w28 := w28) (w48 := w48) (w60 := w60) (w64 := w64)
          (cTag := cTag) (cVal := cVal) (pcTag := pcTag) (pcVal := pcVal)
          hDropSpe rk hst hpc hrun hx24) ?_
      intro s1 P1 hpc1 hrun1 ⟨hst1, _, _, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, _,
        hx25_1, _, hx27_1, hx28_1, hent1⟩
      refine SepWPp.mono_pre (sepConj_mono_left hent1) ?_
      refine frame_call
        (post_after_deser_wp_placed
          (rkCap := rkCap) (rkPtr := rkPtr) (ctLen := ctLen)
          (pqPtr := pqPtr) (pqLen := pqLen) (adPtr := adPtr) (adLen := adLen)
          (w12 := w12) (w52 := w52) (w68 := w68)
          hS hDropSpe hIntoBox hTryClone
          x.bytes rk m' hgt9 hlt hdec hc hpc_tag hout
          hst1 hpc1 hrun1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx27_1 hx28_1)
        fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
      refine Entails.trans (sepConj_mono_left hent) ?_
      dsimp only [sp', out]
      generalize skipFieldStackX 100 = nStk,
        signalMessageResultAt A [] x.ret (SignalMessage.tryFrom protoSignalCodec x.bytes) = resOut
      sep_interval

end CryptoVerification.LibsignalTripleRatchet.Wire
