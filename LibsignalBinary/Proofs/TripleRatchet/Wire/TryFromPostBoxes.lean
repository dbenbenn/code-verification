/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDeser -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
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

private theorem replace_sub {prog : Program} {ret : BitVec 64} {s : State}
    {P Old New F : SepProp} {Q : State → SepProp → Prop} {qp : State → SepProp → Prop}
    (himp : Old ⊢ New)
    (hk : SepWPp prog ret s (New ∗ F) Q qp)
    (hframe : P ⊢ Old ∗ F := by sep_accu) :
    SepWPp prog ret s P Q qp :=
  SepWPp.mono_pre (Entails.trans hframe (sepConj_mono_left himp)) hk

private theorem pure_anywhere (φ : Prop) {prog : Program} {ret : BitVec 64} {s : State}
    {P F : SepProp} {Q : State → SepProp → Prop} {qp : State → SepProp → Prop}
    (hk : φ → SepWPp prog ret s F Q qp)
    (hent : P ⊢ ⌜φ⌝ ∗ F := by sep_accu) :
    SepWPp prog ret s P Q qp :=
  SepWPp.mono_pre hent (SepWPp.pure_pre hk)

private theorem frame_post {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P Goal F : SepProp} {Q' Q : State → SepProp → Prop}
    (hwp : SepWPp prog ret s Goal Q' (tryFromQp s0))
    (hframe : P ⊢ Goal ∗ F)
    (hpost : ∀ sf Pf, Q' sf Pf → Q sf (Pf ∗ F)) :
    SepWPp prog ret s P Q (tryFromQp s0) :=
  SepWPp.mono_pre hframe (SepWPp.frame_tryFrom hwp hpost)

theorem cap_add1_ne_of_lt {cap : BitVec 64} (hlt : cap.toNat < 2 ^ 63) :
    (cap + 1#64 != 0#64) = true := by
  have h2 : cap < 0x8000000000000000#64 := by simpa [BitVec.lt_def] using hlt
  bv_kernel

theorem tryFromQp_of_panicked {s0 s : Arm64.State} {P : SepProp}
    (htr : (Rust.panicked s).trace = s0.trace ++ [allocFailedEvent]) :
    tryFromQp s0 (Rust.panicked s) P :=
  fun _ hm => allowPanic_panicked (allocFailedIn_of_eq htr) hm

theorem post_vecU8Buf_lt (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecU8Buf A cap ptr bs := by
  dsimp only [vecU8Buf]
  refine Entails.pure_left fun ⟨hle, hlt, hptr⟩ => ?_
  rw [pure_true_emp hlt, emp_sepConj, pure_true_emp ⟨hle, hlt, hptr⟩, emp_sepConj]
  exact Entails.refl _

theorem optVecU8Buf_pq_to_vecU8Buf (A : RustAlloc) (pqCap pqPtr pqLen : BitVec 64)
    (pqOpt : Option (List (BitVec 8))) :
    let pqCap' := if (pqCap + 1#64 == 0#64) then 0#64 else pqCap
    let pqPtr' := if (pqCap + 1#64 != 0#64) then pqPtr else 1#64
    let pqLen' := if (pqCap + 1#64 == 0#64) then 0#64 else pqLen
    optVecU8Buf A pqCap pqPtr pqLen pqOpt ⊢
      ⌜pqLen' = BitVec.ofNat 64 (pqOpt.getD []).length⌝ ∗
        vecU8Buf A pqCap' pqPtr' (pqOpt.getD []) := by
  cases pqOpt with
  | none =>
    dsimp only [optVecU8Buf, Option.getD]
    rw [← sepConj_emp ⌜pqCap = noneCap⌝]
    refine Entails.pure_left fun hcap => ?_
    subst hcap
    have heq : (noneCap + 1#64 == 0#64) = true := by decide
    have hne : (noneCap + 1#64 != 0#64) = false := by decide
    have h0 : (0#64 : BitVec 64) = BitVec.ofNat 64 ([] : List (BitVec 8)).length := rfl
    rw [heq, hne]
    simp only [ite_true, Bool.false_eq_true, ite_false]
    rw [vecU8Buf_zero, pure_true_emp h0, pure_true_emp ⟨rfl, by decide⟩, emp_sepConj]
    exact Entails.refl _
  | some pq =>
    dsimp only [optVecU8Buf, Option.getD]
    refine Entails.pure_left fun hlen => ?_
    subst hlen
    refine Entails.trans (post_vecU8Buf_lt A pqCap pqPtr pq) ?_
    refine Entails.pure_left fun hlt => ?_
    have heq := cap_add1_eq_of_lt hlt
    have hne := cap_add1_ne_of_lt hlt
    rw [heq, hne]
    simp only [Bool.false_eq_true, ite_false, ite_true]
    rw [pure_true_emp trivial, emp_sepConj]
    exact Entails.refl _

theorem post_memRegion48_split24 (sp' : BitVec 64) :
    memRegion (sp' + 176#64) 48 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        vecHeader (sp' + 176#64) w0 w1 w2) ∗
        memRegion (sp' + 200#64) 24 := by
  dsimp only [vecHeader]
  simp only [sepExists_sepConj_left]
  sep_interval_eq

theorem vecHeader_memRegion24_entails_48 (sp' w0 w1 w2 : BitVec 64) :
    vecHeader (sp' + 176#64) w0 w1 w2 ∗ memRegion (sp' + 200#64) 24 ⊢
      memRegion (sp' + 176#64) 48 := by
  unfold vecHeader; sep_interval

/-!
# `<SignalMessage>::try_from` Post-Loop Box Conversion & Message Packing

Proves `Vec<u8>::into_boxed_slice` conversion for `ciphertext` and `addresses` (`+0x578..+0x6c0`),
`Box<[u8]>::try_clone_from_ref_in` on `serialized`, and 120-byte `SignalMessage` `sret` packing
(`+0x6c0..+0x764` → `+0x440`), along with relocatable `[LibsignalPlacement]` variants (Block `85`).
-/

/-- Pending heap ownership for `m'.addresses : Option (List (BitVec 8))` after `+0x5c0..+0x5e4` / `+0x6bc`. -/
@[expose] def optBoxU8Pending (A : RustAlloc) (x22 w96 : BitVec 64) : Option (List (BitVec 8)) → SepProp
  | none => ⌜x22 = 0#64⌝
  | some bs => ⌜w96 = BitVec.ofNat 64 bs.length⌝ ∗ boxU8Buf A x22 bs

theorem optBoxU8At_of_pending (A : RustAlloc) (a x22 w96 : BitVec 64)
    (adOpt : Option (List (BitVec 8))) :
    (a ↦₆₄ x22) ∗ ((a + 8#64) ↦₆₄ w96) ∗ optBoxU8Pending A x22 w96 adOpt ⊢
      optBoxU8At A a x22 adOpt := by
  cases adOpt with
  | none =>
    dsimp only [optBoxU8Pending, optBoxU8At]
    refine Entails.trans (by bi_entail :
      (a ↦₆₄ x22) ∗ ((a + 8#64) ↦₆₄ w96) ∗ ⌜x22 = 0#64⌝ ⊢
        ⌜x22 = 0#64⌝ ∗ ((a ↦₆₄ x22) ∗ ((a + 8#64) ↦₆₄ w96))) ?_
    exact Entails.pure_left fun hx22 => hx22 ▸
      sepConj_mono_right (pointsTo64_entails_memRegion (a + 8#64) w96)
  | some bs =>
    dsimp only [optBoxU8Pending, optBoxU8At]
    rw [boxU8At_eq_boxU8Buf]
    generalize boxU8Buf A x22 bs = B
    refine Entails.trans (by bi_entail :
      (a ↦₆₄ x22) ∗ ((a + 8#64) ↦₆₄ w96) ∗ (⌜w96 = BitVec.ofNat 64 bs.length⌝ ∗ B) ⊢
        ⌜w96 = BitVec.ofNat 64 bs.length⌝ ∗ ((a ↦₆₄ x22) ∗ ((a + 8#64) ↦₆₄ w96) ∗ B)) ?_
    exact Entails.pure_left fun hw96 => hw96 ▸ Entails.refl _

theorem memRegion32_entails_pkLayoutAt (a : BitVec 64) :
    memRegion a 32 ⊢
      ∃∗ b0 : BitVec 8, ∃∗ b1 : BitVec 8, ∃∗ b2 : BitVec 8, ∃∗ b3 : BitVec 8,
      ∃∗ b4 : BitVec 8, ∃∗ b5 : BitVec 8, ∃∗ b6 : BitVec 8, ∃∗ b7 : BitVec 8,
      ∃∗ b8 : BitVec 8, ∃∗ w9 : BitVec 32, ∃∗ w13 : BitVec 16,
      ∃∗ w15 : BitVec 64, ∃∗ w23 : BitVec 64, ∃∗ b31 : BitVec 8,
        pkLayoutAt a b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 := by
  simp only [pkLayoutAt, sevenBytesHeadAt, pointsTo32_append4, pkRestAt]
  sep_interval

theorem post_memRegion_one_entails (a : BitVec 64) :
    memRegion a 1 ⊢ ∃∗ b : BitVec 8, a ↦₈ b := by
  sep_interval

theorem memRegion104_unpack_x19 (x19 : BitVec 64) :
    memRegion (x19 + 16#64) 104 ⊢
      ∃∗ w16 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ w32 : BitVec 64,
      ∃∗ w40 : BitVec 64, ∃∗ w48 : BitVec 64,
      ∃∗ c0 : BitVec 8, ∃∗ c1 : BitVec 8, ∃∗ c2 : BitVec 8, ∃∗ c3 : BitVec 8,
      ∃∗ c4 : BitVec 8, ∃∗ c5 : BitVec 8, ∃∗ c6 : BitVec 8, ∃∗ c7 : BitVec 8,
      ∃∗ c8 : BitVec 8, ∃∗ cw9 : BitVec 32, ∃∗ cw13 : BitVec 16,
      ∃∗ cw15 : BitVec 64, ∃∗ cw23 : BitVec 64, ∃∗ cb31 : BitVec 8,
      ∃∗ w88 : BitVec 64, ∃∗ w96 : BitVec 64,
      ∃∗ w104 : BitVec 32, ∃∗ w108 : BitVec 32, ∃∗ b112 : BitVec 8,
        ((x19 + 16#64) ↦₆₄ w16) ∗ ((x19 + 24#64) ↦₆₄ w24) ∗
        ((x19 + 32#64) ↦₆₄ w32) ∗ ((x19 + 40#64) ↦₆₄ w40) ∗
        ((x19 + 48#64) ↦₆₄ w48) ∗
        pkLayoutAt (x19 + 56#64) c0 c1 c2 c3 c4 c5 c6 c7 c8 cw9 cw13 cw15 cw23 cb31 ∗
        ((x19 + 88#64) ↦₆₄ w88) ∗ ((x19 + 96#64) ↦₆₄ w96) ∗
        ((x19 + 104#64) ↦₃₂ w104) ∗ ((x19 + 108#64) ↦₃₂ w108) ∗
        ((x19 + 112#64) ↦₈ b112) ∗ memRegion (x19 + 113#64) 7 := by
  simp only [pkLayoutAt, sevenBytesHeadAt, pointsTo32_append4, pkRestAt]
  sep_interval

theorem msgResultAt_ok_intro (A : RustAlloc) (x19 pqCap' pqPtr' ctBoxPtr serBoxPtr adBoxPtr w96 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8) (w9 : BitVec 32) (w13 : BitVec 16)
    (w15 w23 : BitVec 64) (b31 : BitVec 8)
    (msg : SignalMessage) {out : Except SignalProtocolError SignalMessage} (hout : out = .ok msg)
    (hbnd : macLength + 1 ≤ msg.serialized.length ∧ msg.serialized.length < 2 ^ 40 ∧
      msg.ciphertext.length < 2 ^ 40 ∧ msg.pqRatchet.length < 2 ^ 40 ∧
      (∀ ad, msg.addresses = some ad → ad.length < 2 ^ 40))
    (hpk : msg.senderRatchetKey.bytes.toList =
      pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31) :
    (x19 ↦₆₄ pqCap') ∗ ((x19 + 8#64) ↦₆₄ pqPtr') ∗
      ((x19 + 16#64) ↦₆₄ BitVec.ofNat 64 msg.pqRatchet.length) ∗
      vecU8Buf A pqCap' pqPtr' msg.pqRatchet ∗
      ((x19 + 24#64) ↦₆₄ ctBoxPtr) ∗
      ((x19 + 32#64) ↦₆₄ BitVec.ofNat 64 msg.ciphertext.length) ∗
      boxU8Buf A ctBoxPtr msg.ciphertext ∗
      ((x19 + 40#64) ↦₆₄ serBoxPtr) ∗
      ((x19 + 48#64) ↦₆₄ BitVec.ofNat 64 msg.serialized.length) ∗
      boxU8Buf A serBoxPtr msg.serialized ∗
      pkLayoutAt (x19 + 56#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 ∗
      ((x19 + 88#64) ↦₆₄ adBoxPtr) ∗ ((x19 + 96#64) ↦₆₄ w96) ∗
      optBoxU8Pending A adBoxPtr w96 msg.addresses ∗
      ((x19 + 104#64) ↦₃₂ msg.counter) ∗ ((x19 + 108#64) ↦₃₂ msg.previousCounter) ∗
      ((x19 + 112#64) ↦₈ msg.messageVersion) ∗ memRegion (x19 + 113#64) 7 ⊢
      signalMessageResultAt A [] x19 out := by
  subst hout
  dsimp only [signalMessageResultAt]
  refine Entails.trans ?_
    (Entails.sepExists_intro (⟨pqCap', pqPtr', ctBoxPtr, serBoxPtr, adBoxPtr⟩ : SignalMessageGhost))
  dsimp only [signalMessageAt]
  rw [pure_true_emp hbnd, emp_sepConj, hpk, ← pkLayoutAt_eq_pointsToBytes]
  have had := optBoxU8At_of_pending A (x19 + 88#64) adBoxPtr w96 msg.addresses
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at had
  rw [vecU8At_eq_header_buf A x19, boxU8At_eq_boxU8Buf A (x19 + 0x18#64),
    boxU8At_eq_boxU8Buf A (x19 + 0x28#64)]
  dsimp only [vecHeader]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  generalize vecU8Buf A pqCap' pqPtr' msg.pqRatchet = Vpq
  generalize boxU8Buf A ctBoxPtr msg.ciphertext = Bct
  generalize boxU8Buf A serBoxPtr msg.serialized = Bser
  generalize pkLayoutAt (x19 + 56#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 = PK
  generalize optBoxU8Pending A adBoxPtr w96 msg.addresses = Pad at had ⊢
  generalize optBoxU8At A (x19 + 88#64) adBoxPtr msg.addresses = Oad at had ⊢
  exact Entails.trans (by sep_accu) (Entails.trans (sepConj_mono_left had) (by sep_interval))

@[local arm64_norm]
theorem zeroExtend32_lsr4_truncate8 (b_ver : BitVec 8) :
    ((b_ver.zeroExtend 32 : BitVec 32) >>> 4).truncate 8 = b_ver >>> 4 := by
  bv_kernel

private theorem optVecU8Buf_none (A : RustAlloc) (cap ptr len : BitVec 64) :
    optVecU8Buf A cap ptr len none = ⌜cap = noneCap⌝ := rfl

private theorem optVecU8Buf_some (A : RustAlloc) (cap ptr len : BitVec 64) (bs : List (BitVec 8)) :
    optVecU8Buf A cap ptr len (some bs) =
      (⌜len = BitVec.ofNat 64 bs.length⌝ ∗ vecU8Buf A cap ptr bs) := rfl

private theorem optBoxU8Pending_none (A : RustAlloc) (x22 w96 : BitVec 64) :
    optBoxU8Pending A x22 w96 none = ⌜x22 = 0#64⌝ := rfl

private theorem optBoxU8Pending_some (A : RustAlloc) (x22 w96 : BitVec 64) (bs : List (BitVec 8)) :
    optBoxU8Pending A x22 w96 (some bs) =
      (⌜w96 = BitVec.ofNat 64 bs.length⌝ ∗ boxU8Buf A x22 bs) := rfl

section BoxesOpaque
attribute [local irreducible] vecU8Buf boxU8Buf optVecU8Buf optBoxU8Pending vecU8At signalMessageResultAt

theorem post_ct_some_boxes_wp_placed [lsmpl : LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hDropSpe : DropSpeOkWPlaced A H)
    (hIntoBox : IntoBoxedSliceOkPlaced A H)
    {s0 s : State}
    {sp' x19 x20 x21 x23 x24 ctCap ctPtr pqCap pqPtr pqLen adCap adPtr adLen w48 w136 w144 w152 : BitVec 64}
    {w60 prevCounter : BitVec 32}
    (ct : List (BitVec 8)) (pqOpt adOpt : Option (List (BitVec 8)))
    (hct_lt : ctCap.toNat < 2 ^ 63)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 0x578#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = addsPState64 ctCap 1#64)
    (hx8 : s.readReg64 .x8 = prevCounter.zeroExtend 64)
    (hx19 : s.readReg64 .x19 = x19) (hx20 : s.readReg64 .x20 = x20)
    (hx21 : s.readReg64 .x21 = x21) (hx22 : s.readReg64 .x22 = adCap)
    (hx23 : s.readReg64 .x23 = x23) (hx24 : s.readReg64 .x24 = x24)
    (hx25 : s.readReg64 .x25 = pqCap) (hx27 : s.readReg64 .x27 = ctCap)
    (hx28 : s.readReg64 .x28 = ctPtr) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x6c0#64) s
      (((sp' + 16#64) ↦₆₄ adLen) ∗
        ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 ct.length) ∗
        ((sp' + 40#64) ↦₆₄ pqLen) ∗
        ((sp' + 48#64) ↦₆₄ w48) ∗
        ((sp' + 60#64) ↦₃₂ w60) ∗
        ((sp' + 88#64) ↦₆₄ adPtr) ∗
        ((sp' + 96#64) ↦₆₄ pqPtr) ∗
        vecHeader (sp' + 136#64) w136 w144 w152 ∗
        ((sp' + 176#64) ↦₆₄ speWord 2) ∗ memRegion (sp' + 184#64) 40 ∗
        vecU8Buf A ctCap ctPtr ct ∗
        optVecU8Buf A pqCap pqPtr pqLen pqOpt ∗
        optVecU8Buf A adCap adPtr adLen adOpt ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf =>
        ∃ pqCap' pqPtr' ctBoxPtr adBoxPtr w96 : BitVec 64,
          PostEpilogueStatePlaced s0 sp' sf ∧
          sf.pc = (blkPl_85).base + 0x6c0#64 ∧
          sf.status = .Running ∧
          sf.readReg64 .x19 = x19 ∧ sf.readReg64 .x20 = x20 ∧
          sf.readReg64 .x21 = x21 ∧ sf.readReg64 .x22 = adBoxPtr ∧
          sf.readReg64 .x23 = x23 ∧ sf.readReg64 .x24 = x24 ∧
          sf.readReg64 .x25 = pqCap' ∧
          sf.readReg64 .x26 = BitVec.ofNat 64 ct.length ∧
          sf.readReg64 .x27 = BitVec.ofNat 64 (pqOpt.getD []).length ∧
          sf.readReg64 .x28 = pqPtr' ∧
          (Pf ⊢ ((sp' + 16#64) ↦₆₄ adLen) ∗
            ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 ct.length) ∗
            ((sp' + 40#64) ↦₆₄ pqLen) ∗
            ((sp' + 48#64) ↦₆₄ ctBoxPtr) ∗
            ((sp' + 60#64) ↦₃₂ prevCounter) ∗
            ((sp' + 88#64) ↦₆₄ adPtr) ∗
            ((sp' + 96#64) ↦₆₄ w96) ∗
            vecHeader (sp' + 136#64) ctCap ctPtr (BitVec.ofNat 64 ct.length) ∗
            memRegion (sp' + 176#64) 48 ∗
            vecU8Buf A pqCap' pqPtr' (pqOpt.getD []) ∗
            boxU8Buf A ctBoxPtr ct ∗
            optBoxU8Pending A adBoxPtr w96 adOpt ∗
            A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hcallSpe := hDropSpe
  have hcallBox := hIntoBox
  clear hDropSpe hIntoBox
  have hct_eq := cap_add1_eq_of_lt hct_lt
  have hpq_ent := optVecU8Buf_pq_to_vecU8Buf A pqCap pqPtr pqLen pqOpt
  dsimp only at hpq_ent
  refine replace_sub hpq_ent ?_
  refine pure_anywhere
    ((if (pqCap + 1#64 == 0#64) then 0#64 else pqLen) = BitVec.ofNat 64 (pqOpt.getD []).length)
    fun hpq_len => ?_
  clear hpq_ent
  have hstackSpe := stackAt_sub_split sp' dropSpeStackX (skipFieldStackX 100)
  have hstackBox := stackAt_sub_split sp' intoBoxedSliceStackX (skipFieldStackX 100)
  generalize skipFieldStackX 100 = nStk at hstackSpe hstackBox ⊢
  refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ dropSpeName) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl1
  have hspe_eq : speAt A [] (sp' + 176#64) .invalidProtobufEncoding =
      ((sp' + 176#64) ↦₆₄ speWord 2) ∗ memRegion (sp' + 184#64) 40 := by
    dsimp only [speAt]
    have ha : sp' + 176#64 + 8#64 = sp' + 184#64 := by bv_omega
    rw [ha]
  refine SepWPp.call_noPanic_tryFrom_placed (⟨sp' + 176#64, [], .invalidProtobufEncoding⟩ : DropSpeGhost) hcallSpe
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp) hcl1
    (ret_pc := (blkPl_85).base + bv% (1416)) (by simp [arm64_norm])
    (T := speAt A [] (sp' + 176#64) .invalidProtobufEncoding ∗ A.pool ∗ stackAt s.sp dropSpeStackX)
    (φ := sp' + 176#64 = sp' + 176#64)
    (by simp [dropSpeSpecX, hsp_eq, arm64_norm])
    rfl
    (by rw [hspe_eq, hstackSpe, hsp_eq]; sep_focus)
    ?_
  clear hcallSpe
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [dropSpeSpecX]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre (fun htr2 => ?_)
  rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, hx22_cs, hx23_cs, hx24_cs, hx25_cs, _, hx27_cs, hx28_cs, _⟩
  have hsp2_eq : s2.sp = sp' := by simp [hsp2, hsp_eq, arm64_norm]
  have htr2_eq : s2.trace = s0.trace := by simp [htr2, htr, arm64_norm]
  have hx19_2 : s2.readReg64 .x19 = x19 := by simp [hx19_cs, hx19, arm64_norm]
  have hx20_2 : s2.readReg64 .x20 = x20 := by simp [hx20_cs, hx20, arm64_norm]
  have hx21_2 : s2.readReg64 .x21 = x21 := by simp [hx21_cs, hx21, arm64_norm]
  have hx22_2 : s2.readReg64 .x22 = adCap := by simp [hx22_cs, hx22, arm64_norm]
  have hx23_2 : s2.readReg64 .x23 = x23 := by simp [hx23_cs, hx23, arm64_norm]
  have hx24_2 : s2.readReg64 .x24 = x24 := by simp [hx24_cs, hx24, arm64_norm]
  have hx25_2 : s2.readReg64 .x25 = pqCap := by simp [hx25_cs, hx25, arm64_norm]
  have hx27_2 : s2.readReg64 .x27 = ctCap := by simp [hx27_cs, hx27, arm64_norm]
  have hx28_2 : s2.readReg64 .x28 = ctPtr := by simp [hx28_cs, hx28, arm64_norm]
  refine replace_sub (entails_of_eq hstackSpe.symm) ?_
    (hframe := by
      conv_lhs => simp only [hsp_eq, arm64_norm]
      sep_accu)
  dsimp only [vecHeader]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_placed hcl2 (mid := (blkPl_85).ρ intoBoxedSliceName) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hcl3
  have hvec_ct : vecU8At A (sp' + 136#64) ctCap ctPtr ct =
      ((sp' + 136#64) ↦₆₄ ctCap) ∗ ((sp' + 144#64) ↦₆₄ ctPtr) ∗
        ((sp' + 152#64) ↦₆₄ BitVec.ofNat 64 ct.length) ∗ vecU8Buf A ctCap ctPtr ct := by
    rw [vecU8At_eq_header_buf]
    dsimp only [vecHeader]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.call_tryFrom_placed (⟨sp' + 136#64, ctCap, ctPtr, ct⟩ : VecArg) hcallBox
    (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp2_align) hcl3
    (ret_pc := (blkPl_85).base + bv% (1436)) (by simp [arm64_norm])
    (by simp [htr2_eq, arm64_norm])
    (T := vecU8At A (sp' + 136#64) ctCap ctPtr ct ∗ A.pool ∗ stackAt s2.sp intoBoxedSliceStackX)
    (φ := sp' + 136#64 = sp' + 136#64)
    (by simp [intoBoxedSliceSpecX, VecArg.at, hsp2_eq, arm64_norm])
    rfl
    (by rw [hvec_ct, hstackBox, hsp2_eq]; sep_focus)
    ?_
  intro s4 hpc4 hrun4 hsp4 hsp4_align hcl4 hcs4
  dsimp only [intoBoxedSliceSpecX]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre (fun ⟨hx1_4, htr4⟩ => ?_)
  rcases hcs4 with ⟨hx19_4cs, hx20_4cs, hx21_4cs, hx22_4cs, hx23_4cs, hx24_4cs, hx25_4cs, _⟩
  have hsp4_eq : s4.sp = sp' := by simp [hsp4, hsp2_eq, arm64_norm]
  have htr4_eq : s4.trace = s0.trace := by simp [htr4, htr2_eq, arm64_norm]
  have hx19_4 : s4.readReg64 .x19 = x19 := by simp [hx19_4cs, hx19_2, arm64_norm]
  have hx20_4 : s4.readReg64 .x20 = x20 := by simp [hx20_4cs, hx20_2, arm64_norm]
  have hx21_4 : s4.readReg64 .x21 = x21 := by simp [hx21_4cs, hx21_2, arm64_norm]
  have hx22_4 : s4.readReg64 .x22 = adCap := by simp [hx22_4cs, hx22_2, arm64_norm]
  have hx23_4 : s4.readReg64 .x23 = x23 := by simp [hx23_4cs, hx23_2, arm64_norm]
  have hx24_4 : s4.readReg64 .x24 = x24 := by simp [hx24_4cs, hx24_2, arm64_norm]
  have hx25_4 : s4.readReg64 .x25 = pqCap := by simp [hx25_4cs, hx25_2, arm64_norm]
  cases adOpt with
  | none =>
    clear hcallBox
    refine replace_sub (entails_of_eq hstackBox.symm) ?_
      (hframe := by
        conv_lhs => simp only [hsp2_eq, arm64_norm]
        sep_accu)
    rw [optVecU8Buf_none]
    refine pure_anywhere (adCap = noneCap) fun hadCap => ?_
    subst hadCap
    refine SepWPp.of_sepWP_end_placed hcl4 ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun4, arm64_norm]) ?_
    intro hcl5
    refine ⟨if (pqCap + 1#64 == 0#64) then 0#64 else pqCap,
      if (pqCap + 1#64 != 0#64) then pqPtr else 1#64,
      s4.readReg64 .x0, 0#64, pqPtr,
      PostEpilogueStatePlaced.of_steps hcl5 (by simp [hsp4_eq, arm64_norm]) hsp_eq hsp
        (by simp [noneCap, htr4_eq, arm64_norm]),
      by simp [arm64_norm],
      by simp [hrun4, arm64_norm],
      by simp [hx19_4, arm64_norm],
      by simp [hx20_4, arm64_norm],
      by simp [hx21_4, arm64_norm],
      by simp [arm64_norm],
      by simp [hx23_4, arm64_norm],
      by simp [hx24_4, arm64_norm],
      by simp [arm64_norm],
      by simp [arm64_norm],
      by rw [← hpq_len]; simp [arm64_norm],
      by simp [arm64_norm],
      ?_⟩
    rw [optBoxU8Pending_none, pure_true_emp rfl]
    dsimp only [vecHeader]
    generalize
      vecU8Buf A (if (pqCap + 1#64 == 0#64) then 0#64 else pqCap)
        (if (pqCap + 1#64 != 0#64) then pqPtr else 1#64) (pqOpt.getD []) = Vpq,
      boxU8Buf A _ ct = Bct
    simp only [hstackBox, arm64_norm]
    bi_entail
  | some ad =>
    refine replace_sub (entails_of_eq hstackBox.symm) ?_
      (hframe := by
        conv_lhs => simp only [hsp2_eq, arm64_norm]
        sep_accu)
    rw [optVecU8Buf_some]
    refine replace_sub (post_vecU8Buf_lt A adCap adPtr ad) ?_
    refine pure_anywhere (adLen = BitVec.ofNat 64 ad.length) fun hadLen => ?_
    refine pure_anywhere (adCap.toNat < 2 ^ 63) fun had_lt => ?_
    subst hadLen
    have had_eq := cap_add1_eq_of_lt had_lt
    refine replace_sub (entails_of_eq (post_memRegion48_split24 sp')) ?_
    dsimp only [vecHeader]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_pre fun w176 => ?_
    refine SepWPp.exists_pre fun w184 => ?_
    refine SepWPp.exists_pre fun w192 => ?_
    refine SepWPp.of_sepWP_placed hcl4 (mid := (blkPl_85).ρ intoBoxedSliceName) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun4, arm64_norm]) ?_
    intro hcl5
    have hvec_ad : vecU8At A (sp' + 176#64) adCap adPtr ad =
        ((sp' + 176#64) ↦₆₄ adCap) ∗ ((sp' + 184#64) ↦₆₄ adPtr) ∗
          ((sp' + 192#64) ↦₆₄ BitVec.ofNat 64 ad.length) ∗ vecU8Buf A adCap adPtr ad := by
      rw [vecU8At_eq_header_buf]
      dsimp only [vecHeader]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine SepWPp.call_tryFrom_placed (⟨sp' + 176#64, adCap, adPtr, ad⟩ : VecArg) hcallBox
      (by simp [arm64_norm]) (by simp [hrun4, arm64_norm])
      (by simpa [State.spAligned, arm64_norm] using hsp4_align) hcl5
      (ret_pc := (blkPl_85).base + bv% (1500)) (by simp [arm64_norm])
      (by simp [htr4_eq, arm64_norm])
      (T := vecU8At A (sp' + 176#64) adCap adPtr ad ∗ A.pool ∗ stackAt s4.sp intoBoxedSliceStackX)
      (φ := sp' + 176#64 = sp' + 176#64)
      (by simp [intoBoxedSliceSpecX, VecArg.at, hsp4_eq, arm64_norm])
      rfl
      (by rw [hvec_ad, hstackBox, hsp4_eq]; sep_focus)
      ?_
    clear hcallBox
    intro s6 hpc6 hrun6 hsp6 hsp6_align hcl6 hcs6
    dsimp only [intoBoxedSliceSpecX]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun ⟨hx1_6, htr6⟩ => ?_)
    rcases hcs6 with ⟨hx19_6cs, hx20_6cs, hx21_6cs, _, hx23_6cs, hx24_6cs, hx25_6cs, hx26_6cs, hx27_6cs, hx28_6cs, _⟩
    have hsp6_eq : s6.sp = sp' := by simp [hsp6, hsp4_eq, arm64_norm]
    have htr6_eq : s6.trace = s0.trace := by simp [htr6, htr4_eq, arm64_norm]
    have hx19_6 : s6.readReg64 .x19 = x19 := by simp [hx19_6cs, hx19_4, arm64_norm]
    have hx20_6 : s6.readReg64 .x20 = x20 := by simp [hx20_6cs, hx20_4, arm64_norm]
    have hx21_6 : s6.readReg64 .x21 = x21 := by simp [hx21_6cs, hx21_4, arm64_norm]
    have hx23_6 : s6.readReg64 .x23 = x23 := by simp [hx23_6cs, hx23_4, arm64_norm]
    have hx24_6 : s6.readReg64 .x24 = x24 := by simp [hx24_6cs, hx24_4, arm64_norm]
    have hx25_6 : s6.readReg64 .x25 = if (pqCap + 1#64 == 0#64) then 0#64 else pqCap := by
      simp [hx25_6cs, arm64_norm]
    have hx26_6 : s6.readReg64 .x26 = BitVec.ofNat 64 ct.length := by
      simp [hx26_6cs, arm64_norm]
    have hx27_6 : s6.readReg64 .x27 = BitVec.ofNat 64 (pqOpt.getD []).length := by
      simp [hx27_6cs, arm64_norm]
    have hx28_6 : s6.readReg64 .x28 = if (pqCap + 1#64 != 0#64) then pqPtr else 1#64 := by
      simp [hx28_6cs, arm64_norm]
    refine SepWPp.of_sepWP_end_placed hcl6 ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun6, arm64_norm]) ?_
    intro hcl7
    refine ⟨if (pqCap + 1#64 == 0#64) then 0#64 else pqCap,
      if (pqCap + 1#64 != 0#64) then pqPtr else 1#64,
      s4.readReg64 .x0, s6.readReg64 .x0, s6.readReg64 .x1,
      PostEpilogueStatePlaced.of_steps hcl7 (by simp [hsp6_eq, arm64_norm]) hsp_eq hsp
        (by simp [htr6_eq, arm64_norm]),
      by simp [arm64_norm],
      by simp [hrun6, arm64_norm],
      by simp [hx19_6, arm64_norm],
      by simp [hx20_6, arm64_norm],
      by simp [hx21_6, arm64_norm],
      by simp [arm64_norm],
      by simp [hx23_6, arm64_norm],
      by simp [hx24_6, arm64_norm],
      by simp [hx25_6, arm64_norm],
      by simp [hx26_6, arm64_norm],
      by simp [hx27_6, arm64_norm],
      by simp [hx28_6, arm64_norm],
      ?_⟩
    have h48 := vecHeader_memRegion24_entails_48 sp' adCap adPtr (BitVec.ofNat 64 ad.length)
    dsimp only [vecHeader] at h48
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h48
    rw [optBoxU8Pending_some, pure_true_emp hx1_6]
    dsimp only [vecHeader]
    have hx1_6' : s6.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 ad.length := hx1_6
    generalize
      vecU8Buf A (if (pqCap + 1#64 == 0#64) then 0#64 else pqCap)
        (if (pqCap + 1#64 != 0#64) then pqPtr else 1#64) (pqOpt.getD []) = Vpq,
      boxU8Buf A _ ct = Bct,
      boxU8Buf A _ ad = Bad
    simp only [hx1_6', hsp4_eq, hstackBox, arm64_norm]
    exact Entails.trans (by bi_frame) (Entails.trans (sepConj_mono_left h48) (by bi_entail))

theorem post_pack_msg_wp_placed [lsmpl : LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    {s0 s : State}
    {sp' x19 pqCap' pqPtr' ctBoxPtr serBoxPtr adBoxPtr w96 rkCap rkPtr w0 w1 : BitVec 64}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 b_ver : BitVec 8}
    {w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64}
    (rk : List (BitVec 8))
    (msg : SignalMessage) {out : Except SignalProtocolError SignalMessage} (hout : out = .ok msg)
    (hbnd : macLength + 1 ≤ msg.serialized.length ∧ msg.serialized.length < 2 ^ 40 ∧
      msg.ciphertext.length < 2 ^ 40 ∧ msg.pqRatchet.length < 2 ^ 40 ∧
      (∀ ad, msg.addresses = some ad → ad.length < 2 ^ 40))
    (hpk : msg.senderRatchetKey.bytes.toList =
      pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31)
    (hver : b_ver >>> 4 = msg.messageVersion)
    (hser : serBoxPtr ≠ 0#64)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 0x6cc#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = serBoxPtr)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 msg.serialized.length)
    (hx19 : s.readReg64 .x19 = x19)
    (hx22 : s.readReg64 .x22 = adBoxPtr)
    (hx23 : s.readReg64 .x23 = b_ver.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = b7.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = pqCap')
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 msg.ciphertext.length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 msg.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = pqPtr') :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s
      (((sp' + 12#64) ↦₃₂ b8.zeroExtend 32) ∗
        ((sp' + 28#64) ↦₃₂ msg.counter) ∗
        ((sp' + 48#64) ↦₆₄ ctBoxPtr) ∗
        ((sp' + 60#64) ↦₃₂ msg.previousCounter) ∗
        ((sp' + 64#64) ↦₆₄ w15) ∗
        ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
        ((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w23) ∗
        ((sp' + 112#64) ↦₈ b31) ∗
        ((sp' + 120#64) ↦₃₂ w9) ∗ ((sp' + 124#64) ↦₁₆ w13) ∗
        sevenBytesHeadAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6 ∗
        (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ memRegion (x19 + 16#64) 104 ∗
        vecU8Buf A rkCap rkPtr rk ∗
        vecU8Buf A pqCap' pqPtr' msg.pqRatchet ∗
        boxU8Buf A ctBoxPtr msg.ciphertext ∗
        boxU8Buf A serBoxPtr msg.serialized ∗
        optBoxU8Pending A adBoxPtr w96 msg.addresses ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ ((sp' + 12#64) ↦₃₂ b8.zeroExtend 32) ∗
          ((sp' + 28#64) ↦₃₂ msg.counter) ∗
          ((sp' + 48#64) ↦₆₄ ctBoxPtr) ∗
          ((sp' + 60#64) ↦₃₂ msg.previousCounter) ∗
          ((sp' + 64#64) ↦₆₄ w15) ∗
          ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
          ((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w23) ∗
          ((sp' + 112#64) ↦₈ b31) ∗
          ((sp' + 120#64) ↦₃₂ w9) ∗ ((sp' + 124#64) ↦₁₆ w13) ∗
          sevenBytesHeadAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6 ∗
          signalMessageResultAt A [] x19 out ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hnext := fun {s} => @cleanup_698_wp_placed lsmpl A H hS s0 s sp' rkPtr rkCap
  have h56_head := sevenBytesHeadAt_eq_tailAt (x19 + 56#64) b0 b1 b2 b3 b4 b5 b6
  dsimp only [sevenBytesTailAt] at h56_head
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h56_head
  have hmsg := msgResultAt_ok_intro A x19 pqCap' pqPtr' ctBoxPtr serBoxPtr adBoxPtr w96
    b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 msg hout hbnd hpk
  dsimp only [pkLayoutAt] at hmsg
  rw [h56_head] at hmsg
  dsimp only [pkRestAt] at hmsg
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmsg
  generalize skipFieldStackX 100 = nStk,
    vecU8Buf A pqCap' pqPtr' msg.pqRatchet = Vpq,
    boxU8Buf A ctBoxPtr msg.ciphertext = Bct,
    boxU8Buf A serBoxPtr msg.serialized = Bser,
    optBoxU8Pending A adBoxPtr w96 msg.addresses = Pad,
    signalMessageResultAt A [] x19 out = resOut at hnext hmsg ⊢
  generalize hrk_buf : vecU8Buf A rkCap rkPtr rk = Vrk
  refine replace_sub (memRegion104_unpack_x19 x19) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun w16 => ?_
  refine SepWPp.exists_pre fun w24 => ?_
  refine SepWPp.exists_pre fun w32 => ?_
  refine SepWPp.exists_pre fun w40 => ?_
  refine SepWPp.exists_pre fun w48 => ?_
  refine SepWPp.exists_pre fun c0 => ?_
  refine SepWPp.exists_pre fun c1 => ?_
  refine SepWPp.exists_pre fun c2 => ?_
  refine SepWPp.exists_pre fun c3 => ?_
  refine SepWPp.exists_pre fun c4 => ?_
  refine SepWPp.exists_pre fun c5 => ?_
  refine SepWPp.exists_pre fun c6 => ?_
  refine SepWPp.exists_pre fun c7 => ?_
  refine SepWPp.exists_pre fun c8 => ?_
  refine SepWPp.exists_pre fun cw9 => ?_
  refine SepWPp.exists_pre fun cw13 => ?_
  refine SepWPp.exists_pre fun cw15 => ?_
  refine SepWPp.exists_pre fun cw23 => ?_
  refine SepWPp.exists_pre fun cb31 => ?_
  refine SepWPp.exists_pre fun w88 => ?_
  refine SepWPp.exists_pre fun w96_old => ?_
  refine SepWPp.exists_pre fun w104 => ?_
  refine SepWPp.exists_pre fun w108 => ?_
  refine SepWPp.exists_pre fun b112 => ?_
  dsimp only [sevenBytesHeadAt, pkLayoutAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + bv% (1748)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl1
  have h128_tail :
      ((sp' + 128#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ ((sp' + 132#64) ↦₈ b4) ∗
        ((sp' + 133#64) ↦₈ b5) ∗ ((sp' + 134#64) ↦₈ b6) ⊢
        sevenBytesTailAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6 := by
    have h := sevenBytesHeadAt_eq_tailAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6
    dsimp only [sevenBytesHeadAt] at h
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
    exact entails_of_eq h
  refine replace_sub h128_tail ?_
  dsimp only [sevenBytesTailAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_placed hcl1 (mid := (blkPl_85).base + bv% (1776)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl2
  have h56_tail :
      ((x19 + 56#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ ((x19 + 60#64) ↦₈ c4) ∗
        ((x19 + 61#64) ↦₈ c5) ∗ ((x19 + 62#64) ↦₈ c6) ⊢
        sevenBytesTailAt (x19 + 56#64) b0 b1 b2 b3 c4 c5 c6 := by
    have h := sevenBytesHeadAt_eq_tailAt (x19 + 56#64) b0 b1 b2 b3 c4 c5 c6
    dsimp only [sevenBytesHeadAt] at h
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
    exact entails_of_eq h
  have h128_head :
      ((sp' + 128#64) ↦₈ b0) ∗ ((sp' + 129#64) ↦₈ b1) ∗ ((sp' + 130#64) ↦₈ b2) ∗
        ((sp' + 131#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ⊢
        sevenBytesHeadAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6 := by
    have h := (sevenBytesHeadAt_eq_tailAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6).symm
    dsimp only [sevenBytesTailAt] at h
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
    exact entails_of_eq h
  refine replace_sub h56_tail ?_
  refine replace_sub h128_head ?_
  dsimp only [sevenBytesTailAt, pkRestAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_placed hcl2 (mid := (blkPl_85).base + bv% (1860)) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl3
  refine replace_sub hmsg ?_
  subst hrk_buf
  by_cases hcap : rkCap = 0#64
  · clear hnext
    subst hcap
    refine replace_sub (entails_of_eq (vecU8Buf_zero A rkPtr rk)) ?_
    refine pure_anywhere (rk = [] ∧ rkPtr ≠ 0) fun _ => ?_
    refine SepWPp.of_sepWP_end_placed hcl3 ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hcl4
    refine ⟨PostEpilogueStatePlaced.of_steps hcl4 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]),
      ?_⟩
    dsimp only [sevenBytesHeadAt]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    bi_entail
  · refine replace_sub (vecU8Buf_dealloc A rkCap rkPtr rk hcap) ?_
    refine pure_anywhere (0 < rkCap.toNat ∧ rkCap.toNat < 2 ^ 63 ∧ rkPtr ≠ 0)
      fun ⟨hpos, hlt, hptr⟩ => ?_
    refine SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_85).base + bv% (1688)) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hcl4
    refine frame_post
      (hnext
        (PostEpilogueStatePlaced.of_steps hcl4 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm])
        hpos hlt hptr)
      (by dsimp only [sevenBytesHeadAt]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; bi_frame)
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, Entails.trans (sepConj_mono_left hent) (by bi_entail)⟩

theorem post_clone_and_pack_wp_placed [lsmpl : LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hTryClone : TryCloneFromRefOkPlaced A H)
    {s0 s : State}
    {sp' x19 x21 pqCap' pqPtr' ctBoxPtr adBoxPtr w96 rkCap rkPtr w0 w1 : BitVec 64}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 b_ver : BitVec 8}
    {w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64}
    (rk : List (BitVec 8))
    (msg : SignalMessage) {out : Except SignalProtocolError SignalMessage} (hout : out = .ok msg)
    (hbnd : macLength + 1 ≤ msg.serialized.length ∧ msg.serialized.length < 2 ^ 40 ∧
      msg.ciphertext.length < 2 ^ 40 ∧ msg.pqRatchet.length < 2 ^ 40 ∧
      (∀ ad, msg.addresses = some ad → ad.length < 2 ^ 40))
    (hpk : msg.senderRatchetKey.bytes.toList =
      pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31)
    (hver : b_ver >>> 4 = msg.messageVersion)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_85).base + 0x6c0#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x19)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 msg.serialized.length)
    (hx21 : s.readReg64 .x21 = x21)
    (hx22 : s.readReg64 .x22 = adBoxPtr)
    (hx23 : s.readReg64 .x23 = b_ver.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = b7.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = pqCap')
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 msg.ciphertext.length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 msg.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = pqPtr') :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s
      ((x21 ↦ₛ msg.serialized) ∗
        ((sp' + 12#64) ↦₃₂ b8.zeroExtend 32) ∗
        ((sp' + 28#64) ↦₃₂ msg.counter) ∗
        ((sp' + 48#64) ↦₆₄ ctBoxPtr) ∗
        ((sp' + 60#64) ↦₃₂ msg.previousCounter) ∗
        ((sp' + 64#64) ↦₆₄ w15) ∗
        ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
        ((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w23) ∗
        ((sp' + 112#64) ↦₈ b31) ∗
        ((sp' + 120#64) ↦₃₂ w9) ∗ ((sp' + 124#64) ↦₁₆ w13) ∗
        sevenBytesHeadAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6 ∗
        (x19 ↦₆₄ w0) ∗ ((x19 + 8#64) ↦₆₄ w1) ∗ memRegion (x19 + 16#64) 104 ∗
        vecU8Buf A rkCap rkPtr rk ∗
        vecU8Buf A pqCap' pqPtr' msg.pqRatchet ∗
        boxU8Buf A ctBoxPtr msg.ciphertext ∗
        optBoxU8Pending A adBoxPtr w96 msg.addresses ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ (x21 ↦ₛ msg.serialized) ∗
          ((sp' + 12#64) ↦₃₂ b8.zeroExtend 32) ∗
          ((sp' + 28#64) ↦₃₂ msg.counter) ∗
          ((sp' + 48#64) ↦₆₄ ctBoxPtr) ∗
          ((sp' + 60#64) ↦₃₂ msg.previousCounter) ∗
          ((sp' + 64#64) ↦₆₄ w15) ∗
          ((sp' + 72#64) ↦₆₄ rkPtr) ∗ ((sp' + 80#64) ↦₆₄ rkCap) ∗
          ((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w23) ∗
          ((sp' + 112#64) ↦₈ b31) ∗
          ((sp' + 120#64) ↦₃₂ w9) ∗ ((sp' + 124#64) ↦₁₆ w13) ∗
          sevenBytesHeadAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6 ∗
          signalMessageResultAt A [] x19 out ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hcallClone := hTryClone
  clear hTryClone
  have hpack := fun {s serBoxPtr} =>
    @post_pack_msg_wp_placed lsmpl A H hS s0 s sp' x19 pqCap' pqPtr' ctBoxPtr serBoxPtr adBoxPtr
      w96 rkCap rkPtr w0 w1 b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 b_ver w9 w13 w15 w23 rk msg out
      hout hbnd hpk hver
  have hpan := panic_at_handle_alloc_error2_placed hS.alloc.panic_alloc
  have hser_lt40 : msg.serialized.length < 2 ^ 40 := hbnd.2.1
  have hser_toNat : (BitVec.ofNat 64 msg.serialized.length).toNat = msg.serialized.length :=
    Nat.mod_eq_of_lt (by omega)
  have hser_le63 : msg.serialized.length + 1 ≤ 2 ^ 63 := by omega
  have hstackClone := stackAt_sub_split sp' tryCloneFromRefStackX (skipFieldStackX 100)
  generalize skipFieldStackX 100 = nStk,
    sevenBytesHeadAt (sp' + 128#64) b0 b1 b2 b3 b4 b5 b6 = SB7,
    vecU8Buf A rkCap rkPtr rk = Vrk,
    vecU8Buf A pqCap' pqPtr' msg.pqRatchet = Vpq,
    boxU8Buf A ctBoxPtr msg.ciphertext = Bct,
    optBoxU8Pending A adBoxPtr w96 msg.addresses = Pad,
    signalMessageResultAt A [] x19 out = resOut at hpack hstackClone ⊢
  refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ tryCloneFromRefName) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hcl1
  refine SepWPp.call_noPanic_tryFrom_placed (⟨x21, msg.serialized⟩ : TryCloneSliceCall) hcallClone
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp) hcl1
    (ret_pc := (blkPl_85).base + bv% (1740)) (by simp [arm64_norm])
    (T := (x21 ↦ₛ msg.serialized) ∗ A.pool ∗ stackAt s.sp tryCloneFromRefStackX)
    (φ := x21 = x21 ∧ (BitVec.ofNat 64 msg.serialized.length).toNat = msg.serialized.length ∧
      msg.serialized.length + 1 ≤ 2 ^ 63)
    (by simp [tryCloneFromRefSpecX, hsp_eq, arm64_norm])
    ⟨rfl, hser_toNat, hser_le63⟩
    (by rw [hstackClone, hsp_eq]; sep_focus)
    ?_
  clear hcallClone
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [tryCloneFromRefSpecX]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun hx1_2 => ?_
  rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, hx22_cs, hx23_cs, hx24_cs, hx25_cs, hx26_cs, hx27_cs, hx28_cs, _⟩
  have hsp2_eq : s2.sp = sp' := by simp [hsp2, hsp_eq, arm64_norm]
  have hx19_2 : s2.readReg64 .x19 = x19 := by simp [hx19_cs, hx19, arm64_norm]
  have hx22_2 : s2.readReg64 .x22 = adBoxPtr := by simp [hx22_cs, hx22, arm64_norm]
  have hx23_2 : s2.readReg64 .x23 = b_ver.zeroExtend 64 := by simp [hx23_cs, hx23, arm64_norm]
  have hx24_2 : s2.readReg64 .x24 = b7.zeroExtend 64 := by simp [hx24_cs, hx24, arm64_norm]
  have hx25_2 : s2.readReg64 .x25 = pqCap' := by simp [hx25_cs, hx25, arm64_norm]
  have hx26_2 : s2.readReg64 .x26 = BitVec.ofNat 64 msg.ciphertext.length := by
    simp [hx26_cs, hx26, arm64_norm]
  have hx27_2 : s2.readReg64 .x27 = BitVec.ofNat 64 msg.pqRatchet.length := by
    simp [hx27_cs, hx27, arm64_norm]
  have hx28_2 : s2.readReg64 .x28 = pqPtr' := by simp [hx28_cs, hx28, arm64_norm]
  by_cases hoom : s2.readReg64 .x0 = 0#64
  · clear hpack
    simp only [hoom, ite_true, sepConj_assoc]
    rw [← sepConj_assoc, sepConj_comm (x21 ↦ₛ msg.serialized), sepConj_assoc]
    refine SepWPp.pure_pre fun ⟨_, htr2⟩ => ?_
    refine replace_sub (entails_of_eq hstackClone.symm) ?_
      (hframe := by
        conv_lhs => simp only [hsp_eq, arm64_norm]
        sep_accu)
    refine SepWPp.of_sepWP (mid := (blkPl_85).ρ lsAllocHandleErrorSym) ?_
    wp_steps
    refine SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
    refine SepWPp.panic (by simp [hrun2, arm64_norm])
      (by simpa [arm64_norm] using hpan)
      (tryFromQp_of_panicked (by simp [Rust.panicked, htr2, htr, arm64_norm]))
  · clear hpan
    simp only [hoom, ite_false, sepConj_assoc]
    rw [← sepConj_assoc, sepConj_comm (x21 ↦ₛ msg.serialized), sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    refine replace_sub (entails_of_eq hstackClone.symm) ?_
      (hframe := by
        conv_lhs => simp only [hsp_eq, arm64_norm]
        sep_accu)
    have hpack_call := hpack (serBoxPtr := s2.readReg64 .x0) hoom
      ⟨hsp2_eq, hsp2_align, hcl2, by simp [htr2, htr, arm64_norm]⟩
      hpc2 hrun2 rfl hx1_2 hx19_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2
    simp only [arm64_norm] at hpack_call ⊢
    generalize boxU8Buf A _ msg.serialized = Bser at hpack_call ⊢
    exact frame_post hpack_call
      (by bi_frame)
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, Entails.trans (sepConj_mono_left hent) (by bi_entail)⟩

end BoxesOpaque

end CryptoVerification.LibsignalTripleRatchet.Wire
