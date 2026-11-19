/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.Layout -- proof-setup: allow-public-import
import all Init.Data.Repr
import all Init.Data.String.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.SepLogic.WPp

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.AddressText.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
  (vecU8Buf vecU8BufRest vecU8At_eq_header_buf layoutOk_align1)
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession.Cli

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## 1. Call-site `inImage` wrappers (`shim2`, `memcpy2`, `decimalInnerSpec`) -/

@[expose] def decimalInnerSpec (A : RustAlloc) (stk : Nat) : Spec DecimalGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg32 .x1 = x.n⌝ ∗ memRegion x.ret 24 ∗
      stackAt s.sp stk ∗ A.pool
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ vecU8 A x.ret (decimalText x.n.toNat) ∗
      stackAt s0.sp stk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

@[expose] def frameOff : BitVec 64 := 4#64
@[expose] def shimRetOff : BitVec 64 := 76#64
@[expose] def allocRetOff : BitVec 64 := 92#64
@[expose] def memcpy0RetOff : BitVec 64 := 112#64
@[expose] def res0RetOff : BitVec 64 := 144#64
@[expose] def decRetOff : BitVec 64 := 176#64
@[expose] def res1RetOff : BitVec 64 := 332#64
@[expose] def memcpy1RetOff : BitVec 64 := 224#64

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm]
  frameOff shimRetOff allocRetOff memcpy0RetOff res0RetOff decRetOff res1RetOff memcpy1RetOff

@[expose] def Same {α : Type _} (a b : α) : Prop := a = b

theorem same_eq {α : Type _} {a b : α} (h : Same a b) : a = b := h

theorem entails_of_eq {P Q : SepProp} (h : P = Q) : P ⊢ Q :=
  h ▸ Entails.refl _

theorem step_entails {P T T' F Q : SepProp}
    (hent : T ⊢ T') (hf : P = T ∗ F)
    (h : T' ∗ F ⊢ Q) : P ⊢ Q :=
  Entails.trans (hf ▸ sepConj_mono_left hent) h

theorem false_entails (Q : SepProp) : (⌜False⌝ : SepProp) ⊢ Q := by
  rw [← emp_sepConj ⌜False⌝, sepConj_comm]
  exact Entails.pure_left False.elim

theorem onPanic_trace_eq {s0 s sf : State} (htr : s.trace = s0.trace) :
    ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap ⊢
      ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  dsimp only [allocFailedIn]
  rw [htr]
  exact Entails.refl _

theorem decimalText_device_pos :
    ∀ d : BitVec 8, 0 < (decimalText d.toNat).length := by
  decide +kernel

theorem dCap_ne_zero {dCap : BitVec 64} {decLen : Nat}
    (hpos : 0 < decLen) (hle : decLen ≤ dCap.toNat) :
    dCap ≠ 0#64 := by
  intro h
  subst h
  change decLen ≤ 0 at hle
  omega

theorem dCap_beq_zero_false {dCap : BitVec 64} {decLen : Nat}
    (hpos : 0 < decLen) (hle : decLen ≤ dCap.toNat) :
    (dCap == 0#64) = false :=
  beq_false_of_ne (dCap_ne_zero hpos hle)

theorem pure_true_emp {P : Prop} (h : P) : (⌜P⌝ : SepProp) = emp := by
  simp only [h, pure_true]

theorem vecU8Buf_close_slice (A : RustAlloc) (cap ptr : BitVec 64)
    (bs extra : List (BitVec 8))
    (hle : bs.length + extra.length ≤ cap.toNat)
    (hpos : 0 < bs.length + extra.length)
    (h63 : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) :
    A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      ((ptr + BitVec.ofNat 64 bs.length) ↦ₛ extra) ∗
      memRegion (ptr + BitVec.ofNat 64 (bs.length + extra.length))
        (cap.toNat - (bs.length + extra.length)) ⊢
      vecU8Buf A cap ptr (bs ++ extra) := by
  have hne0 : cap ≠ 0 := by
    intro h; subst h; change bs.length + extra.length ≤ 0 at hle; omega
  have hlen : (bs ++ extra).length = bs.length + extra.length := List.length_append
  unfold vecU8Buf
  simp only [hne0, hlen, ↓reduceIte]
  rw [pure_true_emp ⟨hle, h63, hptr⟩, emp_sepConj, pointsToBytes_append]
  apply entails_of_eq
  ac_rfl

theorem sepWPp_weaken_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : P ⊢ P') (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp :=
  fun R hm hL => h R (Satisfies.mono (sepConj_mono_left hent) hm) hL

theorem sepWPp_fold {prog : Program} {ret : BitVec 64} {s : State}
    {P T T' F : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : T ⊢ T') (hf : P = T ∗ F)
    (h : SepWPp prog ret s (T' ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  sepWPp_weaken_pre (hf ▸ sepConj_mono_left hent) h

theorem sepWPp_exists_elim {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {F : α → SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ a : α, SepWPp prog ret s (F a) Q Qp) :
    SepWPp prog ret s (∃∗ a : α, F a) Q Qp := by
  intro R hm hL
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨a, hm⟩
  exact h a R hm hL

@[expose] def preservedTailRegs (s : State) :=
  (s.readReg64 .x25, s.readReg64 .x26, s.readReg64 .x27, s.readReg64 .x28, calleeSavedVRegs s)

theorem preservedTailRegs_mk {s s0 : State}
    (h25 : s.readReg64 .x25 = s0.readReg64 .x25)
    (h26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (h27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (h28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hv : calleeSavedVRegs s = calleeSavedVRegs s0) :
    preservedTailRegs s = preservedTailRegs s0 := by
  simp only [preservedTailRegs, h25, h26, h27, h28, hv]

theorem preservedTailRegs_of_cs {s0 s1 : State} (h : CalleeSavedPreserved s0 s1) :
    preservedTailRegs s1 = preservedTailRegs s0 :=
  preservedTailRegs_mk
    h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.2.2.2.2

theorem preservedTailRegs_elim {s s0 : State} (h : preservedTailRegs s = preservedTailRegs s0) :
    s.readReg64 .x25 = s0.readReg64 .x25 ∧
    s.readReg64 .x26 = s0.readReg64 .x26 ∧
    s.readReg64 .x27 = s0.readReg64 .x27 ∧
    s.readReg64 .x28 = s0.readReg64 .x28 ∧
    calleeSavedVRegs s = calleeSavedVRegs s0 := by
  simpa only [preservedTailRegs, Prod.mk.injEq] using h

theorem preservedTailRegs_step {s0 s1 s2 : State}
    (hcs : CalleeSavedPreserved s1 s2)
    (h25 : s1.readReg64 .x25 = s0.readReg64 .x25)
    (h26 : s1.readReg64 .x26 = s0.readReg64 .x26)
    (h27 : s1.readReg64 .x27 = s0.readReg64 .x27)
    (h28 : s1.readReg64 .x28 = s0.readReg64 .x28)
    (hv : calleeSavedVRegs s1 = calleeSavedVRegs s0) :
    preservedTailRegs s2 = preservedTailRegs s0 :=
  (preservedTailRegs_of_cs hcs).trans (preservedTailRegs_mk h25 h26 h27 h28 hv)

theorem calleeSaved_vregs {s0 s1 : State} (h : CalleeSavedPreserved s0 s1) :
    calleeSavedVRegs s1 = calleeSavedVRegs s0 :=
  h.2.2.2.2.2.2.2.2.2.2.2

theorem calleeSaved_trans {s0 s1 s2 : State}
    (h1 : CalleeSavedPreserved s0 s1) (h2 : CalleeSavedPreserved s1 s2) :
    CalleeSavedPreserved s0 s2 := by
  rcases h1 with ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩
  rcases h2 with ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6,
    b7.trans a7, b8.trans a8, b9.trans a9, b10.trans a10, b11.trans a11, b12.trans a12⟩

end CryptoVerification.SignalSession.Cli.AddressText.Helpers
