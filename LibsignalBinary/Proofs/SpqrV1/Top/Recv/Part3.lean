/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Decodes
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `spqr::recv`: Version Dispatch Exits & `Ordering::Equal` Transition

Version-dispatch cleanup/error exits (`+752`, `+892`, `+912`, `+936`, `+1028`, `+2540`),
`Ordering::Equal` transition (`+792..+820 -> +1532`), and `SepWPpI.call_inImage` for
`spqr::recv` (`0x5462c`).
-/

public section

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Split `memRegion r 48` exposing `(r + 8#64) ↦₈ b8` and `memRegion (r + 9#64) 7` for `strb
    w8, [x19, #0x8]`. -/
theorem ret_48_split_byte8 (r : BitVec 64) :
    memRegion r 48 ⊢
      ∃∗ r0 : BitVec 64, ∃∗ b8 : BitVec 8, ∃∗ r2 : BitVec 64, ∃∗ r3 : BitVec 64,
        (r ↦₆₄ r0) ∗ ((r + 8#64) ↦₈ b8) ∗ memRegion (r + 9#64) 7 ∗
        ((r + 16#64) ↦₆₄ r2) ∗ ((r + 24#64) ↦₆₄ r3) ∗ memRegion (r + 32#64) 16 := by
  rw [ret_48_split r]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro r3
  apply Entails.sepExists_elim; intro r2
  apply Entails.sepExists_elim; intro r1
  apply Entails.sepExists_elim; intro r0
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left (ret8_expose_byte r r1))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro b8
  refine Entails.sepExists_right r0 (Entails.sepExists_right b8
    (Entails.sepExists_right r2 (Entails.sepExists_right r3 ?_)))
  exact Entails.of_eq (by ac_rfl)

theorem cap_ne_zero_one_sle_true {w0 : BitVec 64} (hcap_lt : w0.toNat < 2 ^ 63)
    (hc0 : ¬(w0 == 0#64) = true) :
    (1#64).sle w0 = true := by
  have hne : w0.toNat ≠ 0 := by
    intro h0; apply hc0; rw [beq_iff_eq]; exact BitVec.eq_of_toNat_eq h0
  unfold BitVec.sle BitVec.toInt
  simp only [Nat.reducePow, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reduceMul, ↓reduceIte,
    decide_eq_true_eq]
  split <;> omega

theorem vnHeader_sub4992_entails_memRegion_48 (sp0 w0 w1 : BitVec 64) :
    ((sp0 - 4992#64) ↦₆₄ w0) ∗ ((sp0 - 4984#64) ↦₆₄ w1) ∗ memRegion (sp0 - 4976#64) 32 ⊢
      memRegion (sp0 - 4992#64) 48 := by
  have h8 : (sp0 - 4992#64) + 8#64 = sp0 - 4984#64 := bv_sub_add_lit sp0 4992 8
  have h16 : (sp0 - 4992#64) + 16#64 = sp0 - 4976#64 := bv_sub_add_lit sp0 4992 16
  rw [← h8, ← h16]
  exact vnHeader_entails_memRegion_48 (sp0 - 4992#64) w0 w1

/-- Pinned 352-byte `PqRatchetState` layout keeping the first two words `w0, w1` of
    `versionNegotiation` explicit. -/
@[expose] def pinnedPqRatchetStateAt (H_inner : V1InnerHeapPred) (A : RustAlloc) (w0 w1 : BitVec 64)
    (a : BitVec 64) (st : PqRatchetState) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗
  optVersionNegotiationPBTailAt A w0 w1 (a + 16#64) st.versionNegotiation ∗
  optChainPBAt A (a + 48#64) st.chain ∗
  DecodeState.optProtoPqRatchetInnerAt H_inner A (a + 128#64) st.inner

@[expose] def relocPinnedPqRatchetStateAt (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (w0 w1 : BitVec 64) (st : PqRatchetState) :
    Σ' H, Relocatable (fun a => pinnedPqRatchetStateAt H_inner A w0 w1 a st) 352 H :=
  let h1 := reloc_append 16 8#64 (reloc_pointsTo64 w0) (reloc_pointsTo64 w1) rfl rfl
  let h2 := reloc_append 352 16#64 h1 (relocProtoPqRatchetStateTailAt H_inner A w0 w1 st).2 rfl rfl
  ⟨_, reloc_congr h2 (fun a => by
    unfold pinnedPqRatchetStateAt protoPqRatchetStateTailAt
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc])⟩

theorem optProtoPqRatchetInnerAt_eq_drop {H_inner : V1InnerHeapPred} {A : RustAlloc}
    (h_inner_eq : ∀ a opt, DecodeState.optProtoInnerStateAt H_inner A a opt = Drop.optProtoInnerStateAt A a opt)
    (a : BitVec 64) (opt : Option PqRatchetState.Inner) :
    DecodeState.optProtoPqRatchetInnerAt H_inner A a opt = Drop.optProtoPqRatchetInnerAt A a opt := by
  cases opt with
  | none => rfl
  | some inn =>
    cases inn with
    | v1 v1 => exact h_inner_eq a v1.innerState

theorem allocFailedIn_of_prefix {s0 s sm : State}
    (hpre : s0.trace <+: s.trace)
    (h : allocFailedIn s sm ∧ s.trace <+: sm.trace) :
    allocFailedIn s0 sm ∧ s0.trace <+: sm.trace := by
  have hsub := hpre.trans h.2
  rcases hpre with ⟨t1, ht1⟩
  rcases h with ⟨hmem, t2, ht2⟩
  unfold allocFailedIn at hmem ⊢
  refine ⟨?_, hsub⟩
  have hdrop : sm.trace.drop s.trace.length = t2 := by
    rw [← ht2, List.drop_left]
  have hdrop0 : sm.trace.drop s0.trace.length = t1 ++ t2 := by
    have hsm : sm.trace = s0.trace ++ (t1 ++ t2) := by
      rw [← List.append_assoc, ht1, ht2]
    rw [hsm, List.drop_left]
  rw [hdrop0]
  rw [hdrop] at hmem
  exact List.mem_append_right t1 hmem

theorem panic_prefix_trans {M : SpqrRecvModel} {st msg : VecArg} {s0 s sm : State}
    (hpre : s0.trace <+: s.trace)
    (h : (allocFailedIn s sm ∨ M.recvPanics st.bytes msg.bytes) ∧ s.trace <+: sm.trace) :
    (allocFailedIn s0 sm ∨ M.recvPanics st.bytes msg.bytes) ∧ s0.trace <+: sm.trace := by
  rcases h with ⟨haf | hpan, hsub⟩
  · exact ⟨Or.inl (allocFailedIn_of_prefix hpre ⟨haf, hsub⟩).1, hpre.trans hsub⟩
  · exact ⟨Or.inr hpan, hpre.trans hsub⟩

theorem onPanic_of_allocFailed {M : SpqrRecvModel} {st msg : VecArg} {s sm : State} :
    (⌜allocFailedIn s sm ∧ s.trace <+: sm.trace⌝ ∗ anyHeap : SepProp) ⊢
      ⌜(allocFailedIn s sm ∨ M.recvPanics st.bytes msg.bytes) ∧ s.trace <+: sm.trace⌝ ∗ anyHeap := by
  apply Entails.pure_left; rintro ⟨haf, hsub⟩
  exact Entails.pure_right ⟨Or.inl haf, hsub⟩ (Entails.refl _)

end CryptoVerification.SpqrV1.Top.Recv
