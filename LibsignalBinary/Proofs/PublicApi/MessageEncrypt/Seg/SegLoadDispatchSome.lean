/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegLoadShimPoll -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegLoadDispatch
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.E2E.Record.Support.Repr

/-!
# `segLoad` `Ok(Some r)` Dispatch and Top-Level `segLoad_ok`

Handles the `ans = .ok (some r)` post-poll branches of `session_message_encrypt_with_stores`
(`r.currentSession = some sess` reaching `CurStateV` at `+0x20c`, and `r.currentSession = none`
exiting via `tailFreePrevSessions_ok`) and composes all branches into `segLoad_ok`.
-/

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.RawByteMove CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalPublicApi.MessageEncrypt CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Arithmetic and Frame Helpers for `ans = .ok (some r)` -/

theorem ne_neg2_add2_ne_zero {w0 : BitVec 64} (hne : w0 ≠ 0xFFFFFFFFFFFFFFFE#64) :
    (w0 + 2#64 == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  apply hne
  have h1 : w0 + 2#64 - 2#64 = 0#64 - 2#64 := congrArg (· - 2#64) h
  simpa [BitVec.add_sub_cancel] using h1

theorem ne_neg1_add1_ne_zero {w0 : BitVec 64} (hne : w0 ≠ 0xFFFFFFFFFFFFFFFF#64) :
    (w0 + 1#64 == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  apply hne
  have h1 : w0 + 1#64 - 1#64 = 0#64 - 1#64 := congrArg (· - 1#64) h
  simpa [BitVec.add_sub_cancel] using h1

theorem ne_neg1_add1_bne_zero {w3 : BitVec 64} (hne : w3 ≠ 0xFFFFFFFFFFFFFFFF#64) :
    (w3 + 1#64 != 0#64) = true := by
  rw [bne_iff_ne]
  intro h
  apply hne
  have h1 : w3 + 1#64 - 1#64 = 0#64 - 1#64 := congrArg (· - 1#64) h
  simpa [BitVec.add_sub_cancel] using h1

theorem loadOutRes_some_eq (Scope : SessionRecord (List (BitVec 8)) → Prop) (A : RustAlloc)
    (b : BitVec 64) (r : SessionRecord (List (BitVec 8)))
    (w0 w1 w2 w3 w4 w5 w6 : BitVec 64) (tail : List (BitVec 8)) :
    LoadOutRes Scope A b (.ok (some r)) w0 w1 w2 w3 w4 w5 w6 tail =
      ∃∗ g : RecordGhost,
        ⌜Scope r ∧ g.prevCap.toNat < 2 ^ 63 ∧
          w0 = g.prevCap ∧ w1 = g.prevPtr ∧ w2 = 0#64 ∧ w3 = recordCurCap g ∧
          RecordTailInline g r w4 w5 w6 tail⌝ ∗
          recordHeap A g r := rfl

theorem memRegion_0x110_split_record (sp : BitVec 64) :
    memRegion (sp + 0x110#64) 0x358 =
      cells (sp + 0x110#64) 7 ∗
      memRegion (sp + 0x148#64) 312 ∗
      memRegion (sp + 0x280#64) 0x1e8 := by
  have hc7 : memRegion (sp + 0x110#64) 56 = cells (sp + 0x110#64) 7 :=
    ProofLib.memRegion_cells (sp + 0x110#64) 7 (by decide)
  rw [memRegion_split (sp + 0x110#64) 56 800 (by decide),
      memRegion_split (sp + 0x110#64 + 56#64) 312 0x1e8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [hc7]

theorem recordWords56At_fold_sp110 (sp w0 w1 w2 w3 w4 w5 w6 : BitVec 64) :
    ((sp + 0x110#64) ↦₆₄ w0) ∗ ((sp + 0x118#64) ↦₆₄ w1) ∗
    ((sp + 0x120#64) ↦₆₄ w2) ∗ ((sp + 0x128#64) ↦₆₄ w3) ∗
    ((sp + 0x130#64) ↦₆₄ w4) ∗ ((sp + 0x138#64) ↦₆₄ w5) ∗
    ((sp + 0x140#64) ↦₆₄ w6) ⊢
      recordWords56At (sp + 0x110#64) w0 w1 w2 w3 w4 w5 w6 := by
  unfold recordWords56At
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_0x46a_0x716_fold (sp w4 w5 w6 : BitVec 64) (tail : List (BitVec 8))
    (htail : tail.length = 312) :
    memRegion (sp + 0x46a#64) 0x116 ∗
    memRegion (sp + 0x580#64) 368 ∗
    memRegion (sp + 0x6f0#64) 8 ∗
    ((sp + 0x6f8#64) ↦ₛ tail) ∗
    ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
    ((sp + 0x840#64) ↦₆₄ w6) ∗
    memRegion (sp + 0x848#64) 0x338 ⊢
      memRegion (sp + 0x46a#64) 0x716 := by
  have ht : ((sp + 0x6f8#64) ↦ₛ tail) ⊢ memRegion (sp + 0x6f8#64) 312 := by
    have h := pointsToBytes_entails_memRegion (sp + 0x6f8#64) tail
    rwa [htail] at h
  rw [memRegion_split (sp + 0x46a#64) 0x116 1536 (by decide),
      memRegion_split (sp + 0x46a#64 + 0x116#64) 368 1168 (by decide),
      memRegion_split (sp + 0x46a#64 + 0x116#64 + 368#64) 8 1160 (by decide),
      memRegion_split (sp + 0x46a#64 + 0x116#64 + 368#64 + 8#64) 312 848 (by decide),
      memRegion_split (sp + 0x46a#64 + 0x116#64 + 368#64 + 8#64 + 312#64) 8 840 (by decide),
      memRegion_split (sp + 0x46a#64 + 0x116#64 + 368#64 + 8#64 + 312#64 + 8#64) 8 832 (by decide),
      memRegion_split (sp + 0x46a#64 + 0x116#64 + 368#64 + 8#64 + 312#64 + 8#64 + 8#64) 8 824 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono ht (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)))))))

theorem memRegion_0x848_split_0x9d0_0xb00 (sp : BitVec 64) :
    memRegion (sp + 0x848#64) 0x338 =
      memRegion (sp + 0x848#64) 0x188 ∗
      cells (sp + 0x9d0#64) 3 ∗
      memRegion (sp + 0x9e8#64) 0x118 ∗
      cells (sp + 0xb00#64) 3 ∗
      memRegion (sp + 0xb18#64) 0x68 := by
  rw [memRegion_0x848_split_0x9d0 sp]
  have hc3 : memRegion (sp + 0xb00#64) 24 = cells (sp + 0xb00#64) 3 :=
    ProofLib.memRegion_cells (sp + 0xb00#64) 3 (by decide)
  rw [memRegion_split (sp + 0x9e8#64) 0x118 0x80 (by decide),
      memRegion_split (sp + 0x9e8#64 + 0x118#64) 24 0x68 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [hc3]

theorem memRegion_0x9e8_0x198_fold (sp w0 w1 w2 : BitVec 64) :
    memRegion (sp + 0x9e8#64) 0x118 ∗
    ((sp + 0xb00#64) ↦₆₄ w0) ∗ ((sp + 0xb08#64) ↦₆₄ w1) ∗
    ((sp + 0xb10#64) ↦₆₄ w2) ∗
    memRegion (sp + 0xb18#64) 0x68 ⊢
      memRegion (sp + 0x9e8#64) 0x198 := by
  rw [memRegion_split (sp + 0x9e8#64) 0x118 0x80 (by decide),
      memRegion_split (sp + 0x9e8#64 + 0x118#64) 8 0x78 (by decide),
      memRegion_split (sp + 0x9e8#64 + 0x118#64 + 8#64) 8 0x70 (by decide),
      memRegion_split (sp + 0x9e8#64 + 0x118#64 + 8#64 + 8#64) 8 0x68 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _))))

theorem memRegion_0x280_0x1ea_fold (sp : BitVec 64) :
    memRegion (sp + 0x280#64) 0x1e8 ∗
    ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ⊢
      memRegion (sp + 0x280#64) 0x1ea := by
  rw [memRegion_split (sp + 0x280#64) 0x1e8 2 (by decide),
      memRegion_split (sp + 0x280#64 + 0x1e8#64) 1 1 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_right (sepConj_mono (pointsTo8_entails_memRegion _ _)
    (pointsTo8_entails_memRegion _ _))

theorem vecU8_eq_pure_words3_sep_buf (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs =
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜cap.toNat < 2 ^ 63⌝ ∗
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 0x10#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs := by
  rw [vecU8_eq_words3_sep_buf]
  apply ProofLib.sepProp_eq_of_entails
  · apply Entails.sepExists_elim; intro cap
    apply Entails.sepExists_elim; intro ptr
    refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
    have hbuf : vecU8Buf A cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecU8Buf A cap ptr bs :=
      vecU8Buf_pqCap_lt A cap ptr bs
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hbuf))) ?_
    exact Entails.of_eq (by ac_rfl)
  · apply Entails.sepExists_elim; intro cap
    apply Entails.sepExists_elim; intro ptr
    apply Entails.pure_left; intro _
    exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

theorem recordNoCur_fold_sp110 (A : RustAlloc) (sp : BitVec 64) (g : RecordGhost)
    (r : SessionRecord (List (BitVec 8))) {w4 w5 w6 : BitVec 64} {tail : List (BitVec 8)}
    (htail_inl : RecordTailInline g r w4 w5 w6 tail) (hcur : r.currentSession = none) :
    (recordWords56At (sp + 0x110#64) g.prevCap g.prevPtr 0#64 0xFFFFFFFFFFFFFFFF#64 w4 w5 w6 ∗
      ((sp + 0x148#64) ↦ₛ tail) ∗ recordHeap A g r) ⊢
    vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗
      memRegion (sp + 0x128#64) 0x158 := by
  obtain ⟨_, hw3_eq⟩ := curSession_none_of_recordTailInline htail_inl hcur
  rw [← hw3_eq]
  have hrec := sessionRecordAt_of_words56_sep_tail A (sp + 0x110#64) g r htail_inl
  have h38 : sp + 0x110#64 + 0x38#64 = sp + 0x148#64 := by bv_arith
  rw [h38] at hrec
  exact Entails.trans hrec (sessionRecordAt_noCur_weaken A sp g r hcur)

/-! ## Active Current-Session Branch (`r.currentSession = some sess`) -/

theorem sp_sub_0x60_eq_sub_0xbe0_add_0xb80 (sp0 : BitVec 64) :
    sp0 - 0x60#64 = sp0 - 0xbe0#64 + 0xb80#64 := by bv_arith

theorem vecU8_eq_words3_sep_buf_lt (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs = ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
      ⌜cap.toNat < 2 ^ 63⌝ ∗
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A cap ptr bs := by
  rw [vecU8_eq_words3_sep_buf]
  apply ProofLib.sepProp_eq_of_entails
  · apply Entails.sepExists_elim; intro cap
    apply Entails.sepExists_elim; intro ptr
    refine Entails.trans ?_ (Entails.sepExists_intro cap)
    refine Entails.trans ?_ (Entails.sepExists_intro ptr)
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (vecU8Buf_pqCap_lt A cap ptr bs)))) ?_
    exact Entails.of_eq (by ac_rfl)
  · apply Entails.sepExists_elim; intro cap
    apply Entails.sepExists_elim; intro ptr
    refine Entails.trans ?_ (Entails.sepExists_intro cap)
    refine Entails.trans ?_ (Entails.sepExists_intro ptr)
    exact Entails.pure_left fun _ => Entails.refl _

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad
