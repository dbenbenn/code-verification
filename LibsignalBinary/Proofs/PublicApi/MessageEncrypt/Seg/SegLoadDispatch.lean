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
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.CodeLayout

/-!
# `segLoad` Post-Poll Error Dispatch (`+0x160..+0x180`, `+0x41c..+0x45c`)

Handles the `ans = .error ()` (store hook error) and `ans = .ok none` (`SessionNotFound`) branches
at post-poll dispatch `+0x160` of `session_message_encrypt_with_stores`, routing both to
`tailWriteErr_ok`.
-/

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalPublicApi.MessageEncrypt CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Frame and `.rodata` Helpers -/

theorem enc_sp_bound_of_kit {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b)
    (ikit : IdentityStoreSpec A b)
    {sp : Nat} (h : withStoresEncStackV kit ikit ≤ sp) : withStoresEncStack ≤ sp := by
  unfold withStoresEncStackV encSubStackV encSubStack withStoresEncStack encFrameSize at *
  omega

theorem satisfies_pure_left {p : Prop} {Q : SepProp} {m : Memory} (h : m ⊨ ⌜p⌝ ∗ Q) :
    p ∧ (m ⊨ Q) :=
  (satisfies_pure_sepConj p Q m).mp h

theorem satisfies_sepExists_left {α : Type _} {P : α → SepProp} {Q : SepProp} {m : Memory}
    (h : m ⊨ (∃∗ a, P a) ∗ Q) : ∃ a, m ⊨ P a ∗ Q := by
  rw [sepExists_sepConj_left] at h
  exact (satisfies_sepExists _ m).mp h

theorem memRegion_0x110_0x35a_fold (sp : BitVec 64) (b0 b1 : BitVec 8) :
    memRegion (sp + 0x110#64) 0x358 ∗ ((sp + 0x468#64) ↦₈ b0) ∗ ((sp + 0x469#64) ↦₈ b1) ⊢
      memRegion (sp + 0x110#64) 0x35a := by
  rw [memRegion_split (sp + 0x110#64) 0x358 2 (by decide),
      memRegion_split (sp + 0x110#64 + 0x358#64) 1 1 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_right
    (sepConj_mono (pointsTo8_entails_memRegion _ _) (pointsTo8_entails_memRegion _ _))

theorem memRegion_0x848_split_0x9d0 (sp : BitVec 64) :
    memRegion (sp + 0x848#64) 0x338 =
      memRegion (sp + 0x848#64) 0x188 ∗
      cells (sp + 0x9d0#64) 3 ∗
      memRegion (sp + 0x9e8#64) 0x198 := by
  have hc3 : memRegion (sp + 0x9d0#64) 24 = cells (sp + 0x9d0#64) 3 :=
    ProofLib.memRegion_cells (sp + 0x9d0#64) 3 (by decide)
  rw [memRegion_split (sp + 0x848#64) 0x188 0x1b0 (by decide),
      memRegion_split (sp + 0x848#64 + 0x188#64) 24 0x198 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [hc3]

theorem pollWith_0x9d0_fold (sp w3 w4 w5 v830 v838 v840 : BitVec 64) (tail : List (BitVec 8))
    (htail : tail.length = 312) :
    (memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 368 ∗
      memRegion (sp + 0x6f0#64) 8 ∗
      ((sp + 0x6f8#64) ↦ₛ tail) ∗
      ((sp + 0x830#64) ↦₆₄ v830) ∗ ((sp + 0x838#64) ↦₆₄ v838) ∗
      ((sp + 0x840#64) ↦₆₄ v840) ∗
      memRegion (sp + 0x848#64) 0x188) ∗
    (((sp + 0x9d0#64) ↦₆₄ w3) ∗ ((sp + 0x9d8#64) ↦₆₄ w4) ∗ ((sp + 0x9e0#64) ↦₆₄ w5)) ∗
    memRegion (sp + 0x9e8#64) 0x198 ⊢
      pollWith sp 0x9d0 [w3, w4, w5] := by
  dsimp only [pollWith, words64At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
  have ht : ((sp + 0x6f8#64) ↦ₛ tail) ⊢ memRegion (sp + 0x6f8#64) 312 := by
    have h := pointsToBytes_entails_memRegion (sp + 0x6f8#64) tail
    rwa [htail] at h
  refine sepConj_mono_left ?_
  rw [memRegion_split (sp + 0x46a#64) 0x116 1104 (by decide),
      memRegion_split (sp + 0x46a#64 + 0x116#64) 368 736 (by decide),
      memRegion_split (sp + 0x46a#64 + 0x116#64 + 368#64) 8 728 (by decide),
      memRegion_split (sp + 0x46a#64 + 0x116#64 + 368#64 + 8#64) 312 416 (by decide),
      memRegion_split (sp + 0x46a#64 + 0x116#64 + 368#64 + 8#64 + 312#64) 8 408 (by decide),
      memRegion_split (sp + 0x46a#64 + 0x116#64 + 368#64 + 8#64 + 312#64 + 8#64) 8 400 (by decide),
      memRegion_split (sp + 0x46a#64 + 0x116#64 + 368#64 + 8#64 + 312#64 + 8#64 + 8#64) 8 392 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono ht (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)))))))

/-! ## Store Error Branch (`ans = .error ()`) -/

theorem loadOutRes_none_eq (Scope : SessionRecord (List (BitVec 8)) → Prop) (A : RustAlloc)
    (b w0 w1 w2 w3 w4 w5 w6 : BitVec 64) (tail : List (BitVec 8)) :
    LoadOutRes Scope A b (.ok none) w0 w1 w2 w3 w4 w5 w6 tail =
      ⌜w0 = 0xFFFFFFFFFFFFFFFF#64⌝ := rfl

theorem stack_encSub_extHook (sp : BitVec 64) :
    stackAt sp encSubStack =
      memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
        stackAt sp extHookStack := by
  have h := stackAt_split_bottom sp extHookStack (encSubStack - extHookStack) (by decide)
  rwa [show extHookStack + (encSubStack - extHookStack) = encSubStack by decide] at h

theorem stack_encSub_extHook_back (sp : BitVec 64) :
    memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
        stackAt sp extHookStack =
      stackAt sp encSubStack :=
  (stack_encSub_extHook sp).symm

theorem memRegion_0x580_split_24 (sp : BitVec 64) :
    memRegion (sp + 0x580#64) 368 =
      memRegion (sp + 0x580#64) 24 ∗ memRegion (sp + 0x598#64) 344 := by
  rw [memRegion_split (sp + 0x580#64) 24 344 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_0x598_split (sp : BitVec 64) :
    memRegion (sp + 0x598#64) 344 =
      (∃∗ b0 : BitVec 8, (sp + 0x598#64) ↦₈ b0) ∗
      memRegion (sp + 0x599#64) 7 ∗
      (∃∗ v5a0 : BitVec 64, (sp + 0x5a0#64) ↦₆₄ v5a0) ∗
      memRegion (sp + 0x5a8#64) 328 := by
  rw [memRegion_split (sp + 0x598#64) 1 343 (by decide),
      memRegion_split (sp + 0x598#64 + 1#64) 7 336 (by decide),
      memRegion_split (sp + 0x598#64 + 1#64 + 7#64) 8 328 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [ProofLib.memRegion_one (sp + 0x598#64), ProofLib.memRegion_eight (sp + 0x5a0#64)]

theorem memRegion_0x580_368_fold (sp w0 w1 w2 w3 w4 : BitVec 64) :
    ((sp + 0x580#64) ↦₆₄ w0) ∗ ((sp + 0x588#64) ↦₆₄ w1) ∗
    ((sp + 0x590#64) ↦₆₄ w2) ∗ ((sp + 0x598#64) ↦₆₄ w3) ∗
    ((sp + 0x5a0#64) ↦₆₄ w4) ∗ memRegion (sp + 0x5a8#64) 328 ⊢
      memRegion (sp + 0x580#64) 368 := by
  rw [memRegion_split (sp + 0x580#64) 8 360 (by decide),
      memRegion_split (sp + 0x580#64 + 8#64) 8 352 (by decide),
      memRegion_split (sp + 0x580#64 + 8#64 + 8#64) 8 344 (by decide),
      memRegion_split (sp + 0x580#64 + 8#64 + 8#64 + 8#64) 8 336 (by decide),
      memRegion_split (sp + 0x580#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 328 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)))))

theorem vecU8_eq_words3_sep_buf (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs =
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 0x10#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8
  apply ProofLib.sepProp_eq_of_entails
  · apply Entails.sepExists_elim; intro cap
    apply Entails.sepExists_elim; intro ptr
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.of_eq (by ac_rfl)))
  · apply Entails.sepExists_elim; intro cap
    apply Entails.sepExists_elim; intro ptr
    refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    exact Entails.of_eq (by ac_rfl)

theorem devWord_of_pointsTo8_memRegion7_1432 (sp : BitVec 64) (dev : BitVec 8) :
    ((sp + 1432#64) ↦₈ dev) ∗ memRegion (sp + 1433#64) 7 ⊢
      ∃∗ w3 : BitVec 64, ⌜DevWord dev w3⌝ ∗ ((sp + 1432#64) ↦₆₄ w3) := by
  have h := devWord_of_pointsTo8_memRegion7 (sp + 1432#64) dev
  have h1 : sp + 1432#64 + 1#64 = sp + 1433#64 := by bv_arith
  rwa [h1] at h

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad
