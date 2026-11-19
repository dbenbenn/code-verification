/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.ChainKey.MessageKeys -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
import ProofLib
import LibsignalBinary.Proofs.TripleRatchet.ChainKey.NextChainKey
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# Contract-Backed Callee Bridges on `tripleRatchetProgAtExt`

Layout-independent stack splits and `ChainKey::next_chain_key` verification (`NextChainKeyOkX`) on
`tripleRatchetProgAtExt` under `extHookStack`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalTripleRatchet.ExtCallees

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Encrypt

/-- Stack split of `rootStack` (`262,144` B) into `dropChainStackX` (`16,464` B) plus frame. -/
theorem stackAt_rootStack_split_dropChainX (sp : BitVec 64) :
    stackAt sp rootStack =
      stackAt sp dropChainStackX ∗ memRegion (sp - 262144#64) (rootStack - dropChainStackX) := by
  rw [stackAt_sub sp rootStack dropChainStackX (by decide) (by decide), sepConj_comm]
  simp only [rootStack]
  rfl

abbrev hmacStackX : Nat := 2048 + extHookStack

abbrev nextChainKeyStackX : Nat := nextChainKeyStack + extHookStack

theorem stackAt_split_ge (sp : BitVec 64) {small big : Nat}
    (hle : small ≤ big) (hmax : big < 2 ^ 64) :
    stackAt sp big =
      memRegion (sp - BitVec.ofNat 64 big) (big - small) ∗ stackAt sp small :=
  stackAt_sub sp big small hle hmax

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem stackAt_nextChainKeyX (sp : BitVec 64) :
    stackAt sp nextChainKeyStackX =
      memRegion (sp - 20480#64) 1968 ∗
      stackAt (sp - 80#64) hmacStackX ∗
      memRegion (sp - 80#64) 12 ∗
      memRegion (sp - 68#64) 32 ∗
      (∃∗ b0 : BitVec 8, (sp - 36#64) ↦₈ b0) ∗
      memRegion (sp - 35#64) 3 ∗
      (∃∗ v29 : BitVec 64, (sp - 32#64) ↦₆₄ v29) ∗
      (∃∗ v30 : BitVec 64, (sp - 24#64) ↦₆₄ v30) ∗
      (∃∗ v20 : BitVec 64, (sp - 16#64) ↦₆₄ v20) ∗
      (∃∗ v19 : BitVec 64, (sp - 8#64) ↦₆₄ v19) := by
  show memRegion (sp - BitVec.ofNat 64 20480) 20480 = _
  rw [LibsignalTripleRatchet.mr_cut' sp 20480 18512 1968 18512 20480 rfl rfl (by decide) (by decide) (by decide)]
  rw [LibsignalTripleRatchet.mr_cut' sp 18512 80 18432 80 18512 rfl rfl (by decide) (by decide) (by decide)]
  rw [LibsignalTripleRatchet.mr_cut' sp 80 68 12 68 80 rfl rfl (by decide) (by decide) (by decide)]
  rw [LibsignalTripleRatchet.mr_cut' sp 68 36 32 36 68 rfl rfl (by decide) (by decide) (by decide)]
  rw [LibsignalTripleRatchet.mr_cut' sp 36 35 1 35 36 rfl rfl (by decide) (by decide) (by decide)]
  rw [LibsignalTripleRatchet.mr_cut' sp 35 32 3 32 35 rfl rfl (by decide) (by decide) (by decide)]
  rw [LibsignalTripleRatchet.mr_cut' sp 32 24 8 24 32 rfl rfl (by decide) (by decide) (by decide)]
  rw [LibsignalTripleRatchet.mr_cut' sp 24 16 8 16 24 rfl rfl (by decide) (by decide) (by decide)]
  rw [LibsignalTripleRatchet.mr_cut' sp 16 8 8 8 16 rfl rfl (by decide) (by decide) (by decide)]
  rw [memRegion_one (sp - 36#64), ProofLib.memRegion_eight (sp - 32#64), ProofLib.memRegion_eight (sp - 24#64),
      ProofLib.memRegion_eight (sp - 16#64), ProofLib.memRegion_eight (sp - 8#64)]
  have h18512 : sp - 80#64 - 18432#64 = sp - 18512#64 := by bv_arith
  unfold stackAt
  change _ =
    memRegion (sp - 20480#64) 1968 ∗
    memRegion (sp - 80#64 - 18432#64) 18432 ∗
    memRegion (sp - 80#64) 12 ∗
    memRegion (sp - 68#64) 32 ∗
    (∃∗ b0 : BitVec 8, (sp - 36#64) ↦₈ b0) ∗
    memRegion (sp - 35#64) 3 ∗
    (∃∗ v29 : BitVec 64, (sp - 32#64) ↦₆₄ v29) ∗
    (∃∗ v30 : BitVec 64, (sp - 24#64) ↦₆₄ v30) ∗
    (∃∗ v20 : BitVec 64, (sp - 16#64) ↦₆₄ v20) ∗
    (∃∗ v19 : BitVec 64, (sp - 8#64) ↦₆₄ v19)
  rw [h18512]

private theorem stackAt_nextChainKeyX_repack (sp : BitVec 64) (w0 w1 w2 w3 v29 v30 v20 v19 : BitVec 64)
    (b0 : BitVec 8) :
    memRegion (sp - 20480#64) 1968 ∗
    stackAt (sp - 80#64) hmacStackX ∗
    memRegion (sp - 80#64) 12 ∗
    ((sp - 68#64) ↦₆₄ w0) ∗
    ((sp - 60#64) ↦₆₄ w1) ∗
    ((sp - 52#64) ↦₆₄ w2) ∗
    ((sp - 44#64) ↦₆₄ w3) ∗
    ((sp - 36#64) ↦₈ b0) ∗
    memRegion (sp - 35#64) 3 ∗
    ((sp - 32#64) ↦₆₄ v29) ∗
    ((sp - 24#64) ↦₆₄ v30) ∗
    ((sp - 16#64) ↦₆₄ v20) ∗
    ((sp - 8#64) ↦₆₄ v19) ⊢
      stackAt sp nextChainKeyStackX := by
  rw [stackAt_nextChainKeyX sp]
  have hw0 := pointsTo64_entails_memRegion (sp - 68#64) w0
  have hw1 := pointsTo64_entails_memRegion (sp - 60#64) w1
  have hw2 := pointsTo64_entails_memRegion (sp - 52#64) w2
  have hw3 := pointsTo64_entails_memRegion (sp - 44#64) w3
  have h60 : sp - 68#64 + 8#64 = sp - 60#64 := by bv_arith
  have h52 : sp - 60#64 + 8#64 = sp - 52#64 := by bv_arith
  have h44 : sp - 52#64 + 8#64 = sp - 44#64 := by bv_arith
  have h32 :
      ((sp - 68#64) ↦₆₄ w0) ∗ ((sp - 60#64) ↦₆₄ w1) ∗ ((sp - 52#64) ↦₆₄ w2) ∗ ((sp - 44#64) ↦₆₄ w3) ⊢
        memRegion (sp - 68#64) 32 := by
    refine Entails.trans (sepConj_mono hw0 (sepConj_mono hw1 (sepConj_mono hw2 hw3))) ?_
    rw [← h44, ← memRegion_split (sp - 52#64) 8 8 (by decide),
        ← h52, ← memRegion_split (sp - 60#64) 8 16 (by decide),
        ← h60, ← memRegion_split (sp - 68#64) 8 24 (by decide)]
    exact Entails.refl _
  have hb0 : ((sp - 36#64) ↦₈ b0) ⊢ ∃∗ b : BitVec 8, (sp - 36#64) ↦₈ b :=
    Entails.sepExists_right b0 (Entails.refl _)
  have hv29 : ((sp - 32#64) ↦₆₄ v29) ⊢ ∃∗ v : BitVec 64, (sp - 32#64) ↦₆₄ v :=
    Entails.sepExists_right v29 (Entails.refl _)
  have hv30 : ((sp - 24#64) ↦₆₄ v30) ⊢ ∃∗ v : BitVec 64, (sp - 24#64) ↦₆₄ v :=
    Entails.sepExists_right v30 (Entails.refl _)
  have hv20 : ((sp - 16#64) ↦₆₄ v20) ⊢ ∃∗ v : BitVec 64, (sp - 16#64) ↦₆₄ v :=
    Entails.sepExists_right v20 (Entails.refl _)
  have hv19 : ((sp - 8#64) ↦₆₄ v19) ⊢ ∃∗ v : BitVec 64, (sp - 8#64) ↦₆₄ v :=
    Entails.sepExists_right v19 (Entails.refl _)
  have hpull :
      (memRegion (sp - 20480#64) 1968 ∗
        stackAt (sp - 80#64) hmacStackX ∗
        memRegion (sp - 80#64) 12 ∗
        ((sp - 68#64) ↦₆₄ w0) ∗
        ((sp - 60#64) ↦₆₄ w1) ∗
        ((sp - 52#64) ↦₆₄ w2) ∗
        ((sp - 44#64) ↦₆₄ w3) ∗
        ((sp - 36#64) ↦₈ b0) ∗
        memRegion (sp - 35#64) 3 ∗
        ((sp - 32#64) ↦₆₄ v29) ∗
        ((sp - 24#64) ↦₆₄ v30) ∗
        ((sp - 16#64) ↦₆₄ v20) ∗
        ((sp - 8#64) ↦₆₄ v19)) =
      (memRegion (sp - 20480#64) 1968 ∗
        stackAt (sp - 80#64) hmacStackX ∗
        memRegion (sp - 80#64) 12 ∗
        (((sp - 68#64) ↦₆₄ w0) ∗ ((sp - 60#64) ↦₆₄ w1) ∗
         ((sp - 52#64) ↦₆₄ w2) ∗ ((sp - 44#64) ↦₆₄ w3)) ∗
        ((sp - 36#64) ↦₈ b0) ∗
        memRegion (sp - 35#64) 3 ∗
        ((sp - 32#64) ↦₆₄ v29) ∗
        ((sp - 24#64) ↦₆₄ v30) ∗
        ((sp - 16#64) ↦₆₄ v20) ∗
        ((sp - 8#64) ↦₆₄ v19)) := by ac_rfl
  rw [hpull]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono h32 (sepConj_mono hb0 (sepConj_mono_right
      (sepConj_mono hv29 (sepConj_mono hv30 (sepConj_mono hv20 hv19))))))))

private theorem pure_and_entails_pure_sep_of {P P' Q : Prop} {R : SepProp}
    (h : P → P' ∧ Q) :
    ⌜P⌝ ∗ R ⊢ ⌜P'⌝ ∗ (⌜Q⌝ ∗ R) := by
  apply Entails.pure_left
  intro hp
  rcases h hp with ⟨hp', hq⟩
  exact Entails.pure_right hp' (Entails.pure_right hq (Entails.refl R))

end CryptoVerification.Cli.LibsignalTripleRatchet.ExtCallees
