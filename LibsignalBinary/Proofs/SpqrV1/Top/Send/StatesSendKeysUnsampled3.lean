/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampled2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2Encoder
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `spqr::send::<HookRng>`: Inlined `.keysUnsampled` Arm (`+2588..+3068` and Top-Level Arm)

**Checked by Lean.**

Verifies `step_keysUnsampled_2588_to_3068` (`PolyEncoder::encode_bytes`, `next_chunk`,
and `chunkedKeysSampledAt` assembly) and the complete `.keysUnsampled` arm
`step_send_arm_keysUnsampled` (`0x309d0 -> 0x31458`, `+372..+3068`).
-/

public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.GF.UnacceleratedMul CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Drop CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local arm64_norm ↓, local wp_norm ↓]
  DoReserveNorm.sp_setPC_pre DoReserveNorm.sp_setMem_setPC_pre
  DoReserveNorm.readReg64_setPC_pre DoReserveNorm.readReg64_setMem_setPC_pre
  DoReserveNorm.readReg32_setPC_pre DoReserveNorm.readReg32_setMem_setPC_pre
  DoReserveNorm.readReg_setPC_pre DoReserveNorm.readReg_setMem_setPC_pre

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
theorem chunkAt_5208_4192_1360_eq (sp : BitVec 64) (chunk : Chunk)
    (cw0 cw1 cw2 cw3 : BitVec 64)
    (hchunk : ∀ a : BitVec 64,
      chunkAt a chunk =
        (a ↦₆₄ cw0) ∗ ((a + 8#64) ↦₆₄ cw1) ∗ ((a + 16#64) ↦₆₄ cw2) ∗
        ((a + 24#64) ↦₆₄ cw3) ∗ ((a + 32#64) ↦₁₆ chunk.index)) :
    chunkAt (sp + 5208#64) chunk =
      ((sp + 5208#64) ↦₆₄ cw0) ∗ ((sp + 5216#64) ↦₆₄ cw1) ∗
      ((sp + 5224#64) ↦₆₄ cw2) ∗ ((sp + 5232#64) ↦₆₄ cw3) ∗ ((sp + 5240#64) ↦₁₆ chunk.index) ∧
    chunkAt (sp + 4192#64) chunk =
      ((sp + 4192#64) ↦₆₄ cw0) ∗ ((sp + 4200#64) ↦₆₄ cw1) ∗
      ((sp + 4208#64) ↦₆₄ cw2) ∗ ((sp + 4216#64) ↦₆₄ cw3) ∗ ((sp + 4224#64) ↦₁₆ chunk.index) ∧
    chunkAt (sp + 1360#64) chunk =
      ((sp + 1360#64) ↦₆₄ cw0) ∗ ((sp + 1368#64) ↦₆₄ cw1) ∗
      ((sp + 1376#64) ↦₆₄ cw2) ∗ ((sp + 1384#64) ↦₆₄ cw3) ∗ ((sp + 1392#64) ↦₁₆ chunk.index) :=
  ⟨chunkAt_sp_add_eq sp 5208#64 5216#64 5224#64 5232#64 5240#64 chunk cw0 cw1 cw2 cw3 hchunk,
   chunkAt_sp_add_eq sp 4192#64 4200#64 4208#64 4216#64 4224#64 chunk cw0 cw1 cw2 cw3 hchunk,
   chunkAt_sp_add_eq sp 1360#64 1368#64 1376#64 1384#64 1392#64 chunk cw0 cw1 cw2 cw3 hchunk⟩

theorem words3_7104_entails_memRegion (sp w0 w1 w2 : BitVec 64) :
    ((sp + 7104#64) ↦₆₄ w0) ∗ ((sp + 7112#64) ↦₆₄ w1) ∗ ((sp + 7120#64) ↦₆₄ w2) ⊢
    memRegion (sp + 7104#64) 24 := by
  have h := words3_entails_memRegion (sp + 7104#64) w0 w1 w2
  rwa [show (sp + 7104#64) + 8#64 = sp + 7112#64 by rw [BitVec.add_assoc]; rfl,
       show (sp + 7104#64) + 16#64 = sp + 7120#64 by rw [BitVec.add_assoc]; rfl] at h

theorem keysUnsampled_src_entails_memRegion_928 (sp epoch : BitVec 64)
    (g : AuthenticatorGhost) (auth : Authenticator) :
    ((sp + 2384#64) ↦₆₄ 2#64) ∗
    authInlineWordsAt g (sp + 2392#64) auth ∗
    ((sp + 2440#64) ↦₆₄ epoch) ∗
    memRegion (sp + 2448#64) 864 ⊢
    memRegion (sp + 0x950#64) 928 := by
  rw [ProofLib.memRegion_split' (b := sp + 2384#64) (n := 8) (k := 920) (b' := sp + 2392#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 2392#64) (n := 48) (k := 872) (b' := sp + 2440#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 2440#64) (n := 8) (k := 864) (b' := sp + 2448#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (authInlineWordsAt_entails_memRegion g (sp + 2392#64) auth)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) (Entails.refl _)))

theorem authenticatorAt_entails_exists_inline_heap (A : RustAlloc) (a : BitVec 64) (auth : Authenticator) :
    authenticatorAt A a auth ⊢
    ∃∗ g : AuthenticatorGhost, authInlineWordsAt g a auth ∗ authHeapBufs A g auth := by
  unfold authenticatorAt vecU8
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply ProofLib.Entails.sepExists_elim; intro mcap
  apply ProofLib.Entails.sepExists_elim; intro mptr
  apply ProofLib.Entails.sepExists_elim; intro rcap
  apply ProofLib.Entails.sepExists_elim; intro rptr
  refine Entails.sepExists_right ⟨⟨rcap, rptr⟩, ⟨mcap, mptr⟩⟩ ?_
  dsimp only [authInlineWordsAt, authHeapBufs, vecU8At, vecHeader, RustHeap.vecU8Buf]
  rw [show (a + 0x18#64 : BitVec 64) = a + 24#64 from rfl,
      show (a + 24#64) + 8#64 = a + 32#64 by rw [BitVec.add_assoc]; rfl,
      show (a + 24#64) + 16#64 = a + 40#64 by rw [BitVec.add_assoc]; rfl]
  exact Entails.of_eq (by ac_rfl)

theorem SepWPp.mono_pre' {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q onPanic : State → SepProp → Prop}
    (hent : P ⊢ P') (h : SepWPp prog ret s P' Q onPanic) :
    SepWPp prog ret s P Q onPanic :=
  fun R hm hL => h R (Satisfies.mono (sepConj_mono_left hent) hm) hL

theorem take_64_len {α : Type} {l : List α} (h : 64 ≤ l.length) : (l.take 64).length = 64 := by
  rw [List.length_take]; omega

theorem sub_drop_64_len {α : Type} {l : List α} (h : 64 ≤ l.length) :
    l.length - (l.drop 64).length = 64 := by
  rw [List.length_drop]; omega

end CryptoVerification.SpqrV1.Top.Send
