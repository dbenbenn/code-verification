/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Frame -- proof-setup: allow-public-import
import ProofLib
import ProofLib.Sep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Getters
open ProofLib.ProgramReflection

namespace ReceiveRatchetFrom

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

/-! ## Step `+0x10c..+0x244` (`trFrom_step_10c_to_244`) -/

@[expose] def scRawCells (sp : BitVec 64)
    (w0 w8 w16 w24 : BitVec 64) (d32 : BitVec 32)
    (b36 : BitVec 8) (d37 : BitVec 32) (h41 : BitVec 16) (w43 w51 w59 : BitVec 64) (b67 : BitVec 8)
    (d68 : BitVec 32) (w72 : BitVec 64) (h80 : BitVec 16) (b82 : BitVec 8) (d83 : BitVec 32)
    (b87 : BitVec 8) (h88 : BitVec 16) (b90 : BitVec 8) (w91 : BitVec 64) (b99 : BitVec 8)
    (d100 : BitVec 32) : SepProp :=
  ((sp - 432#64) ↦₆₄ w0) ∗ ((sp - 424#64) ↦₆₄ w8) ∗ ((sp - 416#64) ↦₆₄ w16) ∗
  ((sp - 408#64) ↦₆₄ w24) ∗ ((sp - 400#64) ↦₃₂ d32) ∗
  ((sp - 396#64) ↦₈ b36) ∗ ((sp - 395#64) ↦₃₂ d37) ∗ ((sp - 391#64) ↦₁₆ h41) ∗
  ((sp - 389#64) ↦₆₄ w43) ∗ ((sp - 381#64) ↦₆₄ w51) ∗ ((sp - 373#64) ↦₆₄ w59) ∗
  ((sp - 365#64) ↦₈ b67) ∗
  ((sp - 364#64) ↦₃₂ d68) ∗ ((sp - 360#64) ↦₆₄ w72) ∗ ((sp - 352#64) ↦₁₆ h80) ∗
  ((sp - 350#64) ↦₈ b82) ∗ ((sp - 349#64) ↦₃₂ d83) ∗ ((sp - 345#64) ↦₈ b87) ∗
  ((sp - 344#64) ↦₁₆ h88) ∗ ((sp - 342#64) ↦₈ b90) ∗ ((sp - 341#64) ↦₆₄ w91) ∗
  ((sp - 333#64) ↦₈ b99) ∗ ((sp - 332#64) ↦₃₂ d100)

theorem stack_456_160_split (sp : BitVec 64) :
    memRegion (sp - 456#64) 160 =
      (∃∗ c_456 : BitVec 64, (sp - 456#64) ↦₆₄ c_456) ∗
      (∃∗ c_448 : BitVec 64, (sp - 448#64) ↦₆₄ c_448) ∗
      (∃∗ c_440 : BitVec 64, (sp - 440#64) ↦₆₄ c_440) ∗
      (∃∗ s_432 : BitVec 64, (sp - 432#64) ↦₆₄ s_432) ∗
      (∃∗ s_424 : BitVec 64, (sp - 424#64) ↦₆₄ s_424) ∗
      (∃∗ s_416 : BitVec 64, (sp - 416#64) ↦₆₄ s_416) ∗
      (∃∗ s_408 : BitVec 64, (sp - 408#64) ↦₆₄ s_408) ∗
      (∃∗ s_400 : BitVec 32, (sp - 400#64) ↦₃₂ s_400) ∗
      (∃∗ s_396 : BitVec 8, (sp - 396#64) ↦₈ s_396) ∗
      (∃∗ s_395 : BitVec 32, (sp - 395#64) ↦₃₂ s_395) ∗
      (∃∗ s_391 : BitVec 16, (sp - 391#64) ↦₁₆ s_391) ∗
      (∃∗ s_389 : BitVec 64, (sp - 389#64) ↦₆₄ s_389) ∗
      (∃∗ s_381 : BitVec 64, (sp - 381#64) ↦₆₄ s_381) ∗
      (∃∗ s_373 : BitVec 64, (sp - 373#64) ↦₆₄ s_373) ∗
      (∃∗ s_365 : BitVec 8, (sp - 365#64) ↦₈ s_365) ∗
      (∃∗ s_364 : BitVec 32, (sp - 364#64) ↦₃₂ s_364) ∗
      (∃∗ s_360 : BitVec 64, (sp - 360#64) ↦₆₄ s_360) ∗
      (∃∗ s_352 : BitVec 16, (sp - 352#64) ↦₁₆ s_352) ∗
      (∃∗ s_350 : BitVec 8, (sp - 350#64) ↦₈ s_350) ∗
      (∃∗ s_349 : BitVec 32, (sp - 349#64) ↦₃₂ s_349) ∗
      (∃∗ s_345 : BitVec 8, (sp - 345#64) ↦₈ s_345) ∗
      (∃∗ s_344 : BitVec 16, (sp - 344#64) ↦₁₆ s_344) ∗
      (∃∗ s_342 : BitVec 8, (sp - 342#64) ↦₈ s_342) ∗
      (∃∗ s_341 : BitVec 64, (sp - 341#64) ↦₆₄ s_341) ∗
      (∃∗ s_333 : BitVec 8, (sp - 333#64) ↦₈ s_333) ∗
      (∃∗ s_332 : BitVec 32, (sp - 332#64) ↦₃₂ s_332) ∗
      (∃∗ k_328 : BitVec 8, (sp - 328#64) ↦₈ k_328) ∗
      (∃∗ k_327 : BitVec 8, (sp - 327#64) ↦₈ k_327) ∗
      (∃∗ k_326 : BitVec 8, (sp - 326#64) ↦₈ k_326) ∗
      (∃∗ k_325 : BitVec 8, (sp - 325#64) ↦₈ k_325) ∗
      (∃∗ k_324 : BitVec 8, (sp - 324#64) ↦₈ k_324) ∗
      (∃∗ k_323 : BitVec 8, (sp - 323#64) ↦₈ k_323) ∗
      (∃∗ k_322 : BitVec 8, (sp - 322#64) ↦₈ k_322) ∗
      (∃∗ k_321 : BitVec 64, (sp - 321#64) ↦₆₄ k_321) ∗
      (∃∗ k_313 : BitVec 64, (sp - 313#64) ↦₆₄ k_313) ∗
      (∃∗ k_305 : BitVec 64, (sp - 305#64) ↦₆₄ k_305) ∗
      (∃∗ k_297 : BitVec 8, (sp - 297#64) ↦₈ k_297) := by
  sep_interval_eq

theorem stack_256_24_split (sp : BitVec 64) :
    memRegion (sp - 256#64) 24 =
      (∃∗ t_256 : BitVec 64, (sp - 256#64) ↦₆₄ t_256) ∗
      (∃∗ t_248 : BitVec 8, (sp - 248#64) ↦₈ t_248) ∗
      memRegion (sp - 247#64) 7 ∗
      (∃∗ t_240 : BitVec 8, (sp - 240#64) ↦₈ t_240) ∗
      (∃∗ t_239 : BitVec 8, (sp - 239#64) ↦₈ t_239) ∗
      (∃∗ t_238 : BitVec 8, (sp - 238#64) ↦₈ t_238) ∗
      (∃∗ t_237 : BitVec 8, (sp - 237#64) ↦₈ t_237) ∗
      (∃∗ t_236 : BitVec 8, (sp - 236#64) ↦₈ t_236) ∗
      (∃∗ t_235 : BitVec 8, (sp - 235#64) ↦₈ t_235) ∗
      (∃∗ t_234 : BitVec 8, (sp - 234#64) ↦₈ t_234) ∗
      memRegion (sp - 233#64) 1 := by
  sep_interval_eq

theorem stack_184_24_split_10c (sp : BitVec 64) :
    memRegion (sp - 184#64) 24 =
      (∃∗ t_184 : BitVec 64, (sp - 184#64) ↦₆₄ t_184) ∗
      (∃∗ t_176 : BitVec 8, (sp - 176#64) ↦₈ t_176) ∗
      memRegion (sp - 175#64) 15 := by
  sep_interval_eq

theorem rk_10c_pack_stack (sp : BitVec 64) {bs : List (BitVec 8)}
    {b0 b1 b2 b3 b4 b5 b6 : BitVec 8} {w7 w15 w23 : BitVec 64} {b31 : BitVec 8}
    (h : ∀ a : BitVec 64, (a ↦ₛ bs) =
      ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₈ b3) ∗
       ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗
       ((a + 7#64) ↦₆₄ w7) ∗ ((a + 15#64) ↦₆₄ w15) ∗ ((a + 23#64) ↦₆₄ w23) ∗
       ((a + 31#64) ↦₈ b31))) :
    (((sp - 328#64) ↦₈ b0) ∗ ((sp - 327#64) ↦₈ b1) ∗ ((sp - 326#64) ↦₈ b2) ∗
     ((sp - 325#64) ↦₈ b3) ∗ ((sp - 324#64) ↦₈ b4) ∗ ((sp - 323#64) ↦₈ b5) ∗
     ((sp - 322#64) ↦₈ b6) ∗ ((sp - 321#64) ↦₆₄ w7) ∗ ((sp - 313#64) ↦₆₄ w15) ∗
     ((sp - 305#64) ↦₆₄ w23) ∗ ((sp - 297#64) ↦₈ b31)) ⊢
      ((sp - 328#64) ↦ₛ bs) := by
  rw [h (sp - 328#64)]
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg]
  exact Entails.refl _

theorem sp_256_split_32_16_2 (sp : BitVec 64) (v : BitVec 64) :
    ((sp - 256#64) ↦₆₄ v) ⊢
      ∃∗ h_252 : BitVec 16, ∃∗ d_256 : BitVec 32,
        ((sp - 256#64) ↦₃₂ d_256) ∗ ((sp - 252#64) ↦₁₆ h_252) ∗ memRegion (sp - 250#64) 2 := by
  refine Entails.trans (Q := (∃∗ d_256 : BitVec 32, (sp - 256#64) ↦₃₂ d_256) ∗
    (∃∗ h_252 : BitVec 16, (sp - 252#64) ↦₁₆ h_252) ∗ memRegion (sp - 250#64) 2)
    (by sep_interval) (by bi_entail)

theorem stack_256_24_fold (sp : BitVec 64)
    (d_256 : BitVec 32) (h_252 : BitVec 16)
    (t_248 t_240 t_239 t_238 t_237 t_236 t_235 t_234 : BitVec 8) :
    (((sp - 256#64) ↦₃₂ d_256) ∗ ((sp - 252#64) ↦₁₆ h_252) ∗ memRegion (sp - 250#64) 2 ∗
     ((sp - 248#64) ↦₈ t_248) ∗ memRegion (sp - 247#64) 7 ∗
     ((sp - 240#64) ↦₈ t_240) ∗ ((sp - 239#64) ↦₈ t_239) ∗
     ((sp - 238#64) ↦₈ t_238) ∗ ((sp - 237#64) ↦₈ t_237) ∗
     ((sp - 236#64) ↦₈ t_236) ∗ ((sp - 235#64) ↦₈ t_235) ∗
     ((sp - 234#64) ↦₈ t_234) ∗ memRegion (sp - 233#64) 1) ⊢
      memRegion (sp - 256#64) 24 := by
  sep_interval

theorem stack_280_184_fold_10c (sp : BitVec 64)
    (w_232 : BitVec 64) (b_224 : BitVec 8)
    (b_216 b_215 b_214 b_213 b_212 b_211 b_210 : BitVec 8)
    (w_208 : BitVec 64) (b_200 : BitVec 8) (d_192 : BitVec 32) (h_188 : BitVec 16)
    (t_184 : BitVec 64) (t_176 : BitVec 8)
    (u_160 u_152 u_144 : BitVec 64) :
    (memRegion (sp - 280#64) 24 ∗
     memRegion (sp - 256#64) 24 ∗
     ((sp - 232#64) ↦₆₄ w_232) ∗
     ((sp - 224#64) ↦₈ b_224) ∗ memRegion (sp - 223#64) 7 ∗
     ((sp - 216#64) ↦₈ b_216) ∗ ((sp - 215#64) ↦₈ b_215) ∗
     ((sp - 214#64) ↦₈ b_214) ∗ ((sp - 213#64) ↦₈ b_213) ∗
     ((sp - 212#64) ↦₈ b_212) ∗ ((sp - 211#64) ↦₈ b_211) ∗
     ((sp - 210#64) ↦₈ b_210) ∗ memRegion (sp - 209#64) 1 ∗
     ((sp - 208#64) ↦₆₄ w_208) ∗
     ((sp - 200#64) ↦₈ b_200) ∗ memRegion (sp - 199#64) 7 ∗
     ((sp - 192#64) ↦₃₂ d_192) ∗ ((sp - 188#64) ↦₁₆ h_188) ∗ memRegion (sp - 186#64) 2 ∗
     ((sp - 184#64) ↦₆₄ t_184) ∗ ((sp - 176#64) ↦₈ t_176) ∗ memRegion (sp - 175#64) 15 ∗
     ((sp - 160#64) ↦₆₄ u_160) ∗ ((sp - 152#64) ↦₆₄ u_152) ∗ ((sp - 144#64) ↦₆₄ u_144) ∗
     memRegion (sp - 136#64) 16 ∗ memRegion (sp - 120#64) 24) ⊢
      memRegion (sp - 280#64) 184 := by
  sep_interval

theorem vecU8At_nil_pq_ss (A : RustAlloc) (ss : BitVec 64) :
    (((ss + 120#64) ↦₆₄ 0#64) ∗ ((ss + 128#64) ↦₆₄ 1#64) ∗ ((ss + 136#64) ↦₆₄ 0#64)) ⊢
      vecU8At A (ss + 120#64) 0#64 1#64 [] := by
  have h := vecU8At_nil_0_1 A (ss + 120#64)
  simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h

theorem sessionAfter208Frame_intro (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) :
    (sessionFromBase A ss G st ∗
     (ss ↦₆₄ G.localIk.cap) ∗ ((ss + 8#64) ↦₆₄ G.localIk.ptr) ∗
     ((ss + 16#64) ↦₆₄ BitVec.ofNat 64 G.localIk.bytes.length) ∗
     vecU8Rest A G.localIk.cap G.localIk.ptr G.localIk.bytes ∗
     ((ss + 48#64) ↦₆₄ G.root.cap) ∗ ((ss + 56#64) ↦₆₄ G.root.ptr) ∗
     ((ss + 64#64) ↦₆₄ 32#64) ∗
     (G.root.ptr ↦ₛ CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
     vecU8Rest A G.root.cap G.root.ptr (CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
     vecAt A 104 8 (chainAt A) (ss + 72#64) 0#64 8#64 [] ∗
     vecU8At A (ss + 120#64) 0#64 1#64 [] ∗
     optSenderChainAt A (ss + 144#64) G.sender st.senderChain ∗
     ((ss + 332#64) ↦₃₂ st.previousCounter)) ⊢
      sessionAfter208Frame A ss G st := by
  unfold sessionAfter208Frame
  exact Entails.refl _

theorem scRawCells_fold (sp : BitVec 64)
    (w0 w8 w16 w24 : BitVec 64) (d32 : BitVec 32)
    (b36 : BitVec 8) (d37 : BitVec 32) (h41 : BitVec 16) (w43 w51 w59 : BitVec 64) (b67 : BitVec 8)
    (d68 : BitVec 32) (w72 : BitVec 64) (h80 : BitVec 16) (b82 : BitVec 8) (d83 : BitVec 32)
    (b87 : BitVec 8) (h88 : BitVec 16) (b90 : BitVec 8) (w91 : BitVec 64) (b99 : BitVec 8)
    (d100 : BitVec 32) :
    (((sp - 432#64) ↦₆₄ w0) ∗ ((sp - 424#64) ↦₆₄ w8) ∗ ((sp - 416#64) ↦₆₄ w16) ∗
     ((sp - 408#64) ↦₆₄ w24) ∗ ((sp - 400#64) ↦₃₂ d32) ∗
     ((sp - 396#64) ↦₈ b36) ∗ ((sp - 395#64) ↦₃₂ d37) ∗ ((sp - 391#64) ↦₁₆ h41) ∗
     ((sp - 389#64) ↦₆₄ w43) ∗ ((sp - 381#64) ↦₆₄ w51) ∗ ((sp - 373#64) ↦₆₄ w59) ∗
     ((sp - 365#64) ↦₈ b67) ∗
     ((sp - 364#64) ↦₃₂ d68) ∗ ((sp - 360#64) ↦₆₄ w72) ∗ ((sp - 352#64) ↦₁₆ h80) ∗
     ((sp - 350#64) ↦₈ b82) ∗ ((sp - 349#64) ↦₃₂ d83) ∗ ((sp - 345#64) ↦₈ b87) ∗
     ((sp - 344#64) ↦₁₆ h88) ∗ ((sp - 342#64) ↦₈ b90) ∗ ((sp - 341#64) ↦₆₄ w91) ∗
     ((sp - 333#64) ↦₈ b99) ∗ ((sp - 332#64) ↦₃₂ d100)) ⊢
      scRawCells sp w0 w8 w16 w24 d32 b36 d37 h41 w43 w51 w59 b67
        d68 w72 h80 b82 d83 b87 h88 b90 w91 b99 d100 := by
  unfold scRawCells
  exact Entails.refl _

theorem memRegion_100_to_bytes (a : BitVec 64) :
    memRegion a 100 ⊢ ∃∗ bs : List (BitVec 8), ⌜bs.length = 100⌝ ∗ (a ↦ₛ bs) := by
  have hsplit : memRegion a 100 =
      memRegion a 32 ∗ memRegion (a + 32#64) 32 ∗
      memRegion (a + 64#64) 32 ∗ (∃∗ d3 : BitVec 32, (a + 96#64) ↦₃₂ d3) := by
    sep_interval_eq
  rw [hsplit]
  refine Entails.trans (sepConj_mono (memRegion_32_to_bytes a)
    (sepConj_mono (memRegion_32_to_bytes (a + 32#64))
      (sepConj_mono (memRegion_32_to_bytes (a + 64#64)) (Entails.refl _)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro d3
  apply Entails.sepExists_elim; intro bs2
  apply Entails.sepExists_elim; intro bs1
  apply Entails.sepExists_elim; intro bs0
  apply Entails.pure_left; intro h0
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; intro h1'
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm]
  apply Entails.pure_left; intro h2'
  let out100 := bs0 ++ bs1 ++ bs2 ++ unpack32 d3
  have hout_len : out100.length = 100 := by
    have hd3 : (unpack32 d3).length = 4 := rfl
    simp [out100, h0, h1', h2', hd3]
  have hout_pts : (a ↦ₛ out100) =
      ((a ↦ₛ bs0) ∗ ((a + 32#64) ↦ₛ bs1) ∗ ((a + 64#64) ↦ₛ bs2) ∗ ((a + 96#64) ↦₃₂ d3)) := by
    dsimp only [out100]
    simp only [List.append_assoc, pointsToBytes_append, h0, h1', h2',
      ← pointsTo32_eq_pointsToBytes, BitVec.add_assoc, BitVec.reduceAdd]
  apply entails_exists_right out100
  apply Entails.pure_right hout_len
  rw [hout_pts]
  exact Entails.refl _

theorem scRawCells_to_memRegion_100 (sp : BitVec 64)
    (d4 : BitVec 32) (w8 w16 w24 : BitVec 64) (d32 : BitVec 32)
    (b36 : BitVec 8) (d37 : BitVec 32) (h41 : BitVec 16) (w43 w51 w59 : BitVec 64) (b67 : BitVec 8)
    (d68 : BitVec 32) (w72 : BitVec 64) (h80 : BitVec 16) (b82 : BitVec 8) (d83 : BitVec 32)
    (b87 : BitVec 8) (h88 : BitVec 16) (b90 : BitVec 8) (w91 : BitVec 64) (b99 : BitVec 8)
    (d100 : BitVec 32) :
    (((sp - 428#64) ↦₃₂ d4) ∗ ((sp - 424#64) ↦₆₄ w8) ∗ ((sp - 416#64) ↦₆₄ w16) ∗
     ((sp - 408#64) ↦₆₄ w24) ∗ ((sp - 400#64) ↦₃₂ d32) ∗
     ((sp - 396#64) ↦₈ b36) ∗ ((sp - 395#64) ↦₃₂ d37) ∗ ((sp - 391#64) ↦₁₆ h41) ∗
     ((sp - 389#64) ↦₆₄ w43) ∗ ((sp - 381#64) ↦₆₄ w51) ∗ ((sp - 373#64) ↦₆₄ w59) ∗
     ((sp - 365#64) ↦₈ b67) ∗
     ((sp - 364#64) ↦₃₂ d68) ∗ ((sp - 360#64) ↦₆₄ w72) ∗ ((sp - 352#64) ↦₁₆ h80) ∗
     ((sp - 350#64) ↦₈ b82) ∗ ((sp - 349#64) ↦₃₂ d83) ∗ ((sp - 345#64) ↦₈ b87) ∗
     ((sp - 344#64) ↦₁₆ h88) ∗ ((sp - 342#64) ↦₈ b90) ∗ ((sp - 341#64) ↦₆₄ w91) ∗
     ((sp - 333#64) ↦₈ b99) ∗ ((sp - 332#64) ↦₃₂ d100)) ⊢
      memRegion (sp - 428#64) 100 := by
  sep_interval

theorem scRawCells_none_entails (sp : BitVec 64)
    (w8 w16 w24 : BitVec 64) (d32 : BitVec 32)
    (b36 : BitVec 8) (d37 : BitVec 32) (h41 : BitVec 16) (w43 w51 w59 : BitVec 64) (b67 : BitVec 8)
    (d68 : BitVec 32) (w72 : BitVec 64) (h80 : BitVec 16) (b82 : BitVec 8) (d83 : BitVec 32)
    (b87 : BitVec 8) (h88 : BitVec 16) (b90 : BitVec 8) (w91 : BitVec 64) (b99 : BitVec 8)
    (d100 : BitVec 32) :
    scRawCells sp 0#64 w8 w16 w24 d32 b36 d37 h41 w43 w51 w59 b67
      d68 w72 h80 b82 d83 b87 h88 b90 w91 b99 d100 ⊢
      ∃∗ senderPad : List (BitVec 8),
        ⌜senderPad.length = 100⌝ ∗
        ((sp - 432#64) ↦ₛ optSenderChainBytes none senderPad) := by
  unfold scRawCells
  have h0_64 : ((sp - 432#64) ↦₆₄ 0#64) =
      (((sp - 432#64) ↦₈ 0#8) ∗ ((sp - 431#64) ↦₈ 0#8) ∗
       ((sp - 430#64) ↦₈ 0#8) ∗ ((sp - 429#64) ↦₈ 0#8) ∗
       ((sp - 428#64) ↦₃₂ 0#32)) := by
    have hsplit : ((sp - 432#64) ↦₆₄ 0#64) =
        ((sp - 432#64) ↦₃₂ (0#8 ++ 0#8 ++ 0#8 ++ 0#8)) ∗ ((sp - 432#64 + 4#64) ↦₃₂ 0#32) :=
      pointsTo64_eq_pointsTo32 (sp - 432#64) (0#8 ++ 0#8 ++ 0#8 ++ 0#8) 0#32
    rw [hsplit, pointsTo32_eq_bytes4 (sp - 432#64)]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg, sepConj_assoc]
  rw [h0_64]
  simp only [sepConj_assoc]
  have hmr := Entails.trans
    (scRawCells_to_memRegion_100 sp 0#32 w8 w16 w24 d32 b36 d37 h41 w43 w51 w59 b67
      d68 w72 h80 b82 d83 b87 h88 b90 w91 b99 d100)
    (memRegion_100_to_bytes (sp - 428#64))
  refine Entails.trans (sepConj_mono (Entails.refl _)
    (sepConj_mono (Entails.refl _)
      (sepConj_mono (Entails.refl _)
        (sepConj_mono (Entails.refl _) hmr)))) ?_
  simp only [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro senderPad
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
  apply Entails.pure_left; intro hlen
  apply entails_exists_right senderPad
  apply Entails.pure_right hlen
  rw [optSenderChainBytes_none_eq (sp - 432#64) senderPad]
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg]
  exact Entails.refl _

theorem scRawCells_some_entails (sp : BitVec 64) (sc : SenderChain) (senderPad : List (BitVec 8))
    {pk_b0 pk_b1 pk_b2 pk_b3 pk_b4 pk_b5 pk_b6 pk_b7 pk_b8 pk_b9 pk_b10 pk_b11
     pk_b12 pk_b13 pk_b14 pk_b15 pk_b16 pk_b17 pk_b18 pk_b19 pk_b20 pk_b21 pk_b22
     pk_b23 pk_b24 pk_b25 pk_b26 pk_b27 : BitVec 8}
    {pk_d28 : BitVec 32}
    {sk_b0 : BitVec 8} {sk_d1 : BitVec 32} {sk_h5 : BitVec 16}
    {sk_w7 sk_w15 sk_w23 : BitVec 64} {sk_b31 : BitVec 8}
    {ck_d0 : BitVec 32}
    {ck_b4 ck_b5 ck_b6 ck_b7 ck_b8 ck_b9 ck_b10 ck_b11 ck_b12 ck_b13 ck_b14
     ck_b15 ck_b16 ck_b17 ck_b18 ck_b19 ck_b20 ck_b21 ck_b22 : BitVec 8}
    {ck_w23 : BitVec 64} {ck_b31 : BitVec 8}
    (hpk2 : ∀ a : BitVec 64,
      ((a ↦₆₄ (pk_b3 ++ pk_b2 ++ pk_b1 ++ pk_b0 ++ 0#8 ++ 0#8 ++ 0#8 ++ 1#8)) ∗
       ((a + 8#64) ↦₆₄ (pk_b11 ++ pk_b10 ++ pk_b9 ++ pk_b8 ++ pk_b7 ++ pk_b6 ++ pk_b5 ++ pk_b4)) ∗
       ((a + 16#64) ↦₆₄ (pk_b19 ++ pk_b18 ++ pk_b17 ++ pk_b16 ++ pk_b15 ++ pk_b14 ++ pk_b13 ++ pk_b12)) ∗
       ((a + 24#64) ↦₆₄ (pk_b27 ++ pk_b26 ++ pk_b25 ++ pk_b24 ++ pk_b23 ++ pk_b22 ++ pk_b21 ++ pk_b20)) ∗
       ((a + 32#64) ↦₃₂ pk_d28)) =
      ((a ↦₈ 1#8) ∗ ((a + 1#64) ↦₈ 0#8) ∗ ((a + 2#64) ↦₈ 0#8) ∗ ((a + 3#64) ↦₈ 0#8) ∗
       ((a + 4#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList)))
    (hsk : ∀ a : BitVec 64,
      (a ↦ₛ sc.ratchetKey.privateKey.bytes.toList) =
        ((a ↦₈ sk_b0) ∗ ((a + 1#64) ↦₃₂ sk_d1) ∗ ((a + 5#64) ↦₁₆ sk_h5) ∗
         ((a + 7#64) ↦₆₄ sk_w7) ∗ ((a + 15#64) ↦₆₄ sk_w15) ∗ ((a + 23#64) ↦₆₄ sk_w23) ∗
         ((a + 31#64) ↦₈ sk_b31)))
    (hck2 : ∀ a : BitVec 64,
      (a ↦ₛ CryptoGames.HMAC.keyToBytes32 sc.chainKey.key) =
        ((a ↦₃₂ ck_d0) ∗
         ((a + 4#64) ↦₆₄ (ck_b11 ++ ck_b10 ++ ck_b9 ++ ck_b8 ++ ck_b7 ++ ck_b6 ++ ck_b5 ++ ck_b4)) ∗
         ((a + 12#64) ↦₁₆ (ck_b13 ++ ck_b12)) ∗
         ((a + 14#64) ↦₈ ck_b14) ∗
         ((a + 15#64) ↦₃₂ (ck_b18 ++ ck_b17 ++ ck_b16 ++ ck_b15)) ∗
         ((a + 19#64) ↦₈ ck_b19) ∗
         ((a + 20#64) ↦₁₆ (ck_b21 ++ ck_b20)) ∗
         ((a + 22#64) ↦₈ ck_b22) ∗
         ((a + 23#64) ↦₆₄ ck_w23) ∗
         ((a + 31#64) ↦₈ ck_b31))) :
    scRawCells sp
      (pk_b3 ++ pk_b2 ++ pk_b1 ++ pk_b0 ++ 0#8 ++ 0#8 ++ 0#8 ++ 1#8)
      (pk_b11 ++ pk_b10 ++ pk_b9 ++ pk_b8 ++ pk_b7 ++ pk_b6 ++ pk_b5 ++ pk_b4)
      (pk_b19 ++ pk_b18 ++ pk_b17 ++ pk_b16 ++ pk_b15 ++ pk_b14 ++ pk_b13 ++ pk_b12)
      (pk_b27 ++ pk_b26 ++ pk_b25 ++ pk_b24 ++ pk_b23 ++ pk_b22 ++ pk_b21 ++ pk_b20)
      ((pk_d28.zeroExtend 64).setWidth 32)
      ((sk_b0.zeroExtend 64).setWidth 8) sk_d1 sk_h5 sk_w7 sk_w15 sk_w23
      ((sk_b31.zeroExtend 64).setWidth 8)
      ((ck_d0.zeroExtend 64).setWidth 32)
      (ck_b11 ++ ck_b10 ++ ck_b9 ++ ck_b8 ++ ck_b7 ++ ck_b6 ++ ck_b5 ++ ck_b4)
      (((0#8 ++ ck_b14 ++ ck_b13 ++ ck_b12 : BitVec 32).zeroExtend 64).setWidth 16)
      ((((((0#8 ++ ck_b14 ++ ck_b13 ++ ck_b12 : BitVec 32).zeroExtend 64).setWidth 32) >>> 16).zeroExtend 64).setWidth 8)
      ((ck_b22 ++ ck_b21 ++ ck_b20 ++ ck_b19 ++ ck_b18 ++ ck_b17 ++ ck_b16 ++ ck_b15).setWidth 32)
      (((ck_b22 ++ ck_b21 ++ ck_b20 ++ ck_b19 ++ ck_b18 ++ ck_b17 ++ ck_b16 ++ ck_b15) >>> 32).setWidth 8)
      (((0#8 ++ ck_b22 ++ ck_b21 ++ ck_b20 : BitVec 32).zeroExtend 64).setWidth 16)
      ((((((0#8 ++ ck_b22 ++ ck_b21 ++ ck_b20 : BitVec 32).zeroExtend 64).setWidth 32) >>> 16).zeroExtend 64).setWidth 8)
      ck_w23 ck_b31 ((sc.chainKey.index.zeroExtend 64).setWidth 32) ⊢
      ((sp - 432#64) ↦ₛ optSenderChainBytes (some sc) senderPad) := by
  simp only [arm64_norm]
  unfold scRawCells
  have h1 := hpk2 (sp - 432#64)
  rw [optSenderChainBytes_some_eq (sp - 432#64) sc senderPad,
      hsk (sp - 432#64 + 36#64),
      hck2 (sp - 432#64 + 68#64)]
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg,
    ← sepConj_assoc] at h1 ⊢
  rw [h1]
  exact Entails.refl _

theorem stack_256_96_split (sp : BitVec 64) :
    memRegion (sp - 256#64) 96 =
      memRegion (sp - 256#64) 24 ∗
      (∃∗ w_232 : BitVec 64, (sp - 232#64) ↦₆₄ w_232) ∗
      (∃∗ b_224 : BitVec 8, (sp - 224#64) ↦₈ b_224) ∗ memRegion (sp - 223#64) 7 ∗
      (∃∗ b_216 : BitVec 8, (sp - 216#64) ↦₈ b_216) ∗
      (∃∗ b_215 : BitVec 8, (sp - 215#64) ↦₈ b_215) ∗
      (∃∗ b_214 : BitVec 8, (sp - 214#64) ↦₈ b_214) ∗
      (∃∗ b_213 : BitVec 8, (sp - 213#64) ↦₈ b_213) ∗
      (∃∗ b_212 : BitVec 8, (sp - 212#64) ↦₈ b_212) ∗
      (∃∗ b_211 : BitVec 8, (sp - 211#64) ↦₈ b_211) ∗
      (∃∗ b_210 : BitVec 8, (sp - 210#64) ↦₈ b_210) ∗ memRegion (sp - 209#64) 1 ∗
      (∃∗ w_208 : BitVec 64, (sp - 208#64) ↦₆₄ w_208) ∗
      (∃∗ b_200 : BitVec 8, (sp - 200#64) ↦₈ b_200) ∗ memRegion (sp - 199#64) 7 ∗
      (∃∗ d_192 : BitVec 32, (sp - 192#64) ↦₃₂ d_192) ∗
      (∃∗ h_188 : BitVec 16, (sp - 188#64) ↦₁₆ h_188) ∗ memRegion (sp - 186#64) 2 ∗
      memRegion (sp - 184#64) 24 := by
  sep_interval_eq

theorem stack_456_160_split_deser (sp : BitVec 64) :
    memRegion (sp - 456#64) 160 =
      memRegion (sp - 456#64) 33 ∗ memRegion (sp - 423#64) 127 := by
  sep_interval_eq

theorem stack_456_160_fold_some (sp : BitVec 64)
    (b_456 b_455 b_454 b_453 b_452 b_451 b_450 b_449
     b_448 b_447 b_446 b_445 b_444 b_443 b_442 b_441 : BitVec 8)
    (w_440 : BitVec 64) (d_432 : BitVec 32) (b_428 : BitVec 8) (d_427 : BitVec 32) :
    (((sp - 456#64) ↦₈ b_456) ∗ ((sp - 455#64) ↦₈ b_455) ∗
     ((sp - 454#64) ↦₈ b_454) ∗ ((sp - 453#64) ↦₈ b_453) ∗
     ((sp - 452#64) ↦₈ b_452) ∗ ((sp - 451#64) ↦₈ b_451) ∗
     ((sp - 450#64) ↦₈ b_450) ∗ ((sp - 449#64) ↦₈ b_449) ∗
     ((sp - 448#64) ↦₈ b_448) ∗ ((sp - 447#64) ↦₈ b_447) ∗
     ((sp - 446#64) ↦₈ b_446) ∗ ((sp - 445#64) ↦₈ b_445) ∗
     ((sp - 444#64) ↦₈ b_444) ∗ ((sp - 443#64) ↦₈ b_443) ∗
     ((sp - 442#64) ↦₈ b_442) ∗ ((sp - 441#64) ↦₈ b_441) ∗
     ((sp - 440#64) ↦₆₄ w_440) ∗ ((sp - 432#64) ↦₃₂ d_432) ∗
     ((sp - 428#64) ↦₈ b_428) ∗ ((sp - 427#64) ↦₃₂ d_427) ∗
     memRegion (sp - 423#64) 127) ⊢
      memRegion (sp - 456#64) 160 := by
  sep_interval

theorem stack_184_24_split_some (sp : BitVec 64) :
    memRegion (sp - 184#64) 24 =
      (∃∗ t_184 : BitVec 8, (sp - 184#64) ↦₈ t_184) ∗
      (∃∗ t_183 : BitVec 8, (sp - 183#64) ↦₈ t_183) ∗
      (∃∗ t_182 : BitVec 8, (sp - 182#64) ↦₈ t_182) ∗
      (∃∗ t_181 : BitVec 8, (sp - 181#64) ↦₈ t_181) ∗
      (∃∗ t_180 : BitVec 8, (sp - 180#64) ↦₈ t_180) ∗
      (∃∗ t_179 : BitVec 8, (sp - 179#64) ↦₈ t_179) ∗
      (∃∗ t_178 : BitVec 8, (sp - 178#64) ↦₈ t_178) ∗
      (∃∗ t_177 : BitVec 8, (sp - 177#64) ↦₈ t_177) ∗
      (∃∗ t_176 : BitVec 8, (sp - 176#64) ↦₈ t_176) ∗
      (∃∗ t_175 : BitVec 8, (sp - 175#64) ↦₈ t_175) ∗
      (∃∗ t_174 : BitVec 8, (sp - 174#64) ↦₈ t_174) ∗
      (∃∗ t_173 : BitVec 8, (sp - 173#64) ↦₈ t_173) ∗
      (∃∗ t_172 : BitVec 8, (sp - 172#64) ↦₈ t_172) ∗
      (∃∗ t_171 : BitVec 8, (sp - 171#64) ↦₈ t_171) ∗
      (∃∗ t_170 : BitVec 8, (sp - 170#64) ↦₈ t_170) ∗
      (∃∗ t_169 : BitVec 8, (sp - 169#64) ↦₈ t_169) ∗
      (∃∗ t_168 : BitVec 8, (sp - 168#64) ↦₈ t_168) ∗
      (∃∗ t_167 : BitVec 8, (sp - 167#64) ↦₈ t_167) ∗
      (∃∗ t_166 : BitVec 8, (sp - 166#64) ↦₈ t_166) ∗
      memRegion (sp - 165#64) 1 ∗
      (∃∗ t_164 : BitVec 16, (sp - 164#64) ↦₁₆ t_164) ∗
      (∃∗ t_162 : BitVec 8, (sp - 162#64) ↦₈ t_162) ∗
      memRegion (sp - 161#64) 1 := by
  sep_interval_eq

theorem stack_184_24_fold_some (sp : BitVec 64)
    (t_184 t_183 t_182 t_181 t_180 t_179 t_178 t_177
     t_176 t_175 t_174 t_173 t_172 t_171 t_170 t_169
     t_168 t_167 t_166 : BitVec 8)
    (t_164 : BitVec 16) (t_162 : BitVec 8) :
    (((sp - 184#64) ↦₈ t_184) ∗ ((sp - 183#64) ↦₈ t_183) ∗
     ((sp - 182#64) ↦₈ t_182) ∗ ((sp - 181#64) ↦₈ t_181) ∗
     ((sp - 180#64) ↦₈ t_180) ∗ ((sp - 179#64) ↦₈ t_179) ∗
     ((sp - 178#64) ↦₈ t_178) ∗ ((sp - 177#64) ↦₈ t_177) ∗
     ((sp - 176#64) ↦₈ t_176) ∗ ((sp - 175#64) ↦₈ t_175) ∗
     ((sp - 174#64) ↦₈ t_174) ∗ ((sp - 173#64) ↦₈ t_173) ∗
     ((sp - 172#64) ↦₈ t_172) ∗ ((sp - 171#64) ↦₈ t_171) ∗
     ((sp - 170#64) ↦₈ t_170) ∗ ((sp - 169#64) ↦₈ t_169) ∗
     ((sp - 168#64) ↦₈ t_168) ∗ ((sp - 167#64) ↦₈ t_167) ∗
     ((sp - 166#64) ↦₈ t_166) ∗ memRegion (sp - 165#64) 1 ∗
     ((sp - 164#64) ↦₁₆ t_164) ∗ ((sp - 162#64) ↦₈ t_162) ∗
     memRegion (sp - 161#64) 1) ⊢
      memRegion (sp - 184#64) 24 := by
  sep_interval

theorem trFromGhost_model_fst (x : TrFromGhost) :
    x.model.1 =
      match x.st.remoteIdentity with
      | some rem =>
        .ok ⟨⟨x.st.rootKey, x.st.senderChain, x.st.receiverChains,
              x.st.previousCounter, maxForwardJumps⟩,
             x.st.pqRatchetState, x.st.localIdentity, rem⟩
      | none => .error (.invalidSessionStructure .missingRemoteIdentity) := by
  rcases x with ⟨ss, G, ⟨sv, lik, rik, rk, pc, sc, rcs, ppk, pqr⟩, ret⟩
  cases rik <;> rfl

end ReceiveRatchetFrom
end CryptoVerification.LibsignalTripleRatchet
