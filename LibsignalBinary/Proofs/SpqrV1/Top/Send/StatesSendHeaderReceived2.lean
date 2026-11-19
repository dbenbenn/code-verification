/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendHeaderReceived1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampled3 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2Encoder
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOk

/-!
# `spqr::send::<HookRng>`: Inlined `States::send` `.headerReceived` Arm (Part 2: `+1680..+3068`)

**Checked by Lean.**

Verifies `+1680..+3068` (`PolyEncoder::encode_bytes`, `next_chunk`, and state/chunk
relocation) and assembles `step_send_arm_headerReceived` (`0x30d7c -> 0x31458`).
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

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero

theorem encodeBytesResult_ct1 (ct1 : List.Vector (BitVec 8) 960) :
    ∃ enc : PolyEncoder,
      encodeBytesResult ct1.toList = .ok enc ∧
      expectEncodeBytes spqrPolyApi "v1/chunked/send_ct.rs:131" ct1.toList = .ok enc := by
  have h960 : ct1.toList.length = 960 := List.Vector.toList_length _
  obtain ⟨enc, h1, _, h2⟩ := encodeBytesResult_of_len_even_le
    (msg := ct1.toList) (by omega) (by omega)
  exact ⟨enc, h1, h2⟩

theorem send_ct1_chunk_ok_elim {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F))
    {tape tape' : Bytes}
    {outSt : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)}
    {chunk : Chunk}
    {ek : EpochSecret}
    (hsend : st.send_ct1_chunk K tape = .ok (outSt, chunk, ek, tape')) :
    ∃ (h32 : 32 ≤ tape.length)
      (ct1 : List.Vector (BitVec 8) 960)
      (es : List.Vector (BitVec 8) 2080)
      (ss : List.Vector (BitVec 8) 32)
      (sending_ct1 : PolyEncoder),
      let rand : List.Vector (BitVec 8) 32 := ⟨tape.take 32, by rw [List.length_take]; omega⟩
      let info := sckaKeyInfoPrefix ++ epochBeBytes st.uc.epoch
      let secret := hkdfToVecUnchecked F (List.replicate 32 0#8) ss.toList info 32
      let auth' := st.uc.auth.update F st.uc.epoch secret
      K.encaps1 st.uc.hdr rand = some (ct1, es, ss) ∧
      encodeBytesResult ct1.toList = .ok sending_ct1 ∧
      sending_ct1.nextChunk = .ok (outSt.sending_ct1, chunk) ∧
      outSt.uc = { epoch := st.uc.epoch, auth := auth', hdr := st.uc.hdr, es := es.toList, ct1 := ct1.toList } ∧
      outSt.receiving_ek = st.receiving_ek ∧
      ek = { epoch := st.uc.epoch, secret := secret } ∧
      tape' = tape.drop 32 := by
  have h32 : 32 ≤ tape.length := by
    apply Classical.byContradiction
    intro hlt
    rw [send_ct1_chunk_of_lt_32 K st (by omega)] at hsend
    cases hsend
  refine ⟨h32, ?_⟩
  let rand : List.Vector (BitVec 8) 32 := ⟨tape.take 32, by rw [List.length_take]; omega⟩
  cases hencaps : K.encaps1 st.uc.hdr rand with
  | none =>
    rw [send_ct1_chunk_of_encaps1_none K st h32 hencaps] at hsend
    cases hsend
  | some triple =>
    rcases triple with ⟨ct1, es, ss⟩
    obtain ⟨sending_ct1, henc_res, henc_exp⟩ := encodeBytesResult_ct1 ct1
    refine ⟨ct1, es, ss, sending_ct1, hencaps, henc_res, ?_⟩
    cases hnc : sending_ct1.nextChunk with
    | error p =>
      rw [send_ct1_chunk_of_nextChunk_err K st h32 hencaps henc_exp hnc] at hsend
      cases hsend
    | ok pair =>
      rcases pair with ⟨sending_ct1', chunk'⟩
      have hok := send_ct1_chunk_of_ok K st h32 hencaps henc_exp hnc
      dsimp only at hok
      rw [hok] at hsend
      injection hsend with htuple
      injection htuple with hout hrest1
      injection hrest1 with hch hrest2
      injection hrest2 with hek htp
      have hsnd : sending_ct1' = outSt.sending_ct1 :=
        congrArg Chunked.SendCt.Ct1Sampled.sending_ct1 hout
      have huc : _ = outSt.uc :=
        congrArg Chunked.SendCt.Ct1Sampled.uc hout
      have hrek : st.receiving_ek = outSt.receiving_ek :=
        congrArg Chunked.SendCt.Ct1Sampled.receiving_ek hout
      rw [← hsnd, ← huc, ← hrek, ← hch, ← hek, ← htp]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Sub-Step 3 (`entry + 1680#64 -> entry + 1896#64`) -/

theorem memRegion_961_split_48_913 (sp : BitVec 64) :
    memRegion (sp + 4704#64) 961 =
      (∃∗ d0 : BitVec 64, (sp + 4704#64) ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (sp + 4712#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (sp + 4720#64) ↦₆₄ d2) ∗
      (∃∗ d3 : BitVec 64, (sp + 4728#64) ↦₆₄ d3) ∗
      (∃∗ d4 : BitVec 64, (sp + 4736#64) ↦₆₄ d4) ∗
      (∃∗ d5 : BitVec 64, (sp + 4744#64) ↦₆₄ d5) ∗
      memRegion (sp + 4752#64) 913 := by
  rw [ProofLib.memRegion_split' (b := sp + 4704#64) (n := 48) (k := 913) (b' := sp + 4752#64) rfl (by bv_omega) (by decide),
      memRegion_48_eq_words6 (sp + 4704#64)]
  simp only [BitVec.add_assoc, arm64_norm]

theorem memRegion_4080_48_eq_words6 (sp : BitVec 64) :
    memRegion (sp + 4080#64) 48 =
      (∃∗ d0 : BitVec 64, (sp + 4080#64) ↦₆₄ d0) ∗ (∃∗ d1 : BitVec 64, (sp + 4088#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (sp + 4096#64) ↦₆₄ d2) ∗ (∃∗ d3 : BitVec 64, (sp + 4104#64) ↦₆₄ d3) ∗
      (∃∗ d4 : BitVec 64, (sp + 4112#64) ↦₆₄ d4) ∗ (∃∗ d5 : BitVec 64, (sp + 4120#64) ↦₆₄ d5) := by
  rw [memRegion_48_eq_words6 (sp + 4080#64)]; simp only [BitVec.add_assoc, arm64_norm]

theorem memRegion_7104_24_eq_words3 (sp : BitVec 64) :
    memRegion (sp + 7104#64) 24 =
      (∃∗ d0 : BitVec 64, (sp + 7104#64) ↦₆₄ d0) ∗ (∃∗ d1 : BitVec 64, (sp + 7112#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (sp + 7120#64) ↦₆₄ d2) := by
  rw [memRegion_24_eq_words3 (sp + 7104#64)]; simp only [BitVec.add_assoc, arm64_norm]

theorem fold_7536_to_memRegion_400 (sp w0 w1 w2 : BitVec 64) :
    ((sp + 7536#64) ↦₆₄ w0) ∗ ((sp + 7544#64) ↦₆₄ w1) ∗ ((sp + 7552#64) ↦₆₄ w2) ∗
    memRegion (sp + 7560#64) 8 ∗ memRegion (sp + 7568#64) 368 ⊢
    memRegion (sp + 7536#64) 400 := by
  have h24 := words3_entails_memRegion (sp + 7536#64) w0 w1 w2
  simp only [BitVec.add_assoc, arm64_norm] at h24
  rw [ProofLib.memRegion_split' (b := sp + 7536#64) (n := 24) (k := 376) (b' := sp + 7560#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7560#64) (n := 8) (k := 368) (b' := sp + 7568#64) rfl (by bv_omega) (by decide)]
  exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono h24 (Entails.refl _))

theorem fold_4080_and_4704 (sp : BitVec 64) (g : AuthenticatorGhost) (auth : Authenticator) :
    ((sp + 4080#64) ↦₆₄ g.rootKey.cap) ∗ ((sp + 4088#64) ↦₆₄ g.rootKey.ptr) ∗
    ((sp + 4096#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
    ((sp + 4104#64) ↦₆₄ g.macKey.cap) ∗ ((sp + 4112#64) ↦₆₄ g.macKey.ptr) ∗
    ((sp + 4120#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
    ((sp + 4704#64) ↦₆₄ g.rootKey.cap) ∗ ((sp + 4712#64) ↦₆₄ g.rootKey.ptr) ∗
    ((sp + 4720#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
    ((sp + 4728#64) ↦₆₄ g.macKey.cap) ∗ ((sp + 4736#64) ↦₆₄ g.macKey.ptr) ∗
    ((sp + 4744#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
    memRegion (sp + 4752#64) 913 ∗ memRegion (sp + 5665#64) 1439 ⊢
    authInlineWordsAt g (sp + 4080#64) auth ∗ memRegion (sp + 4704#64) 928 ∗
    memRegion (sp + 5632#64) 34 ∗ memRegion (sp + 5666#64) 1438 := by
  have h48 := authInlineWordsAt_entails_memRegion g (sp + 4704#64) auth
  have h2400 : memRegion (sp + 4704#64) 48 ∗ (memRegion (sp + 4752#64) 913 ∗ memRegion (sp + 5665#64) 1439) =
      memRegion (sp + 4704#64) 928 ∗ memRegion (sp + 5632#64) 34 ∗ memRegion (sp + 5666#64) 1438 := by
    rw [← ProofLib.memRegion_split' (b := sp + 4752#64) (n := 913) (k := 1439) (b' := sp + 5665#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := sp + 4704#64) (n := 48) (k := 2352) (b' := sp + 4752#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 4704#64) (n := 928) (k := 1472) (b' := sp + 5632#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 5632#64) (n := 34) (k := 1438) (b' := sp + 5666#64) rfl (by bv_omega) (by decide)]
  rw [← h2400]
  have h4080 : authInlineWordsAt g (sp + 4080#64) auth =
      ((sp + 4080#64) ↦₆₄ g.rootKey.cap) ∗ ((sp + 4088#64) ↦₆₄ g.rootKey.ptr) ∗
      ((sp + 4096#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      ((sp + 4104#64) ↦₆₄ g.macKey.cap) ∗ ((sp + 4112#64) ↦₆₄ g.macKey.ptr) ∗
      ((sp + 4120#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) := by
    dsimp only [authInlineWordsAt]; simp only [BitVec.add_assoc, arm64_norm, sepConj_assoc]
  have h4704 : authInlineWordsAt g (sp + 4704#64) auth =
      ((sp + 4704#64) ↦₆₄ g.rootKey.cap) ∗ ((sp + 4712#64) ↦₆₄ g.rootKey.ptr) ∗
      ((sp + 4720#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      ((sp + 4728#64) ↦₆₄ g.macKey.cap) ∗ ((sp + 4736#64) ↦₆₄ g.macKey.ptr) ∗
      ((sp + 4744#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) := by
    dsimp only [authInlineWordsAt]; simp only [BitVec.add_assoc, arm64_norm, sepConj_assoc]
  rw [h4080]
  refine Entails.trans (Entails.of_eq ?_) (sepConj_mono_right (sepConj_mono_left h48))
  rw [h4704]; ac_rfl

theorem Relocatable.of_authenticatorAt (A : RustAlloc) (auth : Authenticator) :
    Relocatable 48 (fun a => authenticatorAt A a auth) := by
  intro src
  refine Entails.trans (authenticatorAt_extract A src auth) ?_
  apply ProofLib.Entails.sepExists_elim; intro g
  rw [wordsAt_eq_pointsToBytes]
  refine Entails.sepExists_right (wordsBytes (authWordsList g)) ?_
  have hlen : (wordsBytes (authWordsList g)).length = 48 := by
    rw [length_wordsBytes, length_authWordsList]
  exact Entails.pure_right hlen (Entails.refl _)

theorem Relocatable.of_polyEncoder_and_auth (A : RustAlloc) (enc : PolyEncoder) (auth : Authenticator) :
    Relocatable 448 (fun a => polyEncoderAt A a enc ∗ authenticatorAt A (a + 400#64) auth) :=
  Relocatable.sepConj (off := 400#64) (m := 448) rfl rfl
    (Relocatable.of_polyEncoderAt A enc) (Relocatable.of_authenticatorAt A auth)

theorem live_pointsTo_entails_vecU8 {A : RustAlloc} (a cap ptr : BitVec 64) (bs : Bytes)
    (hlen : bs.length = cap.toNat) (hpos : 0 < cap.toNat) (hlt : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ cap) ∗
    A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ⊢
    vecU8 A a bs := by
  have hlen_bv : BitVec.ofNat 64 bs.length = cap := by simp [hlen]
  refine Entails.trans (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
    (sepConj_mono (Entails.refl _) ?_))) (fold_vecU8_of_inline a cap ptr cap bs hlen_bv)
  unfold RustHeap.vecU8Buf
  have hc : cap ≠ 0 := by intro h0; subst h0; revert hpos; decide
  simp only [hlen, hc, ↓reduceIte, Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp]
  exact Entails.pure_right ⟨Nat.le_refl _, hlt, hptr⟩ (Entails.refl _)

theorem fold_chunkedCt1SampledAt_4704 {F : ShaCompress} {A : RustAlloc}
    (sp epoch hdr_cap hdr_ptr es_ptr ct1_ptr : BitVec 64)
    (auth' : Authenticator) (hdr : Bytes)
    (es : List.Vector (BitVec 8) 2080) (ct1 : List.Vector (BitVec 8) 960)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F))
    (outSt : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (huc : outSt.uc = { epoch := epoch, auth := auth', hdr := hdr, es := es.toList, ct1 := ct1.toList })
    (hrek : outSt.receiving_ek = st.receiving_ek)
    (hct1_ne : ct1_ptr ≠ 0) :
    polyEncoderAt A (sp + 4704#64) outSt.sending_ct1 ∗
    authenticatorAt A (sp + 5104#64) auth' ∗
    (((sp + 5152#64) ↦₆₄ hdr_cap) ∗ ((sp + 5160#64) ↦₆₄ hdr_ptr) ∗
     ((sp + 5168#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ (hdr_ptr ↦ₛ hdr) ∗ vecU8Rest A hdr_cap hdr_ptr hdr) ∗
    (((sp + 5176#64) ↦₆₄ 2080#64) ∗ ((sp + 5184#64) ↦₆₄ es_ptr) ∗ ((sp + 5192#64) ↦₆₄ 2080#64) ∗
     RustHeap.vecU8Buf A 2080#64 es_ptr es.toList) ∗
    (((sp + 5200#64) ↦₆₄ 960#64) ∗ ((sp + 5208#64) ↦₆₄ ct1_ptr) ∗ ((sp + 5216#64) ↦₆₄ 960#64) ∗
     A.live ct1_ptr 960 1 ∗ (ct1_ptr ↦ₛ ct1.toList)) ∗
    ((sp + 5224#64) ↦₆₄ epoch) ∗
    polyDecoderAt A (sp + 5232#64) st.receiving_ek ⊢
    ((sp + 4704#64) ↦₆₄ polyEncoderTagVal outSt.sending_ct1.s) ∗
    chunkedCt1SampledTail920At A (sp + 4712#64) outSt := by
  rw [← show (sp + 4704#64) + 8#64 = sp + 4712#64 by bv_omega,
      ← chunkedCt1SampledAt_eq_tag_tail920 A (sp + 4704#64) outSt]
  unfold chunkedCt1SampledAt unchunkedCt1SentAt
  rw [huc, hrek]
  have hhdr := vecU8_fold_rest (A := A) (sp + 5152#64) hdr_cap hdr_ptr hdr
  have hes := fold_vecU8_of_inline (A := A) (sp + 5176#64) 2080#64 es_ptr 2080#64 es.toList
    (by rw [List.Vector.toList_length])
  have hct1 := live_pointsTo_entails_vecU8 (A := A) (sp + 5200#64) 960#64 ct1_ptr ct1.toList
    (List.Vector.toList_length ct1) (by decide) (by decide) hct1_ne
  simp only [BitVec.add_assoc, arm64_norm] at hhdr hes hct1
  refine Entails.trans (sepConj_mono (Entails.refl _)
    (sepConj_mono (Entails.refl _)
      (sepConj_mono hhdr (sepConj_mono hes (sepConj_mono hct1 (Entails.refl _)))))) ?_
  simp only [BitVec.add_assoc, arm64_norm]
  exact Entails.of_eq (by ac_rfl)

theorem chunkAt_5632_4192_1360_eq (sp : BitVec 64) (chunk : Chunk) (cw0 cw1 cw2 cw3 : BitVec 64)
    (hchunk : ∀ a : BitVec 64, chunkAt a chunk =
      (a ↦₆₄ cw0) ∗ ((a + 8#64) ↦₆₄ cw1) ∗ ((a + 16#64) ↦₆₄ cw2) ∗ ((a + 24#64) ↦₆₄ cw3) ∗ ((a + 32#64) ↦₁₆ chunk.index)) :
    chunkAt (sp + 5632#64) chunk =
      ((sp + 5632#64) ↦₆₄ cw0) ∗ ((sp + 5640#64) ↦₆₄ cw1) ∗ ((sp + 5648#64) ↦₆₄ cw2) ∗ ((sp + 5656#64) ↦₆₄ cw3) ∗ ((sp + 5664#64) ↦₁₆ chunk.index) ∧
    chunkAt (sp + 4192#64) chunk =
      ((sp + 4192#64) ↦₆₄ cw0) ∗ ((sp + 4200#64) ↦₆₄ cw1) ∗ ((sp + 4208#64) ↦₆₄ cw2) ∗ ((sp + 4216#64) ↦₆₄ cw3) ∗ ((sp + 4224#64) ↦₁₆ chunk.index) ∧
    chunkAt (sp + 1360#64) chunk =
      ((sp + 1360#64) ↦₆₄ cw0) ∗ ((sp + 1368#64) ↦₆₄ cw1) ∗ ((sp + 1376#64) ↦₆₄ cw2) ∗ ((sp + 1384#64) ↦₆₄ cw3) ∗ ((sp + 1392#64) ↦₁₆ chunk.index) :=
  ⟨chunkAt_sp_add_eq sp 5632#64 5640#64 5648#64 5656#64 5664#64 chunk cw0 cw1 cw2 cw3 hchunk,
   chunkAt_sp_add_eq sp 4192#64 4200#64 4208#64 4216#64 4224#64 chunk cw0 cw1 cw2 cw3 hchunk,
   chunkAt_sp_add_eq sp 1360#64 1368#64 1376#64 1384#64 1392#64 chunk cw0 cw1 cw2 cw3 hchunk⟩

theorem memRegion_4192_merge_400 (sp : BitVec 64) :
    memRegion (sp + 4192#64) 48 ∗ memRegion (sp + 4240#64) 352 = memRegion (sp + 4192#64) 400 :=
  (ProofLib.memRegion_split' (b := sp + 4192#64) (n := 48) (k := 352) (b' := sp + 4240#64) rfl (by bv_omega) (by decide)).symm

theorem memRegion_4704_928_split (sp : BitVec 64) :
    memRegion (sp + 4704#64) 928 =
      memRegion (sp + 4704#64) 448 ∗ memRegion (sp + 5152#64) 80 ∗ memRegion (sp + 5232#64) 400 := by
  rw [ProofLib.memRegion_split' (b := sp + 4704#64) (n := 448) (k := 480) (b' := sp + 5152#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 5152#64) (n := 80) (k := 400) (b' := sp + 5232#64) rfl (by bv_omega) (by decide)]

theorem memRegion_5666_1438_split (sp : BitVec 64) :
    memRegion (sp + 5666#64) 1438 =
      memRegion (sp + 5666#64) 6 ∗ memRegion (sp + 5672#64) 32 ∗ memRegion (sp + 5704#64) 1400 := by
  rw [ProofLib.memRegion_split' (b := sp + 5666#64) (n := 6) (k := 1432) (b' := sp + 5672#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 5672#64) (n := 32) (k := 1400) (b' := sp + 5704#64) rfl (by bv_omega) (by decide)]

theorem memRegion_5152_80_eq_words10 (sp : BitVec 64) :
    memRegion (sp + 5152#64) 80 =
      (∃∗ d0 : BitVec 64, (sp + 5152#64) ↦₆₄ d0) ∗ (∃∗ d1 : BitVec 64, (sp + 5160#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (sp + 5168#64) ↦₆₄ d2) ∗ (∃∗ d3 : BitVec 64, (sp + 5176#64) ↦₆₄ d3) ∗
      (∃∗ d4 : BitVec 64, (sp + 5184#64) ↦₆₄ d4) ∗ (∃∗ d5 : BitVec 64, (sp + 5192#64) ↦₆₄ d5) ∗
      (∃∗ d6 : BitVec 64, (sp + 5200#64) ↦₆₄ d6) ∗ (∃∗ d7 : BitVec 64, (sp + 5208#64) ↦₆₄ d7) ∗
      (∃∗ d8 : BitVec 64, (sp + 5216#64) ↦₆₄ d8) ∗ (∃∗ d9 : BitVec 64, (sp + 5224#64) ↦₆₄ d9) := by
  rw [ProofLib.memRegion_split' (b := sp + 5152#64) (n := 64) (k := 16) (b' := sp + 5216#64) rfl (by bv_omega) (by decide),
      memRegion_64_eq_words8 (sp + 5152#64),
      ProofLib.memRegion_split' (b := sp + 5216#64) (n := 8) (k := 8) (b' := sp + 5224#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 5216#64), ProofLib.memRegion_eight (sp + 5224#64)]
  simp only [BitVec.add_assoc, arm64_norm, sepConj_assoc]

theorem memRegion_5672_32_eq_words4 (sp : BitVec 64) :
    memRegion (sp + 5672#64) 32 =
      (∃∗ d0 : BitVec 64, (sp + 5672#64) ↦₆₄ d0) ∗ (∃∗ d1 : BitVec 64, (sp + 5680#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (sp + 5688#64) ↦₆₄ d2) ∗ (∃∗ d3 : BitVec 64, (sp + 5696#64) ↦₆₄ d3) := by
  rw [memRegion_32_eq_words4 (sp + 5672#64)]; simp only [BitVec.add_assoc, arm64_norm, sepConj_assoc]

theorem memRegion_4592_48_eq_words6 (sp : BitVec 64) :
    memRegion (sp + 4592#64) 48 =
      (∃∗ d0 : BitVec 64, (sp + 4592#64) ↦₆₄ d0) ∗ (∃∗ d1 : BitVec 64, (sp + 4600#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (sp + 4608#64) ↦₆₄ d2) ∗ (∃∗ d3 : BitVec 64, (sp + 4616#64) ↦₆₄ d3) ∗
      (∃∗ d4 : BitVec 64, (sp + 4624#64) ↦₆₄ d4) ∗ (∃∗ d5 : BitVec 64, (sp + 4632#64) ↦₆₄ d5) := by
  rw [memRegion_48_eq_words6 (sp + 4592#64)]; simp only [BitVec.add_assoc, arm64_norm, sepConj_assoc]

theorem memRegion_448_expose_chunk_slot (sp : BitVec 64) :
    memRegion (sp + 4192#64) 448 =
      (∃∗ d0 : BitVec 64, (sp + 4192#64) ↦₆₄ d0) ∗ (∃∗ d1 : BitVec 64, (sp + 4200#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (sp + 4208#64) ↦₆₄ d2) ∗ (∃∗ d3 : BitVec 64, (sp + 4216#64) ↦₆₄ d3) ∗
      (∃∗ d4 : BitVec 16, (sp + 4224#64) ↦₁₆ d4) ∗ memRegion (sp + 4226#64) 414 := by
  rw [ProofLib.memRegion_split' (b := sp + 4192#64) (n := 8) (k := 440) (b' := sp + 4200#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4200#64) (n := 8) (k := 432) (b' := sp + 4208#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4208#64) (n := 8) (k := 424) (b' := sp + 4216#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4216#64) (n := 8) (k := 416) (b' := sp + 4224#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4224#64) (n := 2) (k := 414) (b' := sp + 4226#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 4192#64), ProofLib.memRegion_eight (sp + 4200#64),
      ProofLib.memRegion_eight (sp + 4208#64), ProofLib.memRegion_eight (sp + 4216#64),
      ProofLib.memRegion_two (sp + 4224#64)]

theorem memRegion_4064_16_eq_words2 (sp : BitVec 64) :
    memRegion (sp + 4064#64) 16 =
      (∃∗ d0 : BitVec 64, (sp + 4064#64) ↦₆₄ d0) ∗ (∃∗ d1 : BitVec 64, (sp + 4072#64) ↦₆₄ d1) := by
  rw [ProofLib.memRegion_split' (b := sp + 4064#64) (n := 8) (k := 8) (b' := sp + 4072#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 4064#64), ProofLib.memRegion_eight (sp + 4072#64)]

theorem memRegion_1408_16_eq_words2 (sp : BitVec 64) :
    memRegion (sp + 1408#64) 16 =
      (∃∗ d0 : BitVec 64, (sp + 1408#64) ↦₆₄ d0) ∗ (∃∗ d1 : BitVec 64, (sp + 1416#64) ↦₆₄ d1) := by
  rw [ProofLib.memRegion_split' (b := sp + 1408#64) (n := 8) (k := 8) (b' := sp + 1416#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 1408#64), ProofLib.memRegion_eight (sp + 1416#64)]

theorem fold_headerReceived_step5_regions (sp : BitVec 64) (chunk : Chunk)
    (w_tag w_4064 w_4072 w_5672 w_5680 w_5688 w_5696 w_7104 w_7112 w_7120 : BitVec 64) :
    (((sp + 4064#64) ↦₆₄ w_4064) ∗ ((sp + 4072#64) ↦₆₄ w_4072)) ∗
    (chunkAt (sp + 4192#64) chunk ∗ memRegion (sp + 4226#64) 414) ∗
    (((sp + 4704#64) ↦₆₄ w_tag) ∗ memRegion (sp + 4712#64) 920 ∗
     chunkAt (sp + 5632#64) chunk ∗ memRegion (sp + 5666#64) 6 ∗
     (((sp + 5672#64) ↦₆₄ w_5672) ∗ ((sp + 5680#64) ↦₆₄ w_5680) ∗
      ((sp + 5688#64) ↦₆₄ w_5688) ∗ ((sp + 5696#64) ↦₆₄ w_5696)) ∗
     memRegion (sp + 5704#64) 1400) ∗
    (((sp + 7104#64) ↦₆₄ w_7104) ∗ ((sp + 7112#64) ↦₆₄ w_7112) ∗ ((sp + 7120#64) ↦₆₄ w_7120)) ⊢
    memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4192#64) 448 ∗
    memRegion (sp + 4704#64) 2400 ∗ memRegion (sp + 7104#64) 24 := by
  have h4064 : ((sp + 4064#64) ↦₆₄ w_4064) ∗ ((sp + 4072#64) ↦₆₄ w_4072) ⊢ memRegion (sp + 4064#64) 16 := by
    rw [ProofLib.memRegion_split' (b := sp + 4064#64) (n := 8) (k := 8) (b' := sp + 4072#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) (ProofLib.pointsTo64_entails_memRegion _ _)
  have h4192 : chunkAt (sp + 4192#64) chunk ∗ memRegion (sp + 4226#64) 414 ⊢ memRegion (sp + 4192#64) 448 := by
    rw [ProofLib.memRegion_split' (b := sp + 4192#64) (n := 34) (k := 414) (b' := sp + 4226#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (chunkAt_entails_memRegion _ _)
  have h5672 := words4At_entails_memRegion (sp + 5672#64) w_5672 w_5680 w_5688 w_5696
  dsimp only [words4At] at h5672; simp only [BitVec.add_assoc, arm64_norm, sepConj_assoc] at h5672
  have h4704 :
      ((sp + 4704#64) ↦₆₄ w_tag) ∗ memRegion (sp + 4712#64) 920 ∗
      chunkAt (sp + 5632#64) chunk ∗ memRegion (sp + 5666#64) 6 ∗
      (((sp + 5672#64) ↦₆₄ w_5672) ∗ ((sp + 5680#64) ↦₆₄ w_5680) ∗
       ((sp + 5688#64) ↦₆₄ w_5688) ∗ ((sp + 5696#64) ↦₆₄ w_5696)) ∗
      memRegion (sp + 5704#64) 1400 ⊢ memRegion (sp + 4704#64) 2400 := by
    rw [ProofLib.memRegion_split' (b := sp + 4704#64) (n := 8) (k := 2392) (b' := sp + 4712#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 4712#64) (n := 920) (k := 1472) (b' := sp + 5632#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 5632#64) (n := 34) (k := 1438) (b' := sp + 5666#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 5666#64) (n := 6) (k := 1432) (b' := sp + 5672#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 5672#64) (n := 32) (k := 1400) (b' := sp + 5704#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (Entails.refl _) (sepConj_mono (chunkAt_entails_memRegion _ _)
        (sepConj_mono (Entails.refl _) (sepConj_mono h5672 (Entails.refl _)))))
  have h7104 := words3_7104_entails_memRegion sp w_7104 w_7112 w_7120
  exact sepConj_mono h4064 (sepConj_mono h4192 (sepConj_mono h4704 h7104))

theorem chunkedStatesAt_headerReceived_expose {F : ShaCompress} {A : RustAlloc}
    (sp : BitVec 64) (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    chunkedStatesAt A (sp + 0x950#64) (.headerReceived st) ⊢
    ∃∗ g : AuthenticatorGhost, ∃∗ hdr_cap : BitVec 64, ∃∗ hdr_ptr : BitVec 64,
      ⌜st.uc.hdr.length < 2 ^ 63⌝ ∗
      (((sp + 0x950#64) ↦₆₄ 8#64) ∗
       authInlineWordsAt g (sp + 2392#64) st.uc.auth ∗ authHeapBufs A g st.uc.auth ∗
       ((sp + 2440#64) ↦₆₄ hdr_cap) ∗ ((sp + 2448#64) ↦₆₄ hdr_ptr) ∗
       ((sp + 2456#64) ↦₆₄ BitVec.ofNat 64 st.uc.hdr.length) ∗
       (hdr_ptr ↦ₛ st.uc.hdr) ∗ vecU8Rest A hdr_cap hdr_ptr st.uc.hdr ∗
       ((sp + 2464#64) ↦₆₄ st.uc.epoch) ∗
       polyDecoderAt A (sp + 2472#64) st.receiving_ek ∗ memRegion (sp + 2872#64) 440) := by
  rw [chunkedStatesAt_eq_word0_tail920 A (sp + 0x950#64) (.headerReceived st)]
  dsimp only [chunkedStatesWord0, chunkedStatesTail920At, chunkedHeaderReceivedAt, unchunkedHeaderReceivedAt]
  have hauth := authenticatorAt_entails_exists_inline_heap A (sp + 2392#64) st.uc.auth
  have hhdr : vecU8 A (sp + 2440#64) st.uc.hdr ⊢
      ∃∗ hdr_cap : BitVec 64, ∃∗ hdr_ptr : BitVec 64, ⌜st.uc.hdr.length < 2 ^ 63⌝ ∗
        (((sp + 2440#64) ↦₆₄ hdr_cap) ∗ ((sp + 2448#64) ↦₆₄ hdr_ptr) ∗
         ((sp + 2456#64) ↦₆₄ BitVec.ofNat 64 st.uc.hdr.length) ∗
         (hdr_ptr ↦ₛ st.uc.hdr) ∗ vecU8Rest A hdr_cap hdr_ptr st.uc.hdr) := by
    unfold vecU8
    apply ProofLib.Entails.sepExists_elim; intro cap; apply ProofLib.Entails.sepExists_elim; intro ptr
    refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
    have hex := vecU8At_expose_rest (A := A) (sp + 2440#64) cap ptr st.uc.hdr
    simp only [BitVec.add_assoc, arm64_norm] at hex ⊢; exact hex
  simp only [BitVec.add_assoc, arm64_norm] at hauth hhdr ⊢
  refine Entails.trans (sepConj_mono_right (sepConj_mono hauth (sepConj_mono_left hhdr))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply ProofLib.Entails.sepExists_elim; intro cap
  apply ProofLib.Entails.sepExists_elim; intro ptr
  apply ProofLib.Entails.sepExists_elim; intro g
  refine Entails.sepExists_right g (Entails.sepExists_right cap (Entails.sepExists_right ptr ?_))
  exact Entails.of_eq (by ac_rfl)

theorem fold_arm_headerReceived_950 {F : ShaCompress} (sp hdr_cap hdr_ptr : BitVec 64)
    (g : AuthenticatorGhost) (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    ((sp + 0x950#64) ↦₆₄ 8#64) ∗ authInlineWordsAt g (sp + 2392#64) st.uc.auth ∗
    (((sp + 2440#64) ↦₆₄ hdr_cap) ∗ ((sp + 2448#64) ↦₆₄ hdr_ptr) ∗
     ((sp + 2456#64) ↦₆₄ BitVec.ofNat 64 st.uc.hdr.length) ∗ ((sp + 2464#64) ↦₆₄ st.uc.epoch)) ∗
    memRegion (sp + 2472#64) 400 ∗ memRegion (sp + 2872#64) 440 ⊢
    memRegion (sp + 0x950#64) 928 := by
  have h1 := authInlineWordsAt_entails_memRegion g (sp + 2392#64) st.uc.auth
  have h2 := words4At_entails_memRegion (sp + 2440#64) hdr_cap hdr_ptr
    (BitVec.ofNat 64 st.uc.hdr.length) st.uc.epoch
  dsimp only [words4At] at h2; simp only [BitVec.add_assoc, arm64_norm] at h2
  have h480 : memRegion (sp + 2392#64) 48 ∗ memRegion (sp + 2440#64) 32 ∗
      memRegion (sp + 2472#64) 400 ∗ memRegion (sp + 2872#64) 440 = memRegion (sp + 0x958#64) 920 := by
    rw [ProofLib.memRegion_split' (b := sp + 0x958#64) (n := 48) (k := 872) (b' := sp + 2440#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 2440#64) (n := 32) (k := 840) (b' := sp + 2472#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 2472#64) (n := 400) (k := 440) (b' := sp + 2872#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (sepConj_mono_right (sepConj_mono h1 (sepConj_mono_left h2))) ?_
  rw [h480]; exact word0_tail920_entails_memRegion_928 sp 8#64

end CryptoVerification.SpqrV1.Top.Send
