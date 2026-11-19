/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2Encoder -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk` (`0x61768`)

**Checked by Lean.**

Verifies `keys_sampled_recv_ct1_chunk_ok_ext` (`0x61768`, 107 instructions) against
`keysSampledRecvCt1ChunkSpec A F`.
-/

public section

namespace CryptoVerification.SpqrV1.States.Leaves

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero

/-! ## 1. Instruction Decode Tree (`0x61768..0x61910`) -/

theorem keys_sampled_recv_ct1_chunk_ok_elim {F : ShaCompress}
    {st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)}
    {chunk : Chunk}
    {outSt : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)}
    (h : st.recv_ct1_chunk st.uc.epoch chunk = .ok outSt) :
    encodeBytesResult st.uc.ek = .ok outSt.sending_ek ∧
    st.uc.ek.length ≤ 1048576 ∧
    outSt = { uc := { epoch := st.uc.epoch, auth := st.uc.auth, dk := st.uc.dk },
              sending_ek := outSt.sending_ek,
              receiving_ct1 := addChunkTotal (emptyPolyDecoder 480) chunk } := by
  unfold Chunked.SendEk.KeysSampled.recv_ct1_chunk at h
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
  change (do
    let receivingCt1 ← expectDecoderNew spqrPolyApi "v1/chunked/send_ek.rs:88" 960
    let receivingCt1 ← spqrPolyApi.add_chunk receivingCt1 chunk
    let sendingEk ← expectEncodeBytes spqrPolyApi "v1/chunked/send_ek.rs:92" st.uc.ek
    Except.ok { uc := { epoch := st.uc.epoch, auth := st.uc.auth, dk := st.uc.dk },
                sending_ek := sendingEk, receiving_ct1 := receivingCt1 }) =
      Except.ok outSt at h
  rw [expectDecoderNew_960] at h
  cases henc : expectEncodeBytes spqrPolyApi "v1/chunked/send_ek.rs:92" st.uc.ek with
  | error e =>
    rw [henc] at h
    dsimp only [Bind.bind, Except.bind, spqrPolyApi, liftM, monadLift, MonadLift.monadLift,
      liftSpqrPanic] at h
    rw [addChunk_eq_ok (emptyPolyDecoder 480) chunk rfl] at h
    contradiction
  | ok enc' =>
    rw [henc] at h
    dsimp only [Bind.bind, Except.bind, spqrPolyApi, liftM, monadLift, MonadLift.monadLift,
      liftSpqrPanic] at h
    rw [addChunk_eq_ok (emptyPolyDecoder 480) chunk rfl] at h
    dsimp only [Except.mapError] at h
    injection h with h
    subst h
    obtain ⟨hres, hle⟩ := encodeBytesResult_of_expectEncodeBytes_ok henc
    exact ⟨hres, hle, rfl⟩

attribute [local irreducible] addChunkTotal emptyPolyDecoder

@[local arm64_norm, local wp_norm] theorem sp_sub_80_sub_896 (sp : BitVec 64) :
    (sp - 80#64) - 896#64 = sp - 976#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_976_add_896 (sp : BitVec 64) :
    (sp - 976#64) + 896#64 = sp - 80#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_sub_80 (sp : BitVec 64) :
    (sp - 80#64) - 80#64 = sp - 160#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_sub_16 (sp : BitVec 64) :
    (sp - 80#64) - 16#64 = sp - 96#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_16' (sp : BitVec 64) :
    (sp - 80#64) + 16#64 = sp - 64#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_24' (sp : BitVec 64) :
    (sp - 80#64) + 24#64 = sp - 56#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_32' (sp : BitVec 64) :
    (sp - 80#64) + 32#64 = sp - 48#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_40' (sp : BitVec 64) :
    (sp - 80#64) + 40#64 = sp - 40#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_48' (sp : BitVec 64) :
    (sp - 80#64) + 48#64 = sp - 32#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_56' (sp : BitVec 64) :
    (sp - 80#64) + 56#64 = sp - 24#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_64' (sp : BitVec 64) :
    (sp - 80#64) + 64#64 = sp - 16#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_72' (sp : BitVec 64) :
    (sp - 80#64) + 72#64 = sp - 8#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_80' (sp : BitVec 64) :
    (sp - 80#64) + 80#64 = sp := by bv_omega

theorem wordsAt_9 (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 : BitVec 64) :
    wordsAt a [w0, w1, w2, w3, w4, w5, w6, w7, w8] =
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
      ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗
      ((a + 64#64) ↦₆₄ w8) := by
  conv_lhs => rw [wordsAt]
  simp only [wordsAt_cons_off, wordsAt_nil, sepConj_emp,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl, show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl,
    show (24#64 + 8#64 : BitVec 64) = 32#64 from rfl, show (32#64 + 8#64 : BitVec 64) = 40#64 from rfl,
    show (40#64 + 8#64 : BitVec 64) = 48#64 from rfl, show (48#64 + 8#64 : BitVec 64) = 56#64 from rfl,
    show (56#64 + 8#64 : BitVec 64) = 64#64 from rfl]

theorem cells_9_unfold (a : BitVec 64) :
    memRegion a 72 ⊢
      ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5, ∃∗ v6, ∃∗ v7, ∃∗ v8,
        wordsAt a [v0, v1, v2, v3, v4, v5, v6, v7, v8] := by
  rw [ProofLib.memRegion_cells a 9 (by decide), ProofLib.cells_succ]
  simp only [wordsAt_9, cells_succ_off, ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_right,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl, show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl,
    show (24#64 + 8#64 : BitVec 64) = 32#64 from rfl, show (32#64 + 8#64 : BitVec 64) = 40#64 from rfl,
    show (40#64 + 8#64 : BitVec 64) = 48#64 from rfl, show (48#64 + 8#64 : BitVec 64) = 56#64 from rfl,
    show (56#64 + 8#64 : BitVec 64) = 64#64 from rfl]
  exact Entails.refl _

theorem stackAt_976_split (sp : BitVec 64) :
    stackAt sp keysSampledRecvCt1ChunkStack =
      memRegion (sp - 17920#64) 12640 ∗ stackAt (sp - 976#64) addChunkStack ∗
      memRegion (sp - 976#64) 8 ∗ memRegion (sp - 968#64) 8 ∗
      memRegion (sp - 960#64) 128 ∗ memRegion (sp - 832#64) 128 ∗ memRegion (sp - 704#64) 128 ∗
      memRegion (sp - 576#64) 8 ∗ memRegion (sp - 568#64) 1 ∗ memRegion (sp - 567#64) 7 ∗
      memRegion (sp - 560#64) 400 ∗
      memRegion (sp - 160#64) 72 ∗ memRegion (sp - 88#64) 8 ∗
      memRegion (sp - 80#64) 80 := by
  change memRegion (sp - 17920#64) 17920 =
    memRegion (sp - 17920#64) 12640 ∗ memRegion (sp - 976#64 - 4304#64) 4304 ∗ _
  have hsub : sp - 976#64 - 4304#64 = sp - 5280#64 := by bv_omega
  rw [hsub,
      ProofLib.memRegion_split' (b := sp - 17920#64) (n := 12640) (k := 5280) (b' := sp - 5280#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 5280#64) (n := 4304) (k := 976) (b' := sp - 976#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 976#64) (n := 8) (k := 968) (b' := sp - 968#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 968#64) (n := 8) (k := 960) (b' := sp - 960#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 960#64) (n := 128) (k := 832) (b' := sp - 832#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 832#64) (n := 128) (k := 704) (b' := sp - 704#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 704#64) (n := 128) (k := 576) (b' := sp - 576#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 576#64) (n := 8) (k := 568) (b' := sp - 568#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 568#64) (n := 1) (k := 567) (b' := sp - 567#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 567#64) (n := 7) (k := 560) (b' := sp - 560#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 560#64) (n := 400) (k := 160) (b' := sp - 160#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 160#64) (n := 72) (k := 88) (b' := sp - 88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 88#64) (n := 8) (k := 80) (b' := sp - 80#64) rfl (by bv_omega) (by decide)]

theorem stackAt_976_addChunk_to_encodeBytesX (sp : BitVec 64) :
    memRegion (sp - 17920#64) 12640 ∗ stackAt (sp - 976#64) addChunkStack ⊢
    stackAt (sp - 976#64) encodeBytesStackX := by
  change memRegion (sp - 17920#64) 12640 ∗ memRegion (sp - 976#64 - 4304#64) 4304 ⊢
    memRegion (sp - 976#64 - 16944#64) 16944
  have h1 : sp - 976#64 - 4304#64 = sp - 5280#64 := by bv_omega
  have h2 : sp - 976#64 - 16944#64 = sp - 17920#64 := by bv_omega
  rw [h1, h2, ← ProofLib.memRegion_split' (b := sp - 17920#64) (n := 12640) (k := 4304) (b' := sp - 5280#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem unchunkedHeaderSentAt_400_eq (A : RustAlloc) {F : ShaCompress}
    (stA : BitVec 64) (st : Unchunked.SendEk.HeaderSent (spqrAuthApi F)) :
    unchunkedHeaderSentAt A (stA + 400#64) st =
      authenticatorAt A (stA + 400#64) st.auth ∗
      vecU8 A (stA + 448#64) st.ek ∗
      vecU8 A (stA + 472#64) st.dk ∗
      ((stA + 496#64) ↦₆₄ st.epoch) := by
  unfold unchunkedHeaderSentAt
  simp only [BitVec.add_assoc, arm64_norm]

theorem stA_400_104_fold (stA : BitVec 64) (g : AuthWords)
    (ekCap ekPtr ekLen : BitVec 64) (gdk : VecWords) (ep : BitVec 64) :
    wordsAt (stA + 400#64) (authWordsList g) ∗
      ((stA + 448#64) ↦₆₄ ekCap) ∗ ((stA + 456#64) ↦₆₄ ekPtr) ∗ ((stA + 464#64) ↦₆₄ ekLen) ∗
      wordsAt (stA + 472#64) (vecWordsList gdk) ∗
      ((stA + 496#64) ↦₆₄ ep) ⊢
    memRegion (stA + 400#64) 104 := by
  have h1 : wordsAt (stA + 400#64) (authWordsList g) ⊢ memRegion (stA + 400#64) 48 :=
    wordsAt_entails_memRegion (authWordsList g) (stA + 400#64) 48 rfl
  have h2 :
      ((stA + 448#64) ↦₆₄ ekCap) ∗ ((stA + 456#64) ↦₆₄ ekPtr) ∗ ((stA + 464#64) ↦₆₄ ekLen) ⊢
      memRegion (stA + 448#64) 24 := by
    have heq :
        (((stA + 448#64) ↦₆₄ ekCap) ∗ ((stA + 456#64) ↦₆₄ ekPtr) ∗ ((stA + 464#64) ↦₆₄ ekLen)) =
        wordsAt (stA + 448#64) [ekCap, ekPtr, ekLen] := by
      simp only [wordsAt, wordsAt_cons_off, wordsAt_nil, sepConj_emp, BitVec.add_assoc, arm64_norm]
    rw [heq]; exact wordsAt_entails_memRegion [ekCap, ekPtr, ekLen] (stA + 448#64) 24 rfl
  have h3 : wordsAt (stA + 472#64) (vecWordsList gdk) ⊢ memRegion (stA + 472#64) 24 :=
    wordsAt_entails_memRegion (vecWordsList gdk) (stA + 472#64) 24 rfl
  have h4 : ((stA + 496#64) ↦₆₄ ep) ⊢ memRegion (stA + 496#64) 8 :=
    ProofLib.pointsTo64_entails_memRegion (stA + 496#64) ep
  have hreord :
      wordsAt (stA + 400#64) (authWordsList g) ∗
      ((stA + 448#64) ↦₆₄ ekCap) ∗ ((stA + 456#64) ↦₆₄ ekPtr) ∗ ((stA + 464#64) ↦₆₄ ekLen) ∗
      wordsAt (stA + 472#64) (vecWordsList gdk) ∗
      ((stA + 496#64) ↦₆₄ ep) =
      wordsAt (stA + 400#64) (authWordsList g) ∗
      (((stA + 448#64) ↦₆₄ ekCap) ∗ ((stA + 456#64) ↦₆₄ ekPtr) ∗ ((stA + 464#64) ↦₆₄ ekLen)) ∗
      wordsAt (stA + 472#64) (vecWordsList gdk) ∗
      ((stA + 496#64) ↦₆₄ ep) := by ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 h4))) ?_
  rw [← ProofLib.memRegion_split' (b := stA + 472#64) (n := 24) (k := 8) (b' := stA + 496#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := stA + 448#64) (n := 24) (k := 32) (b' := stA + 472#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := stA + 400#64) (n := 48) (k := 56) (b' := stA + 448#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem outA_headerSent_recompose (A : RustAlloc) {F : ShaCompress}
    (outA sp : BitVec 64)
    (auth : Authenticator) (dk : Bytes) (epoch : Epoch)
    (sending_ek : PolyEncoder) (receiving_ct1 : PolyDecoder)
    (outSt : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (hout : outSt = { uc := { epoch := epoch, auth := auth, dk := dk },
                      sending_ek := sending_ek, receiving_ct1 := receiving_ct1 })
    (g : AuthWords) (gdk : VecWords) :
    polyEncoderAt A outA sending_ek ∗
      wordsAt (outA + 400#64) (authWordsList g) ∗
      relocatedHeap (fun dst => authenticatorAt A dst auth) (wordsBytes (authWordsList g)) ∗
      wordsAt (outA + 448#64) (vecWordsList gdk) ∗
      relocatedHeap (fun dst => vecU8 A dst dk) (wordsBytes (vecWordsList gdk)) ∗
      ((outA + 472#64) ↦₆₄ epoch) ∗
      polyDecoderAt A (outA + 480#64) receiving_ct1 ∗
      wordsAt (sp - 160#64) (authWordsList g ++ vecWordsList gdk) ⊢
    chunkedHeaderSentAt A outA outSt ∗ memRegion (sp - 160#64) 72 := by
  subst hout
  have hauth :
      wordsAt (outA + 400#64) (authWordsList g) ∗
        relocatedHeap (fun dst => authenticatorAt A dst auth) (wordsBytes (authWordsList g)) ⊢
      authenticatorAt A (outA + 400#64) auth := by
    rw [wordsAt_eq_pointsToBytes]; exact relocatedHeap_recompose _ _ (outA + 400#64)
  have hdk :
      wordsAt (outA + 448#64) (vecWordsList gdk) ∗
        relocatedHeap (fun dst => vecU8 A dst dk) (wordsBytes (vecWordsList gdk)) ⊢
      vecU8 A (outA + 448#64) dk := by
    rw [wordsAt_eq_pointsToBytes]; exact relocatedHeap_recompose _ _ (outA + 448#64)
  have hsp72 :
      wordsAt (sp - 160#64) (authWordsList g ++ vecWordsList gdk) ⊢
      memRegion (sp - 160#64) 72 :=
    wordsAt_entails_memRegion (authWordsList g ++ vecWordsList gdk) (sp - 160#64) 72 rfl
  have huc_eq :
      unchunkedEkSentAt A (outA + 400#64) ({ epoch := epoch, auth := auth, dk := dk } : Unchunked.SendEk.EkSent (spqrAuthApi F)) =
        authenticatorAt A (outA + 400#64) auth ∗
        vecU8 A (outA + 448#64) dk ∗
        ((outA + 472#64) ↦₆₄ epoch) := by
    unfold unchunkedEkSentAt
    simp only [BitVec.add_assoc, arm64_norm]
  unfold chunkedHeaderSentAt
  rw [huc_eq]
  have hreord :
      polyEncoderAt A outA sending_ek ∗
      wordsAt (outA + 400#64) (authWordsList g) ∗
      relocatedHeap (fun dst => authenticatorAt A dst auth) (wordsBytes (authWordsList g)) ∗
      wordsAt (outA + 448#64) (vecWordsList gdk) ∗
      relocatedHeap (fun dst => vecU8 A dst dk) (wordsBytes (vecWordsList gdk)) ∗
      ((outA + 472#64) ↦₆₄ epoch) ∗
      polyDecoderAt A (outA + 480#64) receiving_ct1 ∗
      wordsAt (sp - 160#64) (authWordsList g ++ vecWordsList gdk) =
      (polyEncoderAt A outA sending_ek ∗
        ((wordsAt (outA + 400#64) (authWordsList g) ∗
          relocatedHeap (fun dst => authenticatorAt A dst auth) (wordsBytes (authWordsList g))) ∗
         (wordsAt (outA + 448#64) (vecWordsList gdk) ∗
          relocatedHeap (fun dst => vecU8 A dst dk) (wordsBytes (vecWordsList gdk))) ∗
         ((outA + 472#64) ↦₆₄ epoch)) ∗
        polyDecoderAt A (outA + 480#64) receiving_ct1) ∗
      wordsAt (sp - 160#64) (authWordsList g ++ vecWordsList gdk) := by ac_rfl
  rw [hreord]
  exact sepConj_mono
    (sepConj_mono_right (sepConj_mono_left (sepConj_mono hauth (sepConj_mono_left hdk))))
    hsp72

theorem stackAt_976_to_dropPoly16 (s0 : State) (w8 d56 : BitVec 64) :
    stackAt (s0.sp - 976#64) encodeBytesStackX ∗
      memRegion (s0.sp - 976#64) 8 ∗
      ((s0.sp - 968#64) ↦₆₄ w8) ∗
      memRegion (s0.sp - 960#64) 400 ∗
      memRegion (s0.sp - 560#64) 400 ∗
      memRegion (s0.sp - 160#64) 72 ∗
      memRegion (s0.sp - 88#64) 8 ∗
      sendCt2SavedCells s0 d56 ⊢
    memRegion (s0.sp - 17920#64) 13792 ∗ stackAt s0.sp dropGluePoly16Stack := by
  have hw8 := ProofLib.pointsTo64_entails_memRegion (s0.sp - 968#64) w8
  have hsaved := sendCt2SavedCells_entails_memRegion_80 s0 d56
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono hw8
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hsaved))))))) ?_
  change memRegion (s0.sp - 976#64 - 16944#64) 16944 ∗
      (memRegion (s0.sp - 976#64) 8 ∗ (memRegion (s0.sp - 968#64) 8 ∗
        (memRegion (s0.sp - 960#64) 400 ∗ (memRegion (s0.sp - 560#64) 400 ∗
          (memRegion (s0.sp - 160#64) 72 ∗ (memRegion (s0.sp - 88#64) 8 ∗
            memRegion (s0.sp - 80#64) 80)))))) ⊢
    memRegion (s0.sp - 17920#64) 13792 ∗ memRegion (s0.sp - 4128#64) 4128
  have hsub : s0.sp - 976#64 - 16944#64 = s0.sp - 17920#64 := by bv_omega
  rw [hsub,
      ← ProofLib.memRegion_split' (b := s0.sp - 88#64) (n := 8) (k := 80) (b' := s0.sp - 80#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := s0.sp - 160#64) (n := 72) (k := 88) (b' := s0.sp - 88#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := s0.sp - 560#64) (n := 400) (k := 160) (b' := s0.sp - 160#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := s0.sp - 960#64) (n := 400) (k := 560) (b' := s0.sp - 560#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := s0.sp - 968#64) (n := 8) (k := 960) (b' := s0.sp - 960#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := s0.sp - 976#64) (n := 8) (k := 968) (b' := s0.sp - 968#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := s0.sp - 17920#64) (n := 16944) (k := 976) (b' := s0.sp - 976#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := s0.sp - 17920#64) (n := 13792) (k := 4128) (b' := s0.sp - 4128#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem stackAt_976_from_dropPoly16 (sp : BitVec 64) :
    memRegion (sp - 17920#64) 13792 ∗ stackAt sp dropGluePoly16Stack ⊢
    stackAt sp keysSampledRecvCt1ChunkStack := by
  change memRegion (sp - 17920#64) 13792 ∗ memRegion (sp - 4128#64) 4128 ⊢
    memRegion (sp - 17920#64) 17920
  rw [← ProofLib.memRegion_split' (b := sp - 17920#64) (n := 13792) (k := 4128) (b' := sp - 4128#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

/-- Framed call rule for `rustDeallocSpec A` (`__rust_dealloc`). -/
theorem call_rustDealloc_cs {A : RustAlloc} {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (rustDeallocSpec A))
    (ptr : BitVec 64) (size align : Nat)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = ptr)
    (hx1 : (s.readReg64 Reg.x1).toNat = size)
    (hx2 : (s.readReg64 Reg.x2).toNat = align)
    (hsplit : P = (A.pool ∗ A.live ptr size align ∗ memRegion ptr size ∗
      stackAt sp_call allocHookStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog target_pc sf ((A.pool ∗ stackAt sp_call allocHookStack) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  refine SepWP.call_subroutine_frame hcall (x := (ptr, size, align)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    rw [hsplit] at hm
    dsimp only [rustDeallocSpec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, by simpa only [sepConj_assoc] using hm⟩
  · dsimp only [rustDeallocSpec]
    rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun htr => ?_
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

/-! ## 3. Phase 2 (`entry + 236#64` = `0x61854`): `memcpy`s, `uc` copy, `dealloc`, and `drop_glue::<Poly16>` -/

@[simp] theorem trace_writeVReg128 (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).trace = s.trace := rfl

theorem satisfies_ac {m : Memory} {P Q : SepProp} (h : P = Q) (hm : m ⊨ P) : m ⊨ Q :=
  h ▸ hm

theorem sepWP_congr_pre {prog : Program} {target : BitVec 64} {s : State} {P P' : SepProp}
    {post : State → SepProp → Prop} (h : P = P') (hwp : SepWP prog target s P' post) :
    SepWP prog target s P post :=
  h ▸ hwp

/-- Framed call rule for `addChunkSpec A` (`0x6c420`) when followed by another `SepWPp` call at `next_pc`. -/
theorem call_addChunk_next {A : RustAlloc} {prog : Program} {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (addChunkSpec A))
    (decA chunkA : BitVec 64) (dec : PolyDecoder) (chunk : Chunk)
    (hsorted : PolyDecoderStrictSorted dec)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = decA)
    (hx1 : s.readReg64 Reg.x1 = chunkA)
    (hsplit : P = (polyDecoderAt A decA dec ∗ chunkAt chunkA chunk ∗
      A.pool ∗ stackAt sp_call addChunkStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      PolyDecoderStrictSorted (addChunkTotal dec chunk) →
      SepWP prog next_pc sf
        ((polyDecoderAt A decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call addChunkStack) ∗ Frame)
        (fun sm Pm =>
          SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
            (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
              (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)))) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) := by
  apply SepWP.done hpc hrun
  refine SepWPp.call hcall (x := ⟨decA, chunkA, dec, chunk⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [addChunkSpec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hsorted⟩, hm⟩
  · rw [← sepConj_assoc]
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢
    rw [htrace] at haf htr_sub
    exact ⟨haf, htr_sub⟩
  · dsimp only [addChunkSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun ⟨htr, hsorted'⟩ => ?_
    apply SepWPp.of_sepWP (mid := next_pc)
    have hassoc :
        (polyDecoderAt A decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call addChunkStack) ∗ Frame =
        (polyDecoderAt A decA (addChunkTotal dec chunk) ∗
          (chunkAt chunkA chunk ∗ (A.pool ∗ stackAt sp_call addChunkStack))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hsorted'

/-! ## 4. Main Proof: `<KeysSampled>::recv_ct1_chunk` (`0x61768`, 107 insns) -/

end CryptoVerification.SpqrV1.States.Leaves
