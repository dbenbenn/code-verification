/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart4 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart6
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart7
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart8
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ct1Sampled` Arm, Part 9 (Paths 5b & 5c)

Composes Path 5b (`outMsg = some decoded, recv_ek = .ok uc_ek, ack = false` →
`States.ekReceivedCt1Sampled`) and Path 5c (`ack = true` → `States.ct2Sampled`) from `+11496` to
`s0.x30`.
-/

public section

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Poly.DecodedMessage
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

theorem memRegion_3872_split (fsp : BitVec 64) :
    memRegion (fsp + 3872#64) 272 =
      memRegion (fsp + 3872#64) 112 ∗ memRegion (fsp + 3984#64) 112 ∗
        memRegion (fsp + 4096#64) 24 ∗ memRegion (fsp + 4120#64) 24 := by
  rw [ProofLib.memRegion_split' (b := fsp + 3872#64) (n := 112) (k := 160) (b' := fsp + 3984#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3984#64) (n := 112) (k := 48) (b' := fsp + 4096#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 4096#64) (n := 24) (k := 24) (b' := fsp + 4120#64) rfl (by bv_omega) (by decide)]

/-! ## 1. Path 5b (`outMsg = some decoded, recv_ek = .ok uc_ek, ack = false`: `+11496 -> s0.x30`) -/

theorem statesRecvRoAt_eq_unchunkedSendCt2 (b : BitVec 64) :
    statesRecvRoAt b =
      unchunkedSendCt2RoAt b ∗
        (statesRecvJumpTableAt b ∗ tokenInitAt b ∗ reduceTableAt b) := by
  dsimp only [statesRecvRoAt]
  ac_rfl

theorem memRegion_some_ok_ack_split_976 (fsp : BitVec 64) :
    memRegion (fsp + 576#64) 376 ∗
      memRegion (fsp + 976#64) 880 ∗
      memRegion (fsp + 3152#64) 544 ⊢
    ∃∗ v576 : BitVec 64, ∃∗ v584 : BitVec 64, ∃∗ v592 : BitVec 64, ∃∗ bs352_576 : List (BitVec 8),
    ∃∗ v976 : BitVec 64, ∃∗ v984 : BitVec 64, ∃∗ v992 : BitVec 64, ∃∗ bs352_976 : List (BitVec 8),
    ∃∗ c_1352 : Words5, ∃∗ c_ca0 : Words5,
      ⌜bs352_576.length = 352⌝ ∗
      ⌜bs352_976.length = 352⌝ ∗
      mid376At (fsp + 576#64) v576 v584 v592 bs352_576 ∗
      mid376At (fsp + 976#64) v976 v984 v992 bs352_976 ∗
      wordsAt (fsp + 1352#64) c_1352.toList ∗
      wordsAt (fsp + 3232#64) c_ca0.toList ∗
      memRegion (fsp + 3272#64) 376 ∗
      (memRegion (fsp + 1392#64) 464 ∗
        memRegion (fsp + 3152#64) 80 ∗
        memRegion (fsp + 3648#64) 48) := by
  rw [ProofLib.memRegion_split' (b := fsp + 976#64) (n := 376) (k := 504) (b' := fsp + 1352#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1352#64) (n := 40) (k := 464) (b' := fsp + 1392#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3152#64) (n := 80) (k := 464) (b' := fsp + 3232#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3232#64) (n := 40) (k := 424) (b' := fsp + 3272#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3272#64) (n := 376) (k := 48) (b' := fsp + 3648#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (sepConj_mono (memRegion_376_entails_mid376At (fsp + 576#64))
    (sepConj_mono (sepConj_mono (memRegion_376_entails_mid376At (fsp + 976#64))
      (sepConj_mono_left (memRegion_40_entails_words5 (fsp + 1352#64))))
      (sepConj_mono_right (sepConj_mono_left (memRegion_40_entails_words5 (fsp + 3232#64)))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro c_ca0
  apply Entails.sepExists_elim; intro c_1352
  apply Entails.sepExists_elim; intro v976; apply Entails.sepExists_elim; intro v984
  apply Entails.sepExists_elim; intro v992; apply Entails.sepExists_elim; intro bs352_976
  apply Entails.sepExists_elim; intro v576; apply Entails.sepExists_elim; intro v584
  apply Entails.sepExists_elim; intro v592; apply Entails.sepExists_elim; intro bs352_576
  refine Entails.sepExists_right v576 (Entails.sepExists_right v584
    (Entails.sepExists_right v592 (Entails.sepExists_right bs352_576
      (Entails.sepExists_right v976 (Entails.sepExists_right v984
        (Entails.sepExists_right v992 (Entails.sepExists_right bs352_976
          (Entails.sepExists_right c_1352 (Entails.sepExists_right c_ca0 ?_)))))))))
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_some_ok_ack_join (fsp w0 w8 w16 : BitVec 64)
    {bs352 : List (BitVec 8)} (hbs : bs352.length = 352)
    (c1 c2 : Words5) (c_enc : Words50) (g : AuthWords) (epoch : BitVec 64) :
    mid376At (fsp + 976#64) w0 w8 w16 bs352 ∗
      wordsAt (fsp + 1352#64) c1.toList ∗
      words50At (fsp + 1856#64) c_enc ∗
      wordsAt (fsp + 2256#64) (ct2SentWordsList g epoch) ∗
      memRegion (fsp + 2752#64) 400 ∗
      wordsAt (fsp + 3232#64) c2.toList ∗
      mid376At (fsp + 3272#64) w0 w8 w16 bs352 ∗
      (memRegion (fsp + 1392#64) 464 ∗
        memRegion (fsp + 2312#64) 440 ∗
        memRegion (fsp + 3152#64) 80 ∗
        memRegion (fsp + 3648#64) 48 ∗
        memRegion (fsp + 3696#64) 128 ∗
        memRegion (fsp + 3824#64) 8 ∗
        memRegion (fsp + 3832#64) 24 ∗
        memRegion (fsp + 3856#64) 128 ∗
        memRegion (fsp + 3984#64) 8 ∗
        memRegion (fsp + 3992#64) 104 ∗
        memRegion (fsp + 4096#64) 48) ⊢
    memRegion (fsp + 976#64) 3168 := by
  have hm1 := mid376At_entails_memRegion_376 (fsp + 976#64) w0 w8 w16 bs352 hbs
  have hw1 := wordsAt_entails_memRegion c1.toList (fsp + 1352#64) 40 rfl
  have henc : words50At (fsp + 1856#64) c_enc ⊢ memRegion (fsp + 1856#64) 400 := by
    rw [words50At_eq_pointsToBytes]
    have h := ProofLib.pointsToBytes_entails_memRegion (fsp + 1856#64) c_enc.toBytes
    rwa [Words50.toBytes_length] at h
  have hct2 := wordsAt_entails_memRegion (ct2SentWordsList g epoch) (fsp + 2256#64) 56 rfl
  have hw2 := wordsAt_entails_memRegion c2.toList (fsp + 3232#64) 40 rfl
  have hm2 := mid376At_entails_memRegion_376 (fsp + 3272#64) w0 w8 w16 bs352 hbs
  refine Entails.trans (sepConj_mono hm1 (sepConj_mono hw1 (sepConj_mono henc
    (sepConj_mono hct2 (sepConj_mono_right (sepConj_mono hw2 (sepConj_mono_left hm2))))))) ?_
  rw [ProofLib.memRegion_split' (b := fsp + 976#64) (n := 376) (k := 2792) (b' := fsp + 1352#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1352#64) (n := 40) (k := 2752) (b' := fsp + 1392#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1392#64) (n := 464) (k := 2288) (b' := fsp + 1856#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1856#64) (n := 400) (k := 1888) (b' := fsp + 2256#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2256#64) (n := 56) (k := 1832) (b' := fsp + 2312#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2312#64) (n := 440) (k := 1392) (b' := fsp + 2752#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2752#64) (n := 400) (k := 992) (b' := fsp + 3152#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3152#64) (n := 80) (k := 912) (b' := fsp + 3232#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3232#64) (n := 40) (k := 872) (b' := fsp + 3272#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3272#64) (n := 376) (k := 496) (b' := fsp + 3648#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3648#64) (n := 48) (k := 448) (b' := fsp + 3696#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3696#64) (n := 128) (k := 320) (b' := fsp + 3824#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3824#64) (n := 8) (k := 312) (b' := fsp + 3832#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3832#64) (n := 24) (k := 288) (b' := fsp + 3856#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3856#64) (n := 128) (k := 160) (b' := fsp + 3984#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3984#64) (n := 8) (k := 152) (b' := fsp + 3992#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3992#64) (n := 104) (k := 48) (b' := fsp + 4096#64) rfl (by bv_omega) (by decide)]
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.States.Recv
