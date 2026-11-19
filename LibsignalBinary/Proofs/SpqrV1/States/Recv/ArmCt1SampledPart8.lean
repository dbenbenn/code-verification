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
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart7
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ct1Sampled` Arm, Part 8 (Paths 4b & 5a)

Assembles Path 4b (`outMsg = none, ack = true`: `+11496 -> s0.x30`), the `outMsg = some decoded`
`<Ct1Sent>::recv_ek` call (`+11496 -> +11528`), Path 5a (`recv_ek = .error`), and Path 5b
prefix helpers.
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

theorem memRegion_none_ack_split (fsp : BitVec 64) (c_uc : Words16) :
    wordsAt (fsp + 3696#64) c_uc.toList ∗
      memRegion (fsp + 3832#64) 24 ∗
      memRegion (fsp + 576#64) 376 ∗
      memRegion (fsp + 976#64) 1776 ∗
      memRegion (fsp + 3152#64) 544 ∗
      memRegion (fsp + 3824#64) 8 ∗
      memRegion (fsp + 3856#64) 288 ⊢
    ∃∗ v576 : BitVec 64, ∃∗ v584 : BitVec 64, ∃∗ v592 : BitVec 64, ∃∗ bs352_576 : List (BitVec 8),
    ∃∗ v976 : BitVec 64, ∃∗ v984 : BitVec 64, ∃∗ v992 : BitVec 64, ∃∗ bs352_976 : List (BitVec 8),
    ∃∗ c_1352 : Words5, ∃∗ vc90 : BitVec 64, ∃∗ vc98 : BitVec 64, ∃∗ c_ca0 : Words5,
    ∃∗ vf10 : BitVec 64, ∃∗ vf18 : BitVec 64,
      ⌜bs352_576.length = 352⌝ ∗
      ⌜bs352_976.length = 352⌝ ∗
      mid376At (fsp + 576#64) v576 v584 v592 bs352_576 ∗
      ((fsp + 976#64) ↦₆₄ v976) ∗
      ((fsp + 984#64) ↦₆₄ v984) ∗
      ((fsp + 992#64) ↦₆₄ v992) ∗
      ((fsp + 1000#64) ↦ₛ bs352_976) ∗
      wordsAt (fsp + 1352#64) c_1352.toList ∗
      ((fsp + 3216#64) ↦₆₄ vc90) ∗
      ((fsp + 3224#64) ↦₆₄ vc98) ∗
      wordsAt (fsp + 3232#64) c_ca0.toList ∗
      memRegion (fsp + 3272#64) 376 ∗
      ((fsp + 3856#64) ↦₆₄ vf10) ∗
      ((fsp + 3864#64) ↦₆₄ vf18) ∗
      (memRegion (fsp + 1392#64) 1360 ∗
        memRegion (fsp + 3152#64) 64 ∗
        memRegion (fsp + 3648#64) 48 ∗
        memRegion (fsp + 3696#64) 128 ∗
        memRegion (fsp + 3824#64) 8 ∗
        memRegion (fsp + 3832#64) 24 ∗
        memRegion (fsp + 3872#64) 272) := by
  refine Entails.trans (sepConj_mono (words16_entails_memRegion_128 (fsp + 3696#64) c_uc)
    (sepConj_mono_right (sepConj_mono_left (memRegion_376_entails_mid376At (fsp + 576#64))))) ?_
  rw [ProofLib.memRegion_split' (b := fsp + 976#64) (n := 376) (k := 1400) (b' := fsp + 1352#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1352#64) (n := 40) (k := 1360) (b' := fsp + 1392#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3152#64) (n := 64) (k := 480) (b' := fsp + 3216#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3216#64) (n := 8) (k := 472) (b' := fsp + 3224#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 3216#64),
      ProofLib.memRegion_split' (b := fsp + 3224#64) (n := 8) (k := 464) (b' := fsp + 3232#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 3224#64),
      ProofLib.memRegion_split' (b := fsp + 3232#64) (n := 40) (k := 424) (b' := fsp + 3272#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3272#64) (n := 376) (k := 48) (b' := fsp + 3648#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3856#64) (n := 8) (k := 280) (b' := fsp + 3864#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 3856#64),
      ProofLib.memRegion_split' (b := fsp + 3864#64) (n := 8) (k := 272) (b' := fsp + 3872#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 3864#64)]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono
      (sepConj_mono (memRegion_376_entails_mid376At (fsp + 976#64))
        (sepConj_mono_left (memRegion_40_entails_words5 (fsp + 1352#64))))
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (memRegion_40_entails_words5 (fsp + 3232#64))))))))))) ?_
  dsimp only [mid376At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro vf18; apply Entails.sepExists_elim; intro vf10
  apply Entails.sepExists_elim; intro c_ca0; apply Entails.sepExists_elim; intro vc98
  apply Entails.sepExists_elim; intro vc90; apply Entails.sepExists_elim; intro c_1352
  apply Entails.sepExists_elim; intro v976; apply Entails.sepExists_elim; intro v984
  apply Entails.sepExists_elim; intro v992; apply Entails.sepExists_elim; intro bs352_976
  apply Entails.sepExists_elim; intro v576; apply Entails.sepExists_elim; intro v584
  apply Entails.sepExists_elim; intro v592; apply Entails.sepExists_elim; intro bs352_576
  refine Entails.sepExists_right v576 (Entails.sepExists_right v584
    (Entails.sepExists_right v592 (Entails.sepExists_right bs352_576
      (Entails.sepExists_right v976 (Entails.sepExists_right v984
        (Entails.sepExists_right v992 (Entails.sepExists_right bs352_976
          (Entails.sepExists_right c_1352 (Entails.sepExists_right vc90
            (Entails.sepExists_right vc98 (Entails.sepExists_right c_ca0
              (Entails.sepExists_right vf10 (Entails.sepExists_right vf18 ?_)))))))))))))
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_none_ack_join (fsp w0 w8 w16 v1 v2 v3 v4 : BitVec 64)
    {bs352 : List (BitVec 8)} (hbs : bs352.length = 352)
    (c1 c2 : Words5) :
    mid376At (fsp + 976#64) w0 w8 w16 bs352 ∗
      wordsAt (fsp + 1352#64) c1.toList ∗
      memRegion (fsp + 2752#64) 400 ∗
      ((fsp + 3216#64) ↦₆₄ v1) ∗
      ((fsp + 3224#64) ↦₆₄ v2) ∗
      wordsAt (fsp + 3232#64) c2.toList ∗
      mid376At (fsp + 3272#64) w0 w8 w16 bs352 ∗
      ((fsp + 3856#64) ↦₆₄ v3) ∗
      ((fsp + 3864#64) ↦₆₄ v4) ∗
      (memRegion (fsp + 1392#64) 1360 ∗
        memRegion (fsp + 3152#64) 64 ∗
        memRegion (fsp + 3648#64) 48 ∗
        memRegion (fsp + 3696#64) 128 ∗
        memRegion (fsp + 3824#64) 8 ∗
        memRegion (fsp + 3832#64) 24 ∗
        memRegion (fsp + 3872#64) 272) ⊢
    memRegion (fsp + 976#64) 3168 := by
  have hm1 := mid376At_entails_memRegion_376 (fsp + 976#64) w0 w8 w16 bs352 hbs
  have hw1 := wordsAt_entails_memRegion c1.toList (fsp + 1352#64) 40 rfl
  have hp1 := ProofLib.pointsTo64_entails_memRegion (fsp + 3216#64) v1
  have hp2 := ProofLib.pointsTo64_entails_memRegion (fsp + 3224#64) v2
  have hw2 := wordsAt_entails_memRegion c2.toList (fsp + 3232#64) 40 rfl
  have hm2 := mid376At_entails_memRegion_376 (fsp + 3272#64) w0 w8 w16 bs352 hbs
  have hp3 := ProofLib.pointsTo64_entails_memRegion (fsp + 3856#64) v3
  have hp4 := ProofLib.pointsTo64_entails_memRegion (fsp + 3864#64) v4
  refine Entails.trans (sepConj_mono hm1 (sepConj_mono hw1 (sepConj_mono_right
    (sepConj_mono hp1 (sepConj_mono hp2 (sepConj_mono hw2
      (sepConj_mono hm2 (sepConj_mono hp3 (sepConj_mono_left hp4))))))))) ?_
  rw [ProofLib.memRegion_split' (b := fsp + 976#64) (n := 376) (k := 2792) (b' := fsp + 1352#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1352#64) (n := 40) (k := 2752) (b' := fsp + 1392#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1392#64) (n := 1360) (k := 1392) (b' := fsp + 2752#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2752#64) (n := 400) (k := 992) (b' := fsp + 3152#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3152#64) (n := 64) (k := 928) (b' := fsp + 3216#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3216#64) (n := 8) (k := 920) (b' := fsp + 3224#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3224#64) (n := 8) (k := 912) (b' := fsp + 3232#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3232#64) (n := 40) (k := 872) (b' := fsp + 3272#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3272#64) (n := 376) (k := 496) (b' := fsp + 3648#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3648#64) (n := 48) (k := 448) (b' := fsp + 3696#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3696#64) (n := 128) (k := 320) (b' := fsp + 3824#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3824#64) (n := 8) (k := 312) (b' := fsp + 3832#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3832#64) (n := 24) (k := 288) (b' := fsp + 3856#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3856#64) (n := 8) (k := 280) (b' := fsp + 3864#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3864#64) (n := 8) (k := 272) (b' := fsp + 3872#64) rfl (by bv_omega) (by decide)]
  exact Entails.of_eq (by ac_rfl)

theorem copyScratch_part1_and_mem576_entails_memRegion_4144
    (fsp selfA : BitVec 64) (sc : CopyScratchStack) (k : EpilogueStoreStack) :
    memRegion (fsp + 576#64) 376 ∗
      copyScratchStackAt fsp sc ∗
      epilogueStoreStackPart1At fsp k ∗
      ((fsp + 232#64) ↦₆₄ selfA) ∗
      ((fsp + 512#64) ↦₆₄ k.w200) ∗
      ((fsp + 520#64) ↦₆₄ k.w208) ∗
      wordsAt (fsp + 528#64) k.tail.toList ∗
      memRegion (fsp + 568#64) 8 ∗
      memRegion (fsp + 952#64) 8 ∗
      memRegion (fsp + 976#64) 3168 ⊢
    memRegion fsp 4144 := by
  rw [memRegion_eq_exists_bytes (fsp + 576#64) 376 (by decide), sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro bs
  rw [sepConj_assoc]
  apply Entails.pure_left; intro hbs
  have h := copyScratch_and_epilogueStack_entails_memRegion_4144 fsp sc
    { k with we8 := selfA, mid := bs } hbs
  dsimp only [epilogueStoreStackPart1At, epilogueStoreStackPart2At,
    EpilogueStoreStack.tail, Words5.toList] at h ⊢
  simp only [wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd] at h ⊢
  exact Entails.trans (Entails.of_eq (by ac_rfl)) h

@[expose] def copyScratchStackWithoutWb0At (fsp : BitVec 64) (sc : CopyScratchStack) : SepProp :=
  wordsAt fsp sc.c0.toList ∗
    ((fsp + 128#64) ↦₆₄ sc.w80) ∗ ((fsp + 136#64) ↦₆₄ sc.w88) ∗
    ((fsp + 144#64) ↦₆₄ sc.w90) ∗ ((fsp + 152#64) ↦₆₄ sc.w98) ∗
    ((fsp + 160#64) ↦₆₄ sc.wa0) ∗ ((fsp + 168#64) ↦₆₄ sc.wa8) ∗
    ((fsp + 184#64) ↦₆₄ sc.wb8) ∗
    ((fsp + 192#64) ↦₆₄ sc.wc0) ∗ ((fsp + 200#64) ↦₆₄ sc.wc8) ∗
    ((fsp + 208#64) ↦₆₄ sc.wd0) ∗ ((fsp + 216#64) ↦₆₄ sc.wd8) ∗
    ((fsp + 240#64) ↦₆₄ sc.wf0)

theorem copyScratchStackAt_eq_wb0 (fsp : BitVec 64) (sc : CopyScratchStack) :
    copyScratchStackAt fsp sc =
      ((fsp + 176#64) ↦₆₄ sc.wb0) ∗ copyScratchStackWithoutWb0At fsp sc := by
  dsimp only [copyScratchStackAt, copyScratchStackWithoutWb0At]
  ac_rfl

theorem copyScratchStackAt_wb0_reconstruct (fsp : BitVec 64) (sc : CopyScratchStack) (w : BitVec 64) :
    ((fsp + 176#64) ↦₆₄ w) ∗ copyScratchStackWithoutWb0At fsp sc =
      copyScratchStackAt fsp { sc with wb0 := w } := by
  dsimp only [copyScratchStackAt, copyScratchStackWithoutWb0At]
  ac_rfl

theorem memRegion_128_split_two_words (a : BitVec 64) :
    memRegion a 128 ⊢
    ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ memRegion (a + 16#64) 112 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 120) (b' := a + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a,
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 112) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (a + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w1; apply Entails.sepExists_elim; intro w0
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.of_eq (by ac_rfl)))

theorem memRegion_some_ok_no_ack_split (fsp : BitVec 64) (c_ek : Words16) :
    wordsAt (fsp + 1856#64) c_ek.toList ∗
      memRegion (fsp + 576#64) 376 ∗
      memRegion (fsp + 976#64) 880 ∗
      memRegion (fsp + 1984#64) 768 ∗
      memRegion (fsp + 3152#64) 544 ∗
      memRegion (fsp + 3696#64) 128 ∗
      memRegion (fsp + 3824#64) 8 ∗
      memRegion (fsp + 3832#64) 24 ∗
      memRegion (fsp + 3984#64) 160 ⊢
    ∃∗ v576 : BitVec 64, ∃∗ v584 : BitVec 64, ∃∗ v592 : BitVec 64, ∃∗ bs352_576 : List (BitVec 8),
    ∃∗ v976 : BitVec 64, ∃∗ v984 : BitVec 64, ∃∗ v992 : BitVec 64, ∃∗ bs352_976 : List (BitVec 8),
    ∃∗ c_1352 : Words5, ∃∗ vc90 : BitVec 64, ∃∗ vc98 : BitVec 64, ∃∗ c_ca0 : Words5,
    ∃∗ v4096 : BitVec 64, ∃∗ v4104 : BitVec 64, ∃∗ v4112 : BitVec 64,
      ⌜bs352_576.length = 352⌝ ∗
      ⌜bs352_976.length = 352⌝ ∗
      mid376At (fsp + 576#64) v576 v584 v592 bs352_576 ∗
      ((fsp + 976#64) ↦₆₄ v976) ∗
      ((fsp + 984#64) ↦₆₄ v984) ∗
      ((fsp + 992#64) ↦₆₄ v992) ∗
      ((fsp + 1000#64) ↦ₛ bs352_976) ∗
      wordsAt (fsp + 1352#64) c_1352.toList ∗
      ((fsp + 3216#64) ↦₆₄ vc90) ∗
      ((fsp + 3224#64) ↦₆₄ vc98) ∗
      wordsAt (fsp + 3232#64) c_ca0.toList ∗
      memRegion (fsp + 3272#64) 376 ∗
      ((fsp + 4096#64) ↦₆₄ v4096) ∗
      ((fsp + 4104#64) ↦₆₄ v4104) ∗
      ((fsp + 4112#64) ↦₆₄ v4112) ∗
      (memRegion (fsp + 1392#64) 1360 ∗
        memRegion (fsp + 3152#64) 64 ∗
        memRegion (fsp + 3648#64) 48 ∗
        memRegion (fsp + 3696#64) 128 ∗
        memRegion (fsp + 3824#64) 8 ∗
        memRegion (fsp + 3832#64) 24 ∗
        memRegion (fsp + 3984#64) 112 ∗
        memRegion (fsp + 4120#64) 24) := by
  refine Entails.trans (sepConj_mono (words16_entails_memRegion_128 (fsp + 1856#64) c_ek)
    (sepConj_mono_left (memRegion_376_entails_mid376At (fsp + 576#64)))) ?_
  rw [ProofLib.memRegion_split' (b := fsp + 976#64) (n := 376) (k := 504) (b' := fsp + 1352#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1352#64) (n := 40) (k := 464) (b' := fsp + 1392#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3152#64) (n := 64) (k := 480) (b' := fsp + 3216#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3216#64) (n := 8) (k := 472) (b' := fsp + 3224#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 3216#64),
      ProofLib.memRegion_split' (b := fsp + 3224#64) (n := 8) (k := 464) (b' := fsp + 3232#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 3224#64),
      ProofLib.memRegion_split' (b := fsp + 3232#64) (n := 40) (k := 424) (b' := fsp + 3272#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3272#64) (n := 376) (k := 48) (b' := fsp + 3648#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3984#64) (n := 112) (k := 48) (b' := fsp + 4096#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 4096#64) (n := 8) (k := 40) (b' := fsp + 4104#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 4096#64),
      ProofLib.memRegion_split' (b := fsp + 4104#64) (n := 8) (k := 32) (b' := fsp + 4112#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 4104#64),
      ProofLib.memRegion_split' (b := fsp + 4112#64) (n := 8) (k := 24) (b' := fsp + 4120#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 4112#64)]
  have h1392 :
      memRegion (fsp + 1392#64) 464 ∗ memRegion (fsp + 1856#64) 128 ∗ memRegion (fsp + 1984#64) 768 =
      memRegion (fsp + 1392#64) 1360 := by
    rw [ProofLib.memRegion_split' (b := fsp + 1392#64) (n := 464) (k := 896) (b' := fsp + 1856#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 1856#64) (n := 128) (k := 768) (b' := fsp + 1984#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono (sepConj_mono (memRegion_376_entails_mid376At (fsp + 976#64))
      (sepConj_mono_left (memRegion_40_entails_words5 (fsp + 1352#64))))
      (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (memRegion_40_entails_words5 (fsp + 3232#64))))))))))) ?_
  dsimp only [mid376At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro v4112; apply Entails.sepExists_elim; intro v4104
  apply Entails.sepExists_elim; intro v4096; apply Entails.sepExists_elim; intro c_ca0
  apply Entails.sepExists_elim; intro vc98; apply Entails.sepExists_elim; intro vc90
  apply Entails.sepExists_elim; intro c_1352; apply Entails.sepExists_elim; intro v976
  apply Entails.sepExists_elim; intro v984; apply Entails.sepExists_elim; intro v992
  apply Entails.sepExists_elim; intro bs352_976; apply Entails.sepExists_elim; intro v576
  apply Entails.sepExists_elim; intro v584; apply Entails.sepExists_elim; intro v592
  apply Entails.sepExists_elim; intro bs352_576
  refine Entails.sepExists_right v576 (Entails.sepExists_right v584
    (Entails.sepExists_right v592 (Entails.sepExists_right bs352_576
      (Entails.sepExists_right v976 (Entails.sepExists_right v984
        (Entails.sepExists_right v992 (Entails.sepExists_right bs352_976
          (Entails.sepExists_right c_1352 (Entails.sepExists_right vc90
            (Entails.sepExists_right vc98 (Entails.sepExists_right c_ca0
              (Entails.sepExists_right v4096 (Entails.sepExists_right v4104
                (Entails.sepExists_right v4112 ?_))))))))))))))
  rw [← h1392]
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.States.Recv
