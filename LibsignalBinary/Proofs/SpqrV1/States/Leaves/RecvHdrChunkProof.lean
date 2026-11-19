/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart3
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart4
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart5
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout
/-!
# `<NoHeaderReceived>::recv_hdr_chunk` — Epilogues & Top-Level Proof

**Checked by Lean.** Verifies the `MacVerifyFailed` epilogue entry (`0x61574 .. 0x615ec`,
offsets `800 .. 920`), the `Ok(.done ...)` epilogue (`0x61678 .. 0x61700`, offsets `1060 .. 1196`),
and the top-level contract `noHeaderReceived_recv_hdr_chunk_okX`.
-/

public section

namespace CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.GF.IsNonZero
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification
open CryptoVerification.LibsignalSpqrV1.PolyDecoder
open CryptoVerification.LibsignalTripleRatchet.Keys
open CryptoVerification.SpqrV1.ChainProofs
open UpdateFacts NextKeyInternalFacts AgreeStateSimp SplitBytes NewFacts

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  HkdfToSliceProof.sp_sub_688_eq_hsp
  HkdfToSliceProof.sp_add_neg688_eq_hsp
  HkdfToSliceProof.sp_sub_96_eq_hsp_592
  HkdfToSliceProof.sp_add_neg96_eq_hsp_592

theorem authenticatorHeapAt_rootKey_eq0 (A : RustAlloc) (g : AuthenticatorGhost) (auth : Authenticator)
    (h0 : g.rootKey.cap = 0#64) :
    authenticatorHeapAt A g auth ⊢
      vecU8HeapAt A g.macKey.cap g.macKey.ptr auth.macKey := by
  have h1 : vecU8HeapAt A g.rootKey.cap g.rootKey.ptr auth.rootKey ⊢ emp :=
    vecU8HeapAt_eq0_emp A g.rootKey.cap g.rootKey.ptr auth.rootKey h0
  refine Entails.trans (authenticatorHeapAt_expose A g auth) ?_
  refine Entails.trans (sepConj_mono_left h1) ?_
  exact Entails.of_eq (emp_sepConj _)

theorem authenticatorHeapAt_rootKey_ne0 (A : RustAlloc) (g : AuthenticatorGhost) (auth : Authenticator)
    (hne : g.rootKey.cap ≠ 0#64) :
    authenticatorHeapAt A g auth ⊢
      ⌜g.rootKey.cap.toNat < 2 ^ 63 ∧ g.rootKey.ptr ≠ 0#64⌝ ∗
        memRegion g.rootKey.ptr g.rootKey.cap.toNat ∗
        A.live g.rootKey.ptr g.rootKey.cap.toNat 1 ∗
        vecU8HeapAt A g.macKey.cap g.macKey.ptr auth.macKey := by
  have h1 := vecU8HeapAt_ne0_dealloc A g.rootKey.cap g.rootKey.ptr auth.rootKey hne
  refine Entails.trans (authenticatorHeapAt_expose A g auth) ?_
  refine Entails.trans (sepConj_mono_left h1) ?_
  unfold vecU8HeapAt
  exact Entails.of_eq (by ac_rfl)

theorem sp_sub_1616_orr_9 (sp : BitVec 64) (halign : (sp &&& 15#64 == 0#64) = true) :
    (sp - 1616#64) ||| 9#64 = sp - 1607#64 := by
  have h : sp &&& 15#64 = 0#64 := of_decide_eq_true halign
  bv_kernel

@[expose] def overlapWord1 (u0 u8 : BitVec 64) : BitVec 64 :=
  (u0 >>> 8) ||| (u8 <<< 56)

theorem hiBytes7_append_loByte_eq (u0 u8 : BitVec 64) :
    Poly.EncoderFromPb.hiBytes7 u0 ++ [Poly.EncoderFromPb.loByte u8] =
      unpack64 (overlapWord1 u0 u8) := by
  simp only [Poly.EncoderFromPb.hiBytes7, Poly.EncoderFromPb.loByte, unpack64, overlapWord1,
    List.drop, List.cons_append, List.nil_append, List.cons.injEq]
  exact ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
    by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel, trivial⟩

theorem hiBytes7_pointsTo64_eq_overlap1 (p u0 u8 : BitVec 64) :
    (p ↦ₛ Poly.EncoderFromPb.hiBytes7 u0) ∗ ((p + 7#64) ↦₆₄ u8) =
      (p ↦₆₄ overlapWord1 u0 u8) ∗ ((p + 8#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 u8) := by
  rw [FromPb.pointsTo64_split_1_7 (p + 7#64) u8]
  have ha : p + 7#64 + 1#64 = p + 8#64 := by bv_omega
  rw [ha, ← sepConj_assoc]
  congr 1
  rw [ProofLib.pointsTo64_eq_pointsToBytes p (overlapWord1 u0 u8),
      ← hiBytes7_append_loByte_eq u0 u8,
      ProofLib.pointsToBytes_append p (Poly.EncoderFromPb.hiBytes7 u0) [Poly.EncoderFromPb.loByte u8],
      Poly.EncoderFromPb.length_hiBytes7,
      ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil, sepConj_emp]

theorem words3_eq_shift1 (b u0 u8 u16 : BitVec 64) :
    (b ↦₆₄ u0) ∗ ((b + 8#64) ↦₆₄ u8) ∗ ((b + 16#64) ↦₆₄ u16) =
      (b ↦₈ Poly.EncoderFromPb.loByte u0) ∗
      ((b + 1#64) ↦₆₄ overlapWord1 u0 u8) ∗
      ((b + 9#64) ↦₆₄ overlapWord1 u8 u16) ∗
      ((b + 17#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 u16) := by
  rw [FromPb.pointsTo64_split_1_7 b u0]
  have h1 := hiBytes7_pointsTo64_eq_overlap1 (b + 1#64) u0 u8
  have ha8 : b + 1#64 + 7#64 = b + 8#64 := by bv_omega
  have ha9 : b + 1#64 + 8#64 = b + 9#64 := by bv_omega
  rw [ha8, ha9] at h1
  have h2 := hiBytes7_pointsTo64_eq_overlap1 (b + 9#64) u8 u16
  have ha16 : b + 9#64 + 7#64 = b + 16#64 := by bv_omega
  have ha17 : b + 9#64 + 8#64 = b + 17#64 := by bv_omega
  rw [ha16, ha17] at h2
  calc ((b ↦₈ Poly.EncoderFromPb.loByte u0) ∗ ((b + 1#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 u0)) ∗
        ((b + 8#64) ↦₆₄ u8) ∗ ((b + 16#64) ↦₆₄ u16)
    _ = (b ↦₈ Poly.EncoderFromPb.loByte u0) ∗
        (((b + 1#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 u0) ∗ ((b + 8#64) ↦₆₄ u8)) ∗
        ((b + 16#64) ↦₆₄ u16) := by ac_rfl
    _ = (b ↦₈ Poly.EncoderFromPb.loByte u0) ∗
        ((b + 1#64) ↦₆₄ overlapWord1 u0 u8) ∗
        (((b + 9#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 u8) ∗ ((b + 16#64) ↦₆₄ u16)) := by
        rw [h1]; ac_rfl
    _ = (b ↦₈ Poly.EncoderFromPb.loByte u0) ∗
        ((b + 1#64) ↦₆₄ overlapWord1 u0 u8) ∗
        ((b + 9#64) ↦₆₄ overlapWord1 u8 u16) ∗
        ((b + 17#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 u16) := by
        rw [h2]

theorem words5_eq_shift1 (b u0 u8 u16 u24 u32 : BitVec 64) :
    (b ↦₆₄ u0) ∗ ((b + 8#64) ↦₆₄ u8) ∗ ((b + 16#64) ↦₆₄ u16) ∗
      ((b + 24#64) ↦₆₄ u24) ∗ ((b + 32#64) ↦₆₄ u32) =
      (b ↦₈ Poly.EncoderFromPb.loByte u0) ∗
      ((b + 1#64) ↦₆₄ overlapWord1 u0 u8) ∗
      ((b + 9#64) ↦₆₄ overlapWord1 u8 u16) ∗
      ((b + 17#64) ↦₆₄ overlapWord1 u16 u24) ∗
      ((b + 25#64) ↦₆₄ overlapWord1 u24 u32) ∗
      ((b + 33#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 u32) := by
  have h12 := words3_eq_shift1 b u0 u8 u16
  have h3 := hiBytes7_pointsTo64_eq_overlap1 (b + 17#64) u16 u24
  have ha24 : b + 17#64 + 7#64 = b + 24#64 := by bv_omega
  have ha25 : b + 17#64 + 8#64 = b + 25#64 := by bv_omega
  rw [ha24, ha25] at h3
  have h4 := hiBytes7_pointsTo64_eq_overlap1 (b + 25#64) u24 u32
  have ha32 : b + 25#64 + 7#64 = b + 32#64 := by bv_omega
  have ha33 : b + 25#64 + 8#64 = b + 33#64 := by bv_omega
  rw [ha32, ha33] at h4
  calc (b ↦₆₄ u0) ∗ ((b + 8#64) ↦₆₄ u8) ∗ ((b + 16#64) ↦₆₄ u16) ∗
        ((b + 24#64) ↦₆₄ u24) ∗ ((b + 32#64) ↦₆₄ u32)
    _ = ((b ↦₆₄ u0) ∗ ((b + 8#64) ↦₆₄ u8) ∗ ((b + 16#64) ↦₆₄ u16)) ∗
        ((b + 24#64) ↦₆₄ u24) ∗ ((b + 32#64) ↦₆₄ u32) := by ac_rfl
    _ = (b ↦₈ Poly.EncoderFromPb.loByte u0) ∗
        ((b + 1#64) ↦₆₄ overlapWord1 u0 u8) ∗
        ((b + 9#64) ↦₆₄ overlapWord1 u8 u16) ∗
        (((b + 17#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 u16) ∗ ((b + 24#64) ↦₆₄ u24)) ∗
        ((b + 32#64) ↦₆₄ u32) := by rw [h12]; ac_rfl
    _ = (b ↦₈ Poly.EncoderFromPb.loByte u0) ∗
        ((b + 1#64) ↦₆₄ overlapWord1 u0 u8) ∗
        ((b + 9#64) ↦₆₄ overlapWord1 u8 u16) ∗
        ((b + 17#64) ↦₆₄ overlapWord1 u16 u24) ∗
        (((b + 25#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 u24) ∗ ((b + 32#64) ↦₆₄ u32)) := by
        rw [h3]; ac_rfl
    _ = (b ↦₈ Poly.EncoderFromPb.loByte u0) ∗
        ((b + 1#64) ↦₆₄ overlapWord1 u0 u8) ∗
        ((b + 9#64) ↦₆₄ overlapWord1 u8 u16) ∗
        ((b + 17#64) ↦₆₄ overlapWord1 u16 u24) ∗
        ((b + 25#64) ↦₆₄ overlapWord1 u24 u32) ∗
        ((b + 33#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 u32) := by
        rw [h4]

@[expose] def merge17 (w16 u16 : BitVec 64) : BitVec 64 :=
  (w16 &&& 0xff#64) ||| (u16 &&& 0xffffffffffffff00#64)

theorem overlapWord1_merge17 (w8 w16 u16 : BitVec 64) :
    overlapWord1 w8 (merge17 w16 u16) = overlapWord1 w8 w16 := by
  simp only [overlapWord1, merge17]; bv_kernel

theorem hiBytes7_merge17 (w16 u16 : BitVec 64) :
    Poly.EncoderFromPb.hiBytes7 (merge17 w16 u16) = Poly.EncoderFromPb.hiBytes7 u16 := by
  simp only [Poly.EncoderFromPb.hiBytes7, unpack64, merge17, List.drop, List.cons.injEq]
  exact ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
    by bv_kernel, by bv_kernel, by bv_kernel, trivial⟩

theorem words3_shift1_unmerge (b w0 w8 w16 u16 : BitVec 64) :
    (b ↦₈ Poly.EncoderFromPb.loByte w0) ∗
      ((b + 1#64) ↦₆₄ overlapWord1 w0 w8) ∗
      ((b + 9#64) ↦₆₄ overlapWord1 w8 w16) ∗
      ((b + 17#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 u16) =
      (b ↦₆₄ w0) ∗ ((b + 8#64) ↦₆₄ w8) ∗ ((b + 16#64) ↦₆₄ merge17 w16 u16) := by
  have h := (words3_eq_shift1 b w0 w8 (merge17 w16 u16)).symm
  rw [overlapWord1_merge17, hiBytes7_merge17] at h
  exact h

@[expose] def polyDecoderNew1152Tail391At (A : RustAlloc) (p : BitVec 64) : SepProp :=
  (p ↦ₛ Poly.EncoderFromPb.hiBytes7 2#64) ∗
    ((p + 7#64) ↦₆₄ 0#64) ∗
    sortedSetPtListOf A (p + 15#64) (List.replicate 15 SortedSetPt.new) ∗
    ((p + 375#64) ↦₆₄ 576#64) ∗
    ((p + 383#64) ↦₈ 0#8) ∗
    memRegion (p + 384#64) 7

theorem polyDecoderNew1152RawAt_eq_head9_tail391 (A : RustAlloc) (a : BitVec 64) :
    polyDecoderNew1152RawAt A a =
      (a ↦₆₄ 0#64) ∗
      ((a + 8#64) ↦₈ 2#8) ∗
      polyDecoderNew1152Tail391At A (a + 9#64) := by
  unfold polyDecoderNew1152RawAt polyDecoderNew1152Tail391At
  rw [FromPb.pointsTo64_split_1_7 (a + 8#64) 2#64]
  have hlo : Poly.EncoderFromPb.loByte 2#64 = 2#8 := rfl
  have ha9 : a + 8#64 + 1#64 = a + 9#64 := by bv_omega
  have ha16 : a + 9#64 + 7#64 = a + 16#64 := by bv_omega
  have ha24 : a + 9#64 + 15#64 = a + 24#64 := by bv_omega
  have ha384 : a + 9#64 + 375#64 = a + 384#64 := by bv_omega
  have ha392 : a + 9#64 + 383#64 = a + 392#64 := by bv_omega
  have ha393 : a + 9#64 + 384#64 = a + 393#64 := by bv_omega
  rw [hlo, ha9, ha16, ha24, ha384, ha392, ha393]
  ac_rfl

@[expose] def polyDecoderNew1152Tail391Split (A : RustAlloc) :
    SplitBytes 391 (polyDecoderNew1152Tail391At A) :=
  have h : ∀ p,
      ((p ↦ₛ Poly.EncoderFromPb.hiBytes7 2#64) ∗
        (((p + BitVec.ofNat 64 7) ↦₆₄ 0#64) ∗
          (sortedSetPtListOf A ((p + BitVec.ofNat 64 7) + BitVec.ofNat 64 8)
              (List.replicate 15 SortedSetPt.new) ∗
            ((((p + BitVec.ofNat 64 7) + BitVec.ofNat 64 8) + BitVec.ofNat 64 360) ↦₆₄ 576#64 ∗
              (((((p + BitVec.ofNat 64 7) + BitVec.ofNat 64 8) + BitVec.ofNat 64 360) + BitVec.ofNat 64 8) ↦₈ 0#8 ∗
                memRegion (((((p + BitVec.ofNat 64 7) + BitVec.ofNat 64 8) + BitVec.ofNat 64 360) + BitVec.ofNat 64 8) + BitVec.ofNat 64 1) 7))))) =
      polyDecoderNew1152Tail391At A p := by
    intro p
    unfold polyDecoderNew1152Tail391At
    have h15 : (p + 7#64) + 8#64 = p + 15#64 := by bv_omega
    have h375 : (p + 15#64) + 360#64 = p + 375#64 := by bv_omega
    have h383 : (p + 375#64) + 8#64 = p + 383#64 := by bv_omega
    have h384 : (p + 383#64) + 1#64 = p + 384#64 := by bv_omega
    simp only [BitVec.ofNat_eq_ofNat, h15, h375, h383, h384, sepConj_assoc]
  have S_hi7 : SplitBytes 7 (fun p => p ↦ₛ Poly.EncoderFromPb.hiBytes7 2#64) :=
    SplitBytes.pointsToBytesFixed (Poly.EncoderFromPb.hiBytes7 2#64)
  have S_pts15 : SplitBytes 360 (fun p => sortedSetPtListOf A p (List.replicate 15 SortedSetPt.new)) :=
    SplitBytes.arrayAtSplit (SplitBytes.sortedSetPtSplit A) (List.replicate 15 SortedSetPt.new) (by decide)
  SplitBytes.congr h <|
    S_hi7.seq
      ((SplitBytes.pointsTo64 0#64).seq
        (S_pts15.seq
          ((SplitBytes.pointsTo64 576#64).seq
            ((SplitBytes.pointsTo8 0#8).seq (SplitBytes.region 7 (by decide)) (by decide))
            (by decide))
          (by decide))
        (by decide))
      (by decide)

theorem authenticatorHeapAt_rootKey_cap_max (A : RustAlloc) (g : AuthenticatorGhost) (auth : Authenticator) :
    authenticatorHeapAt A g auth ⊢ ⌜g.rootKey.cap.toNat < 2 ^ 63⌝ ∗ authenticatorHeapAt A g auth := by
  unfold authenticatorHeapAt
  apply Entails.pure_left; rintro ⟨hle, hmax, hptr_ne⟩
  exact Entails.pure_right hmax (Entails.pure_right ⟨hle, hmax, hptr_ne⟩ (Entails.refl _))

theorem words2_eq_loBytes7_overlap7_hiByte (b w0 w8 : BitVec 64) :
    (b ↦₆₄ w0) ∗ ((b + 8#64) ↦₆₄ w8) =
      (b ↦ₛ Poly.EncoderFromPb.loBytes7 w0) ∗ ((b + 7#64) ↦₆₄ FromPb.overlapWord7 w0 w8) ∗
      ((b + 15#64) ↦₈ Poly.EncoderFromPb.hiByte w8) := by
  rw [FromPb.pointsTo64_split_7_1 (b + 8#64) w8, ← sepConj_assoc,
      FromPb.pointsTo64_loBytes7_eq_loBytes7_overlapWord7 b w0 w8]
  have ha15 : b + 8#64 + 7#64 = b + 15#64 := by bv_omega
  rw [ha15, sepConj_assoc]

theorem collapse_scratch_736 (sp w0 w8 w16 w24 w31 : BitVec 64) (b39 : BitVec 8) :
    memRegion (sp - 736#64) 32 ∗ ((sp - 704#64) ↦₆₄ w0) ∗ ((sp - 696#64) ↦₆₄ w8) ∗
      ((sp - 688#64) ↦₆₄ w16) ∗ ((sp - 680#64) ↦ₛ Poly.EncoderFromPb.loBytes7 w24) ∗
      ((sp - 673#64) ↦₆₄ w31) ∗ ((sp - 665#64) ↦₈ b39) ∗ memRegion (sp - 664#64) 8 ⊢
      memRegion (sp - 736#64) 80 := by
  have hm0 := ProofLib.pointsTo64_entails_memRegion (sp - 704#64) w0
  have hm8 := ProofLib.pointsTo64_entails_memRegion (sp - 696#64) w8
  have hm16 := ProofLib.pointsTo64_entails_memRegion (sp - 688#64) w16
  have hm24 := FromPb.loBytes7_entails_memRegion_7 (sp - 680#64) w24
  have hm31 := ProofLib.pointsTo64_entails_memRegion (sp - 673#64) w31
  have hm39 := pointsTo8_entails_memRegion (sp - 665#64) b39
  rw [ProofLib.memRegion_split' (b := sp - 736#64) (n := 32) (k := 48) (b' := sp - 704#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 704#64) (n := 8) (k := 40) (b' := sp - 696#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 696#64) (n := 8) (k := 32) (b' := sp - 688#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 688#64) (n := 8) (k := 24) (b' := sp - 680#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 680#64) (n := 7) (k := 17) (b' := sp - 673#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 673#64) (n := 8) (k := 9) (b' := sp - 665#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 665#64) (n := 1) (k := 8) (b' := sp - 664#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (sepConj_mono hm0 (sepConj_mono hm8 (sepConj_mono hm16
    (sepConj_mono hm24 (sepConj_mono hm31 (sepConj_mono_left hm39))))))

theorem collapse_poly_1136_head9_tail391 (sp : BitVec 64) :
    ((sp - 1136#64) ↦₆₄ 0#64) ∗ ((sp - 1128#64) ↦₈ 2#8) ∗ memRegion (sp - 1127#64) 391 ⊢
      memRegion (sp - 1136#64) 400 := by
  rw [ProofLib.memRegion_split' (b := sp - 1136#64) (n := 8) (k := 392) (b' := sp - 1128#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1128#64) (n := 1) (k := 391) (b' := sp - 1127#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono_left (pointsTo8_entails_memRegion _ _))

theorem memRegion_out_480_split (out : BitVec 64) :
    memRegion out chunkedHeaderReceivedSize ⊢
      cells out 11 ∗ (∃∗ ub88 : BitVec 8, ((out + 88#64) ↦₈ ub88)) ∗ memRegion (out + 89#64) 391 := by
  unfold chunkedHeaderReceivedSize
  rw [ProofLib.memRegion_split out 88 392 (by decide), ProofLib.memRegion_cells out 11 (by decide),
      ProofLib.memRegion_split' (b := out + 88#64) (n := 1) (k := 391) (b' := out + 89#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_one (out + 88#64)]
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_736_80_split (sp : BitVec 64) :
    memRegion (sp - 736#64) 80 ⊢
      memRegion (sp - 736#64) 32 ∗ cells (sp - 704#64) 5 ∗ memRegion (sp - 664#64) 8 := by
  rw [ProofLib.memRegion_split' (b := sp - 736#64) (n := 32) (k := 48) (b' := sp - 704#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 704#64) (n := 40) (k := 8) (b' := sp - 664#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells (sp - 704#64) 5 (by decide)]
  exact Entails.of_eq (by ac_rfl)

theorem fold_out_ok_done {F : ShaCompress} (A : RustAlloc)
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (g_auth0 : AuthenticatorGhost) (hdrFull : Bytes) (ptr_hdr : BitVec 64)
    (hptr_hdr : ptr_hdr ≠ 0#64) (hge64 : 64 ≤ hdrFull.length)
    (hres : x.self.recv_hdr_chunk x.epoch x.chunk =
      .ok (.done { uc := { auth := x.self.uc.auth, hdr := hdrFull.take 64, epoch := x.epoch }
                   receiving_ek := polyDecoderNew1152 })) :
    (x.outA ↦₆₄ g_auth0.rootKey.cap) ∗ ((x.outA + 8#64) ↦₆₄ g_auth0.rootKey.ptr) ∗
      ((x.outA + 16#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.rootKey.length) ∗
      ((x.outA + 24#64) ↦₆₄ g_auth0.macKey.cap) ∗ ((x.outA + 32#64) ↦₆₄ g_auth0.macKey.ptr) ∗
      ((x.outA + 40#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.macKey.length) ∗
      authenticatorHeapAt A g_auth0 x.self.uc.auth ∗ ((x.outA + 48#64) ↦₆₄ 64#64) ∗
      ((x.outA + 56#64) ↦₆₄ ptr_hdr) ∗ ((x.outA + 64#64) ↦₆₄ 64#64) ∗
      (ptr_hdr ↦ₛ hdrFull.take 64) ∗ A.live ptr_hdr 64 1 ∗
      ((x.outA + 72#64) ↦₆₄ x.epoch) ∗ ((x.outA + 80#64) ↦₆₄ 0#64) ∗
      ((x.outA + 88#64) ↦₈ 2#8) ∗ polyDecoderNew1152Tail391At A (x.outA + 89#64) ⊢
      noHeaderReceivedRecvChunkResultAt A x.outA
        (x.self.recv_hdr_chunk x.epoch x.chunk) := by
  rw [hres]
  dsimp only [noHeaderReceivedRecvChunkResultAt, noHeaderReceivedRecvChunkAt,
    chunkedHeaderReceivedAt, unchunkedHeaderReceivedAt]
  refine Entails.pure_right polyDecoderStrictSorted_new1152 ?_
  rw [show (authenticatorAt A x.outA x.self.uc.auth ∗
        vecU8 A (x.outA + 48#64) (hdrFull.take 64) ∗ ((x.outA + 72#64) ↦₆₄ x.epoch)) ∗
      polyDecoderAt A (x.outA + 80#64) polyDecoderNew1152 =
      authenticatorAt A x.outA x.self.uc.auth ∗ vecU8 A (x.outA + 48#64) (hdrFull.take 64) ∗
      ((x.outA + 72#64) ↦₆₄ x.epoch) ∗ polyDecoderAt A (x.outA + 80#64) polyDecoderNew1152 by ac_rfl]
  have hauth := authenticatorPinAt_entails_authenticatorAt A g_auth0 x.outA x.self.uc.auth
  rw [authenticatorPinAt_eq_cells_heap A g_auth0 x.outA x.self.uc.auth] at hauth
  have htake_len64 : (hdrFull.take 64).length = 64 := by rw [List.length_take, Nat.min_eq_left hge64]
  have htake_len : BitVec.ofNat 64 (hdrFull.take 64).length = 64#64 := by rw [htake_len64]
  have hbuf64 : (ptr_hdr ↦ₛ hdrFull.take 64) ∗ A.live ptr_hdr 64 1 ⊢
      vecU8HeapAt A 64#64 ptr_hdr (hdrFull.take 64) := by
    unfold vecU8HeapAt
    refine Entails.pure_right ⟨by rw [htake_len64]; decide, by decide, hptr_hdr⟩ ?_
    have h64_ne : (64#64 : BitVec 64) ≠ 0 := by decide
    simp only [h64_ne, ↓reduceIte, htake_len64, htake_len,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp]
    exact Entails.of_eq (sepConj_comm _ _)
  have hvec_hdr : ((x.outA + 48#64) ↦₆₄ 64#64) ∗ ((x.outA + 56#64) ↦₆₄ ptr_hdr) ∗
      ((x.outA + 64#64) ↦₆₄ 64#64) ∗ (ptr_hdr ↦ₛ hdrFull.take 64) ∗ A.live ptr_hdr 64 1 ⊢
      vecU8 A (x.outA + 48#64) (hdrFull.take 64) := by
    dsimp only [vecU8]
    refine Entails.sepExists_right 64#64 (Entails.sepExists_right ptr_hdr ?_)
    rw [vecU8At_eq_cells_heap A (x.outA + 48#64) 64#64 ptr_hdr (hdrFull.take 64), htake_len]
    have ha56 : (x.outA + 48#64) + 8#64 = x.outA + 56#64 := by bv_omega
    have ha64 : (x.outA + 48#64) + 16#64 = x.outA + 64#64 := by bv_omega
    rw [ha56, ha64]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hbuf64))
  have hpoly : ((x.outA + 80#64) ↦₆₄ 0#64) ∗ ((x.outA + 88#64) ↦₈ 2#8) ∗
      polyDecoderNew1152Tail391At A (x.outA + 89#64) ⊢
      polyDecoderAt A (x.outA + 80#64) polyDecoderNew1152 := by
    have ha88 : (x.outA + 80#64) + 8#64 = x.outA + 88#64 := by bv_omega
    have ha89 : (x.outA + 80#64) + 9#64 = x.outA + 89#64 := by bv_omega
    rw [← ha88, ← ha89, ← polyDecoderNew1152RawAt_eq_head9_tail391 A (x.outA + 80#64)]
    exact polyDecoderNew1152RawAt_entails_polyDecoderAt A (x.outA + 80#64)
  refine Entails.trans
    (Entails.of_eq (show _ =
      ((x.outA ↦₆₄ g_auth0.rootKey.cap) ∗ ((x.outA + 8#64) ↦₆₄ g_auth0.rootKey.ptr) ∗
        ((x.outA + 16#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.rootKey.length) ∗
        ((x.outA + 24#64) ↦₆₄ g_auth0.macKey.cap) ∗ ((x.outA + 32#64) ↦₆₄ g_auth0.macKey.ptr) ∗
        ((x.outA + 40#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.macKey.length) ∗
        authenticatorHeapAt A g_auth0 x.self.uc.auth) ∗
      (((x.outA + 48#64) ↦₆₄ 64#64) ∗ ((x.outA + 56#64) ↦₆₄ ptr_hdr) ∗
        ((x.outA + 64#64) ↦₆₄ 64#64) ∗ (ptr_hdr ↦ₛ hdrFull.take 64) ∗ A.live ptr_hdr 64 1) ∗
      ((x.outA + 72#64) ↦₆₄ x.epoch) ∗
      (((x.outA + 80#64) ↦₆₄ 0#64) ∗ ((x.outA + 88#64) ↦₈ 2#8) ∗
        polyDecoderNew1152Tail391At A (x.outA + 89#64)) by ac_rfl)) ?_
  exact sepConj_mono hauth (sepConj_mono hvec_hdr (sepConj_mono_right hpoly))

@[local arm64_norm, local wp_norm]
theorem out_32_add_8 (out : BitVec 64) : out + 32#64 + 8#64 = out + 40#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem out_48_add_8 (out : BitVec 64) : out + 48#64 + 8#64 = out + 56#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem out_64_add_8 (out : BitVec 64) : out + 64#64 + 8#64 = out + 72#64 := by bv_omega

theorem sp_1608_words5_shift1 (sp w0 w8 w16 w24 w32 : BitVec 64) :
    ((sp - 1608#64) ↦₆₄ w0) ∗ ((sp - 1600#64) ↦₆₄ w8) ∗ ((sp - 1592#64) ↦₆₄ w16) ∗
      ((sp - 1584#64) ↦₆₄ w24) ∗ ((sp - 1576#64) ↦₆₄ w32) =
      ((sp - 1608#64) ↦₈ Poly.EncoderFromPb.loByte w0) ∗
      ((sp - 1607#64) ↦₆₄ overlapWord1 w0 w8) ∗ ((sp - 1599#64) ↦₆₄ overlapWord1 w8 w16) ∗
      ((sp - 1591#64) ↦₆₄ overlapWord1 w16 w24) ∗ ((sp - 1583#64) ↦₆₄ overlapWord1 w24 w32) ∗
      ((sp - 1575#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 w32) := by
  have h := words5_eq_shift1 (sp - 1608#64) w0 w8 w16 w24 w32
  have ha1 : sp - 1608#64 + 1#64 = sp - 1607#64 := by bv_omega
  have ha8 : sp - 1608#64 + 8#64 = sp - 1600#64 := by bv_omega
  have ha9 : sp - 1608#64 + 9#64 = sp - 1599#64 := by bv_omega
  have ha16 : sp - 1608#64 + 16#64 = sp - 1592#64 := by bv_omega
  have ha17 : sp - 1608#64 + 17#64 = sp - 1591#64 := by bv_omega
  have ha24 : sp - 1608#64 + 24#64 = sp - 1584#64 := by bv_omega
  have ha25 : sp - 1608#64 + 25#64 = sp - 1583#64 := by bv_omega
  have ha32 : sp - 1608#64 + 32#64 = sp - 1576#64 := by bv_omega
  have ha33 : sp - 1608#64 + 33#64 = sp - 1575#64 := by bv_omega
  rw [ha1, ha8, ha9, ha16, ha17, ha24, ha25, ha32, ha33] at h; exact h

theorem sp_1591_words2_unshift1 (sp w16 w24 w32 : BitVec 64) :
    ((sp - 1591#64) ↦₆₄ overlapWord1 w16 w24) ∗ ((sp - 1583#64) ↦₆₄ overlapWord1 w24 w32) ∗
      ((sp - 1575#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 w32) =
      ((sp - 1591#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 w16) ∗
      ((sp - 1584#64) ↦₆₄ w24) ∗ ((sp - 1576#64) ↦₆₄ w32) := by
  have h3 := (hiBytes7_pointsTo64_eq_overlap1 (sp - 1591#64) w16 w24).symm
  have ha24 : sp - 1591#64 + 7#64 = sp - 1584#64 := by bv_omega
  have ha25 : sp - 1591#64 + 8#64 = sp - 1583#64 := by bv_omega
  rw [ha24, ha25] at h3
  have h4 := (hiBytes7_pointsTo64_eq_overlap1 (sp - 1583#64) w24 w32).symm
  have ha32 : sp - 1583#64 + 7#64 = sp - 1576#64 := by bv_omega
  have ha33 : sp - 1583#64 + 8#64 = sp - 1575#64 := by bv_omega
  rw [ha32, ha33] at h4
  calc ((sp - 1591#64) ↦₆₄ overlapWord1 w16 w24) ∗
        ((sp - 1583#64) ↦₆₄ overlapWord1 w24 w32) ∗
        ((sp - 1575#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 w32)
    _ = (((sp - 1591#64) ↦₆₄ overlapWord1 w16 w24) ∗
         ((sp - 1583#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 w24)) ∗
        ((sp - 1576#64) ↦₆₄ w32) := by rw [h4]; ac_rfl
    _ = ((sp - 1591#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 w16) ∗
        ((sp - 1584#64) ↦₆₄ w24) ∗ ((sp - 1576#64) ↦₆₄ w32) := by rw [h3]; ac_rfl

theorem sp_1608_words3_unshift1 (sp w0 w8 w16 : BitVec 64) :
    ((sp - 1608#64) ↦₈ Poly.EncoderFromPb.loByte w0) ∗
      ((sp - 1607#64) ↦₆₄ overlapWord1 w0 w8) ∗ ((sp - 1599#64) ↦₆₄ overlapWord1 w8 w16) ∗
      ((sp - 1591#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 w16) =
      ((sp - 1608#64) ↦₆₄ w0) ∗ ((sp - 1600#64) ↦₆₄ w8) ∗ ((sp - 1592#64) ↦₆₄ w16) := by
  have h := (words3_eq_shift1 (sp - 1608#64) w0 w8 w16).symm
  have ha1 : sp - 1608#64 + 1#64 = sp - 1607#64 := by bv_omega
  have ha8 : sp - 1608#64 + 8#64 = sp - 1600#64 := by bv_omega
  have ha9 : sp - 1608#64 + 9#64 = sp - 1599#64 := by bv_omega
  have ha16 : sp - 1608#64 + 16#64 = sp - 1592#64 := by bv_omega
  have ha17 : sp - 1608#64 + 17#64 = sp - 1591#64 := by bv_omega
  rw [ha1, ha8, ha9, ha16, ha17] at h; exact h

theorem sp_680_words2_shift7 (sp w0 w8 : BitVec 64) :
    ((sp - 680#64) ↦₆₄ w0) ∗ ((sp - 672#64) ↦₆₄ w8) =
      ((sp - 680#64) ↦ₛ Poly.EncoderFromPb.loBytes7 w0) ∗
      ((sp - 673#64) ↦₆₄ FromPb.overlapWord7 w0 w8) ∗
      ((sp - 665#64) ↦₈ Poly.EncoderFromPb.hiByte w8) := by
  have h := words2_eq_loBytes7_overlap7_hiByte (sp - 680#64) w0 w8
  have ha7 : sp - 680#64 + 7#64 = sp - 673#64 := by bv_omega
  have ha8 : sp - 680#64 + 8#64 = sp - 672#64 := by bv_omega
  have ha15 : sp - 680#64 + 15#64 = sp - 665#64 := by bv_omega
  rw [ha7, ha8, ha15] at h; exact h

theorem out_8_words3_shift1 (out u8 u16 u24 : BitVec 64) :
    ((out + 8#64) ↦₆₄ u8) ∗ ((out + 16#64) ↦₆₄ u16) ∗ ((out + 24#64) ↦₆₄ u24) =
      ((out + 8#64) ↦₈ Poly.EncoderFromPb.loByte u8) ∗
      ((out + 9#64) ↦₆₄ overlapWord1 u8 u16) ∗ ((out + 17#64) ↦₆₄ overlapWord1 u16 u24) ∗
      ((out + 25#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 u24) := by
  have h := words3_eq_shift1 (out + 8#64) u8 u16 u24
  have ha9 : out + 8#64 + 1#64 = out + 9#64 := by bv_omega
  have ha16 : out + 8#64 + 8#64 = out + 16#64 := by bv_omega
  have ha17 : out + 8#64 + 9#64 = out + 17#64 := by bv_omega
  have ha24 : out + 8#64 + 16#64 = out + 24#64 := by bv_omega
  have ha25 : out + 8#64 + 17#64 = out + 25#64 := by bv_omega
  rw [ha9, ha16, ha17, ha24, ha25] at h; exact h

theorem out_8_words3_unmerge (out w0 w8 w16 u24 : BitVec 64) :
    ((out + 8#64) ↦₈ Poly.EncoderFromPb.loByte w0) ∗
      ((out + 9#64) ↦₆₄ overlapWord1 w0 w8) ∗ ((out + 17#64) ↦₆₄ overlapWord1 w8 w16) ∗
      ((out + 25#64) ↦ₛ Poly.EncoderFromPb.hiBytes7 u24) =
      ((out + 8#64) ↦₆₄ w0) ∗ ((out + 16#64) ↦₆₄ w8) ∗ ((out + 24#64) ↦₆₄ merge17 w16 u24) := by
  have h := words3_shift1_unmerge (out + 8#64) w0 w8 w16 u24
  have ha9 : out + 8#64 + 1#64 = out + 9#64 := by bv_omega
  have ha16 : out + 8#64 + 8#64 = out + 16#64 := by bv_omega
  have ha17 : out + 8#64 + 9#64 = out + 17#64 := by bv_omega
  have ha24 : out + 8#64 + 16#64 = out + 24#64 := by bv_omega
  have ha25 : out + 8#64 + 17#64 = out + 25#64 := by bv_omega
  rw [ha9, ha16, ha17, ha24, ha25] at h; exact h

theorem poly_1136_split_head9_tail391 (A : RustAlloc) (sp : BitVec 64) :
    polyDecoderNew1152RawAt A (sp - 1136#64) =
      ((sp - 1136#64) ↦₆₄ 0#64) ∗ ((sp - 1128#64) ↦₈ 2#8) ∗
      polyDecoderNew1152Tail391At A (sp - 1127#64) := by
  have h := polyDecoderNew1152RawAt_eq_head9_tail391 A (sp - 1136#64)
  have ha8 : (sp - 1136#64) + 8#64 = sp - 1128#64 := by bv_omega
  have ha9 : (sp - 1136#64) + 9#64 = sp - 1127#64 := by bv_omega
  rw [ha8, ha9] at h; exact h

@[local arm64_norm, local wp_norm]
theorem zeroExtend32_truncate8_loByte (w : BitVec 64) :
    BitVec.truncate 8 (BitVec.truncate 32 (BitVec.zeroExtend 64 (Poly.EncoderFromPb.loByte w))) =
      Poly.EncoderFromPb.loByte w := by
  bv_kernel

@[local arm64_norm, local wp_norm]
theorem bv391_toNat : (391#64 : BitVec 64).toNat = 391 := rfl

theorem collapse_tail_1160_1064 (sp v200 : BitVec 64) :
    memRegion (sp - 1160#64) 24 ∗ memRegion (sp - 1136#64) 400 ∗
      memRegion (sp - 736#64) 80 ∗ memRegion (sp - 656#64) 456 ∗
      ((sp - 200#64) ↦₆₄ v200) ∗ memRegion (sp - 192#64) 24 ∗
      memRegion (sp - 168#64) 48 ∗ memRegion (sp - 120#64) 8 ∗
      memRegion (sp - 112#64) 16 ⊢ memRegion (sp - 1160#64) 1064 := by
  rw [ProofLib.memRegion_split' (b := sp - 1136#64) (n := 384) (k := 16)
        (b' := sp - 752#64) rfl (by bv_omega) (by decide), sepConj_assoc]
  exact rejoin_sp_1160_1064 sp v200

theorem recv_hdr_chunk_eq_macVerifyFailed {F : ShaCompress}
    (self : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (epoch : Epoch) (chunk : Chunk) (receivingHdr : PolyDecoder) (hdrFull : Bytes)
    (hepoch : epoch = self.uc.epoch)
    (hadd : PolyDecoder.addChunk self.receiving_hdr chunk = .ok receivingHdr)
    (hdec : receivingHdr.decodedMessage = .ok (some hdrFull))
    (hge64 : 64 ≤ hdrFull.length) (hmk : self.uc.auth.macKey.length < 2 ^ 32)
    (hle32 : (hdrFull.drop 64).length ≤ 32)
    (hcmp : (compare_prefix (hdrFull.drop 64)
      (self.uc.auth.macHdrUnchecked F epoch (hdrFull.take 64)) != 0#8) = true) :
    self.recv_hdr_chunk epoch chunk = .error (.err .macVerifyFailed) := by
  have hd : (Authenticator.hdrLabel ++ toBEBytes 8 self.uc.epoch ++ hdrFull.take 64).length < 2 ^ 32 := by
    have htake : (hdrFull.take 64).length = 64 := by rw [List.length_take]; omega
    simp only [List.length_append, MacHdrFacts.hdrLabel_length, toBEBytes_8_length, htake]; decide
  have hcmp' : (compare_prefix (hdrFull.drop 64)
      (self.uc.auth.macHdrUnchecked F self.uc.epoch (hdrFull.take 64)) != 0#8) = true := by rwa [← hepoch]
  rw [recv_hdr_chunk_after_decode self epoch chunk receivingHdr hdrFull hepoch hadd hdec (by omega),
      verifyHdrError_of_mac_le_32 F self.uc.auth self.uc.epoch (hdrFull.take 64) (hdrFull.drop 64)
        hmk hd hle32,
      hcmp']
  rfl

theorem recv_hdr_chunk_eq_ok_done {F : ShaCompress}
    (self : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (epoch : Epoch) (chunk : Chunk) (receivingHdr : PolyDecoder) (hdrFull : Bytes)
    (hepoch : epoch = self.uc.epoch)
    (hadd : PolyDecoder.addChunk self.receiving_hdr chunk = .ok receivingHdr)
    (hdec : receivingHdr.decodedMessage = .ok (some hdrFull))
    (hge64 : 64 ≤ hdrFull.length) (hmk : self.uc.auth.macKey.length < 2 ^ 32)
    (hle32 : (hdrFull.drop 64).length ≤ 32)
    (hcmp : (compare_prefix (hdrFull.drop 64)
      (self.uc.auth.macHdrUnchecked F epoch (hdrFull.take 64)) != 0#8) = false) :
    self.recv_hdr_chunk epoch chunk =
      .ok (.done { uc := { auth := self.uc.auth, hdr := hdrFull.take 64, epoch := epoch }
                   receiving_ek := polyDecoderNew1152 }) := by
  have hd : (Authenticator.hdrLabel ++ toBEBytes 8 self.uc.epoch ++ hdrFull.take 64).length < 2 ^ 32 := by
    have htake : (hdrFull.take 64).length = 64 := by rw [List.length_take]; omega
    simp only [List.length_append, MacHdrFacts.hdrLabel_length, toBEBytes_8_length, htake]; decide
  have hcmp' : (compare_prefix (hdrFull.drop 64)
      (self.uc.auth.macHdrUnchecked F self.uc.epoch (hdrFull.take 64)) != 0#8) = false := by rwa [← hepoch]
  rw [recv_hdr_chunk_after_decode self epoch chunk receivingHdr hdrFull hepoch hadd hdec (by omega),
      verifyHdrError_of_mac_le_32 F self.uc.auth self.uc.epoch (hdrFull.take 64) (hdrFull.drop 64)
        hmk hd hle32,
      hcmp', ← hepoch]
  rfl

end CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
