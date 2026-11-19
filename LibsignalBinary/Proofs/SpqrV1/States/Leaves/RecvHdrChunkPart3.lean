/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<NoHeaderReceived>::recv_hdr_chunk` — Part 3 (`0x61488 .. 0x6150c`)

**Checked by Lean.** Verifies `recv_hdr_chunk_hmac_wpp` (offsets `564 .. 696`): `sliceConcat3`,
`libcrux_hmac`, and `ct_mac_data` deallocation.
-/

public section

set_option autoImplicit false

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
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.CodeLayout
open CryptoVerification
open CryptoVerification.LibsignalSpqrV1.PolyDecoder
open CryptoVerification.LibsignalTripleRatchet.Keys
open CryptoVerification.SpqrV1.ChainProofs
open UpdateFacts NextKeyInternalFacts AgreeStateSimp SplitBytes NewFacts

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false toBEBytes_8_length MacHdrFacts.hdrLabel_length
attribute [-arm64_norm]
  HkdfToSliceProof.sp_sub_688_eq_hsp
  HkdfToSliceProof.sp_add_neg688_eq_hsp
  HkdfToSliceProof.sp_sub_96_eq_hsp_592
  HkdfToSliceProof.sp_add_neg96_eq_hsp_592

theorem bytes_rem_entails_memRegion_hdr (ptr cap : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length ≤ cap.toNat) (hmax : cap.toNat + 1 ≤ 2 ^ 63) :
    (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ⊢
      memRegion ptr cap.toNat := by
  rw [ProofLib.memRegion_split' (b := ptr) (n := bs.length) (k := cap.toNat - bs.length)
        (b' := ptr + BitVec.ofNat 64 bs.length) (by omega) rfl (by omega)]
  exact sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)

theorem page_align_mask_hdr {b : BitVec 64} (halign : b &&& 4095#64 = 0#64) :
    b &&& 18446744073709547520#64 = b := by
  have hb : (b &&& 18446744073709547520#64) + (b &&& 4095#64) = b := by bv_kernel
  rw [halign, BitVec.add_zero] at hb
  exact hb

theorem verifyHdrError_of_key_ge_32 (F : ShaCompress) (auth : Authenticator) (ep : Epoch)
    (hdr mac : Bytes) (hk : 2 ^ 32 ≤ auth.macKey.length) :
    auth.verifyHdrError F ep hdr mac = .error hmacU32UnwrapPanic := by
  have hnot : ¬ (auth.macKey.length < 2 ^ 32 ∧
      (Authenticator.hdrLabel ++ toBEBytes 8 ep ++ hdr).length < 2 ^ 32) := by
    omega
  simp only [Authenticator.verifyHdrError, Authenticator.verifyHdr, Authenticator.macHdr, hnot,
    ↓reduceIte, Bind.bind, Except.bind, Except.map]

theorem recv_hdr_chunk_isPanic_of_macKey_ge_32 {F : ShaCompress}
    (self : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (epoch : Epoch) (chunk : Chunk) (receivingHdr : PolyDecoder) (hdrFull : Bytes)
    (hepoch : epoch = self.uc.epoch)
    (hadd : PolyDecoder.addChunk self.receiving_hdr chunk = .ok receivingHdr)
    (hdec : receivingHdr.decodedMessage = .ok (some hdrFull))
    (hge : 64 ≤ hdrFull.length)
    (hk : 2 ^ 32 ≤ self.uc.auth.macKey.length) :
    (self.recv_hdr_chunk epoch chunk).isPanic = true := by
  have hafter := recv_hdr_chunk_after_decode self epoch chunk receivingHdr hdrFull
    hepoch hadd hdec (by omega)
  dsimp only at hafter
  have herr := verifyHdrError_of_key_ge_32 F self.uc.auth self.uc.epoch
    (hdrFull.take 64) (hdrFull.drop 64) hk
  rw [hafter, herr]
  rfl

/-- Call-site specialized `libcrux_hmac::hmac` specification for `recv_hdr_chunk` where
    `2 ^ 32 ≤ x.key.length` implies `P` (`isPanic = true`). -/
@[expose] def libcruxHmacHdrSpec (s0_top : State) (P : Prop) (F : ShaCompress) (A : RustAlloc) :
    Spec LibcruxHmacCall where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.ret ∧ (s.readReg64 .x0).setWidth 32 = 0#32 ∧
      s.readReg64 .x1 = x.keyA ∧ (s.readReg64 .x2).toNat = x.key.length ∧
      s.readReg64 .x3 = x.dataA ∧ (s.readReg64 .x4).toNat = x.data.length ∧
      (s.readReg64 .x5).setWidth 32 = 1#32 ∧ s.readReg64 .x6 = 32#64 ∧
      s.trace = s0_top.trace ∧
      (2 ^ 32 ≤ x.key.length → P) ∧ x.data.length < 2 ^ 32⌝ ∗
      (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
      memRegion x.ret 24 ∗ A.pool ∗ stackAt s.sp extHookStack
  post := fun x s0 sf =>
    ⌜x.key.length < 2 ^ 32 ∧ sf.trace = s0.trace⌝ ∗
      (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
      vecU8 A x.ret (hmacWith F x.key x.data) ∗ A.pool ∗ stackAt s0.sp extHookStack
  onPanic := fun _ s0 sf =>
    ⌜(P ∨ allocFailedIn s0_top sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem onPanic_or_alloc_entails_recvHdr {Q : Prop} {s0 s sf : State} {F : SepProp}
    (htr : s.trace = s0.trace) :
    (⌜Q ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜Q ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  rw [htr, sepConj_assoc]
  exact sepConj_mono_right (entails_anyHeap _)

theorem authenticatorHeapAt_expose_macKey (A : RustAlloc) (g : AuthenticatorGhost)
    (auth : Authenticator) :
    authenticatorHeapAt A g auth ⊢
      ⌜auth.macKey.length ≤ g.macKey.cap.toNat ∧ g.macKey.cap.toNat < 2 ^ 63 ∧ g.macKey.ptr ≠ 0⌝ ∗
        (g.macKey.ptr ↦ₛ auth.macKey) ∗
        vecU8HeapAt A g.rootKey.cap g.rootKey.ptr auth.rootKey ∗
        (if g.macKey.cap = 0 then emp
         else A.live g.macKey.ptr g.macKey.cap.toNat 1 ∗
           memRegion (g.macKey.ptr + BitVec.ofNat 64 auth.macKey.length) (g.macKey.cap.toNat - auth.macKey.length)) := by
  unfold authenticatorHeapAt vecU8HeapAt
  rw [show ⌜auth.rootKey.length ≤ g.rootKey.cap.toNat ∧ g.rootKey.cap.toNat < 2 ^ 63 ∧ g.rootKey.ptr ≠ 0⌝ ∗
        (if g.rootKey.cap = 0 then emp
         else A.live g.rootKey.ptr g.rootKey.cap.toNat 1 ∗ (g.rootKey.ptr ↦ₛ auth.rootKey) ∗
           memRegion (g.rootKey.ptr + BitVec.ofNat 64 auth.rootKey.length) (g.rootKey.cap.toNat - auth.rootKey.length)) ∗
        ⌜auth.macKey.length ≤ g.macKey.cap.toNat ∧ g.macKey.cap.toNat < 2 ^ 63 ∧ g.macKey.ptr ≠ 0⌝ ∗
        (if g.macKey.cap = 0 then emp
         else A.live g.macKey.ptr g.macKey.cap.toNat 1 ∗ (g.macKey.ptr ↦ₛ auth.macKey) ∗
           memRegion (g.macKey.ptr + BitVec.ofNat 64 auth.macKey.length) (g.macKey.cap.toNat - auth.macKey.length)) =
      ⌜auth.macKey.length ≤ g.macKey.cap.toNat ∧ g.macKey.cap.toNat < 2 ^ 63 ∧ g.macKey.ptr ≠ 0⌝ ∗
        ((if g.macKey.cap = 0 then emp
          else A.live g.macKey.ptr g.macKey.cap.toNat 1 ∗ (g.macKey.ptr ↦ₛ auth.macKey) ∗
            memRegion (g.macKey.ptr + BitVec.ofNat 64 auth.macKey.length) (g.macKey.cap.toNat - auth.macKey.length)) ∗
         (⌜auth.rootKey.length ≤ g.rootKey.cap.toNat ∧ g.rootKey.cap.toNat < 2 ^ 63 ∧ g.rootKey.ptr ≠ 0⌝ ∗
           (if g.rootKey.cap = 0 then emp
            else A.live g.rootKey.ptr g.rootKey.cap.toNat 1 ∗ (g.rootKey.ptr ↦ₛ auth.rootKey) ∗
              memRegion (g.rootKey.ptr + BitVec.ofNat 64 auth.rootKey.length) (g.rootKey.cap.toNat - auth.rootKey.length)))) by ac_rfl]
  refine Entails.pure_left fun ⟨hle, hlt, hptr⟩ => ?_
  refine Entails.pure_right ⟨hle, hlt, hptr⟩ ?_
  by_cases hcap : g.macKey.cap = 0
  · have hle0 : auth.macKey.length ≤ (0 : BitVec 64).toNat := hcap ▸ hle
    have hbs : auth.macKey = [] := List.eq_nil_of_length_eq_zero (by change auth.macKey.length ≤ 0 at hle0; omega)
    rw [hbs]
    simp only [hcap, ↓reduceIte, pointsToBytes_nil, emp_sepConj, sepConj_emp]
    exact Entails.refl _
  · simp only [hcap, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)

theorem authenticatorHeapAt_unexpose_macKey (A : RustAlloc) (g : AuthenticatorGhost)
    (auth : Authenticator)
    (hle : auth.macKey.length ≤ g.macKey.cap.toNat)
    (hlt : g.macKey.cap.toNat < 2 ^ 63)
    (hptr : g.macKey.ptr ≠ 0) :
    (g.macKey.ptr ↦ₛ auth.macKey) ∗
      vecU8HeapAt A g.rootKey.cap g.rootKey.ptr auth.rootKey ∗
      (if g.macKey.cap = 0 then emp
       else A.live g.macKey.ptr g.macKey.cap.toNat 1 ∗
         memRegion (g.macKey.ptr + BitVec.ofNat 64 auth.macKey.length) (g.macKey.cap.toNat - auth.macKey.length)) ⊢
      authenticatorHeapAt A g auth := by
  unfold authenticatorHeapAt vecU8HeapAt
  rw [show ⌜auth.rootKey.length ≤ g.rootKey.cap.toNat ∧ g.rootKey.cap.toNat < 2 ^ 63 ∧ g.rootKey.ptr ≠ 0⌝ ∗
        (if g.rootKey.cap = 0 then emp
         else A.live g.rootKey.ptr g.rootKey.cap.toNat 1 ∗ (g.rootKey.ptr ↦ₛ auth.rootKey) ∗
           memRegion (g.rootKey.ptr + BitVec.ofNat 64 auth.rootKey.length) (g.rootKey.cap.toNat - auth.rootKey.length)) ∗
        ⌜auth.macKey.length ≤ g.macKey.cap.toNat ∧ g.macKey.cap.toNat < 2 ^ 63 ∧ g.macKey.ptr ≠ 0⌝ ∗
        (if g.macKey.cap = 0 then emp
         else A.live g.macKey.ptr g.macKey.cap.toNat 1 ∗ (g.macKey.ptr ↦ₛ auth.macKey) ∗
           memRegion (g.macKey.ptr + BitVec.ofNat 64 auth.macKey.length) (g.macKey.cap.toNat - auth.macKey.length)) =
      ⌜auth.macKey.length ≤ g.macKey.cap.toNat ∧ g.macKey.cap.toNat < 2 ^ 63 ∧ g.macKey.ptr ≠ 0⌝ ∗
        ((if g.macKey.cap = 0 then emp
          else A.live g.macKey.ptr g.macKey.cap.toNat 1 ∗ (g.macKey.ptr ↦ₛ auth.macKey) ∗
            memRegion (g.macKey.ptr + BitVec.ofNat 64 auth.macKey.length) (g.macKey.cap.toNat - auth.macKey.length)) ∗
         (⌜auth.rootKey.length ≤ g.rootKey.cap.toNat ∧ g.rootKey.cap.toNat < 2 ^ 63 ∧ g.rootKey.ptr ≠ 0⌝ ∗
           (if g.rootKey.cap = 0 then emp
            else A.live g.rootKey.ptr g.rootKey.cap.toNat 1 ∗ (g.rootKey.ptr ↦ₛ auth.rootKey) ∗
              memRegion (g.rootKey.ptr + BitVec.ofNat 64 auth.rootKey.length) (g.rootKey.cap.toNat - auth.rootKey.length)))) by ac_rfl]
  refine Entails.pure_right ⟨hle, hlt, hptr⟩ ?_
  by_cases hcap : g.macKey.cap = 0
  · have hle0 : auth.macKey.length ≤ (0 : BitVec 64).toNat := hcap ▸ hle
    have hbs : auth.macKey = [] := List.eq_nil_of_length_eq_zero (by change auth.macKey.length ≤ 0 at hle0; omega)
    rw [hbs]
    simp only [hcap, ↓reduceIte, pointsToBytes_nil, emp_sepConj, sepConj_emp]
    exact Entails.refl _
  · simp only [hcap, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)

theorem memRegion_48_sp_168_cells (sp : BitVec 64) :
    memRegion (sp - 168#64) 48 =
      (∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64,
       ∃∗ s3 : BitVec 64, ∃∗ s4 : BitVec 64, ∃∗ s5 : BitVec 64,
        ((sp - 168#64) ↦₆₄ s0) ∗ ((sp - 160#64) ↦₆₄ s1) ∗
        ((sp - 152#64) ↦₆₄ s2) ∗ ((sp - 144#64) ↦₆₄ s3) ∗
        ((sp - 136#64) ↦₆₄ s4) ∗ ((sp - 128#64) ↦₆₄ s5)) := by
  change memRegion (sp - 168#64) (8 * 6) = _
  rw [ProofLib.memRegion_cells (sp - 168#64) 6 (by decide)]
  dsimp only [cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    emp_sepConj, sepConj_emp, wp_norm, arm64_norm]

theorem fold_sp_168_24_24 (sp s0 s1 s2 s3 s4 s5 : BitVec 64) :
    ((sp - 168#64) ↦₆₄ s0) ∗ ((sp - 160#64) ↦₆₄ s1) ∗ ((sp - 152#64) ↦₆₄ s2) ∗
      ((sp - 144#64) ↦₆₄ s3) ∗ ((sp - 136#64) ↦₆₄ s4) ∗ ((sp - 128#64) ↦₆₄ s5) ⊢
      memRegion (sp - 168#64) 24 ∗ memRegion (sp - 144#64) 24 := by
  have h1 : (sp - 168#64) + 8#64 = sp - 160#64 := by bv_omega
  have h2 : (sp - 168#64) + 16#64 = sp - 152#64 := by bv_omega
  have h3 : (sp - 144#64) + 8#64 = sp - 136#64 := by bv_omega
  have h4 : (sp - 144#64) + 16#64 = sp - 128#64 := by bv_omega
  rw [memRegion_24_cells (sp - 168#64), memRegion_24_cells (sp - 144#64), h1, h2, h3, h4]
  have hassoc :
      ((sp - 168#64) ↦₆₄ s0) ∗ ((sp - 160#64) ↦₆₄ s1) ∗ ((sp - 152#64) ↦₆₄ s2) ∗
        ((sp - 144#64) ↦₆₄ s3) ∗ ((sp - 136#64) ↦₆₄ s4) ∗ ((sp - 128#64) ↦₆₄ s5) =
      (((sp - 168#64) ↦₆₄ s0) ∗ ((sp - 160#64) ↦₆₄ s1) ∗ ((sp - 152#64) ↦₆₄ s2)) ∗
        (((sp - 144#64) ↦₆₄ s3) ∗ ((sp - 136#64) ↦₆₄ s4) ∗ ((sp - 128#64) ↦₆₄ s5)) := by ac_rfl
  rw [hassoc]
  exact sepConj_mono
    (Entails.sepExists_right s0 (Entails.sepExists_right s1 (Entails.sepExists_right s2 (Entails.refl _))))
    (Entails.sepExists_right s3 (Entails.sepExists_right s4 (Entails.sepExists_right s5 (Entails.refl _))))

theorem vecU8_expose_nonempty_192 (A : RustAlloc) (sp : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) :
    vecU8 A (sp - 192#64) bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜cap ≠ 0#64 ∧ LayoutOk cap.toNat 1 ∧ ptr ≠ 0#64 ∧ bs.length ≤ cap.toNat⌝ ∗
          ((sp - 192#64) ↦₆₄ cap) ∗
          ((sp - 184#64) ↦₆₄ ptr) ∗
          ((sp - 176#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
          A.live ptr cap.toNat 1 := by
  dsimp only [vecU8]
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [vecU8At_eq_cells_heap A (sp - 192#64) cap ptr bs]
  have h8 : (sp - 192#64) + 8#64 = sp - 184#64 := by bv_omega
  have h16 : (sp - 192#64) + 16#64 = sp - 176#64 := by bv_omega
  rw [h8, h16]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (vecU8HeapAt_expose_nonempty A cap ptr bs hpos)))) ?_
  have hcomm :
      ((sp - 192#64) ↦₆₄ cap) ∗ ((sp - 184#64) ↦₆₄ ptr) ∗
        ((sp - 176#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
          (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
          A.live ptr cap.toNat 1) =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
        ((sp - 192#64) ↦₆₄ cap) ∗ ((sp - 184#64) ↦₆₄ ptr) ∗
        ((sp - 176#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
        A.live ptr cap.toNat 1 := by ac_rfl
  rw [hcomm]
  refine Entails.pure_left fun ⟨hle, hmax, hptr, hcap⟩ => ?_
  have hpos_cap : 0 < cap.toNat := by
    have : cap.toNat ≠ 0 := fun h0 => hcap (BitVec.eq_of_toNat_eq h0)
    omega
  have hlay : LayoutOk cap.toNat 1 := ⟨hpos_cap, ⟨0, rfl⟩, by omega⟩
  exact Entails.pure_right ⟨hcap, hlay, hptr, hle⟩ (Entails.refl _)

theorem memRegion_24_of_sp_192 (sp v0 v1 v2 : BitVec 64) :
    ((sp - 192#64) ↦₆₄ v0) ∗ ((sp - 184#64) ↦₆₄ v1) ∗ ((sp - 176#64) ↦₆₄ v2) ⊢
      memRegion (sp - 192#64) 24 := by
  have h1 : (sp - 192#64) + 8#64 = sp - 184#64 := by bv_omega
  have h2 : (sp - 192#64) + 16#64 = sp - 176#64 := by bv_omega
  rw [memRegion_24_cells (sp - 192#64), h1, h2]
  exact Entails.sepExists_right v0
    (Entails.sepExists_right v1 (Entails.sepExists_right v2 (Entails.refl _)))

theorem macHdrUnchecked_eq_hmacWith_hdr (F : ShaCompress)
    (auth : Authenticator) (ep : Epoch) (hdr : Bytes) :
    auth.macHdrUnchecked F ep hdr =
      hmacWith F auth.macKey (Authenticator.hdrLabel ++ toBEBytes 8 ep ++ hdr) := by
  unfold Authenticator.macHdrUnchecked
  exact hmacWith_take_macSize F _ _

attribute [local irreducible] Chunked.SendCt.NoHeaderReceived.recv_hdr_chunk

end CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
