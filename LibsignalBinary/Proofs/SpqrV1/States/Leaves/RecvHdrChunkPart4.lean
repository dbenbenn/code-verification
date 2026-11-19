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
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart3
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<NoHeaderReceived>::recv_hdr_chunk` — Part 4 (`0x6150c .. 0x61574` / `0x61678`)

**Checked by Lean.** Verifies the constant-time bytewise comparison loop
(`recv_hdr_chunk_compare_loop_wpp`, offsets `740 .. 764`) and MAC tag comparison + deallocation
(`recv_hdr_chunk_mac_compare_wpp`, offsets `696 .. 800` / `1060`).
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

theorem vecU8_expose_nonempty_168 (A : RustAlloc) (sp : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) :
    vecU8 A (sp - 168#64) bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜cap ≠ 0#64 ∧ LayoutOk cap.toNat 1 ∧ ptr ≠ 0#64 ∧ bs.length ≤ cap.toNat⌝ ∗
          ((sp - 168#64) ↦₆₄ cap) ∗
          ((sp - 160#64) ↦₆₄ ptr) ∗
          ((sp - 152#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
          A.live ptr cap.toNat 1 := by
  dsimp only [vecU8]
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [vecU8At_eq_cells_heap A (sp - 168#64) cap ptr bs]
  have h8 : (sp - 168#64) + 8#64 = sp - 160#64 := by bv_omega
  have h16 : (sp - 168#64) + 16#64 = sp - 152#64 := by bv_omega
  rw [h8, h16]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (vecU8HeapAt_expose_nonempty A cap ptr bs hpos)))) ?_
  have hcomm :
      ((sp - 168#64) ↦₆₄ cap) ∗ ((sp - 160#64) ↦₆₄ ptr) ∗
        ((sp - 152#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
          (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
          A.live ptr cap.toNat 1) =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
        ((sp - 168#64) ↦₆₄ cap) ∗ ((sp - 160#64) ↦₆₄ ptr) ∗
        ((sp - 152#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
        A.live ptr cap.toNat 1 := by ac_rfl
  rw [hcomm]
  refine Entails.pure_left fun ⟨hle, hmax, hptr, hcap⟩ => ?_
  have hpos_cap : 0 < cap.toNat := by
    have : cap.toNat ≠ 0 := fun h0 => hcap (BitVec.eq_of_toNat_eq h0)
    omega
  have hlay : LayoutOk cap.toNat 1 := ⟨hpos_cap, ⟨0, rfl⟩, by omega⟩
  exact Entails.pure_right ⟨hcap, hlay, hptr, hle⟩ (Entails.refl _)

theorem rejoin_memRegion_48_24_24 (sp : BitVec 64) (u0 u1 u2 : BitVec 64) :
    ((sp - 168#64) ↦₆₄ u0) ∗ ((sp - 160#64) ↦₆₄ u1) ∗ ((sp - 152#64) ↦₆₄ u2) ∗
      memRegion (sp - 144#64) 24 ⊢
      memRegion (sp - 168#64) 48 := by
  have h1 : (sp - 168#64) + 8#64 = sp - 160#64 := by bv_omega
  have h2 : (sp - 168#64) + 16#64 = sp - 152#64 := by bv_omega
  have h24 :
      ((sp - 168#64) ↦₆₄ u0) ∗ ((sp - 160#64) ↦₆₄ u1) ∗ ((sp - 152#64) ↦₆₄ u2) ⊢
        memRegion (sp - 168#64) 24 := by
    rw [memRegion_24_cells (sp - 168#64), h1, h2]
    exact Entails.sepExists_right u0 (Entails.sepExists_right u1 (Entails.sepExists_right u2 (Entails.refl _)))
  rw [ProofLib.memRegion_split' (b := sp - 168#64) (n := 24) (k := 24)
        (b' := sp - 144#64) rfl (by bv_omega) (by decide)]
  have hassoc :
      ((sp - 168#64) ↦₆₄ u0) ∗ ((sp - 160#64) ↦₆₄ u1) ∗ ((sp - 152#64) ↦₆₄ u2) ∗
        memRegion (sp - 144#64) 24 =
      (((sp - 168#64) ↦₆₄ u0) ∗ ((sp - 160#64) ↦₆₄ u1) ∗ ((sp - 152#64) ↦₆₄ u2)) ∗
        memRegion (sp - 144#64) 24 := by ac_rfl
  rw [hassoc]
  exact sepConj_mono_left h24

theorem stackAt_extHook_eq_16_hdr (sp : BitVec 64) :
    stackAt (sp - 1648#64) extHookStack =
      memRegion (sp - 18032#64) 16368 ∗ stackAt (sp - 1648#64) 16 := by
  have h := stackAt_split_bottom (sp - 1648#64) 16 16368 (by decide)
  have h2 : (sp - 1648#64) - BitVec.ofNat 64 (16 + 16368) = sp - 18032#64 := by
    change (sp - 1648#64) - 16384#64 = sp - 18032#64
    bv_omega
  rw [h2] at h
  exact h

theorem sub_one_ofNat_succ (n : Nat) (hn : n < 32) :
    BitVec.ofNat 64 (n + 1) - 1#64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (BitVec.ofNat 64 (n + 1)).toNat = n + 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2 : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h3 : (1#64 : BitVec 64).toNat = 1 := rfl
  rw [BitVec.toNat_sub_of_le]
  · omega
  · rw [BitVec.le_def]; omega

theorem bne_one_ofNat_cons2 (a a2 : BitVec 8) (lhs'' : List (BitVec 8))
    (hle : (a :: a2 :: lhs'').length ≤ 32) :
    (BitVec.ofNat 64 (a :: a2 :: lhs'').length != 1#64) = true := by
  simp only [bne_iff_ne]
  intro h1
  have h2 := congrArg BitVec.toNat h1
  simp only [List.length_cons] at hle h2
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h2
  change lhs''.length + 1 + 1 = 1 at h2
  omega

theorem sub_one_ofNat_cons2 (a a2 : BitVec 8) (lhs'' : List (BitVec 8))
    (hle : (a :: a2 :: lhs'').length ≤ 32) :
    BitVec.ofNat 64 (a :: a2 :: lhs'').length - 1#64 =
      BitVec.ofNat 64 (a2 :: lhs'').length := by
  simp only [List.length_cons] at hle ⊢
  exact sub_one_ofNat_succ (lhs''.length + 1) (by omega)

theorem xor_orr_loop_step (acc a b : BitVec 8) :
    BitVec.zeroExtend 64
      (BitVec.truncate 32
        (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 b ^^^ BitVec.zeroExtend 64 a)) |||
          BitVec.zeroExtend 64 acc)) =
      BitVec.zeroExtend 64 (acc ||| (a ^^^ b)) := by
  ext i hi
  by_cases h32 : i < 32 <;> simp [h32, Bool.or_comm, Bool.xor_comm]

theorem vecBufAt_expose_of_bytes_live (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8))
    (hne0 : bs.length ≠ 0) (hle : bs.length < 2 ^ 63) :
    vecBufAt A (BitVec.ofNat 64 bs.length) ptr bs ⊢
      (ptr ↦ₛ bs) ∗ A.live ptr bs.length 1 := by
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_ne : BitVec.ofNat 64 bs.length ≠ 0 := by
    intro h0
    have h1 := congrArg BitVec.toNat h0
    rw [htoNat] at h1
    change bs.length = 0 at h1
    omega
  dsimp only [vecBufAt]
  simp only [hcap_ne, ↓reduceIte, htoNat, Nat.sub_self, memRegion_zero, sepConj_emp]
  exact Entails.refl _

theorem isNonZero_foldl_eq_compare_prefix (lhs rhs : List (BitVec 8)) :
    isNonZero (List.foldl (fun r x => r ||| x.1 ^^^ x.2) 0#8 (lhs.zip rhs)) =
      compare_prefix lhs rhs := rfl

theorem tst_ff_zeroExtend_64_false_of_bne {v : BitVec 8} (h : (v != 0#8) = true) :
    (BitVec.truncate 32 (BitVec.zeroExtend 64 v &&& 1095216660735#64) == 0#32) = false := by
  revert v h; decide

theorem tst_ff_zeroExtend_64_true_of_bne_false {v : BitVec 8} (h : (v != 0#8) = false) :
    (BitVec.truncate 32 (BitVec.zeroExtend 64 v &&& 1095216660735#64) == 0#32) = true := by
  revert v h; decide

theorem ule_32_sub_65_iff {n : Nat} (hge : 65 ≤ n) (hlt : n < 2 ^ 63) :
    (32#64 : BitVec 64).ule (BitVec.ofNat 64 n - 65#64) = true ↔ ¬ (n - 64 ≤ 32) := by
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h65 : (65#64 : BitVec 64).toNat = 65 := rfl
  have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
  rw [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_sub_of_le]
  · omega
  · rw [BitVec.le_def]; omega

theorem recv_hdr_chunk_isPanic_of_mac_gt_32 {F : ShaCompress}
    (self : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (epoch : Epoch) (chunk : Chunk) (receivingHdr : PolyDecoder) (hdrFull : Bytes)
    (hepoch : epoch = self.uc.epoch)
    (hadd : PolyDecoder.addChunk self.receiving_hdr chunk = .ok receivingHdr)
    (hdec : receivingHdr.decodedMessage = .ok (some hdrFull))
    (hge : 64 ≤ hdrFull.length)
    (hk : self.uc.auth.macKey.length < 2 ^ 32)
    (hm : ¬ (hdrFull.drop 64).length ≤ 32) :
    (self.recv_hdr_chunk epoch chunk).isPanic = true := by
  have hafter := recv_hdr_chunk_after_decode self epoch chunk receivingHdr hdrFull
    hepoch hadd hdec (by omega)
  dsimp only at hafter
  have htake64 : (hdrFull.take 64).length = 64 := by rw [List.length_take]; omega
  have hd_lt : (Authenticator.hdrLabel ++ toBEBytes 8 self.uc.epoch ++ hdrFull.take 64).length < 2 ^ 32 := by
    simp only [List.length_append, MacHdrFacts.hdrLabel_length, toBEBytes_8_length, htake64]
    decide
  have herr := verifyHdrError_of_mac_gt_32 F self.uc.auth self.uc.epoch
    (hdrFull.take 64) (hdrFull.drop 64) hk hd_lt hm
  rw [hafter, herr]
  rfl

attribute [local irreducible] Chunked.SendCt.NoHeaderReceived.recv_hdr_chunk

/-! ## 2. Constant-Time Bytewise Comparison Loop (`0x61538 .. 0x61550`, offsets `740 .. 764`) -/

end CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
