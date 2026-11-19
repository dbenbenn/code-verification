/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkDefs
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Common -- proof-setup: allow-public-import
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<NoHeaderReceived>::recv_hdr_chunk` — Part 1 (`0x61254 .. 0x61488`)

**Checked by Lean.** Callee `subroutine_ok` wrappers, panic helpers, the `None` (`StillReceiving`)
branch (`recv_hdr_chunk_none_wpp`), and `Some(hdrFull)` length check with `mac`/`hdr` heap
allocations (`recv_hdr_chunk_alloc_mac_hdr_wpp`).
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

abbrev recvHdrChunkPostQp (F : ShaCompress) (_A : RustAlloc) (_b : BitVec 64)
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (⌜((x.self.recv_hdr_chunk x.epoch x.chunk).isPanic = true ∨ allocFailedIn s0 sf) ∧
            s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)

theorem noHeaderReceivedUcAt_expose_entails (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (uc : Unchunked.SendCt.NoHeaderReceived (spqrAuthApi F)) :
    unchunkedNoHeaderReceivedAt A a uc ⊢
      ∃∗ g_auth : AuthenticatorGhost,
        (a ↦₆₄ g_auth.rootKey.cap) ∗
        ((a + 8#64) ↦₆₄ g_auth.rootKey.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 uc.auth.rootKey.length) ∗
        ((a + 24#64) ↦₆₄ g_auth.macKey.cap) ∗
        ((a + 32#64) ↦₆₄ g_auth.macKey.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 uc.auth.macKey.length) ∗
        ((a + 48#64) ↦₆₄ uc.epoch) ∗
        authenticatorHeapAt A g_auth uc.auth := by
  unfold unchunkedNoHeaderReceivedAt
  rw [authenticatorAt_eq_exists_pinned A a uc.auth]
  refine Entails.trans (sepConj_mono_left (Entails.sepExists_elim fun g_auth =>
    Entails.sepExists_right g_auth (Entails.of_eq (authenticatorPinAt_eq_cells_heap A g_auth a uc.auth)))) ?_
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun g_auth => Entails.sepExists_right g_auth ?_
  exact Entails.of_eq (by ac_rfl)

theorem noHeaderReceivedUcAt_fold_entails (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (uc : Unchunked.SendCt.NoHeaderReceived (spqrAuthApi F))
    (g_auth : AuthenticatorGhost) :
    (a ↦₆₄ g_auth.rootKey.cap) ∗
      ((a + 8#64) ↦₆₄ g_auth.rootKey.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 uc.auth.rootKey.length) ∗
      ((a + 24#64) ↦₆₄ g_auth.macKey.cap) ∗
      ((a + 32#64) ↦₆₄ g_auth.macKey.ptr) ∗
      ((a + 40#64) ↦₆₄ BitVec.ofNat 64 uc.auth.macKey.length) ∗
      ((a + 48#64) ↦₆₄ uc.epoch) ∗
      authenticatorHeapAt A g_auth uc.auth ⊢
      unchunkedNoHeaderReceivedAt A a uc := by
  unfold unchunkedNoHeaderReceivedAt
  have harrange :
      (a ↦₆₄ g_auth.rootKey.cap) ∗
        ((a + 8#64) ↦₆₄ g_auth.rootKey.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 uc.auth.rootKey.length) ∗
        ((a + 24#64) ↦₆₄ g_auth.macKey.cap) ∗
        ((a + 32#64) ↦₆₄ g_auth.macKey.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 uc.auth.macKey.length) ∗
        ((a + 48#64) ↦₆₄ uc.epoch) ∗
        authenticatorHeapAt A g_auth uc.auth =
      ((a ↦₆₄ g_auth.rootKey.cap) ∗
        ((a + 8#64) ↦₆₄ g_auth.rootKey.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 uc.auth.rootKey.length) ∗
        ((a + 24#64) ↦₆₄ g_auth.macKey.cap) ∗
        ((a + 32#64) ↦₆₄ g_auth.macKey.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 uc.auth.macKey.length) ∗
        authenticatorHeapAt A g_auth uc.auth) ∗
      ((a + 48#64) ↦₆₄ uc.epoch) := by ac_rfl
  rw [harrange, ← authenticatorPinAt_eq_cells_heap A g_auth a uc.auth]
  exact sepConj_mono_left (authenticatorPinAt_entails_authenticatorAt A g_auth a uc.auth)

theorem noHeaderReceivedCells_entails_memRegion_456
    (a c0 c1 c2 c3 c4 c5 c6 : BitVec 64) :
    (a ↦₆₄ c0) ∗ ((a + 8#64) ↦₆₄ c1) ∗ ((a + 16#64) ↦₆₄ c2) ∗
      ((a + 24#64) ↦₆₄ c3) ∗ ((a + 32#64) ↦₆₄ c4) ∗ ((a + 40#64) ↦₆₄ c5) ∗
      ((a + 48#64) ↦₆₄ c6) ∗ memRegion (a + 56#64) 400 ⊢
      memRegion a chunkedNoHeaderReceivedSize := by
  change _ ⊢ memRegion a 456
  rw [ProofLib.memRegion_split' (b := a) (n := 56) (k := 400)
        (b' := a + 56#64) rfl rfl (by decide),
      ProofLib.memRegion_cells a 7 (by decide)]
  have hc7 :
      (a ↦₆₄ c0) ∗ ((a + 8#64) ↦₆₄ c1) ∗ ((a + 16#64) ↦₆₄ c2) ∗
        ((a + 24#64) ↦₆₄ c3) ∗ ((a + 32#64) ↦₆₄ c4) ∗ ((a + 40#64) ↦₆₄ c5) ∗
        ((a + 48#64) ↦₆₄ c6) ⊢ cells a 7 := by
    dsimp only [cells]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
      emp_sepConj, sepConj_emp]
    exact Entails.sepExists_right c0 (Entails.sepExists_right c1 (Entails.sepExists_right c2
      (Entails.sepExists_right c3 (Entails.sepExists_right c4 (Entails.sepExists_right c5
        (Entails.sepExists_right c6 (Entails.refl _)))))))
  have hgroup :
      (a ↦₆₄ c0) ∗ ((a + 8#64) ↦₆₄ c1) ∗ ((a + 16#64) ↦₆₄ c2) ∗
        ((a + 24#64) ↦₆₄ c3) ∗ ((a + 32#64) ↦₆₄ c4) ∗ ((a + 40#64) ↦₆₄ c5) ∗
        ((a + 48#64) ↦₆₄ c6) ∗ memRegion (a + 56#64) 400 =
      ((a ↦₆₄ c0) ∗ ((a + 8#64) ↦₆₄ c1) ∗ ((a + 16#64) ↦₆₄ c2) ∗
        ((a + 24#64) ↦₆₄ c3) ∗ ((a + 32#64) ↦₆₄ c4) ∗ ((a + 40#64) ↦₆₄ c5) ∗
        ((a + 48#64) ↦₆₄ c6)) ∗ memRegion (a + 56#64) 400 := by ac_rfl
  rw [hgroup]
  exact sepConj_mono_left hc7

theorem memRegion_456_at_fsp_3e0_split (fsp : BitVec 64) :
    memRegion (fsp + 0x3e0#64) 456 =
      (∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64,
       ∃∗ d4 : BitVec 64, ∃∗ d5 : BitVec 64, ∃∗ d6 : BitVec 64,
        ((fsp + 0x3e0#64) ↦₆₄ d0) ∗ ((fsp + 0x3e8#64) ↦₆₄ d1) ∗
        ((fsp + 0x3f0#64) ↦₆₄ d2) ∗ ((fsp + 0x3f8#64) ↦₆₄ d3) ∗
        ((fsp + 0x400#64) ↦₆₄ d4) ∗ ((fsp + 0x408#64) ↦₆₄ d5) ∗
        ((fsp + 0x410#64) ↦₆₄ d6)) ∗
      memRegion (fsp + 0x418#64) 400 := by
  rw [ProofLib.memRegion_split' (b := fsp + 0x3e0#64) (n := 56) (k := 400)
        (b' := fsp + 0x418#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells (fsp + 0x3e0#64) 7 (by decide)]
  congr 1
  dsimp only [cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    emp_sepConj, sepConj_emp]

theorem chunkedNoHeaderReceivedAt_fsp_3e0_entails (A : RustAlloc) {F : ShaCompress}
    (sp : BitVec 64) (uc : Unchunked.SendCt.NoHeaderReceived (spqrAuthApi F))
    (receivingHdr : PolyDecoder) (g_auth : AuthenticatorGhost) :
    ((sp - 656#64) ↦₆₄ g_auth.rootKey.cap) ∗
      ((sp - 648#64) ↦₆₄ g_auth.rootKey.ptr) ∗
      ((sp - 640#64) ↦₆₄ BitVec.ofNat 64 uc.auth.rootKey.length) ∗
      ((sp - 632#64) ↦₆₄ g_auth.macKey.cap) ∗
      ((sp - 624#64) ↦₆₄ g_auth.macKey.ptr) ∗
      ((sp - 616#64) ↦₆₄ BitVec.ofNat 64 uc.auth.macKey.length) ∗
      ((sp - 608#64) ↦₆₄ uc.epoch) ∗
      authenticatorHeapAt A g_auth uc.auth ∗
      polyDecoderAt A (sp - 600#64) receivingHdr ⊢
      chunkedNoHeaderReceivedAt A (sp - 656#64) { uc := uc, receiving_hdr := receivingHdr } := by
  unfold chunkedNoHeaderReceivedAt unchunkedNoHeaderReceivedAt
  have h56 : (sp - 656#64) + 56#64 = sp - 600#64 := by bv_omega
  have h8 : (sp - 656#64) + 8#64 = sp - 648#64 := by bv_omega
  have h16 : (sp - 656#64) + 16#64 = sp - 640#64 := by bv_omega
  have h24 : (sp - 656#64) + 24#64 = sp - 632#64 := by bv_omega
  have h32 : (sp - 656#64) + 32#64 = sp - 624#64 := by bv_omega
  have h40 : (sp - 656#64) + 40#64 = sp - 616#64 := by bv_omega
  have h48 : (sp - 656#64) + 48#64 = sp - 608#64 := by bv_omega
  rw [h56, h48]
  have hauth := authenticatorPinAt_entails_authenticatorAt A g_auth (sp - 656#64) uc.auth
  rw [authenticatorPinAt_eq_cells_heap A g_auth (sp - 656#64) uc.auth, h8, h16, h24, h32, h40] at hauth
  have hgroup :
      ((sp - 656#64) ↦₆₄ g_auth.rootKey.cap) ∗
        ((sp - 648#64) ↦₆₄ g_auth.rootKey.ptr) ∗
        ((sp - 640#64) ↦₆₄ BitVec.ofNat 64 uc.auth.rootKey.length) ∗
        ((sp - 632#64) ↦₆₄ g_auth.macKey.cap) ∗
        ((sp - 624#64) ↦₆₄ g_auth.macKey.ptr) ∗
        ((sp - 616#64) ↦₆₄ BitVec.ofNat 64 uc.auth.macKey.length) ∗
        ((sp - 608#64) ↦₆₄ uc.epoch) ∗
        authenticatorHeapAt A g_auth uc.auth ∗
        polyDecoderAt A (sp - 600#64) receivingHdr =
      ((((sp - 656#64) ↦₆₄ g_auth.rootKey.cap) ∗
          ((sp - 648#64) ↦₆₄ g_auth.rootKey.ptr) ∗
          ((sp - 640#64) ↦₆₄ BitVec.ofNat 64 uc.auth.rootKey.length) ∗
          ((sp - 632#64) ↦₆₄ g_auth.macKey.cap) ∗
          ((sp - 624#64) ↦₆₄ g_auth.macKey.ptr) ∗
          ((sp - 616#64) ↦₆₄ BitVec.ofNat 64 uc.auth.macKey.length) ∗
          authenticatorHeapAt A g_auth uc.auth) ∗
        ((sp - 608#64) ↦₆₄ uc.epoch)) ∗
      polyDecoderAt A (sp - 600#64) receivingHdr := by ac_rfl
  rw [hgroup]
  exact sepConj_mono_left (sepConj_mono_left hauth)

theorem memRegion_480_outA_split (outA : BitVec 64) :
    memRegion outA chunkedHeaderReceivedSize =
      (∃∗ v0 : BitVec 64, outA ↦₆₄ v0) ∗
        memRegion (outA + 8#64) 456 ∗
        memRegion (outA + 464#64) 16 := by
  change memRegion outA 480 = _
  rw [ProofLib.memRegion_split' (b := outA) (n := 8) (k := 472)
        (b' := outA + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := outA + 8#64) (n := 456) (k := 16)
        (b' := outA + 464#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight outA]

/-! ## 3. `None` (`StillReceiving`) Branch (`0x61308 .. 0x6134c` + `0x6161c .. 0x61638`) -/

theorem ofNat_ult_64_of_lt {n : Nat} (h : n < 64) :
    (BitVec.ofNat 64 n).ult 64#64 = true := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    Nat.mod_eq_of_lt (by decide : 64 < 2 ^ 64), decide_eq_true_eq]
  exact h

theorem ofNat_ult_64_of_ge {n : Nat} (hge : 64 ≤ n) (hlt : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).ult 64#64 = false := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    Nat.mod_eq_of_lt (by decide : 64 < 2 ^ 64), decide_eq_false_iff_not]
  omega

theorem ofNat_sub_64_eq {n : Nat} (hge : 64 ≤ n) (hlt : n < 2 ^ 63) :
    BitVec.ofNat 64 n - 64#64 = BitVec.ofNat 64 (n - 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le]
  · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : n - 64 < 2 ^ 64)]
  · rw [BitVec.le_def]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)]
    exact hge

theorem ofNat_sub_64_eq_zero_iff {n : Nat} (hge : 64 ≤ n) (hlt : n < 2 ^ 63) :
    (BitVec.ofNat 64 (n - 64) == 0#64) = decide (n = 64) := by
  by_cases h : n = 64
  · subst h; decide
  · rw [decide_eq_false h]
    apply beq_false_of_ne
    intro h0
    have h1 := congrArg BitVec.toNat h0
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
    change n - 64 = 0 at h1
    omega

theorem addWithCarry64_sub_64_n (a : BitVec 64) :
    (AddWithCarry64 a 18446744073709551551#64 true).2.n = (a - 64#64).getLsbD 63 := by
  dsimp [AddWithCarry64]
  have htrunc :
      BitVec.setWidth 64 (1#65 + (18446744073709551551#65 + BitVec.setWidth 65 a)) =
        a - 64#64 := by
    bv_kernel
  rw [htrunc, BitVec.msb_eq_getLsbD_last]

theorem vecU8HeapAt_split_64 (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hge : 64 ≤ bs.length) :
    vecU8HeapAt A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
      (ptr ↦ₛ bs.take 64) ∗
      ((ptr + 64#64) ↦ₛ bs.drop 64) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
      A.live ptr cap.toNat 1 := by
  dsimp only [vecU8HeapAt]
  apply Entails.pure_left; rintro ⟨hle, hmax, hptr_ne⟩
  have hcap_ne : cap ≠ 0 := by
    intro h0; subst h0
    have hle0 : bs.length ≤ 0 := hle
    omega
  simp only [hcap_ne, ↓reduceIte]
  have htake_len : (bs.take 64).length = 64 := by rw [List.length_take]; omega
  have happ : bs.take 64 ++ bs.drop 64 = bs := List.take_append_drop 64 bs
  conv_lhs => arg 2; arg 1; rw [← happ, pointsToBytes_append, htake_len]
  refine Entails.pure_right ⟨hle, hmax, hptr_ne, hcap_ne⟩ ?_
  exact Entails.of_eq (by ac_rfl)

@[simp] theorem ofNat_64_eq : BitVec.ofNat 64 64 = 64#64 := rfl
@[simp] theorem ofNat_64_toNat : (64#64 : BitVec 64).toNat = 64 := rfl

theorem savedRegsAt_of_cells12_hdr (s0 : State) :
    ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
      ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
      ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
      ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
      ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
      ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ⊢ savedRegsAt s0 :=
  Entails.refl _

theorem cells11_sp_1648_expand (sp : BitVec 64) :
    cells (sp - 1648#64) 11 =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64,
        ((sp - 1648#64) ↦₆₄ c0) ∗ ((sp - 1640#64) ↦₆₄ c1) ∗
        ((sp - 1632#64) ↦₆₄ c2) ∗ ((sp - 1624#64) ↦₆₄ c3) ∗
        ((sp - 1616#64) ↦₆₄ c4) ∗ ((sp - 1608#64) ↦₆₄ c5) ∗
        ((sp - 1600#64) ↦₆₄ c6) ∗ ((sp - 1592#64) ↦₆₄ c7) ∗
        ((sp - 1584#64) ↦₆₄ c8) ∗ ((sp - 1576#64) ↦₆₄ c9) ∗
        ((sp - 1568#64) ↦₆₄ c10)) := by
  dsimp only [cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    emp_sepConj, sepConj_emp, wp_norm, arm64_norm]

theorem cells11_sp_1648_fold (sp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : BitVec 64) :
    ((sp - 1648#64) ↦₆₄ c0) ∗ ((sp - 1640#64) ↦₆₄ c1) ∗
      ((sp - 1632#64) ↦₆₄ c2) ∗ ((sp - 1624#64) ↦₆₄ c3) ∗
      ((sp - 1616#64) ↦₆₄ c4) ∗ ((sp - 1608#64) ↦₆₄ c5) ∗
      ((sp - 1600#64) ↦₆₄ c6) ∗ ((sp - 1592#64) ↦₆₄ c7) ∗
      ((sp - 1584#64) ↦₆₄ c8) ∗ ((sp - 1576#64) ↦₆₄ c9) ∗
      ((sp - 1568#64) ↦₆₄ c10) ⊢ cells (sp - 1648#64) 11 := by
  rw [cells11_sp_1648_expand sp]
  exact Entails.sepExists_right c0 (Entails.sepExists_right c1 (Entails.sepExists_right c2
    (Entails.sepExists_right c3 (Entails.sepExists_right c4 (Entails.sepExists_right c5
      (Entails.sepExists_right c6 (Entails.sepExists_right c7 (Entails.sepExists_right c8
        (Entails.sepExists_right c9 (Entails.sepExists_right c10 (Entails.refl _)))))))))))

theorem optKeyBytesAt_none_sp_1160 (A : RustAlloc) (sp : BitVec 64) :
    optKeyBytesAt A (sp - 1160#64) none =
      ((sp - 1160#64) ↦₆₄ noneCap) ∗ memRegion (sp - 1152#64) 16 := by
  unfold optKeyBytesAt
  have h2 : (sp - 1160#64) + 8#64 = sp - 1152#64 := by bv_omega
  rw [h2]

theorem optKeyBytesAt_some_sp_1160 (A : RustAlloc) (sp : BitVec 64) (bs : List (BitVec 8)) :
    optKeyBytesAt A (sp - 1160#64) (some bs) ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((sp - 1160#64) ↦₆₄ cap) ∗
        ((sp - 1152#64) ↦₆₄ ptr) ∗
        ((sp - 1144#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8HeapAt A cap ptr bs := by
  have h2 : (sp - 1160#64) + 8#64 = sp - 1152#64 := by bv_omega
  have h3 : (sp - 1160#64) + 16#64 = sp - 1144#64 := by bv_omega
  have hexp := optKeyBytesAt_some_expose A (sp - 1160#64) bs
  rw [h2, h3] at hexp
  exact hexp

theorem memRegion_24_of_sp_1160 (sp v0 v1 v2 : BitVec 64) :
    ((sp - 1160#64) ↦₆₄ v0) ∗ ((sp - 1152#64) ↦₆₄ v1) ∗ ((sp - 1144#64) ↦₆₄ v2) ⊢
      memRegion (sp - 1160#64) 24 := by
  have h2 : (sp - 1160#64) + 8#64 = sp - 1152#64 := by bv_omega
  have h3 : (sp - 1160#64) + 16#64 = sp - 1144#64 := by bv_omega
  rw [memRegion_24_cells (sp - 1160#64), h2, h3]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1
    (Entails.sepExists_right v2 (Entails.refl _)))

theorem fold_none_addrs_sp_hdr (A : RustAlloc) (sp : BitVec 64) (dec : PolyDecoder) :
    polyDecoderAt A (sp - 1560#64) dec ∗
      ((sp - 1160#64) ↦₆₄ noneCap) ∗ memRegion (sp - 1152#64) 16 ∗
      memRegion (sp - 656#64) 456 ⊢
    polyDecoderAt A ((sp - 1648#64) + 0x58#64) dec ∗
      optKeyBytesAt A ((sp - 1648#64) + 0x1e8#64) none ∗
      memRegion ((sp - 1648#64) + 0x3e0#64) 456 := by
  dsimp only [optKeyBytesAt]
  have h1 : (sp - 1648#64) + 0x58#64 = sp - 1560#64 := by bv_omega
  have h2 : (sp - 1648#64) + 0x1e8#64 = sp - 1160#64 := by bv_omega
  have h3 : (sp - 1160#64) + 8#64 = sp - 1152#64 := by bv_omega
  have h4 : (sp - 1648#64) + 0x3e0#64 = sp - 656#64 := by bv_omega
  rw [h1, h2, h3, h4]
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
