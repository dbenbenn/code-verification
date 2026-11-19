/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.VerifySignatureA -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.VerifySignature
import ProofLib.ProgramReflection.SortedFresh
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy
import LibsignalBinary.Proofs.CodeLayout

/-!
# Contract-Backed `<PublicKey>::verify_signature` on `tripleRatchetProgAtExt`

Proves `SepWP` specifications for
`<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message` and
`verify_signature` on `tripleRatchetProgAtExt` under `PqxdhHookContractsExt`, preserving
`calleeSavedVRegs` across XEdDSA verification.
-/

public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 200000

namespace CryptoVerification.E2E.Pqxdh.Shared

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy
  (packEdBytes unpackEdBytes unpackEdBytes_packEdBytes)
open SignalPqxdh SignalPqxdh.Model

section WithProgramExt
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64

private theorem calleeSavedVRegs_setPC_pre_ext (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := calleeSavedVRegs_setPC s pc
private theorem calleeSavedVRegs_setMem_setPC_pre_ext (s : State) (m : Memory) (pc : BitVec 64) :
    calleeSavedVRegs ((s.setMem m).setPC pc) = calleeSavedVRegs s := by
  rw [calleeSavedVRegs_setPC, calleeSavedVRegs_setMem]

attribute [local arm64_norm ↓, local wp_norm ↓] sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre calleeSavedVRegs_setPC_pre_ext calleeSavedVRegs_setMem_setPC_pre_ext

attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  and64_mask255_ite_1_0 csinc_eq_zero32_ite_1_0

private theorem list_sig_split_63_ext {sig : Bytes} (hsig : sig.length = 64) :
    bytesToBv8 sig = bytesToBv8 (sig.take 63) ++ [(bytesToBv8 sig).getD 63 0#8] := by
  rcases sig with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | ⟨b8, _ | ⟨b9, _ | ⟨b10,
    _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15, _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21,
    _ | ⟨b22, _ | ⟨b23, _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31, _ | ⟨b32,
    _ | ⟨b33, _ | ⟨b34, _ | ⟨b35, _ | ⟨b36, _ | ⟨b37, _ | ⟨b38, _ | ⟨b39, _ | ⟨b40, _ | ⟨b41, _ | ⟨b42, _ | ⟨b43,
    _ | ⟨b44, _ | ⟨b45, _ | ⟨b46, _ | ⟨b47, _ | ⟨b48, _ | ⟨b49, _ | ⟨b50, _ | ⟨b51, _ | ⟨b52, _ | ⟨b53, _ | ⟨b54,
    _ | ⟨b55, _ | ⟨b56, _ | ⟨b57, _ | ⟨b58, _ | ⟨b59, _ | ⟨b60, _ | ⟨b61, _ | ⟨b62, _ | ⟨b63, _ |
      _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (simp at hsig)
  rfl

private theorem sig_focus_63_ext {sig : Bytes} (sigPtr : BitVec 64) (h : sig.length = 64) :
    (sigPtr ↦ₛ bytesToBv8 sig) = ((sigPtr ↦ₛ bytesToBv8 (sig.take 63)) ∗
       ((sigPtr + 63#64) ↦₈ (bytesToBv8 sig).getD 63 0#8)) := by
  have hl63 : (bytesToBv8 (sig.take 63)).length = 63 := by simp [bytesToBv8, h]
  conv => lhs; rw [list_sig_split_63_ext h]
  rw [pointsToBytes_append, hl63]; simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

@[local simp, local wp_norm, local arm64_norm]
private theorem sig_getD63_ushiftRight7_eq_signBit_ext (sig : Bytes) :
    (bytesToBv8 sig).getD 63 0#8 >>> 7 = BitVec.ofNat 8 (((sig.getD 63 0 &&& 0x80) >>> 7).toNat) := by
  rw [bytesToBv8_getD_eq]; rcases sig.getD 63 0 with ⟨bv⟩; revert bv; decide

private theorem cells_12_merge_ext (a v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
      ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗ ((a + 48#64) ↦₆₄ v6) ∗ ((a + 56#64) ↦₆₄ v7) ∗
      ((a + 64#64) ↦₆₄ v8) ∗ ((a + 72#64) ↦₆₄ v9) ∗ ((a + 80#64) ↦₆₄ v10) ∗ ((a + 88#64) ↦₆₄ v11) ⊢ memRegion a 96 := by
  rw [memRegion_cells a 12 (by decide)]
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.sepExists_right v0 <| Entails.sepExists_right v1 <| Entails.sepExists_right v2 <|
    Entails.sepExists_right v3 <| Entails.sepExists_right v4 <| Entails.sepExists_right v5 <|
    Entails.sepExists_right v6 <| Entails.sepExists_right v7 <| Entails.sepExists_right v8 <|
    Entails.sepExists_right v9 <| Entails.sepExists_right v10 <| Entails.sepExists_right v11 <| Entails.refl _

theorem stackAt_verifySig_merge_ext (fsp : BitVec 64) :
    stackAt fsp verifySigHookStackExt ∗ memRegion fsp 1152 ∗ memRegion (fsp + 1152#64) 96 =
      stackAt (fsp + 1248#64) (verifySigHookStackExt + 1248) := by
  have h1248 : memRegion fsp 1152 ∗ memRegion (fsp + 1152#64) 96 = memRegion fsp 1248 :=
    (ProofLib.memRegion_split' (b := fsp) (n := 1152) (k := 96) (b' := fsp + 1152#64) rfl (by bv_omega) (by decide)).symm
  rw [h1248, memRegion_cells fsp 156 (by decide)]
  have hsp : fsp = (fsp + 1248#64) - 1248#64 := by bv_omega
  conv => lhs; rw [hsp]
  exact (stackAt_split_cells (fsp + 1248#64) verifySigHookStackExt 156 (by decide)).symm

theorem stackAt_verifySigHook_split48_memRegion_ext (fsp : BitVec 64) :
    stackAt fsp verifySigHookStackExt = stackAt fsp pqxdhHookStackExt ∗ memRegion (fsp - 16432#64) 48 := by
  rw [stackAt_verifySigHook_split_48_ext fsp, ctEqCells_sepConj_stackAt_ext fsp]

private theorem memRegion168_of_cell_and_memRegion160_v_ext (a : BitVec 64) (v : BitVec 64) :
    (a ↦₆₄ v) ∗ memRegion (a + 8#64) 160 ⊢ memRegion a 168 := by
  refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion a v)) (Entails.of_eq ?_)
  exact (ProofLib.memRegion_split' (b := a) (n := 8) (k := 160) (b' := a + 8#64) rfl (by bv_omega) (by decide)).symm

private theorem memRegion168_of_cell_and_bytes160_ext (a : BitVec 64) (v : BitVec 64)
    {bs : List (BitVec 8)} (hlen : bs.length = 160) : (a ↦₆₄ v) ∗ ((a + 8#64) ↦ₛ bs) ⊢ memRegion a 168 := by
  refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion a v)
    (pointsToBytes_entails_memRegion_n (a + 8#64) bs hlen)) (Entails.of_eq ?_)
  exact (ProofLib.memRegion_split' (b := a) (n := 8) (k := 160) (b' := a + 8#64) rfl (by bv_omega) (by decide)).symm

private theorem exists_unpack64_of_length_160_eq_ext {bs : List (BitVec 8)} (h : bs.length = 160) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : BitVec 64,
      ∀ a : BitVec 64, (a ↦ₛ bs) =
        ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
         ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗
         ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) ∗
         ((a + 96#64) ↦₆₄ w12) ∗ ((a + 104#64) ↦₆₄ w13) ∗ ((a + 112#64) ↦₆₄ w14) ∗ ((a + 120#64) ↦₆₄ w15) ∗
         ((a + 128#64) ↦₆₄ w16) ∗ ((a + 136#64) ↦₆₄ w17) ∗ ((a + 144#64) ↦₆₄ w18) ∗ ((a + 152#64) ↦₆₄ w19)) := by
  have h0 : (bs.take 32).length = 32 := by simp [h]
  have h1 : ((bs.drop 32).take 32).length = 32 := by simp [h]
  have h2 : ((bs.drop 64).take 32).length = 32 := by simp [h]
  have h3 : ((bs.drop 96).take 32).length = 32 := by simp [h]
  have h4 : (bs.drop 128).length = 32 := by simp [h]
  obtain ⟨w0, w1, w2, w3, _, hp0⟩ := exists_unpack64_of_length_32 h0
  obtain ⟨w4, w5, w6, w7, _, hp1⟩ := exists_unpack64_of_length_32 h1
  obtain ⟨w8, w9, w10, w11, _, hp2⟩ := exists_unpack64_of_length_32 h2
  obtain ⟨w12, w13, w14, w15, _, hp3⟩ := exists_unpack64_of_length_32 h3
  obtain ⟨w16, w17, w18, w19, _, hp4⟩ := exists_unpack64_of_length_32 h4
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, fun a => ?_⟩
  have hsplit : bs = bs.take 32 ++ ((bs.drop 32).take 32 ++ ((bs.drop 64).take 32 ++ ((bs.drop 96).take 32 ++ bs.drop 128))) := by
    have s4 : bs.drop 96 = (bs.drop 96).take 32 ++ bs.drop 128 := by simpa [List.drop_drop] using (List.take_append_drop 32 (bs.drop 96)).symm
    have s3 : bs.drop 64 = (bs.drop 64).take 32 ++ bs.drop 96 := by simpa [List.drop_drop] using (List.take_append_drop 32 (bs.drop 64)).symm
    have s2 : bs.drop 32 = (bs.drop 32).take 32 ++ bs.drop 64 := by simpa [List.drop_drop] using (List.take_append_drop 32 (bs.drop 32)).symm
    have s1 : bs = bs.take 32 ++ bs.drop 32 := (List.take_append_drop 32 bs).symm
    rw [s4] at s3; rw [s3] at s2; rw [s2] at s1; exact s1
  conv => lhs; rw [hsplit]
  rw [pointsToBytes_append, h0, hp0, pointsToBytes_append, h1, hp1, pointsToBytes_append, h2, hp2, pointsToBytes_append, h3, hp3, hp4]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem uint8_and7f_ule32_of_and60_eq_false_ext (b : UInt8) (h : (b &&& 0x60 == 0) = false) :
    (32#64).ule (BitVec.zeroExtend 64 b.toBitVec &&& 545460846719#64) = true := by rcases b with ⟨bv⟩; revert bv h; decide
private theorem uint8_and7f_ule32_of_and60_eq_true_ext (b : UInt8) (h : (b &&& 0x60 == 0) = true) :
    (32#64).ule (BitVec.zeroExtend 64 b.toBitVec &&& 545460846719#64) = false := by rcases b with ⟨bv⟩; revert bv h; decide
private theorem truncate32_and7f_eq_ext (sig : Bytes) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 (sig.getD 63 0).toBitVec &&& 545460846719#64) =
      BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32 := by
  rw [bytesToBv8_getD_eq]; generalize sig.getD 63 0 = b; rcases b with ⟨bv⟩; revert bv; decide

private theorem sha512IV_cells_eq_ext (a : BitVec 64) :
    ((a ↦₆₄ 0x6a09e667f3bcc908#64) ∗ ((a + 8#64) ↦₆₄ 0xbb67ae8584caa73b#64) ∗
     ((a + 16#64) ↦₆₄ 0x3c6ef372fe94f82b#64) ∗ ((a + 24#64) ↦₆₄ 0xa54ff53a5f1d36f1#64) ∗
     ((a + 32#64) ↦₆₄ 0x510e527fade682d1#64) ∗ ((a + 40#64) ↦₆₄ 0x9b05688c2b3e6c1f#64) ∗
     ((a + 48#64) ↦₆₄ 0x1f83d9abfb41bd6b#64) ∗ ((a + 56#64) ↦₆₄ 0x5be0cd19137e2179#64)) = (a ↦ₛ sha512IVBytesLE) := by
  rw [sha512IVBytesLE_eq_unpack64]
  simp only [List.append_assoc, pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes, BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_verifySig_split_ext (fsp : BitVec 64) :
    stackAt (fsp + 1248#64) (verifySigHookStackExt + 1248) = stackAt fsp verifySigHookStackExt ∗ memRegion fsp 1152 ∗ cells (fsp + 1152#64) 12 := by
  rw [← stackAt_verifySig_merge_ext fsp, memRegion_cells (fsp + 1152#64) 12 (by decide)]

private theorem memRegion_1152_seg1a_split_ext (fsp : BitVec 64) :
    memRegion fsp 1152 = cells fsp 1 ∗ memRegion (fsp + 8#64) 8 ∗ cells (fsp + 16#64) 4 ∗ memRegion (fsp + 48#64) 752 ∗ memRegion (fsp + 800#64) 168 ∗ memRegion (fsp + 968#64) 184 := by
  rw [ProofLib.memRegion_split' (b := fsp) (n := 8) (k := 1144) (b' := fsp + 8#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b := fsp + 8#64) (n := 8) (k := 1136) (b' := fsp + 16#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 16#64) (n := 32) (k := 1104) (b' := fsp + 48#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b := fsp + 48#64) (n := 752) (k := 352) (b' := fsp + 800#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 800#64) (n := 168) (k := 184) (b' := fsp + 968#64) rfl (by bv_omega) (by decide), memRegion_cells fsp 1 (by decide), memRegion_cells (fsp + 16#64) 4 (by decide)]

private theorem memRegion_1152_seg1a_merge_ext (fsp : BitVec 64) :
    (fsp ↦₆₄ 0#64) ∗ memRegion (fsp + 8#64) 8 ∗ memRegion (fsp + 16#64) 32 ∗ memRegion (fsp + 48#64) 752 ∗ memRegion (fsp + 800#64) 168 ∗ memRegion (fsp + 968#64) 184 ⊢ memRegion fsp 1152 := by
  refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion fsp 0#64)) (Entails.of_eq ?_)
  rw [← ProofLib.memRegion_split' (b := fsp + 800#64) (n := 168) (k := 184) (b' := fsp + 968#64) rfl (by bv_omega) (by decide), ← ProofLib.memRegion_split' (b := fsp + 48#64) (n := 752) (k := 352) (b' := fsp + 800#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp + 16#64) (n := 32) (k := 1104) (b' := fsp + 48#64) rfl (by bv_omega) (by decide), ← ProofLib.memRegion_split' (b := fsp + 8#64) (n := 8) (k := 1136) (b' := fsp + 16#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp) (n := 8) (k := 1144) (b' := fsp + 8#64) rfl (by bv_omega) (by decide)]

private theorem memRegion_752_seg1b_split_ext (fsp : BitVec 64) :
    memRegion (fsp + 48#64) 752 = cells (fsp + 48#64) 20 ∗ cells (fsp + 208#64) 20 ∗ memRegion (fsp + 368#64) 32 ∗ memRegion (fsp + 400#64) 400 := by
  rw [ProofLib.memRegion_split' (b := fsp + 48#64) (n := 160) (k := 592) (b' := fsp + 208#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b := fsp + 208#64) (n := 160) (k := 432) (b' := fsp + 368#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 368#64) (n := 32) (k := 400) (b' := fsp + 400#64) rfl (by bv_omega) (by decide), memRegion_cells (fsp + 48#64) 20 (by decide), memRegion_cells (fsp + 208#64) 20 (by decide)]

private theorem memRegion_752_seg1b_merge_ext (fsp : BitVec 64) {edPt capA : Bytes} (hed : edPt.length = 160) (hcapA : capA.length = 32) :
    memRegion (fsp + 48#64) 160 ∗ ((fsp + 208#64) ↦ₛ bytesToBv8 edPt) ∗ ((fsp + 368#64) ↦ₛ bytesToBv8 capA) ∗ memRegion (fsp + 400#64) 400 ⊢ memRegion (fsp + 48#64) 752 := by
  have h1 : ((fsp + 208#64) ↦ₛ bytesToBv8 edPt) ⊢ memRegion (fsp + 208#64) 160 :=
    pointsToBytes_entails_memRegion_n _ _ (by simp [bytesToBv8, hed])
  have h2 : ((fsp + 368#64) ↦ₛ bytesToBv8 capA) ⊢ memRegion (fsp + 368#64) 32 :=
    pointsToBytes_entails_memRegion_n _ _ (by simp [bytesToBv8, hcapA])
  refine Entails.trans (sepConj_mono_right (sepConj_mono h1 (sepConj_mono_left h2))) (Entails.of_eq ?_)
  rw [← ProofLib.memRegion_split' (b := fsp + 368#64) (n := 32) (k := 400) (b' := fsp + 400#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp + 208#64) (n := 160) (k := 432) (b' := fsp + 368#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp + 48#64) (n := 160) (k := 592) (b' := fsp + 208#64) rfl (by bv_omega) (by decide)]

private theorem seg1b_to_seg1c_split_ext (fsp : BitVec 64) : (fsp ↦₆₄ 0#64) ∗ memRegion (fsp + 8#64) 8 ∗ memRegion (fsp + 400#64) 400 ⊢
    memRegion fsp 4 ∗ memRegion (fsp + 4#64) 4 ∗ cells (fsp + 8#64) 1 ∗ memRegion (fsp + 400#64) 160 ∗ cells (fsp + 560#64) 8 ∗ memRegion (fsp + 624#64) 63 ∗ memRegion (fsp + 687#64) 1 ∗ cells (fsp + 688#64) 10 ∗ memRegion (fsp + 768#64) 32 := by
  refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion fsp 0#64)) (Entails.of_eq ?_)
  rw [ProofLib.memRegion_split' (b := fsp) (n := 4) (k := 4) (b' := fsp + 4#64) rfl (by bv_omega) (by decide), memRegion_cells (fsp + 8#64) 1 (by decide),
    ProofLib.memRegion_split' (b := fsp + 400#64) (n := 160) (k := 240) (b' := fsp + 560#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b := fsp + 560#64) (n := 64) (k := 176) (b' := fsp + 624#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 624#64) (n := 63) (k := 113) (b' := fsp + 687#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b := fsp + 687#64) (n := 1) (k := 112) (b' := fsp + 688#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 688#64) (n := 80) (k := 32) (b' := fsp + 768#64) rfl (by bv_omega) (by decide), memRegion_cells (fsp + 560#64) 8 (by decide), memRegion_cells (fsp + 688#64) 10 (by decide)]
  simp only [sepConj_assoc]

private theorem memRegion_800_seg3a_split_ext (fsp : BitVec 64) :
    memRegion (fsp + 800#64) 168 ∗ memRegion (fsp + 968#64) 184 = cells (fsp + 800#64) 16 ∗ cells (fsp + 928#64) 10 ∗ cells (fsp + 1008#64) 16 ∗ memRegion (fsp + 1136#64) 16 := by
  rw [← ProofLib.memRegion_split' (b := fsp + 800#64) (n := 168) (k := 184) (b' := fsp + 968#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b := fsp + 800#64) (n := 128) (k := 224) (b' := fsp + 928#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 928#64) (n := 80) (k := 144) (b' := fsp + 1008#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b := fsp + 1008#64) (n := 128) (k := 16) (b' := fsp + 1136#64) rfl (by bv_omega) (by decide),
    memRegion_cells (fsp + 800#64) 16 (by decide), memRegion_cells (fsp + 928#64) 10 (by decide), memRegion_cells (fsp + 1008#64) 16 (by decide)]

private theorem seg3a_to_seg3b_split_ext (fsp : BitVec 64) :
    cells (fsp + 800#64) 16 ∗ cells (fsp + 928#64) 10 ∗ cells (fsp + 1008#64) 16 = cells (fsp + 800#64) 4 ∗ memRegion (fsp + 832#64) 128 ∗ memRegion (fsp + 960#64) 48 ∗ memRegion (fsp + 1008#64) 32 ∗ memRegion (fsp + 1040#64) 96 := by
  rw [← memRegion_cells (fsp + 800#64) 16 (by decide), ← memRegion_cells (fsp + 928#64) 10 (by decide), ← memRegion_cells (fsp + 1008#64) 16 (by decide),
    ← ProofLib.memRegion_split' (b := fsp + 928#64) (n := 80) (k := 128) (b' := fsp + 1008#64) rfl (by bv_omega) (by decide), ← ProofLib.memRegion_split' (b := fsp + 800#64) (n := 128) (k := 208) (b' := fsp + 928#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 800#64) (n := 32) (k := 304) (b' := fsp + 832#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b := fsp + 832#64) (n := 128) (k := 176) (b' := fsp + 960#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := fsp + 960#64) (n := 48) (k := 128) (b' := fsp + 1008#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b := fsp + 1008#64) (n := 32) (k := 96) (b' := fsp + 1040#64) rfl (by bv_omega) (by decide),
    memRegion_cells (fsp + 800#64) 4 (by decide)]

private theorem seg3b_to_epilogue_merge_ext (fsp : BitVec 64) (v4 : BitVec 32) (v8 : BitVec 64)
    {capA minusCapA hScalar : Bytes} (hcapA : capA.length = 32) (hnegA : minusCapA.length = 160) (hh : hScalar.length = 32) :
    memRegion fsp 4 ∗ ((fsp + 4#64) ↦₃₂ v4) ∗ ((fsp + 8#64) ↦₆₄ v8) ∗ memRegion (fsp + 16#64) 32 ∗ memRegion (fsp + 48#64) 160 ∗ memRegion (fsp + 208#64) 160 ∗ ((fsp + 368#64) ↦ₛ bytesToBv8 capA) ∗ ((fsp + 400#64) ↦ₛ bytesToBv8 minusCapA) ∗ cells (fsp + 560#64) 16 ∗ cells (fsp + 688#64) 10 ∗ ((fsp + 768#64) ↦ₛ bytesToBv8 hScalar) ∗ memRegion (fsp + 800#64) 160 ∗ memRegion (fsp + 960#64) 48 ∗ memRegion (fsp + 1008#64) 32 ∗ memRegion (fsp + 1040#64) 96 ∗ memRegion (fsp + 1136#64) 16 ⊢ memRegion fsp 1152 := by
  have hw4 : ((fsp + 4#64) ↦₃₂ v4) ⊢ memRegion (fsp + 4#64) 4 := pointsTo32_entails_memRegion _ _
  have hw8 : ((fsp + 8#64) ↦₆₄ v8) ⊢ memRegion (fsp + 8#64) 8 := pointsTo64_entails_memRegion _ _
  have hw368 : ((fsp + 368#64) ↦ₛ bytesToBv8 capA) ⊢ memRegion (fsp + 368#64) 32 := pointsToBytes_entails_memRegion_n _ _ (by simp [bytesToBv8, hcapA])
  have hw400 : ((fsp + 400#64) ↦ₛ bytesToBv8 minusCapA) ⊢ memRegion (fsp + 400#64) 160 := pointsToBytes_entails_memRegion_n _ _ (by simp [bytesToBv8, hnegA])
  have hw768 : ((fsp + 768#64) ↦ₛ bytesToBv8 hScalar) ⊢ memRegion (fsp + 768#64) 32 := pointsToBytes_entails_memRegion_n _ _ (by simp [bytesToBv8, hh])
  rw [← memRegion_cells (fsp + 560#64) 16 (by decide), ← memRegion_cells (fsp + 688#64) 10 (by decide)]
  refine Entails.trans (sepConj_mono_right (sepConj_mono hw4 (sepConj_mono hw8 (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono hw368 (sepConj_mono hw400 (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hw768))))))))))) (Entails.of_eq ?_)
  rw [← ProofLib.memRegion_split' (b := fsp + 1040#64) (n := 96) (k := 16) (b' := fsp + 1136#64) rfl (by bv_omega) (by decide), ← ProofLib.memRegion_split' (b := fsp + 1008#64) (n := 32) (k := 112) (b' := fsp + 1040#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp + 960#64) (n := 48) (k := 144) (b' := fsp + 1008#64) rfl (by bv_omega) (by decide), ← ProofLib.memRegion_split' (b := fsp + 800#64) (n := 160) (k := 192) (b' := fsp + 960#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp + 768#64) (n := 32) (k := 352) (b' := fsp + 800#64) rfl (by bv_omega) (by decide), ← ProofLib.memRegion_split' (b := fsp + 688#64) (n := 80) (k := 384) (b' := fsp + 768#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp + 560#64) (n := 128) (k := 464) (b' := fsp + 688#64) rfl (by bv_omega) (by decide), ← ProofLib.memRegion_split' (b := fsp + 400#64) (n := 160) (k := 592) (b' := fsp + 560#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp + 368#64) (n := 32) (k := 752) (b' := fsp + 400#64) rfl (by bv_omega) (by decide), ← ProofLib.memRegion_split' (b := fsp + 208#64) (n := 160) (k := 784) (b' := fsp + 368#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp + 48#64) (n := 160) (k := 944) (b' := fsp + 208#64) rfl (by bv_omega) (by decide), ← ProofLib.memRegion_split' (b := fsp + 16#64) (n := 32) (k := 1104) (b' := fsp + 48#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp + 8#64) (n := 8) (k := 1136) (b' := fsp + 16#64) rfl (by bv_omega) (by decide), ← ProofLib.memRegion_split' (b := fsp + 4#64) (n := 4) (k := 1144) (b' := fsp + 8#64) rfl (by bv_omega) (by decide),
    ← ProofLib.memRegion_split' (b := fsp) (n := 4) (k := 1148) (b' := fsp + 4#64) rfl (by bv_omega) (by decide)]

private theorem SepWP.seq_seg_ext {prog : Program} {mid target : BitVec 64} {s : State} {P P' P_mid : SepProp}
    {Q_regs : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P' (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_regs sm)) (hP : P ⊢ P')
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → Q_regs sm → SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  SepWP.weaken_pre hP <| SepWP.seq h1 fun sm _ hpc hrun ⟨hent, hQ⟩ => SepWP.weaken_pre hent (h2 sm hpc hrun hQ)

private theorem SepWP.end_seg_ext {prog : Program} {target : BitVec 64} {s : State} {P P' P_out : SepProp}
    {Q_regs : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog target s P' (fun sm Pm => (Pm ⊢ P_out) ∧ Q_regs sm)) (hP : P ⊢ P')
    (hpost : ∀ sm Pm, (Pm ⊢ P_out) → Q_regs sm → post sm Pm) : SepWP prog target s P post :=
  SepWP.weaken_pre hP <| SepWP.mono h1 fun sm Pm _ _ ⟨hent, hQ⟩ => hpost sm Pm hent hQ

private theorem xeddsaVerifyRef_of_montToEd_none_ext (P : Primitives) {pk m sig : Bytes}
    (hmont : P.montToEdBytes pk ((sig.getD 63 0 &&& 0x80) >>> 7) = none) : xeddsaVerifyRef P pk m sig = false := by
  unfold xeddsaVerifyRef; dsimp only; rw [Option.map_eq_none_iff.mp hmont]; split <;> rfl

private theorem xeddsaVerifyRef_of_60_false_ext (P : Primitives) {pk m sig : Bytes}
    (h60 : (sig.getD 63 0 &&& 0x60 == 0) = false) : xeddsaVerifyRef P pk m sig = false := by
  unfold xeddsaVerifyRef; rw [h60, Bool.and_false]; rfl

private theorem xeddsaVerifyRef_of_some_ext (P : Primitives) (hWF : StructuralPrims P)
    (m : Bytes) {pk sig edPt : Bytes}
    (hpk : pk.length = 32) (hsig : sig.length = 64) (h60 : (sig.getD 63 0 &&& 0x60 == 0) = true)
    (hmont : P.montToEdBytes pk ((sig.getD 63 0 &&& 0x80) >>> 7) = some edPt) :
    (let capA := P.compressBytes edPt; let minusCapA := P.edNegBytes edPt; let capR := sig.take 32
     let sRaw := sig.drop 32; let sClamped := sRaw.take 31 ++ [sRaw.getD 31 0 &&& 0x7F]
     let h := P.scalarFromWide (P.sha512 (capR ++ capA ++ m))
     let sScalar := P.scalarFromBytesModOrder sClamped
     let capRCheck := P.compressBytes (P.doubleScalarMulBasepointBytes h minusCapA sScalar)
     if (capRCheck == capR) = true then (1#64 : BitVec 64) else 0#64) =
    (if xeddsaVerifyRef P pk m sig = true then 1#64 else 0#64) := by
  rcases Option.map_eq_some_iff.mp hmont with ⟨pt0, hmont0, rfl⟩
  have hpt0 := hWF.montToEd_lt _ _ pt0 hmont0
  have hunp0 : unpackEdBytes (packEdBytes pt0) = pt0 :=
    unpackEdBytes_packEdBytes hpt0.1 hpt0.2
  have hneg_lt := hWF.edNeg_lt pt0
  have hunp_neg : unpackEdBytes (P.edNegBytes (packEdBytes pt0)) = P.edNeg pt0 := by
    simp only [_root_.SignalPqxdh.Primitives.edNegBytes, hunp0]
    exact unpackEdBytes_packEdBytes hneg_lt.1 hneg_lt.2
  have heq : xeddsaVerifyRef P pk m sig =
      (let capA := P.compressBytes (packEdBytes pt0); let minusCapA := P.edNegBytes (packEdBytes pt0); let capR := sig.take 32
       let sRaw := sig.drop 32; let sClamped := sRaw.take 31 ++ [sRaw.getD 31 0 &&& 0x7F]
       let h := P.scalarFromWide (P.sha512 (capR ++ capA ++ m))
       let sScalar := P.scalarFromBytesModOrder sClamped
       P.compressBytes (P.doubleScalarMulBasepointBytes h minusCapA sScalar) == capR) := by
    unfold xeddsaVerifyRef
    rw [beq_iff_eq.mpr hpk, beq_iff_eq.mpr hsig, h60]
    simp only [Bool.and_self, ↓reduceIte, hmont0,
      _root_.SignalPqxdh.Primitives.compressBytes,
      _root_.SignalPqxdh.Primitives.doubleScalarMulBasepointBytes, hunp0, hunp_neg]
    have hd_lt := hWF.doubleScalarMulBasepoint_lt
      (P.scalarFromWide (P.sha512 (sig.take 32 ++ P.compress pt0 ++ m)))
      (P.edNeg pt0)
      (P.scalarFromBytesModOrder ((sig.drop 32).take 31 ++ [(sig.drop 32).getD 31 0 &&& 0x7F]))
    rw [unpackEdBytes_packEdBytes hd_lt.1 hd_lt.2]
  rw [heq]

private theorem stackAt_1280_split_ext (fsp : BitVec 64) :
    stackAt (fsp + 1280#64) verifySigStackExt = stackAt (fsp + 1248#64) (verifySigHookStackExt + 1248) ∗ cells (fsp + 1248#64) 4 := by
  have h1 : fsp + 1280#64 - 32#64 = fsp + 1248#64 := by bv_omega
  rw [show verifySigStackExt = (verifySigHookStackExt + 1248) + 4 * 8 by decide,
    stackAt_split_cells (fsp + 1280#64) (verifySigHookStackExt + 1248) 4 (by decide), h1]

private theorem stackAt_1280_merge_ext (fsp v0 v1 v2 v3 : BitVec 64) :
    ((fsp + 1248#64) ↦₆₄ v0) ∗ ((fsp + 1256#64) ↦₆₄ v1) ∗ ((fsp + 1264#64) ↦₆₄ v2) ∗ ((fsp + 1272#64) ↦₆₄ v3) ∗
    stackAt (fsp + 1248#64) (verifySigHookStackExt + 1248) ⊢ stackAt (fsp + 1280#64) verifySigStackExt := by
  rw [stackAt_1280_split_ext fsp, sepConj_comm (stackAt _ _), ← sepConj_assoc, ← sepConj_assoc, ← sepConj_assoc]
  refine sepConj_mono_left ?_
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.sepExists_right v0 <| Entails.sepExists_right v1 <| Entails.sepExists_right v2 <|
    Entails.sepExists_right v3 <| Entails.refl _

end WithProgramExt
end CryptoVerification.E2E.Pqxdh.Shared
