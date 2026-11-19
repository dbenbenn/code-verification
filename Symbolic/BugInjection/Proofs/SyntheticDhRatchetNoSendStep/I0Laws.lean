/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.DefsI0

/-!
# Cryptographic Contracts, Hook Agreement, and Satisfiability of `cliCompFitsPinned`
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.I0Laws

open DY.X25519 (isLowOrderKey lowOrderUs)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement
  (x25519PublicKeySymbol x25519AgreementSymbol x25519TorsionSymbol torsionShift
   aesCbcEncryptSymbol aesCbcDecryptSymbol sha256CompressSymbol ExternCryptoLawsHold)
open DY.Libsignal.PQXDH.Refinement
  (kyberEncapsSymbol kyberDecapsSymbol
   libcruxHmacSymbol X25519TorsionShiftsRejected)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup ProtocolSetupWF gamma gamma' randTerm setupRandomsAt setupPublic secretBytes
   X25519PubCanonical kyberEncapsBytes kyberDecapsBytes concretizeRandom concretizeKemPk
   concretizeSign concretizeAll slice)
open DY.Libsignal.Composed.Refinement.Cli (ExternContractsHoldCli HooksMatchInterpretation)
open Symbolic.BugInjection (PQXDHSpqrSetup fillFresh fillFresh_ne_11_17)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
  (compPointIdx compLookupPub compLookupDh compKyberEncaps compKyberDecaps)
open Symbolic.BugInjection.Proofs.Common443.CompI0Laws
  (leBytes_length compHmac_length compI0_kyberCorrectOn
   compLookupPub_length compLookupPub_lt_p25519 compLookupPub_not_lowOrder
   compLookupDh_comm compLookupDh_length compLookupDh_ne_zero_of_not_lowOrder)
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.DefsShaRows (dhRatchetSha256)
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.DefsI0
  (dhAesK0 dhAesA00 dhAesB00 dhAesA01 dhAesB01
   dhAesK1 dhAesA10 dhAesB10 dhAesA11 dhAesB11
   swap2 dhRatchetAesBlock dhRatchetAesPerm dhRatchetAesDec dhRatchetHmac
   dhRatchetI0 dhRatchetHooks0 dhRatchetRecordsI0 cliCompFitsPinned)

theorem dhRatchetI0_publicKey (sk : HwBytes) :
    dhRatchetI0 x25519PublicKeySymbol [sk] = some (compLookupPub sk) := rfl
theorem dhRatchetI0_agreement (sk pk : HwBytes) :
    dhRatchetI0 x25519AgreementSymbol [sk, pk] = some (compLookupDh sk pk) := rfl
theorem dhRatchetI0_torsion (pt : HwBytes) (b : BitVec 8) :
    dhRatchetI0 x25519TorsionSymbol [pt, [b]] = none := rfl
theorem dhRatchetI0_aesEncrypt (text k iv : HwBytes) :
    dhRatchetI0 aesCbcEncryptSymbol [text, k, iv] = some (dhRatchetAesPerm k iv text) := rfl
theorem dhRatchetI0_aesDecrypt (ct k iv : HwBytes) :
    dhRatchetI0 aesCbcDecryptSymbol [ct, k, iv] = dhRatchetAesDec k iv ct := rfl
theorem dhRatchetI0_kyberEncaps (pk rand : HwBytes) :
    dhRatchetI0 kyberEncapsSymbol [pk, rand] = some (compKyberEncaps rand) := rfl
theorem dhRatchetI0_kyberDecaps (sk ct : HwBytes) :
    dhRatchetI0 kyberDecapsSymbol [sk, ct] = some (compKyberDecaps ct) := rfl
theorem dhRatchetI0_hmac (k d : HwBytes) :
    dhRatchetI0 libcruxHmacSymbol [k, d] = some (dhRatchetHmac k d) := rfl
theorem dhRatchetI0_sha256Compress (st blk : HwBytes) :
    dhRatchetI0 sha256CompressSymbol [st, blk] = some (dhRatchetSha256 st blk) := rfl

theorem torsionShift_dhRatchetI0 (p : HwBytes) (t : Fin 8) :
    torsionShift dhRatchetI0 p t = p := by
  unfold torsionShift; split <;> rfl

theorem dhRatchetHmac_length (k d : HwBytes) : (dhRatchetHmac k d).length = 32 := by
  unfold dhRatchetHmac
  split
  · exact leBytes_length 32 _
  · exact compHmac_length k d

theorem swap2_involutive {a0 b0 a1 b1 : CryptoGames.CBC.Block}
    (h01 : a0 ≠ a1) (h02 : a0 ≠ b1) (h11 : b0 ≠ a1) (h12 : b0 ≠ b1)
    (x : CryptoGames.CBC.Block) :
    swap2 a0 b0 a1 b1 (swap2 a0 b0 a1 b1 x) = x := by
  unfold swap2
  by_cases hx0 : x = a0
  · subst hx0
    by_cases hab0 : x = b0 <;> simp [hab0]
  · have hb0 : (x == a0) = false := beq_eq_false_iff_ne.mpr hx0
    by_cases hxb0 : x = b0
    · subst hxb0; simp [hb0]
    · have hbb0 : (x == b0) = false := beq_eq_false_iff_ne.mpr hxb0
      by_cases hx1 : x = a1
      · subst hx1
        have hb1_a0 : (b1 == a0) = false := beq_eq_false_iff_ne.mpr h02.symm
        have hb1_b0 : (b1 == b0) = false := beq_eq_false_iff_ne.mpr h12.symm
        by_cases hab1 : x = b1 <;> simp [hb0, hbb0, hb1_a0, hb1_b0, hab1]
      · have hb1 : (x == a1) = false := beq_eq_false_iff_ne.mpr hx1
        by_cases hxb1 : x = b1
        · subst hxb1
          have ha1_a0 : (a1 == a0) = false := beq_eq_false_iff_ne.mpr h01.symm
          have ha1_b0 : (a1 == b0) = false := beq_eq_false_iff_ne.mpr h11.symm
          simp [hb0, hbb0, hb1, ha1_a0, ha1_b0]
        · have hbb1 : (x == b1) = false := beq_eq_false_iff_ne.mpr hxb1
          simp [hb0, hbb0, hb1, hbb1]

private theorem dhAes0_disjoint :
    dhAesA00 ≠ dhAesA01 ∧ dhAesA00 ≠ dhAesB01 ∧
      dhAesB00 ≠ dhAesA01 ∧ dhAesB00 ≠ dhAesB01 := by
  decide

private theorem dhAes1_disjoint :
    dhAesA10 ≠ dhAesA11 ∧ dhAesA10 ≠ dhAesB11 ∧
      dhAesB10 ≠ dhAesA11 ∧ dhAesB10 ≠ dhAesB11 := by
  decide

theorem dhRatchetAesBlock_involutive (k : CryptoGames.CBC.AesKey) (b : CryptoGames.CBC.Block) :
    dhRatchetAesBlock k (dhRatchetAesBlock k b) = b := by
  unfold dhRatchetAesBlock
  cases hk0 : (k == CryptoGames.HKDF.bytesToKey32 dhAesK0)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases hk1 : (k == CryptoGames.HKDF.bytesToKey32 dhAesK1) <;>
      simp only [Bool.false_eq_true, ↓reduceIte]
    case true =>
      obtain ⟨h1, h2, h3, h4⟩ := dhAes1_disjoint
      exact swap2_involutive h1 h2 h3 h4 b
  · simp only [↓reduceIte]
    obtain ⟨h1, h2, h3, h4⟩ := dhAes0_disjoint
    exact swap2_involutive h1 h2 h3 h4 b

private theorem cbcEncrypt_eq (f : ByteSpecs.Block → ByteSpecs.Block) :
    ∀ (iv : ByteSpecs.Block) {n : Nat} (P : List.Vector ByteSpecs.Block n),
      CryptoGames.CBC.cbcEncrypt f iv P = ByteSpecs.cbcEncrypt f iv P
  | _, 0, _ => rfl
  | iv, _ + 1, P => by
    simp only [CryptoGames.CBC.cbcEncrypt, ByteSpecs.cbcEncrypt]
    rw [cbcEncrypt_eq f (f (P.head ^^^ iv)) P.tail]

private theorem cbcDecryptBlocks_eq (g : ByteSpecs.Block → ByteSpecs.Block)
    (iv : ByteSpecs.Block) :
    ∀ (cs : List ByteSpecs.Block),
      CryptoGames.CBC.cbcDecryptBlocks g iv cs = ByteSpecs.cbcDecryptBlocks g iv cs
  | [] => rfl
  | c :: cs => by
    simp only [CryptoGames.CBC.cbcDecryptBlocks, ByteSpecs.cbcDecryptBlocks]
    rw [cbcDecryptBlocks_eq g c cs]

private theorem aesCbcEncrypt_eq_byteSpecs
    (E : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block)
    (k : CryptoGames.CBC.AesKey) (iv : CryptoGames.CBC.Block) (p : List (BitVec 8)) :
    CryptoGames.LibsignalSession.aesCbcEncrypt E k iv p =
      (ByteSpecs.cbcEncrypt (E k) iv
        (ByteSpecs.pkcs7Blocks (⟨p, rfl⟩ : ByteSpecs.Plain p.length))).toList.flatMap
        ByteSpecs.blockToBytesLE := by
  let vp : List.Vector (BitVec 8) p.length := ⟨p, rfl⟩
  change (CryptoGames.CBC.cbcEncrypt (E k) iv (CryptoGames.CBC.pkcs7Blocks vp)).toList.flatMap
      CryptoGames.CBC.blockToBytesLE =
    (ByteSpecs.cbcEncrypt (E k) iv (ByteSpecs.pkcs7Blocks vp)).toList.flatMap
      ByteSpecs.blockToBytesLE
  have hpk : CryptoGames.CBC.pkcs7Blocks vp = ByteSpecs.pkcs7Blocks vp := rfl
  have hbl : CryptoGames.CBC.blockToBytesLE = ByteSpecs.blockToBytesLE := rfl
  rw [hbl]
  exact congrArg (fun v => v.toList.flatMap ByteSpecs.blockToBytesLE)
    (hpk ▸ cbcEncrypt_eq (E k) iv (ByteSpecs.pkcs7Blocks vp))

private theorem aesCbcDecrypt_eq_byteSpecs
    (D : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block)
    (k : CryptoGames.CBC.AesKey) (iv : CryptoGames.CBC.Block) (c : List (BitVec 8)) :
    CryptoGames.LibsignalSession.aesCbcDecrypt D k iv c = ByteSpecs.cbcDecRaw D k iv c := by
  unfold CryptoGames.LibsignalSession.aesCbcDecrypt CryptoGames.CBC.cbcDecRaw ByteSpecs.cbcDecRaw
  have hch : CryptoGames.CBC.chunks16 c = ByteSpecs.chunks16 c := rfl
  have hbl : CryptoGames.CBC.blockToBytesLE = ByteSpecs.blockToBytesLE := rfl
  have hunp : CryptoGames.CBC.pkcs7Unpad = ByteSpecs.pkcs7Unpad := rfl
  rw [hch, cbcDecryptBlocks_eq, hbl, hunp]

private theorem eq_replicate_of_all_beq :
    ∀ (l : List (BitVec 8)) (x : BitVec 8),
      l.all (· == x) = true → l = List.replicate l.length x
  | [], _, _ => rfl
  | y :: ys, x, h => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    have ih := eq_replicate_of_all_beq ys x h.2
    simp only [h.1, List.length_cons, List.replicate_succ, List.cons.injEq, true_and]
    exact ih

private theorem length_cbcDecryptBlocks (g : ByteSpecs.Block → ByteSpecs.Block) :
    ∀ (iv : ByteSpecs.Block) (cs : List ByteSpecs.Block),
      (ByteSpecs.cbcDecryptBlocks g iv cs).length = cs.length
  | _, [] => rfl
  | iv, c :: cs => by simp [ByteSpecs.cbcDecryptBlocks, length_cbcDecryptBlocks g c cs]

private theorem length_flatMap_blockToBytesLE :
    ∀ (cs : List ByteSpecs.Block),
      (cs.flatMap ByteSpecs.blockToBytesLE).length = 16 * cs.length
  | [] => rfl
  | c :: cs => by
    have h16 : (ByteSpecs.blockToBytesLE c).length = 16 := by simp [ByteSpecs.blockToBytesLE]
    simp only [List.flatMap_cons, List.length_append, h16, length_flatMap_blockToBytesLE cs, List.length_cons]
    omega

private def cbcEncryptList (f : ByteSpecs.Block → ByteSpecs.Block) (iv : ByteSpecs.Block) :
    List ByteSpecs.Block → List ByteSpecs.Block
  | [] => []
  | b :: bs => let c := f (b ^^^ iv); c :: cbcEncryptList f c bs

private theorem toList_cbcEncrypt (f : ByteSpecs.Block → ByteSpecs.Block) :
    ∀ (iv : ByteSpecs.Block) {n : Nat} (P : List.Vector ByteSpecs.Block n),
      (ByteSpecs.cbcEncrypt f iv P).toList = cbcEncryptList f iv P.toList
  | _, 0, P => by
    cases P with
    | mk l hl => cases l with | nil => rfl | cons _ _ => cases hl
  | iv, _ + 1, P => by
    simp only [ByteSpecs.cbcEncrypt, List.Vector.toList_cons]
    rw [toList_cbcEncrypt f (f (P.head ^^^ iv)) P.tail]
    cases P with
    | mk l hl => cases l with | nil => cases hl | cons _ _ => rfl

private theorem cbcEncryptList_cbcDecryptBlocks {f : ByteSpecs.Block → ByteSpecs.Block}
    (hinv : ∀ b, f (f b) = b) :
    ∀ (iv : ByteSpecs.Block) (cs : List ByteSpecs.Block),
      cbcEncryptList f iv (ByteSpecs.cbcDecryptBlocks f iv cs) = cs
  | _, [] => rfl
  | iv, c :: cs => by
    have hxor : f ((f c ^^^ iv) ^^^ iv) = c := by
      rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, hinv]
    simp only [ByteSpecs.cbcDecryptBlocks, cbcEncryptList, hxor, cbcEncryptList_cbcDecryptBlocks hinv c cs]

private theorem flatMap_ofFn_chunks16 (m : Nat) :
    ∀ (bs : List (BitVec 8)), bs.length = 16 * m →
      (List.ofFn fun i : Fin m =>
        ByteSpecs.bytesToBlock ((bs.drop (16 * i.val)).take 16)).flatMap ByteSpecs.blockToBytesLE = bs := by
  induction m with
  | zero => intro bs h; simp only [Nat.mul_zero, List.length_eq_zero_iff] at h; subst h; rfl
  | succ m ih =>
    intro bs h; rw [List.ofFn_succ, List.flatMap_cons]
    simp only [Fin.val_zero, Nat.mul_zero, List.drop_zero, Fin.val_succ]
    rw [ByteSpecs.blockToBytesLE_bytesToBlock (bs.take 16) (by rw [List.length_take, h]; omega)]
    have hrest : (List.ofFn fun i : Fin m => ByteSpecs.bytesToBlock ((bs.drop (16 * (i.val + 1))).take 16)) =
      List.ofFn fun i : Fin m => ByteSpecs.bytesToBlock (((bs.drop 16).drop (16 * i.val)).take 16) := by
      congr 1; ext i; rw [List.drop_drop, show 16 * (i.val + 1) = 16 + 16 * i.val by omega]
    rw [hrest, ih (bs.drop 16) (by simp [h]; omega), List.take_append_drop]

private theorem flatMap_chunks16 (ct : List (BitVec 8)) (h : ct.length % 16 = 0) :
    (ByteSpecs.chunks16 ct).flatMap ByteSpecs.blockToBytesLE = ct :=
  flatMap_ofFn_chunks16 (ct.length / 16) ct (by omega)

private theorem chunks16_pkcs7Bytes (p : List (BitVec 8)) :
    ByteSpecs.chunks16 (ByteSpecs.pkcs7Bytes (⟨p, rfl⟩ : ByteSpecs.Plain p.length)) =
      (ByteSpecs.pkcs7Blocks (⟨p, rfl⟩ : ByteSpecs.Plain p.length)).toList := by
  unfold ByteSpecs.chunks16 ByteSpecs.pkcs7Blocks; rw [List.Vector.toList_ofFn]
  have hlen : (ByteSpecs.pkcs7Bytes (⟨p, rfl⟩ : ByteSpecs.Plain p.length)).length / 16 = ByteSpecs.nBlocks p.length := by
    simp only [ByteSpecs.pkcs7Bytes, List.length_append, List.Vector.toList_mk, List.length_replicate, ByteSpecs.padLen, ByteSpecs.nBlocks]; omega
  refine List.ext_getElem (by simp [hlen]) fun _ _ _ => by simp

theorem dhRatchetAesDec_dhRatchetAesPerm (k iv text : HwBytes) :
    dhRatchetAesDec k iv (dhRatchetAesPerm k iv text) = some text := by
  unfold dhRatchetAesDec dhRatchetAesPerm
  rw [aesCbcEncrypt_eq_byteSpecs, aesCbcDecrypt_eq_byteSpecs]
  exact ByteSpecs.cbcDecRaw_correct dhRatchetAesBlock_involutive _ _ (⟨text, rfl⟩ : ByteSpecs.Plain text.length)

theorem dhRatchetAesPerm_of_dhRatchetAesDec {k iv ct pt : HwBytes}
    (hdec : dhRatchetAesDec k iv ct = some pt) :
    dhRatchetAesPerm k iv pt = ct := by
  unfold dhRatchetAesDec at hdec; unfold dhRatchetAesPerm
  rw [aesCbcDecrypt_eq_byteSpecs] at hdec; rw [aesCbcEncrypt_eq_byteSpecs]
  unfold ByteSpecs.cbcDecRaw at hdec
  split at hdec
  · cases hdec
  · rename_i hct; push Not at hct; obtain ⟨_, hmod⟩ := hct
    let m := ct.length / 16
    have hclen : ct.length = 16 * m := by dsimp [m]; omega
    set P := ByteSpecs.cbcDecryptBlocks (dhRatchetAesBlock (CryptoGames.HKDF.bytesToKey32 k)) (CryptoGames.CBC.bytesToBlock iv) (ByteSpecs.chunks16 ct)
    set bs := P.flatMap ByteSpecs.blockToBytesLE
    have hPlen : P.length = m := by simp [P, length_cbcDecryptBlocks, ByteSpecs.chunks16, m]
    have hbslen : bs.length = 16 * m := by rw [show bs = P.flatMap ByteSpecs.blockToBytesLE from rfl, length_flatMap_blockToBytesLE, hPlen]
    unfold ByteSpecs.pkcs7Unpad at hdec
    cases hlast : bs.getLast? with
    | none => simp [hlast] at hdec
    | some last =>
      simp only [hlast] at hdec
      split at hdec
      · cases hdec
      · rename_i hbounds; push Not at hbounds; obtain ⟨_, _, _⟩ := hbounds
        split at hdec
        · rename_i hall; injection hdec with hp
          have hdrop_len : (bs.drop (bs.length - last.toNat)).length = last.toNat := by rw [List.length_drop]; omega
          have hdrop : bs.drop (bs.length - last.toNat) = List.replicate last.toNat last := by
            have := eq_replicate_of_all_beq _ _ hall; rwa [hdrop_len] at this
          have hplen : pt.length = 16 * m - last.toNat := by rw [← hp, List.length_take, hbslen]; omega
          have hpad : ByteSpecs.padLen pt.length = last.toNat := by unfold ByteSpecs.padLen; rw [hplen]; omega
          have hlast_eq : BitVec.ofNat 8 (ByteSpecs.padLen pt.length) = last := by rw [hpad]; simp
          have hbs_eq : bs = ByteSpecs.pkcs7Bytes (⟨pt, rfl⟩ : ByteSpecs.Plain pt.length) := by
            calc bs = bs.take (bs.length - last.toNat) ++ bs.drop (bs.length - last.toNat) := (List.take_append_drop _ _).symm
              _ = pt ++ List.replicate last.toNat last := by rw [hp, hdrop]
              _ = pt ++ List.replicate (ByteSpecs.padLen pt.length) (BitVec.ofNat 8 (ByteSpecs.padLen pt.length)) := by rw [← hpad, hlast_eq]
              _ = ByteSpecs.pkcs7Bytes (⟨pt, rfl⟩ : ByteSpecs.Plain pt.length) := rfl
          have hP_eq : P = (ByteSpecs.pkcs7Blocks (⟨pt, rfl⟩ : ByteSpecs.Plain pt.length)).toList := by
            have hch := congrArg ByteSpecs.chunks16 hbs_eq
            simpa [bs, ByteSpecs.chunks16_flatMap, chunks16_pkcs7Bytes] using hch
          have henc : (ByteSpecs.cbcEncrypt (dhRatchetAesBlock (CryptoGames.HKDF.bytesToKey32 k)) (CryptoGames.CBC.bytesToBlock iv)
              (ByteSpecs.pkcs7Blocks (⟨pt, rfl⟩ : ByteSpecs.Plain pt.length))).toList = ByteSpecs.chunks16 ct := by
            rw [toList_cbcEncrypt, ← hP_eq]
            exact cbcEncryptList_cbcDecryptBlocks (dhRatchetAesBlock_involutive _) _ (ByteSpecs.chunks16 ct)
          rw [henc, flatMap_chunks16 ct hmod]
        · cases hdec

theorem dhRatchetAesPerm_length (k iv text : HwBytes) :
    (dhRatchetAesPerm k iv text).length = 16 * (text.length / 16 + 1) := by
  unfold dhRatchetAesPerm
  rw [aesCbcEncrypt_eq_byteSpecs, length_flatMap_blockToBytesLE, List.Vector.toList_length]; rfl

theorem dhRatchetI0_cryptoEquationsHold : ExternCryptoLawsHold dhRatchetI0 where
  x25519_agreement_commutes a b := by
    simp only [dhRatchetI0_publicKey, dhRatchetI0_agreement, Option.getD_some]
    exact congrArg some (compLookupDh_comm a b)
  x25519_agreement_length a p := by simp [dhRatchetI0_agreement, compLookupDh_length]
  x25519_public_key_length a := by simp [dhRatchetI0_publicKey, compLookupPub_length]
  x25519_agreement_reads_u_coordinate a b b' hb hb' hu := by
    simp only [dhRatchetI0_agreement]; congr 1
    have hl : isLowOrderKey (b.map BitVec.toNat) = isLowOrderKey (b'.map BitVec.toNat) := by
      simp only [isLowOrderKey, List.length_map, hb, hb']
      exact congrArg (fun u => (32 == 32 && lowOrderUs.contains u)) hu
    have hp : compPointIdx b = compPointIdx b' := by simp only [compPointIdx, hb, hb', hu]
    unfold compLookupDh; rw [hl, hp]
  x25519_agreement_torsion_invariant secret point t := by
    rw [torsionShift_dhRatchetI0]
  x25519_agreement_zero_iff_low_order a b _ _ := by
    rw [dhRatchetI0_agreement, Option.getD_some]
    cases h : isLowOrderKey (b.map BitVec.toNat)
    · simp only [Bool.false_eq_true, iff_false]; exact compLookupDh_ne_zero_of_not_lowOrder a b h
    · unfold compLookupDh; simp [h]
  x25519_public_key_not_low_order a _ := by simp [dhRatchetI0_publicKey, compLookupPub_not_lowOrder]
  aes_cbc_decrypt_inverts_encrypt plaintext key iv := by
    rw [dhRatchetI0_aesEncrypt, dhRatchetI0_aesDecrypt, Option.getD_some]
    exact dhRatchetAesDec_dhRatchetAesPerm key iv plaintext
  aes_cbc_encrypt_of_decrypt c k iv p _ _ h := by
    rw [dhRatchetI0_aesDecrypt] at h; rw [dhRatchetI0_aesEncrypt]
    exact congrArg some (dhRatchetAesPerm_of_dhRatchetAesDec h)
  hmac_tag_length k d t h := by
    rw [dhRatchetI0_hmac, Option.some.injEq] at h; rw [← h]; exact dhRatchetHmac_length k d

theorem dhRatchetI0_pubCanonical : X25519PubCanonical dhRatchetI0 := by
  intro s; rw [dhRatchetI0_publicKey, Option.getD_some]; exact compLookupPub_lt_p25519 s

theorem dhRatchetI0_torsionShiftsRejected : X25519TorsionShiftsRejected dhRatchetI0 := by
  intro s t k _ hu hne _
  rw [torsionShift_dhRatchetI0] at hu
  exact hne hu

theorem dhRatchetI0_externContractsHoldCli : ExternContractsHoldCli dhRatchetI0 :=
  ⟨dhRatchetI0_cryptoEquationsHold, dhRatchetI0_pubCanonical, dhRatchetI0_torsionShiftsRejected⟩

theorem dhRatchetI0_hooksAgree : HooksMatchInterpretation dhRatchetI0 dhRatchetHooks0 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p k iv _ _; rfl
  · intro c k iv _ _; rfl
  · intro a b; rfl
  · intro a; rfl
  · intro pk rand
    rw [dhRatchetI0_kyberEncaps]
    exact congrArg some (List.take_append_drop 1568 (compKyberEncaps rand.toList)).symm
  · intro sk ct; rfl

theorem dhRatchetI0_kyberCorrectOn (r : ProtocolSetup) (cts : List HwBytes) :
    ∀ ct ∈ cts, ∀ e ss, e.length = 32 → kyberEncapsBytes dhRatchetI0 r e = some (ct, ss) →
      kyberDecapsBytes dhRatchetI0 r ct = some ss :=
  compI0_kyberCorrectOn r cts

theorem dhRatchetI0_gamma_randTerm_pos (w : PQXDHSpqrSetup) (i n : Nat) (hn : n ≠ 0) :
    gamma dhRatchetI0 w.compSem w.compGhost (randTerm i n) = w.compGhost.σ i n := by
  unfold gamma gamma'; conv => lhs; unfold randTerm
  rw [DY.Bytes.rec_eq (concretizeRandom w.compGhost) (concretizeAll dhRatchetI0 w.compSem w.compGhost)]
  simp only [concretizeRandom, hn, ite_false]; rfl

theorem dhRatchetI0_gamma_kemPk (w : PQXDHSpqrSetup) (sk : DY.Bytes) :
    gamma dhRatchetI0 w.compSem w.compGhost (DY.PQKem.kemPk sk) =
      w.compSem.kemPk (gamma dhRatchetI0 w.compSem w.compGhost sk) := by
  unfold gamma gamma'
  show ((({sk} : DY.PQKem.Pk.SubF DY.Bytes).pack).rec (concretizeAll dhRatchetI0 w.compSem w.compGhost)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeKemPk w.compSem) (concretizeAll dhRatchetI0 w.compSem w.compGhost)]; rfl

theorem dhRatchetI0_gamma_sign (w : PQXDHSpqrSetup) (sk n m : DY.Bytes) :
    gamma dhRatchetI0 w.compSem w.compGhost (DY.Signature.sign sk n m) =
      w.compSem.sign (gamma dhRatchetI0 w.compSem w.compGhost sk)
        (gamma dhRatchetI0 w.compSem w.compGhost n) (gamma dhRatchetI0 w.compSem w.compGhost m) := by
  unfold gamma gamma'
  show ((({sk, nonce := n, msg := m} : DY.Signature.Sign.SubF DY.Bytes).pack).rec (concretizeAll dhRatchetI0 w.compSem w.compGhost)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeSign w.compSem) (concretizeAll dhRatchetI0 w.compSem w.compGhost)]; rfl

theorem dhRatchetRecordsI0_ne (w : PQXDHSpqrSetup) :
    (dhRatchetRecordsI0 w).alice ≠ (dhRatchetRecordsI0 w).bob := by
  show ("alice" : String) ≠ "bob"; decide

theorem dhRatchetRecordsI0_randomsAt (w : PQXDHSpqrSetup) :
    setupRandomsAt (dhRatchetRecordsI0 w) =
      [(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)] := by
  rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq (dhRatchetRecordsI0 w) (dhRatchetRecordsI0_ne w)]; rfl

theorem cliCompFitsPinned_sub_fits :
    ∀ iw r, cliCompFitsPinned iw r →
      Symbolic.BugInjection.Synthetic.Witnesses.DhRatchetNoSendStepCli.fits iw r := by
  rintro iw r ⟨⟨hc, _, _, _, _, _⟩, hext, hhooks⟩
  exact ⟨hc, hext, hhooks⟩

theorem cliCompFitsPinned_satisfiable :
    ∃ iw r, cliCompFitsPinned iw r := by
  let w := Symbolic.BugInjection.Synthetic.Witnesses.DhRatchetNoSendStepCli.setup
  have hpl : w.Plausible := by decide +kernel
  have hw : w.withOpk = false := rfl
  obtain ⟨ha, hb, hs, hss, hk, hks, hsec, hslice, hnd, _, _⟩ := hpl
  have h5 := Symbolic.Swarm.CREF.b1_setupPublic_5 (dhRatchetRecordsI0 w) (dhRatchetRecordsI0_ne w)
  have h6 := Symbolic.Swarm.CREF.b1_setupPublic_6 (dhRatchetRecordsI0 w) (dhRatchetRecordsI0_ne w)
  have h7 := Symbolic.Swarm.CREF.b1_setupPublic_7 (dhRatchetRecordsI0 w) (dhRatchetRecordsI0_ne w)
  have hR := dhRatchetRecordsI0_randomsAt w
  have o5 : (dhRatchetRecordsI0 w).opaqueBytes (setupPublic (dhRatchetRecordsI0 w) 5) = w.spkSig := by
    rw [h5]; show gamma dhRatchetI0 w.compSem w.compGhost _ = _
    rw [dhRatchetI0_gamma_sign]
    show (if gamma dhRatchetI0 w.compSem w.compGhost (randTerm 11 64) = fillFresh 11 64 then _ else _) = _
    rw [dhRatchetI0_gamma_randTerm_pos w 11 64 (by decide)]
    simp [PQXDHSpqrSetup.compGhost, PQXDHSpqrSetup.fresh]
  have o6 : (dhRatchetRecordsI0 w).opaqueBytes (setupPublic (dhRatchetRecordsI0 w) 6) = w.kyberPk := by
    rw [h6]; show gamma dhRatchetI0 w.compSem w.compGhost _ = _; rw [dhRatchetI0_gamma_kemPk]; rfl
  have o7 : (dhRatchetRecordsI0 w).opaqueBytes (setupPublic (dhRatchetRecordsI0 w) 7) = w.kyberPkSig := by
    rw [h7]; show gamma dhRatchetI0 w.compSem w.compGhost _ = _
    rw [dhRatchetI0_gamma_sign]
    show (if gamma dhRatchetI0 w.compSem w.compGhost (randTerm 17 64) = fillFresh 11 64 then _ else _) = _
    rw [dhRatchetI0_gamma_randTerm_pos w 17 64 (by decide)]
    simp [PQXDHSpqrSetup.compGhost, PQXDHSpqrSetup.fresh, fillFresh_ne_11_17]
  have hwf : ProtocolSetupWF (dhRatchetRecordsI0 w) := by
    refine ⟨dhRatchetRecordsI0_ne w, ?_, ?_, ?_, ?_, ?_, hsec, ?_⟩
    · rw [hR]; intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [dhRatchetRecordsI0, PQXDHSpqrSetup.fresh, fillFresh, ha, hb, hs]
    · rw [hR]; simpa [hw, dhRatchetRecordsI0, PQXDHSpqrSetup.fresh] using hnd
    · exact (congrArg List.length o5).trans hss
    · exact (congrArg List.length o6).trans hk
    · exact (congrArg List.length o7).trans hks
    · exact hslice.trans o6.symm
  have hs0 : secretBytes (dhRatchetRecordsI0 w) 0 = w.aliceId := by
    rw [secretBytes, hR]; simp [dhRatchetRecordsI0, PQXDHSpqrSetup.fresh]
  have hs1 : secretBytes (dhRatchetRecordsI0 w) 1 = w.bobId := by
    rw [secretBytes, hR]; simp [dhRatchetRecordsI0, PQXDHSpqrSetup.fresh]
  have hs2 : secretBytes (dhRatchetRecordsI0 w) 2 = w.spk := by
    rw [secretBytes, hR]; simp [dhRatchetRecordsI0, PQXDHSpqrSetup.fresh]
  have hs3 : secretBytes (dhRatchetRecordsI0 w) 3 = fillFresh 11 64 := by
    rw [secretBytes, hR]; simp [dhRatchetRecordsI0, PQXDHSpqrSetup.fresh]
  have hs4 : secretBytes (dhRatchetRecordsI0 w) 4 = fillFresh 16 64 := by
    rw [secretBytes, hR]; simp [dhRatchetRecordsI0, PQXDHSpqrSetup.fresh]
  have hs5 : secretBytes (dhRatchetRecordsI0 w) 5 = fillFresh 17 64 := by
    rw [secretBytes, hR]; simp [dhRatchetRecordsI0, PQXDHSpqrSetup.fresh]
  exact ⟨(dhRatchetI0, dhRatchetHooks0), dhRatchetRecordsI0 w,
    ⟨⟨hwf, rfl, rfl, rfl, rfl, rfl, hs0, hs1, hs2, o5, o6, o7, rfl,
      dhRatchetI0_cryptoEquationsHold, dhRatchetI0_pubCanonical,
      dhRatchetI0_kyberCorrectOn (dhRatchetRecordsI0 w) w.kyberCts⟩,
     rfl, ⟨hs3, hs4, hs5⟩, ⟨rfl, rfl⟩,
     dhRatchetI0_torsionShiftsRejected, fun _ h => nomatch h⟩,
    dhRatchetI0_externContractsHoldCli, dhRatchetI0_hooksAgree⟩

end Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.I0Laws
