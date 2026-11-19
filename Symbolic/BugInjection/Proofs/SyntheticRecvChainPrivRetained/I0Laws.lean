/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0
public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.I0LawsAux

/-!
# Cryptographic Contracts, Hook Agreement, and Satisfiability of `rcprCompFitsPinned`
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.I0Laws

open DY.X25519 (isLowOrderKey lowOrderUs uCoord leValue p25519)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement
  (x25519PublicKeySymbol x25519AgreementSymbol x25519TorsionSymbol torsionShift
   aesCbcEncryptSymbol aesCbcDecryptSymbol sha256CompressSymbol ExternCryptoLawsHold)
open DY.Libsignal.PQXDH.Refinement
  (kyberEncapsSymbol kyberDecapsSymbol
   mlkem768FromSeedSymbol libcruxHmacSymbol X25519TorsionShiftsRejected)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup ProtocolSetupWF gamma gamma' randTerm setupRandomsAt setupPublic secretBytes
   X25519PubCanonical kyberEncapsBytes kyberDecapsBytes concretizeRandom concretizeKemPk
   concretizeSign concretizeAll slice)
open DY.Libsignal.Composed.Refinement.Cli (ExternContractsHoldCli HooksMatchInterpretation)
open Symbolic.BugInjection (PQXDHSpqrSetup TorsionShiftsRecorded fillFresh fillFresh_ne_11_17)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
  (compDefaultPub compDefaultDh compKyberEncaps compKyberDecaps compKyberCt0 compKyberCt1
   compKyberCt2 compDefaultKyberCt compKyberSs0 compKyberSs1 compKyberSs2 compDefaultKyberSs
   compHmac)
open Symbolic.BugInjection.Proofs.Common443.CompI0Laws
  (leBytes_length compHmac_length compI0_kyberCorrectOn)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0Rows (rcprSha256)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0
  (rcprPubOfIdx rcprPubOfOpt rcprSecretIdx rcprPointIdxOfU rcprPointIdx
   rcprDhByIdx rcprLookupPub rcprLookupDh
   rcprAesBlock rcprAesPerm rcprAesDec
   rcprI0 rcprHooks0 rcprRecordsI0 rcprCompFitsPinned
   rcprAesPt0 rcprAesK0 rcprAesIv0 rcprAesCt0 rcprAesA0 rcprAesB0
   rcprAesPt1 rcprAesK1 rcprAesIv1 rcprAesCt1 rcprAesA1 rcprAesB1)

theorem rcprI0_publicKey (sk : HwBytes) :
    rcprI0 x25519PublicKeySymbol [sk] = some (rcprLookupPub sk) := rfl
theorem rcprI0_agreement (sk pk : HwBytes) :
    rcprI0 x25519AgreementSymbol [sk, pk] = some (rcprLookupDh sk pk) := rfl
theorem rcprI0_torsion (pt : HwBytes) (b : BitVec 8) :
    rcprI0 x25519TorsionSymbol [pt, [b]] = none := rfl
theorem rcprI0_aesEncrypt (text k iv : HwBytes) :
    rcprI0 aesCbcEncryptSymbol [text, k, iv] = some (rcprAesPerm k iv text) := rfl
theorem rcprI0_aesDecrypt (ct k iv : HwBytes) :
    rcprI0 aesCbcDecryptSymbol [ct, k, iv] = rcprAesDec k iv ct := rfl
theorem rcprI0_kyberEncaps (pk rand : HwBytes) :
    rcprI0 kyberEncapsSymbol [pk, rand] = some (compKyberEncaps rand) := rfl
theorem rcprI0_kyberDecaps (sk ct : HwBytes) :
    rcprI0 kyberDecapsSymbol [sk, ct] = some (compKyberDecaps ct) := rfl
theorem rcprI0_hmac (k d : HwBytes) :
    rcprI0 libcruxHmacSymbol [k, d] = some (compHmac k d) := rfl
theorem rcprI0_sha256Compress (st blk : HwBytes) :
    rcprI0 sha256CompressSymbol [st, blk] = some (rcprSha256 st blk) := rfl
theorem rcprI0_mlkem768FromSeed (seed : HwBytes) :
    rcprI0 mlkem768FromSeedSymbol [seed] =
      some (Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0.compMlkem768FromSeed seed) := rfl

theorem rcprPubOfOpt_lt_p25519 : ∀ o : Option (Fin 7),
    leValue ((rcprPubOfOpt o).map BitVec.toNat) < p25519
  | none => by decide
  | some i => by revert i; decide

theorem rcprLookupPub_lt_p25519 (s : HwBytes) :
    leValue ((rcprLookupPub s).map BitVec.toNat) < p25519 :=
  rcprPubOfOpt_lt_p25519 (rcprSecretIdx s)

theorem rcprPubOfOpt_not_lowOrder : ∀ o : Option (Fin 7),
    isLowOrderKey ((rcprPubOfOpt o).map BitVec.toNat) = false
  | none => by decide
  | some i => by revert i; decide

theorem rcprLookupPub_not_lowOrder (s : HwBytes) :
    isLowOrderKey ((rcprLookupPub s).map BitVec.toNat) = false :=
  rcprPubOfOpt_not_lowOrder (rcprSecretIdx s)

theorem rcprPointIdx_rcprPubOfOpt : ∀ o : Option (Fin 7),
    rcprPointIdx (rcprPubOfOpt o) = o
  | none => by decide
  | some i => by revert i; decide

theorem rcprPointIdx_rcprLookupPub (s : HwBytes) :
    rcprPointIdx (rcprLookupPub s) = rcprSecretIdx s :=
  rcprPointIdx_rcprPubOfOpt (rcprSecretIdx s)

theorem rcprDhByIdx_comm (i j : Fin 7) : rcprDhByIdx i j = rcprDhByIdx j i := by
  revert i j; decide

theorem rcprLookupDh_comm (a b : HwBytes) :
    rcprLookupDh a (rcprLookupPub b) = rcprLookupDh b (rcprLookupPub a) := by
  unfold rcprLookupDh
  rw [rcprLookupPub_not_lowOrder, rcprLookupPub_not_lowOrder,
      rcprPointIdx_rcprLookupPub, rcprPointIdx_rcprLookupPub]
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases rcprSecretIdx a <;> cases rcprSecretIdx b <;>
    first | rfl | exact rcprDhByIdx_comm _ _

theorem rcprDhByIdx_ne_zero (i j : Fin 7) :
    rcprDhByIdx i j ≠ List.replicate 32 0#8 := by
  revert i j; decide

theorem rcprLookupDh_ne_zero_of_not_lowOrder (s p : HwBytes)
    (hlo : isLowOrderKey (p.map BitVec.toNat) = false) :
    rcprLookupDh s p ≠ List.replicate 32 0#8 := by
  unfold rcprLookupDh; rw [hlo]; simp only [Bool.false_eq_true, ↓reduceIte]
  cases rcprSecretIdx s <;> cases rcprPointIdx p <;> dsimp only <;>
    first | exact rcprDhByIdx_ne_zero _ _ | decide

theorem torsionShift_rcprI0 (p : HwBytes) (t : Fin 8) :
    torsionShift rcprI0 p t = p := by
  unfold torsionShift; split <;> rfl

private theorem swap_involutive (a b x : CryptoGames.CBC.Block) :
    (if (if x == a then b else if x == b then a else x) == a then b
     else if (if x == a then b else if x == b then a else x) == b then a
     else (if x == a then b else if x == b then a else x)) = x := by
  by_cases hxa : x = a
  · subst hxa; by_cases hab : x = b <;> simp [hab]
  · have hba : (x == a) = false := beq_eq_false_iff_ne.mpr hxa
    by_cases hxb : x = b
    · subst hxb; simp [hba]
    · have hbb : (x == b) = false := beq_eq_false_iff_ne.mpr hxb
      simp [hba, hbb]

theorem rcprAesBlock_involutive (k : CryptoGames.CBC.AesKey) (b : CryptoGames.CBC.Block) :
    rcprAesBlock k (rcprAesBlock k b) = b := by
  unfold rcprAesBlock
  cases h0 : (k == CryptoGames.HKDF.bytesToKey32 rcprAesK0) <;> simp only [Bool.false_eq_true, ↓reduceIte]
  case true => exact swap_involutive _ _ b
  cases h1 : (k == CryptoGames.HKDF.bytesToKey32 rcprAesK1) <;> simp only [Bool.false_eq_true, ↓reduceIte]
  case true => exact swap_involutive _ _ b

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
    | mk l hl => cases l with | nil => cases hl | cons b bs => rfl

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

theorem rcprAesDec_rcprAesPerm (k iv text : HwBytes) :
    rcprAesDec k iv (rcprAesPerm k iv text) = some text := by
  unfold rcprAesDec rcprAesPerm
  rw [aesCbcEncrypt_eq_byteSpecs, aesCbcDecrypt_eq_byteSpecs]
  exact ByteSpecs.cbcDecRaw_correct rcprAesBlock_involutive _ _ (⟨text, rfl⟩ : ByteSpecs.Plain text.length)

theorem rcprAesPerm_of_rcprAesDec {k iv ct pt : HwBytes}
    (hdec : rcprAesDec k iv ct = some pt) :
    rcprAesPerm k iv pt = ct := by
  unfold rcprAesDec at hdec; unfold rcprAesPerm
  rw [aesCbcDecrypt_eq_byteSpecs] at hdec; rw [aesCbcEncrypt_eq_byteSpecs]
  unfold ByteSpecs.cbcDecRaw at hdec
  split at hdec
  · cases hdec
  · rename_i hct; push Not at hct; obtain ⟨hcne, hmod⟩ := hct
    let m := ct.length / 16
    have hclen : ct.length = 16 * m := by dsimp [m]; omega
    set P := ByteSpecs.cbcDecryptBlocks (rcprAesBlock (CryptoGames.HKDF.bytesToKey32 k)) (CryptoGames.CBC.bytesToBlock iv) (ByteSpecs.chunks16 ct)
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
      · rename_i hbounds; push Not at hbounds; obtain ⟨hn0, hn16, hnlen⟩ := hbounds
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
          have henc : (ByteSpecs.cbcEncrypt (rcprAesBlock (CryptoGames.HKDF.bytesToKey32 k)) (CryptoGames.CBC.bytesToBlock iv)
              (ByteSpecs.pkcs7Blocks (⟨pt, rfl⟩ : ByteSpecs.Plain pt.length))).toList = ByteSpecs.chunks16 ct := by
            rw [toList_cbcEncrypt, ← hP_eq]
            exact cbcEncryptList_cbcDecryptBlocks (rcprAesBlock_involutive _) _ (ByteSpecs.chunks16 ct)
          rw [henc, flatMap_chunks16 ct hmod]
        · cases hdec

theorem rcprAesPerm_length (k iv text : HwBytes) :
    (rcprAesPerm k iv text).length = 16 * (text.length / 16 + 1) := by
  unfold rcprAesPerm
  rw [aesCbcEncrypt_eq_byteSpecs, length_flatMap_blockToBytesLE, List.Vector.toList_length]; rfl

theorem rcprI0_cryptoEquationsHold : ExternCryptoLawsHold rcprI0 where
  x25519_agreement_commutes a b := by
    simp only [rcprI0_publicKey, rcprI0_agreement, Option.getD_some]
    exact congrArg some (rcprLookupDh_comm a b)
  x25519_agreement_length a p := by simp [rcprI0_agreement, DefsI0.rcprLookupDh_length]
  x25519_public_key_length a := by simp [rcprI0_publicKey, DefsI0.rcprLookupPub_length]
  x25519_agreement_reads_u_coordinate a b b' hb hb' hu := by
    simp only [rcprI0_agreement]; congr 1
    have hl : isLowOrderKey (b.map BitVec.toNat) = isLowOrderKey (b'.map BitVec.toNat) := by
      simp only [isLowOrderKey, List.length_map, hb, hb']
      exact congrArg (fun u => (32 == 32 && lowOrderUs.contains u)) hu
    have hp : rcprPointIdx b = rcprPointIdx b' := by simp only [rcprPointIdx, hb, hb', hu]
    unfold rcprLookupDh; rw [hl, hp]
  x25519_agreement_torsion_invariant secret point t := by
    rw [torsionShift_rcprI0]
  x25519_agreement_zero_iff_low_order a b _ _ := by
    rw [rcprI0_agreement, Option.getD_some]
    cases h : isLowOrderKey (b.map BitVec.toNat)
    · simp only [Bool.false_eq_true, iff_false]; exact rcprLookupDh_ne_zero_of_not_lowOrder a b h
    · unfold rcprLookupDh; simp [h]
  x25519_public_key_not_low_order a _ := by simp [rcprI0_publicKey, rcprLookupPub_not_lowOrder]
  aes_cbc_decrypt_inverts_encrypt plaintext key iv := by
    rw [rcprI0_aesEncrypt, rcprI0_aesDecrypt, Option.getD_some]
    exact rcprAesDec_rcprAesPerm key iv plaintext
  aes_cbc_encrypt_of_decrypt c k iv p _ _ h := by
    rw [rcprI0_aesDecrypt] at h; rw [rcprI0_aesEncrypt]
    exact congrArg some (rcprAesPerm_of_rcprAesDec h)
  hmac_tag_length k d t h := by
    rw [rcprI0_hmac, Option.some.injEq] at h; rw [← h]; exact compHmac_length k d

theorem rcprI0_pubCanonical : X25519PubCanonical rcprI0 := by
  intro s; rw [rcprI0_publicKey, Option.getD_some]; exact rcprLookupPub_lt_p25519 s

theorem rcprI0_torsionShiftsRejected : X25519TorsionShiftsRejected rcprI0 := by
  intro s t k _ hu hne _
  rw [torsionShift_rcprI0] at hu
  exact hne hu

theorem rcprI0_externContractsHoldCli : ExternContractsHoldCli rcprI0 :=
  ⟨rcprI0_cryptoEquationsHold, rcprI0_pubCanonical, rcprI0_torsionShiftsRejected⟩

theorem rcprI0_hooksAgree : HooksMatchInterpretation rcprI0 rcprHooks0 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p k iv _ _; rfl
  · intro c k iv _ _; rfl
  · intro a b; rfl
  · intro a; rfl
  · intro pk rand
    rw [rcprI0_kyberEncaps]
    exact congrArg some (List.take_append_drop 1568 (compKyberEncaps rand.toList)).symm
  · intro sk ct; rfl

theorem rcprI0_kyberCorrectOn (r : ProtocolSetup) (cts : List HwBytes) :
    ∀ ct ∈ cts, ∀ e ss, e.length = 32 → kyberEncapsBytes rcprI0 r e = some (ct, ss) →
      kyberDecapsBytes rcprI0 r ct = some ss :=
  compI0_kyberCorrectOn r cts

theorem rcprI0_gamma_randTerm_pos (w : PQXDHSpqrSetup) (i n : Nat) (hn : n ≠ 0) :
    gamma rcprI0 w.compSem w.compGhost (randTerm i n) = w.compGhost.σ i n := by
  unfold gamma gamma'; conv => lhs; unfold randTerm
  rw [DY.Bytes.rec_eq (concretizeRandom w.compGhost) (concretizeAll rcprI0 w.compSem w.compGhost)]
  simp only [concretizeRandom, hn, ite_false]; rfl

theorem rcprI0_gamma_kemPk (w : PQXDHSpqrSetup) (sk : DY.Bytes) :
    gamma rcprI0 w.compSem w.compGhost (DY.PQKem.kemPk sk) =
      w.compSem.kemPk (gamma rcprI0 w.compSem w.compGhost sk) := by
  unfold gamma gamma'
  show ((({sk} : DY.PQKem.Pk.SubF DY.Bytes).pack).rec (concretizeAll rcprI0 w.compSem w.compGhost)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeKemPk w.compSem) (concretizeAll rcprI0 w.compSem w.compGhost)]; rfl

theorem rcprI0_gamma_sign (w : PQXDHSpqrSetup) (sk n m : DY.Bytes) :
    gamma rcprI0 w.compSem w.compGhost (DY.Signature.sign sk n m) =
      w.compSem.sign (gamma rcprI0 w.compSem w.compGhost sk)
        (gamma rcprI0 w.compSem w.compGhost n) (gamma rcprI0 w.compSem w.compGhost m) := by
  unfold gamma gamma'
  show ((({sk, nonce := n, msg := m} : DY.Signature.Sign.SubF DY.Bytes).pack).rec (concretizeAll rcprI0 w.compSem w.compGhost)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeSign w.compSem) (concretizeAll rcprI0 w.compSem w.compGhost)]; rfl

theorem rcprRecordsI0_ne (w : PQXDHSpqrSetup) :
    (rcprRecordsI0 w).alice ≠ (rcprRecordsI0 w).bob := by
  show ("alice" : String) ≠ "bob"; decide

theorem rcprRecordsI0_randomsAt (w : PQXDHSpqrSetup) :
    setupRandomsAt (rcprRecordsI0 w) =
      [(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)] := by
  rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq (rcprRecordsI0 w) (rcprRecordsI0_ne w)]; rfl

theorem rcprCompFitsPinned_sub_fits :
    ∀ iw r, rcprCompFitsPinned iw r →
      Symbolic.BugInjection.Synthetic.Witnesses.RecvChainPrivRetainedCli.fits iw r := by
  rintro iw r ⟨⟨hc, _, _, _, _, _⟩, hext, hhooks⟩
  exact ⟨hc, hext, hhooks⟩

theorem rcprCompFitsPinned_satisfiable :
    ∃ iw r, rcprCompFitsPinned iw r := by
  let w := Symbolic.BugInjection.Synthetic.Witnesses.RecvChainPrivRetainedCli.setup
  have hpl : w.Plausible := by decide +kernel
  have hw : w.withOpk = false := rfl
  obtain ⟨ha, hb, hs, hss, hk, hks, hsec, hslice, hnd, _, _⟩ := hpl
  have h5 := Symbolic.Swarm.CREF.b1_setupPublic_5 (rcprRecordsI0 w) (rcprRecordsI0_ne w)
  have h6 := Symbolic.Swarm.CREF.b1_setupPublic_6 (rcprRecordsI0 w) (rcprRecordsI0_ne w)
  have h7 := Symbolic.Swarm.CREF.b1_setupPublic_7 (rcprRecordsI0 w) (rcprRecordsI0_ne w)
  have hR := rcprRecordsI0_randomsAt w
  have o5 : (rcprRecordsI0 w).opaqueBytes (setupPublic (rcprRecordsI0 w) 5) = w.spkSig := by
    rw [h5]; show gamma rcprI0 w.compSem w.compGhost _ = _
    rw [rcprI0_gamma_sign]
    show (if gamma rcprI0 w.compSem w.compGhost (randTerm 11 64) = fillFresh 11 64 then _ else _) = _
    rw [rcprI0_gamma_randTerm_pos w 11 64 (by decide)]
    simp [PQXDHSpqrSetup.compGhost, PQXDHSpqrSetup.fresh]
  have o6 : (rcprRecordsI0 w).opaqueBytes (setupPublic (rcprRecordsI0 w) 6) = w.kyberPk := by
    rw [h6]; show gamma rcprI0 w.compSem w.compGhost _ = _; rw [rcprI0_gamma_kemPk]; rfl
  have o7 : (rcprRecordsI0 w).opaqueBytes (setupPublic (rcprRecordsI0 w) 7) = w.kyberPkSig := by
    rw [h7]; show gamma rcprI0 w.compSem w.compGhost _ = _
    rw [rcprI0_gamma_sign]
    show (if gamma rcprI0 w.compSem w.compGhost (randTerm 17 64) = fillFresh 11 64 then _ else _) = _
    rw [rcprI0_gamma_randTerm_pos w 17 64 (by decide)]
    simp [PQXDHSpqrSetup.compGhost, PQXDHSpqrSetup.fresh, fillFresh_ne_11_17]
  have hwf : ProtocolSetupWF (rcprRecordsI0 w) := by
    refine ⟨rcprRecordsI0_ne w, ?_, ?_, ?_, ?_, ?_, hsec, ?_⟩
    · rw [hR]; intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [rcprRecordsI0, PQXDHSpqrSetup.fresh, fillFresh, ha, hb, hs]
    · rw [hR]; simpa [hw, rcprRecordsI0, PQXDHSpqrSetup.fresh] using hnd
    · dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSigTerm]; rw [o5]; exact hss
    · dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkPubTerm]; rw [o6]; exact hk
    · dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkSigTerm]; rw [o7]; exact hks
    · show slice w.kyberSec 1537 1568 = _
      dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkPubTerm]; rw [o6]; exact hslice
  have hs0 : secretBytes (rcprRecordsI0 w) 0 = w.aliceId := by
    rw [secretBytes, hR]; simp [rcprRecordsI0, PQXDHSpqrSetup.fresh]
  have hs1 : secretBytes (rcprRecordsI0 w) 1 = w.bobId := by
    rw [secretBytes, hR]; simp [rcprRecordsI0, PQXDHSpqrSetup.fresh]
  have hs2 : secretBytes (rcprRecordsI0 w) 2 = w.spk := by
    rw [secretBytes, hR]; simp [rcprRecordsI0, PQXDHSpqrSetup.fresh]
  have hs3 : secretBytes (rcprRecordsI0 w) 3 = fillFresh 11 64 := by
    rw [secretBytes, hR]; simp [rcprRecordsI0, PQXDHSpqrSetup.fresh]
  have hs4 : secretBytes (rcprRecordsI0 w) 4 = fillFresh 16 64 := by
    rw [secretBytes, hR]; simp [rcprRecordsI0, PQXDHSpqrSetup.fresh]
  have hs5 : secretBytes (rcprRecordsI0 w) 5 = fillFresh 17 64 := by
    rw [secretBytes, hR]; simp [rcprRecordsI0, PQXDHSpqrSetup.fresh]
  exact ⟨(rcprI0, rcprHooks0), rcprRecordsI0 w,
    ⟨⟨hwf, rfl, rfl, rfl, rfl, rfl, hs0, hs1, hs2, o5, o6, o7, rfl,
      rcprI0_cryptoEquationsHold, rcprI0_pubCanonical,
      rcprI0_kyberCorrectOn (rcprRecordsI0 w) w.kyberCts⟩,
     rfl, ⟨hs3, hs4, hs5⟩, ⟨rfl, rfl⟩,
     rcprI0_torsionShiftsRejected, fun _ h => nomatch h⟩,
    rcprI0_externContractsHoldCli, rcprI0_hooksAgree⟩

export Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.I0LawsAux
  (FE FR OnTabE OnTabR FE_eq FR_eq
   rcprSha256_row_of_untagged rcprSha256_length rcprSha256_inj_of_untagged
   onTabE_of_sha256With_untagged hmacWith_eqE hmac_inner_untaggedE hmac_outer_first_onTabE
   rows_mod32_nodup rows_out_nodupE rows_take8_nodupE rows_out_ltE rows_ltE
   rows_out_ne_ivE rows_out_roundtripE
   rowOfTake8E rowByOutE keyOfRow1E keyOfTake8E row_stepE
   keyOfTake8_hmacWithE keyOfTake8_hmacWithR
   FE_inj_of_untagged FE_ne_iv AllUntaggedE
   sha256With_inj_of_untaggedE sha256With_inj_of_untaggedR
   normKeyE normKeyE_length_le hmacWith_eq_normKeyE
   hmacWith_msg_inj_of_untaggedE hmacWith_msg_inj_of_untaggedR
   hmacWith_inj_of_untaggedE hmacWith_inj_of_untaggedR
   rcprHmacKeys32 rcprHmacKeys32_untagged hmacWith_key_untagged_of_untaggedE
   gamma_hmacE gamma_hmacR gamma_hmacE_length gamma_hmacR_length
   gamma_concatE gamma_concatR gamma_trunc8E gamma_trunc8R
   gamma_computeMacE gamma_computeMacR
   spqrKeyBytes_length gamma_spqrSendKey_length gamma_spqrRecvKey_length
   gamma_trMsgKeys_congr_prk computeMac_pins_macKey_prk_seed
   computeMac_pins_salt_and_seed not_macTagForgeryOrCollision_of_honest_mac)

end Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.I0Laws
