/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticKeepOpk.DefsI0
public import Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
public import Symbolic.BugInjection.Proofs.Common443.CompRI0ShaInj
public import Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound

/-!
# Cryptographic Contracts, Hook Agreement, Satisfiability, and SHA/MAC Collision Laws for `keepOpkI0`

Proves:
1. Primitive unfolding and length/AES/Kyber lemmas for `keepOpkI0`.
2. `ExternContractsHoldCli keepOpkI0`, `HooksMatchInterpretation keepOpkI0 keepOpkHooks0`, and
   `keepOpkI0_kyberCorrectOn`.
3. `keepOpkCompFitsPinned_sub_fits` and `keepOpkCompFitsPinned_satisfiable` (`withOpk = true`, `opkId = 3`).
4. Untagged SHA-256 / HMAC-SHA-256 / `computeMac` injectivity on `keepOpkSha256Rows` and universal
   discharge `not_macTagForgeryOrCollision_of_honest_mac`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticKeepOpk.I0Laws

open ByteSpecs
  (ShaState sha256IV sha256Pad chunks64 sha256With hmacWith toBEBytes)
open DY.X25519 (isLowOrderKey lowOrderUs uCoord leValue p25519)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement
  (x25519PublicKeySymbol x25519AgreementSymbol x25519TorsionSymbol torsionShift
   aesCbcEncryptSymbol aesCbcDecryptSymbol sha256CompressSymbol
   sha256CompressFunction shaStateBytes shaStateOfBytes ExternCryptoLawsHold)
open DY.Libsignal.PQXDH.Refinement
  (kyberEncapsSymbol kyberDecapsSymbol
   mlkem768FromSeedSymbol libcruxHmacSymbol X25519TorsionShiftsRejected)
open DY.Libsignal.TripleRatchet (hmac hkdfBlock1 hkdfBlock2 hkdfBlock3 trMsgKeys computeMac TRSignalMsg)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli (ExternContractsHoldCli HooksMatchInterpretation)
open Symbolic.BugInjection (PQXDHSpqrSetup TorsionShiftsRecorded fillFresh fillFresh_ne_11_17)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
  (bytesToNat compTag4 compTag4Ipad compTag4Opad compDefaultPub compDefaultDh
   compDefaultSha256 compShaMix28 compDefaultHmac compHmacMix28
   compDefaultKyberCt compDefaultKyberSs)
open Symbolic.BugInjection.Proofs.Common443.CompI0Laws
  (leBytes_length)
open Symbolic.BugInjection.Proofs.Common443.CompRTag
  (sha256With_length sha256Pad_length_mod sha256Pad_append64 chunks64_append64
   chunks64_padTail64_32 padTail64 sha256With_take4_of_offTable hmacWith_take4_of_inner)
open Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
  (compDefaultSha256_take4 leBytes_bytesToNat tagW toBEBytes_tagW shaStateOfBytes_compTag4_head
   shaStateBytes_take4_of_head kblk kblk_length ivNat map_xor_xor digestOfOut
   nodup_of_natNodup leBytes_len bytesToNat_leBytes shaStateBytes_shaStateOfBytes
   find?_eq_some_of_nodup)
open Symbolic.BugInjection.Proofs.Common443.CompRI0ShaInj
  (eq_of_bytesToNat_eq shaStateOfBytes_shaStateBytes' digest_inj chunks64_inj sha256Pad_inj
   eq_nil_or_snoc kblk_inj)
open Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound
  (ms_pack_lit ms_pack_kdf ms_pack_trunc ms_pack_concat)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.DefsI0
  (keepOpkSha256Bucket keepOpkSha256Rows keepOpkSha256
   keepOpkPubOfIdx keepOpkPubOfOpt keepOpkSecretIdx keepOpkPointIdxOfU keepOpkPointIdx
   keepOpkDhByIdx keepOpkLookupPub keepOpkLookupDh
   keepOpkAesPt0 keepOpkAesK0 keepOpkAesIv0 keepOpkAesCt0 keepOpkAesA0 keepOpkAesB0
   keepOpkAesPt1 keepOpkAesK1 keepOpkAesIv1 keepOpkAesCt1 keepOpkAesA1 keepOpkAesB1
   keepOpkAesBlock keepOpkAesPerm keepOpkAesDec
   keepOpkKyberE0 keepOpkKyberCt0 keepOpkKyberSs0
   keepOpkKyberE1 keepOpkKyberCt1 keepOpkKyberSs1
   keepOpkKyberEncaps keepOpkKyberDecaps
   keepOpkKyberCt0_length keepOpkKyberCt1_length
   keepOpkMlkem768FromSeed keepOpkHmac
   keepOpkI0 keepOpkHooks0 keepOpkRecordsI0 keepOpkCompFitsPinned)

/-! ## 1. Unfolding & Primitive Helper Lemmas -/

theorem keepOpkI0_publicKey (sk : HwBytes) :
    keepOpkI0 x25519PublicKeySymbol [sk] = some (keepOpkLookupPub sk) := rfl
theorem keepOpkI0_agreement (sk pk : HwBytes) :
    keepOpkI0 x25519AgreementSymbol [sk, pk] = some (keepOpkLookupDh sk pk) := rfl
theorem keepOpkI0_torsion (pt : HwBytes) (b : BitVec 8) :
    keepOpkI0 x25519TorsionSymbol [pt, [b]] = none := rfl
theorem keepOpkI0_aesEncrypt (text k iv : HwBytes) :
    keepOpkI0 aesCbcEncryptSymbol [text, k, iv] = some (keepOpkAesPerm k iv text) := rfl
theorem keepOpkI0_aesDecrypt (ct k iv : HwBytes) :
    keepOpkI0 aesCbcDecryptSymbol [ct, k, iv] = keepOpkAesDec k iv ct := rfl
theorem keepOpkI0_kyberEncaps (pk rand : HwBytes) :
    keepOpkI0 kyberEncapsSymbol [pk, rand] = some (keepOpkKyberEncaps rand) := rfl
theorem keepOpkI0_kyberDecaps (sk ct : HwBytes) :
    keepOpkI0 kyberDecapsSymbol [sk, ct] = some (keepOpkKyberDecaps ct) := rfl
theorem keepOpkI0_hmac (k d : HwBytes) :
    keepOpkI0 libcruxHmacSymbol [k, d] = some (keepOpkHmac k d) := rfl
theorem keepOpkI0_sha256Compress (st blk : HwBytes) :
    keepOpkI0 sha256CompressSymbol [st, blk] = some (keepOpkSha256 st blk) := rfl
theorem keepOpkI0_mlkem768FromSeed (seed : HwBytes) :
    keepOpkI0 mlkem768FromSeedSymbol [seed] = some (keepOpkMlkem768FromSeed seed) := rfl

theorem keepOpkHmac_length (k d : HwBytes) : (keepOpkHmac k d).length = 32 := by
  have hd : (compDefaultHmac k d).length = 32 := by simp [compDefaultHmac, compTag4, compHmacMix28]
  unfold keepOpkHmac
  split
  · dsimp only
    split
    · exact leBytes_length 32 _
    · split
      · exact leBytes_length 32 _
      · exact hd
  · exact hd

theorem keepOpkMlkem768FromSeed_length (seed : HwBytes) :
    (keepOpkMlkem768FromSeed seed).length = 2400 := by
  unfold keepOpkMlkem768FromSeed
  split
  · dsimp only
    split
    · exact leBytes_length 2400 _
    · split
      · exact leBytes_length 2400 _
      · rfl
  · rfl

/-! ## 2. X25519 & AES-256-CBC Laws -/

theorem keepOpkPubOfOpt_lt_p25519 : ∀ o : Option (Fin 10),
    leValue ((keepOpkPubOfOpt o).map BitVec.toNat) < p25519
  | none => by decide
  | some i => by revert i; decide

theorem keepOpkLookupPub_lt_p25519 (s : HwBytes) :
    leValue ((keepOpkLookupPub s).map BitVec.toNat) < p25519 :=
  keepOpkPubOfOpt_lt_p25519 (keepOpkSecretIdx s)

theorem keepOpkPubOfOpt_not_lowOrder : ∀ o : Option (Fin 10),
    isLowOrderKey ((keepOpkPubOfOpt o).map BitVec.toNat) = false
  | none => by decide
  | some i => by revert i; decide

theorem keepOpkLookupPub_not_lowOrder (s : HwBytes) :
    isLowOrderKey ((keepOpkLookupPub s).map BitVec.toNat) = false :=
  keepOpkPubOfOpt_not_lowOrder (keepOpkSecretIdx s)

theorem keepOpkPointIdx_keepOpkPubOfOpt : ∀ o : Option (Fin 10),
    keepOpkPointIdx (keepOpkPubOfOpt o) = o
  | none => by decide
  | some i => by revert i; decide

theorem keepOpkPointIdx_keepOpkLookupPub (s : HwBytes) :
    keepOpkPointIdx (keepOpkLookupPub s) = keepOpkSecretIdx s :=
  keepOpkPointIdx_keepOpkPubOfOpt (keepOpkSecretIdx s)

theorem keepOpkDhByIdx_comm (i j : Fin 10) : keepOpkDhByIdx i j = keepOpkDhByIdx j i := by
  revert i j; decide

theorem keepOpkLookupDh_comm (a b : HwBytes) :
    keepOpkLookupDh a (keepOpkLookupPub b) = keepOpkLookupDh b (keepOpkLookupPub a) := by
  unfold keepOpkLookupDh
  rw [keepOpkLookupPub_not_lowOrder, keepOpkLookupPub_not_lowOrder,
      keepOpkPointIdx_keepOpkLookupPub, keepOpkPointIdx_keepOpkLookupPub]
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases keepOpkSecretIdx a <;> cases keepOpkSecretIdx b <;>
    first | rfl | exact keepOpkDhByIdx_comm _ _

theorem keepOpkDhByIdx_ne_zero (i j : Fin 10) :
    keepOpkDhByIdx i j ≠ List.replicate 32 0#8 := by
  revert i j; decide

theorem keepOpkLookupDh_ne_zero_of_not_lowOrder (s p : HwBytes)
    (hlo : isLowOrderKey (p.map BitVec.toNat) = false) :
    keepOpkLookupDh s p ≠ List.replicate 32 0#8 := by
  unfold keepOpkLookupDh; rw [hlo]; simp only [Bool.false_eq_true, ↓reduceIte]
  cases keepOpkSecretIdx s <;> cases keepOpkPointIdx p <;> dsimp only <;>
    first | exact keepOpkDhByIdx_ne_zero _ _ | decide

theorem torsionShift_keepOpkI0 (p : HwBytes) (t : Fin 8) :
    torsionShift keepOpkI0 p t = p := by
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

theorem keepOpkAesBlock_involutive (k : CryptoGames.CBC.AesKey) (b : CryptoGames.CBC.Block) :
    keepOpkAesBlock k (keepOpkAesBlock k b) = b := by
  unfold keepOpkAesBlock
  cases h0 : (k == CryptoGames.HKDF.bytesToKey32 keepOpkAesK0) <;> simp only [Bool.false_eq_true, ↓reduceIte]
  case true => exact swap_involutive _ _ b
  cases h1 : (k == CryptoGames.HKDF.bytesToKey32 keepOpkAesK1) <;> simp only [Bool.false_eq_true, ↓reduceIte]
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

theorem keepOpkAesDec_keepOpkAesPerm (k iv text : HwBytes) :
    keepOpkAesDec k iv (keepOpkAesPerm k iv text) = some text := by
  unfold keepOpkAesDec keepOpkAesPerm
  rw [aesCbcEncrypt_eq_byteSpecs, aesCbcDecrypt_eq_byteSpecs]
  exact ByteSpecs.cbcDecRaw_correct keepOpkAesBlock_involutive _ _ (⟨text, rfl⟩ : ByteSpecs.Plain text.length)

theorem keepOpkAesPerm_of_keepOpkAesDec {k iv ct pt : HwBytes}
    (hdec : keepOpkAesDec k iv ct = some pt) :
    keepOpkAesPerm k iv pt = ct := by
  unfold keepOpkAesDec at hdec; unfold keepOpkAesPerm
  rw [aesCbcDecrypt_eq_byteSpecs] at hdec; rw [aesCbcEncrypt_eq_byteSpecs]
  unfold ByteSpecs.cbcDecRaw at hdec
  split at hdec
  · cases hdec
  · rename_i hct; push Not at hct; obtain ⟨hcne, hmod⟩ := hct
    let m := ct.length / 16
    have hclen : ct.length = 16 * m := by dsimp [m]; omega
    set P := ByteSpecs.cbcDecryptBlocks (keepOpkAesBlock (CryptoGames.HKDF.bytesToKey32 k)) (CryptoGames.CBC.bytesToBlock iv) (ByteSpecs.chunks16 ct)
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
          have henc : (ByteSpecs.cbcEncrypt (keepOpkAesBlock (CryptoGames.HKDF.bytesToKey32 k)) (CryptoGames.CBC.bytesToBlock iv)
              (ByteSpecs.pkcs7Blocks (⟨pt, rfl⟩ : ByteSpecs.Plain pt.length))).toList = ByteSpecs.chunks16 ct := by
            rw [toList_cbcEncrypt, ← hP_eq]
            exact cbcEncryptList_cbcDecryptBlocks (keepOpkAesBlock_involutive _) _ (ByteSpecs.chunks16 ct)
          rw [henc, flatMap_chunks16 ct hmod]
        · cases hdec

theorem keepOpkAesPerm_length (k iv text : HwBytes) :
    (keepOpkAesPerm k iv text).length = 16 * (text.length / 16 + 1) := by
  unfold keepOpkAesPerm
  rw [aesCbcEncrypt_eq_byteSpecs, length_flatMap_blockToBytesLE, List.Vector.toList_length]; rfl

private theorem shiftLeft8_or_assoc (acc x y : BitVec 128) (n : Nat) :
    (((acc <<< n) ||| x) <<< 8) ||| y = (acc <<< (n + 8)) ||| ((x <<< 8) ||| y) := by
  ext i hi
  simp only [BitVec.getElem_or, BitVec.getElem_shiftLeft]
  by_cases h8 : i < 8
  · have hlt : i < n + 8 := by omega
    simp [h8, hlt]
  · have hsub : i - 8 < n ↔ i < n + 8 := by omega
    have hidx : i - 8 - n = i - (n + 8) := by omega
    simp [h8, hsub, hidx, Bool.or_assoc]

private theorem foldr_bytesToBlock_acc :
    ∀ (l : List (BitVec 8)) (acc : BitVec 128),
      l.foldr (fun (b : BitVec 8) (a : BitVec 128) => (a <<< 8) ||| b.zeroExtend 128) acc =
        (acc <<< (8 * l.length)) |||
          l.foldr (fun (b : BitVec 8) (a : BitVec 128) => (a <<< 8) ||| b.zeroExtend 128) 0#128
  | [], acc => by simp
  | b :: bs, acc => by
    simp only [List.foldr_cons, List.length_cons]
    rw [foldr_bytesToBlock_acc bs acc, shiftLeft8_or_assoc]
    have hmul : 8 * bs.length + 8 = 8 * (bs.length + 1) := by omega
    rw [hmul]

private theorem shiftLeft_128_eq_zero (x : BitVec 128) : x <<< (8 * 16 : Nat) = 0#128 := by
  ext i hi
  have hlt : i < 8 * 16 := hi
  simp only [BitVec.getElem_shiftLeft, BitVec.getElem_zero, hlt, decide_true, Bool.not_true, Bool.false_and]

private theorem bytesToBlock_take16 (iv : HwBytes) :
    CryptoGames.CBC.bytesToBlock (iv.take 16) = CryptoGames.CBC.bytesToBlock iv := by
  by_cases h : iv.length ≤ 16
  · rw [List.take_of_length_le h]
  · have hlen : (iv.take 16).length = 16 := by simp; omega
    conv_rhs =>
      rw [← List.take_append_drop 16 iv]
      unfold CryptoGames.CBC.bytesToBlock
      rw [List.foldr_append, foldr_bytesToBlock_acc (iv.take 16), hlen,
        shiftLeft_128_eq_zero, BitVec.zero_or]
    rfl

theorem keepOpkAesPerm_take16_iv (k iv text : HwBytes) :
    keepOpkAesPerm k (iv.take 16) text = keepOpkAesPerm k iv text := by
  unfold keepOpkAesPerm; rw [bytesToBlock_take16]

theorem keepOpkAesDec_take16_iv (k iv ct : HwBytes) :
    keepOpkAesDec k (iv.take 16) ct = keepOpkAesDec k iv ct := by
  unfold keepOpkAesDec; rw [bytesToBlock_take16]

theorem keepOpkAesPerm_pt0 : keepOpkAesPerm keepOpkAesK0 keepOpkAesIv0 keepOpkAesPt0 = keepOpkAesCt0 := by decide
theorem keepOpkAesPerm_pt1 : keepOpkAesPerm keepOpkAesK1 keepOpkAesIv1 keepOpkAesPt1 = keepOpkAesCt1 := by decide

theorem keepOpkAesPerm_pt0_of_take16 {k iv : HwBytes} (hk : k = keepOpkAesK0) (hiv : iv.take 16 = keepOpkAesIv0) :
    keepOpkAesPerm k iv keepOpkAesPt0 = keepOpkAesCt0 := by
  rw [hk, ← keepOpkAesPerm_take16_iv, hiv, keepOpkAesPerm_pt0]

theorem keepOpkAesPerm_pt1_of_take16 {k iv : HwBytes} (hk : k = keepOpkAesK1) (hiv : iv.take 16 = keepOpkAesIv1) :
    keepOpkAesPerm k iv keepOpkAesPt1 = keepOpkAesCt1 := by
  rw [hk, ← keepOpkAesPerm_take16_iv, hiv, keepOpkAesPerm_pt1]

/-! ## 3. Kyber-1024, Extern Contracts, Hook Agreement & Satisfiability -/

private theorem keepOpkKyberCt1_beq_ct0 : (keepOpkKyberCt1 == keepOpkKyberCt0) = false := by
  exact Bool.eq_false_iff.mpr (fun h => by
    have := congrArg List.head? (eq_of_beq h)
    revert this; decide)

private theorem compDefaultKyberCt_beq_ct0 : (compDefaultKyberCt == keepOpkKyberCt0) = false := by
  exact Bool.eq_false_iff.mpr (fun h => by
    have := congrArg List.head? (eq_of_beq h)
    revert this; decide)

private theorem compDefaultKyberCt_beq_ct1 : (compDefaultKyberCt == keepOpkKyberCt1) = false := by
  exact Bool.eq_false_iff.mpr (fun h => by
    have := congrArg List.head? (eq_of_beq h)
    revert this; decide)

private theorem keepOpkKyberDecaps_ct0 : keepOpkKyberDecaps keepOpkKyberCt0 = keepOpkKyberSs0 := by
  simp [keepOpkKyberDecaps]

private theorem keepOpkKyberDecaps_ct1 : keepOpkKyberDecaps keepOpkKyberCt1 = keepOpkKyberSs1 := by
  simp [keepOpkKyberDecaps, keepOpkKyberCt1_beq_ct0]

private theorem keepOpkKyberDecaps_default : keepOpkKyberDecaps compDefaultKyberCt = compDefaultKyberSs := by
  simp [keepOpkKyberDecaps, compDefaultKyberCt_beq_ct0, compDefaultKyberCt_beq_ct1]

private theorem take_append_of_eq_length {α : Type} {l1 l2 : List α} {n : Nat} (h : l1.length = n) :
    (l1 ++ l2).take n = l1 := by subst h; exact List.take_left

private theorem drop_append_of_eq_length {α : Type} {l1 l2 : List α} {n : Nat} (h : l1.length = n) :
    (l1 ++ l2).drop n = l2 := by subst h; exact List.drop_left

theorem keepOpkI0_kyberCorrectOn (r : ProtocolSetup) (cts : List HwBytes) :
    ∀ ct ∈ cts, ∀ e ss, e.length = 32 → kyberEncapsBytes keepOpkI0 r e = some (ct, ss) →
      kyberDecapsBytes keepOpkI0 r ct = some ss := by
  intro ct _ e ss _ he
  unfold kyberEncapsBytes at he
  rw [keepOpkI0_kyberEncaps, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨hct, hss⟩ := he
  unfold kyberDecapsBytes
  rw [keepOpkI0_kyberDecaps, Option.some.injEq]
  unfold keepOpkKyberEncaps at hct hss
  split at hct <;> rename_i h0
  · simp only [h0, ↓reduceIte] at hss
    rw [take_append_of_eq_length keepOpkKyberCt0_length] at hct
    rw [drop_append_of_eq_length keepOpkKyberCt0_length] at hss
    rw [← hct, ← hss, keepOpkKyberDecaps_ct0]
  · split at hct <;> rename_i h1
    · simp only [h0, h1, Bool.false_eq_true, ↓reduceIte] at hss
      rw [take_append_of_eq_length keepOpkKyberCt1_length] at hct
      rw [drop_append_of_eq_length keepOpkKyberCt1_length] at hss
      rw [← hct, ← hss, keepOpkKyberDecaps_ct1]
    · simp only [h0, h1, Bool.false_eq_true, ↓reduceIte] at hss
      have hdlen : compDefaultKyberCt.length = 1568 := rfl
      rw [take_append_of_eq_length hdlen] at hct
      rw [drop_append_of_eq_length hdlen] at hss
      rw [← hct, ← hss, keepOpkKyberDecaps_default]

theorem keepOpkI0_cryptoEquationsHold : ExternCryptoLawsHold keepOpkI0 where
  x25519_agreement_commutes a b := by
    simp only [keepOpkI0_publicKey, keepOpkI0_agreement, Option.getD_some]
    exact congrArg some (keepOpkLookupDh_comm a b)
  x25519_agreement_length a p := by simp [keepOpkI0_agreement, DefsI0.keepOpkLookupDh_length]
  x25519_public_key_length a := by simp [keepOpkI0_publicKey, DefsI0.keepOpkLookupPub_length]
  x25519_agreement_reads_u_coordinate a b b' hb hb' hu := by
    simp only [keepOpkI0_agreement]; congr 1
    have hl : isLowOrderKey (b.map BitVec.toNat) = isLowOrderKey (b'.map BitVec.toNat) := by
      simp only [isLowOrderKey, List.length_map, hb, hb']
      exact congrArg (fun u => (32 == 32 && lowOrderUs.contains u)) hu
    have hp : keepOpkPointIdx b = keepOpkPointIdx b' := by simp only [keepOpkPointIdx, hb, hb', hu]
    unfold keepOpkLookupDh; rw [hl, hp]
  x25519_agreement_torsion_invariant secret point t := by
    rw [torsionShift_keepOpkI0]
  x25519_agreement_zero_iff_low_order a b _ _ := by
    rw [keepOpkI0_agreement, Option.getD_some]
    cases h : isLowOrderKey (b.map BitVec.toNat)
    · simp only [Bool.false_eq_true, iff_false]; exact keepOpkLookupDh_ne_zero_of_not_lowOrder a b h
    · unfold keepOpkLookupDh; simp [h]
  x25519_public_key_not_low_order a _ := by simp [keepOpkI0_publicKey, keepOpkLookupPub_not_lowOrder]
  aes_cbc_decrypt_inverts_encrypt plaintext key iv := by
    rw [keepOpkI0_aesEncrypt, keepOpkI0_aesDecrypt, Option.getD_some]
    exact keepOpkAesDec_keepOpkAesPerm key iv plaintext
  aes_cbc_encrypt_of_decrypt c k iv p _ _ h := by
    rw [keepOpkI0_aesDecrypt] at h; rw [keepOpkI0_aesEncrypt]
    exact congrArg some (keepOpkAesPerm_of_keepOpkAesDec h)
  hmac_tag_length k d t h := by
    rw [keepOpkI0_hmac, Option.some.injEq] at h; rw [← h]; exact keepOpkHmac_length k d

theorem keepOpkI0_pubCanonical : X25519PubCanonical keepOpkI0 := by
  intro s; rw [keepOpkI0_publicKey, Option.getD_some]; exact keepOpkLookupPub_lt_p25519 s

theorem keepOpkI0_torsionShiftsRejected : X25519TorsionShiftsRejected keepOpkI0 := by
  intro s t k _ hu hne _
  rw [torsionShift_keepOpkI0] at hu
  exact hne hu

theorem keepOpkI0_externContractsHoldCli : ExternContractsHoldCli keepOpkI0 :=
  ⟨keepOpkI0_cryptoEquationsHold, keepOpkI0_pubCanonical, keepOpkI0_torsionShiftsRejected⟩

theorem keepOpkI0_hooksAgree : HooksMatchInterpretation keepOpkI0 keepOpkHooks0 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p k iv _ _; rfl
  · intro c k iv _ _; rfl
  · intro a b; rfl
  · intro a; rfl
  · intro pk rand
    rw [keepOpkI0_kyberEncaps]
    exact congrArg some (List.take_append_drop 1568 (keepOpkKyberEncaps rand.toList)).symm
  · intro sk ct; rfl

theorem keepOpkI0_gamma_randTerm_pos (w : PQXDHSpqrSetup) (i n : Nat) (hn : n ≠ 0) :
    gamma keepOpkI0 w.compSem w.compGhost (randTerm i n) = w.compGhost.σ i n := by
  unfold gamma gamma'; conv => lhs; unfold randTerm
  rw [DY.Bytes.rec_eq (concretizeRandom w.compGhost) (concretizeAll keepOpkI0 w.compSem w.compGhost)]
  simp only [concretizeRandom, hn, ite_false]; rfl

theorem keepOpkI0_gamma_kemPk (w : PQXDHSpqrSetup) (sk : DY.Bytes) :
    gamma keepOpkI0 w.compSem w.compGhost (DY.PQKem.kemPk sk) =
      w.compSem.kemPk (gamma keepOpkI0 w.compSem w.compGhost sk) := by
  unfold gamma gamma'
  show ((({sk} : DY.PQKem.Pk.SubF DY.Bytes).pack).rec (concretizeAll keepOpkI0 w.compSem w.compGhost)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeKemPk w.compSem) (concretizeAll keepOpkI0 w.compSem w.compGhost)]; rfl

theorem keepOpkI0_gamma_sign (w : PQXDHSpqrSetup) (sk n m : DY.Bytes) :
    gamma keepOpkI0 w.compSem w.compGhost (DY.Signature.sign sk n m) =
      w.compSem.sign (gamma keepOpkI0 w.compSem w.compGhost sk)
        (gamma keepOpkI0 w.compSem w.compGhost n) (gamma keepOpkI0 w.compSem w.compGhost m) := by
  unfold gamma gamma'
  show ((({sk, nonce := n, msg := m} : DY.Signature.Sign.SubF DY.Bytes).pack).rec (concretizeAll keepOpkI0 w.compSem w.compGhost)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeSign w.compSem) (concretizeAll keepOpkI0 w.compSem w.compGhost)]; rfl

theorem keepOpkRecordsI0_ne (w : PQXDHSpqrSetup) :
    (keepOpkRecordsI0 w).alice ≠ (keepOpkRecordsI0 w).bob := by
  show ("alice" : String) ≠ "bob"; decide

theorem keepOpkRecordsI0_randomsAt (w : PQXDHSpqrSetup) :
    setupRandomsAt (keepOpkRecordsI0 w) =
      [(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)] ++
        (if w.withOpk then [(22, 32)] else []) :=
  Symbolic.Swarm.CREF.b1_setupRandomsAt_eq (keepOpkRecordsI0 w) (keepOpkRecordsI0_ne w)

theorem keepOpkCompFitsPinned_sub_fits :
    ∀ iw r, keepOpkCompFitsPinned iw r →
      Symbolic.BugInjection.Synthetic.Witnesses.KeepOpkCli.fits iw r := by
  rintro iw r ⟨⟨hc, _, _, _, _, _⟩, hext, hhooks⟩
  exact ⟨hc, hext, hhooks⟩

theorem keepOpkCompFitsPinned_satisfiable :
    ∃ iw r, keepOpkCompFitsPinned iw r := by
  let w := Symbolic.BugInjection.Synthetic.Witnesses.KeepOpkCli.setup
  have hpl : w.Plausible := by decide +kernel
  obtain ⟨ha, hb, hs, hss, hk, hks, hsec, hslice, hnd7, hopk_pl, _⟩ := hpl
  have hopk : w.withOpk = true := rfl
  have hopk_len := hopk_pl hopk
  have h5 := Symbolic.Swarm.CREF.b1_setupPublic_5 (keepOpkRecordsI0 w) (keepOpkRecordsI0_ne w)
  have h6 := Symbolic.Swarm.CREF.b1_setupPublic_6 (keepOpkRecordsI0 w) (keepOpkRecordsI0_ne w)
  have h7 := Symbolic.Swarm.CREF.b1_setupPublic_7 (keepOpkRecordsI0 w) (keepOpkRecordsI0_ne w)
  have hR : setupRandomsAt (keepOpkRecordsI0 w) =
      [(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64), (22, 32)] := by
    rw [keepOpkRecordsI0_randomsAt w]; rfl
  have o5 : (keepOpkRecordsI0 w).opaqueBytes (setupPublic (keepOpkRecordsI0 w) 5) = w.spkSig := by
    rw [h5]; show gamma keepOpkI0 w.compSem w.compGhost _ = _
    rw [keepOpkI0_gamma_sign]
    show (if gamma keepOpkI0 w.compSem w.compGhost (randTerm 11 64) = fillFresh 11 64 then _ else _) = _
    rw [keepOpkI0_gamma_randTerm_pos w 11 64 (by decide)]
    simp [PQXDHSpqrSetup.compGhost, PQXDHSpqrSetup.fresh]
  have o6 : (keepOpkRecordsI0 w).opaqueBytes (setupPublic (keepOpkRecordsI0 w) 6) = w.kyberPk := by
    rw [h6]; show gamma keepOpkI0 w.compSem w.compGhost _ = _; rw [keepOpkI0_gamma_kemPk]; rfl
  have o7 : (keepOpkRecordsI0 w).opaqueBytes (setupPublic (keepOpkRecordsI0 w) 7) = w.kyberPkSig := by
    rw [h7]; show gamma keepOpkI0 w.compSem w.compGhost _ = _
    rw [keepOpkI0_gamma_sign]
    show (if gamma keepOpkI0 w.compSem w.compGhost (randTerm 17 64) = fillFresh 11 64 then _ else _) = _
    rw [keepOpkI0_gamma_randTerm_pos w 17 64 (by decide)]
    simp [PQXDHSpqrSetup.compGhost, PQXDHSpqrSetup.fresh, fillFresh_ne_11_17]
  have hwf : ProtocolSetupWF (keepOpkRecordsI0 w) := by
    refine ⟨keepOpkRecordsI0_ne w, ?_, ?_, ?_, ?_, ?_, hsec, ?_⟩
    · rw [hR]; intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [keepOpkRecordsI0, PQXDHSpqrSetup.fresh, hopk, fillFresh, ha, hb, hs, hopk_len]
    · rw [hR]; simpa [keepOpkRecordsI0, PQXDHSpqrSetup.fresh, hopk] using hnd7
    · dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSigTerm]; rw [o5]; exact hss
    · dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkPubTerm]; rw [o6]; exact hk
    · dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkSigTerm]; rw [o7]; exact hks
    · show slice w.kyberSec 1537 1568 = _
      dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkPubTerm]; rw [o6]; exact hslice
  have hs0 : secretBytes (keepOpkRecordsI0 w) 0 = w.aliceId := by
    rw [secretBytes, hR]; simp [keepOpkRecordsI0, PQXDHSpqrSetup.fresh]
  have hs1 : secretBytes (keepOpkRecordsI0 w) 1 = w.bobId := by
    rw [secretBytes, hR]; simp [keepOpkRecordsI0, PQXDHSpqrSetup.fresh]
  have hs2 : secretBytes (keepOpkRecordsI0 w) 2 = w.spk := by
    rw [secretBytes, hR]; simp [keepOpkRecordsI0, PQXDHSpqrSetup.fresh]
  have hs3 : secretBytes (keepOpkRecordsI0 w) 3 = fillFresh 11 64 := by
    rw [secretBytes, hR]; simp [keepOpkRecordsI0, PQXDHSpqrSetup.fresh]
  have hs4 : secretBytes (keepOpkRecordsI0 w) 4 = fillFresh 16 64 := by
    rw [secretBytes, hR]; simp [keepOpkRecordsI0, PQXDHSpqrSetup.fresh]
  have hs5 : secretBytes (keepOpkRecordsI0 w) 5 = fillFresh 17 64 := by
    rw [secretBytes, hR]; simp [keepOpkRecordsI0, PQXDHSpqrSetup.fresh]
  have hs6 : secretBytes (keepOpkRecordsI0 w) 6 = w.opk := by
    rw [secretBytes, hR]; simp [keepOpkRecordsI0, PQXDHSpqrSetup.fresh, hopk]
  have hopk_fit : (keepOpkRecordsI0 w).withOpk = true ∧ (keepOpkRecordsI0 w).opkId = w.opkId ∧
      secretBytes (keepOpkRecordsI0 w) 6 = w.opk := ⟨rfl, rfl, hs6⟩
  exact ⟨(keepOpkI0, keepOpkHooks0), keepOpkRecordsI0 w,
    ⟨⟨hwf, hopk_fit, rfl, rfl, rfl, rfl, hs0, hs1, hs2, o5, o6, o7, rfl,
      keepOpkI0_cryptoEquationsHold, keepOpkI0_pubCanonical,
      keepOpkI0_kyberCorrectOn (keepOpkRecordsI0 w) w.kyberCts⟩,
     rfl, ⟨hs3, hs4, hs5⟩, ⟨rfl, rfl⟩,
     keepOpkI0_torsionShiftsRejected, fun _ h => nomatch h⟩,
    keepOpkI0_externContractsHoldCli, keepOpkI0_hooksAgree⟩

/-! ## 4. SHA-256 / HMAC / `computeMac` Injectivity & Universal MAC Forgery/Collision Discharge -/

private theorem shaStateOfBytes_head_eq_take4 (bytes : HwBytes) :
    (shaStateOfBytes bytes).head = (shaStateOfBytes (bytes.take 4)).head := by
  rcases bytes with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, bs⟩⟩⟩⟩ <;> rfl

abbrev FK : ShaState → HwBytes → ShaState := sha256CompressFunction keepOpkI0
def OnTabK (s : ShaState) (b : HwBytes) : Prop := (keepOpkSha256 (shaStateBytes s) b).take 4 ≠ compTag4

theorem FK_eq (s : ShaState) (b : HwBytes) :
    FK s b = shaStateOfBytes (keepOpkSha256 (shaStateBytes s) b) := by
  show sha256CompressFunction keepOpkI0 s b = _
  unfold sha256CompressFunction; rw [keepOpkI0_sha256Compress, Option.getD_some]

theorem sha256CompressFunction_keepOpkI0_head (st : ShaState) (blk : HwBytes) :
    (FK st blk).head = (shaStateOfBytes ((keepOpkSha256 (shaStateBytes st) blk).take 4)).head := by
  rw [FK_eq, shaStateOfBytes_head_eq_take4]

theorem keepOpkSha256_row_of_untagged {st blk : HwBytes} (h : (keepOpkSha256 st blk).take 4 ≠ compTag4) :
    st.take 4 ≠ compTag4 ∧ st.length = 32 ∧ blk.length = 64 ∧
      ∃ row ∈ keepOpkSha256Rows, row.1 = bytesToNat st ∧ row.2.1 = bytesToNat blk ∧
        keepOpkSha256 st blk = leBytes 32 row.2.2 := by
  unfold keepOpkSha256 at h ⊢
  by_cases htag : (st.take 4 == compTag4 || blk.take 4 == compTag4 || blk.take 4 == compTag4Ipad || blk.take 4 == compTag4Opad) = true
  · simp only [htag, ↓reduceIte] at h; exact absurd (compDefaultSha256_take4 st blk) h
  · have hst : st.take 4 ≠ compTag4 := fun he => by apply htag; simp [he]
    simp only [htag, ↓reduceIte, Bool.false_eq_true] at h ⊢
    by_cases hlen : (st.length == 32 && blk.length == 64) = true
    · simp only [hlen, ↓reduceIte] at h ⊢; simp only [Bool.and_eq_true, beq_iff_eq] at hlen
      cases hf : List.find? (fun r => r.1 == bytesToNat st && r.2.1 == bytesToNat blk) (keepOpkSha256Bucket (bytesToNat blk % 64)) with
      | none => simp only [hf] at h; exact absurd (compDefaultSha256_take4 st blk) h
      | some row =>
        rcases row with ⟨r1, r2, r3⟩
        have hmem_b := List.mem_of_find?_eq_some hf
        have hmem : (r1, r2, r3) ∈ keepOpkSha256Rows :=
          List.mem_flatMap.mpr ⟨bytesToNat blk % 64, List.mem_range.mpr (Nat.mod_lt _ (by decide)), hmem_b⟩
        have hp := List.find?_some hf; simp only [Bool.and_eq_true, beq_iff_eq] at hp
        exact ⟨hst, hlen.1, hlen.2, ⟨r1, r2, r3⟩, hmem, hp.1, hp.2, rfl⟩
    · simp only [hlen, ↓reduceIte, Bool.false_eq_true] at h; exact absurd (compDefaultSha256_take4 st blk) h

theorem keepOpkSha256_length (st blk : HwBytes) : (keepOpkSha256 st blk).length = 32 := by
  have hd : (compDefaultSha256 st blk).length = 32 := by simp [compDefaultSha256, compTag4, compShaMix28]
  unfold keepOpkSha256
  split
  · exact hd
  · split
    · dsimp only; split
      · exact leBytes_len _ _
      · exact hd
    · exact hd

theorem hstepK : ∀ s b, ¬ OnTabK s b → (FK s b).head = tagW := by
  intro s b h; rw [sha256CompressFunction_keepOpkI0_head, Classical.not_not.mp h, shaStateOfBytes_compTag4_head]

theorem hT1_K : ∀ s b, s.head = tagW → ¬ OnTabK s b := by
  intro s b hs h; apply h; have hst := shaStateBytes_take4_of_head s hs
  unfold keepOpkSha256; simp only [hst, beq_self_eq_true, Bool.true_or, ↓reduceIte]; exact compDefaultSha256_take4 _ _

theorem hT2_K : ∀ s b, b.take 4 = toBEBytes 4 tagW → ¬ OnTabK s b := by
  intro s b hb h; rw [toBEBytes_tagW] at hb; apply h
  unfold keepOpkSha256; simp only [hb, beq_self_eq_true, Bool.true_or, Bool.or_true, ↓reduceIte]; exact compDefaultSha256_take4 _ _

theorem onTabK_of_sha256With_untagged (m : HwBytes) (h : (sha256With FK m).take 4 ≠ compTag4)
    (l₁ : List HwBytes) (b : HwBytes) (l₂ : List HwBytes)
    (hsplit : chunks64 (sha256Pad m) = l₁ ++ b :: l₂) : OnTabK (l₁.foldl FK sha256IV) b := by
  intro hoff; apply h
  rw [sha256With_take4_of_offTable OnTabK tagW FK hstepK hT1_K m l₁ b l₂ hsplit (fun h' => h' hoff), toBEBytes_tagW]

theorem hmacWith_eqK (k m : HwBytes) (hk : k.length ≤ 64) :
    hmacWith FK k m = sha256With FK (kblk k 0x5c ++ sha256With FK (kblk k 0x36 ++ m)) := by
  have hk' : ¬ 64 < k.length := by omega
  simp only [hmacWith, hk', ↓reduceIte, kblk]

theorem hmac_inner_untaggedK (k m : HwBytes) (hk : k.length ≤ 64)
    (h : (hmacWith FK k m).take 4 ≠ compTag4) :
    (sha256With FK (kblk k 0x36 ++ m)).take 4 ≠ compTag4 := by
  intro hin; apply h
  rw [hmacWith_take4_of_inner OnTabK tagW FK hstepK hT1_K hT2_K k m hk (by rw [toBEBytes_tagW]; exact hin), toBEBytes_tagW]

theorem hmac_outer_first_onTabK (k m : HwBytes) (hk : k.length ≤ 64)
    (h : (hmacWith FK k m).take 4 ≠ compTag4) : OnTabK sha256IV (kblk k 0x5c) := by
  rw [hmacWith_eqK k m hk] at h; have hx := kblk_length k 0x5c hk
  exact onTabK_of_sha256With_untagged _ h [] _ (chunks64 (padTail64 (sha256With FK (kblk k 0x36 ++ m))))
    (by rw [sha256Pad_append64 _ _ hx, chunks64_append64 _ _ hx]; rfl)

def low32Bytes (v : HwBytes) : Nat :=
  (v.getD 3 0#8).toNat + 256 * (v.getD 2 0#8).toNat +
    65536 * (v.getD 1 0#8).toNat + 16777216 * (v.getD 0 0#8).toNat

private theorem ext0 (a b c d : BitVec 8) :
    (BitVec.ofNat 32 (a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat)).extractLsb' 0 8 = a := by
  apply BitVec.eq_of_toNat_eq; have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega
private theorem ext8 (a b c d : BitVec 8) :
    (BitVec.ofNat 32 (a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat)).extractLsb' 8 8 = b := by
  apply BitVec.eq_of_toNat_eq; have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega
private theorem ext16 (a b c d : BitVec 8) :
    (BitVec.ofNat 32 (a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat)).extractLsb' 16 8 = c := by
  apply BitVec.eq_of_toNat_eq; have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega
private theorem ext24 (a b c d : BitVec 8) :
    (BitVec.ofNat 32 (a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat)).extractLsb' 24 8 = d := by
  apply BitVec.eq_of_toNat_eq; have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega

theorem low32Bytes_digestOfOut_take8 (o : Nat) :
    low32Bytes ((digestOfOut o).take 8) = o % 4294967296 := by
  let b0 : BitVec 8 := BitVec.ofNat 8 o
  let b1 : BitVec 8 := BitVec.ofNat 8 (o / 256)
  let b2 : BitVec 8 := BitVec.ofNat 8 (o / 256 / 256)
  let b3 : BitVec 8 := BitVec.ofNat 8 (o / 256 / 256 / 256)
  have hle : leBytes 32 o = b0 :: b1 :: b2 :: b3 :: leBytes 28 (o / 256 / 256 / 256 / 256) := rfl
  unfold low32Bytes digestOfOut; rw [hle]
  simp only [shaStateOfBytes, List.Vector.toList_ofFn, List.ofFn_succ, List.ofFn_zero,
    Fin.val_zero, Fin.val_succ, Nat.mul_zero, Nat.zero_add, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.flatMap_cons, toBEBytes, List.cons_append,
    List.nil_append, List.take_succ_cons, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd,
    ext0, ext8, ext16, ext24]
  simp only [b0, b1, b2, b3, BitVec.toNat_ofNat, Nat.div_div_eq_div_mul, Nat.reduceMul]; omega

theorem rows_mod32_nodup : (keepOpkSha256Rows.map fun r => r.2.2 % 4294967296).Nodup := by
  apply nodup_of_natNodup; decide +kernel

theorem rows_out_nodupK : (keepOpkSha256Rows.map fun r => r.2.2).Nodup := by
  have h := rows_mod32_nodup
  have hfun : (fun r : Nat × Nat × Nat => r.2.2 % 4294967296) =
    ((fun x : Nat => x % 4294967296) ∘ fun r : Nat × Nat × Nat => r.2.2) := rfl
  rw [hfun, ← List.map_map] at h; exact List.Nodup.of_map _ h

theorem rows_take8_nodupK : (keepOpkSha256Rows.map fun r => (digestOfOut r.2.2).take 8).Nodup := by
  have h := rows_mod32_nodup
  have hfun : (fun r : Nat × Nat × Nat => r.2.2 % 4294967296) =
    (low32Bytes ∘ fun r : Nat × Nat × Nat => (digestOfOut r.2.2).take 8) := by
    funext r; exact (low32Bytes_digestOfOut_take8 r.2.2).symm
  rw [hfun, ← List.map_map] at h; exact List.Nodup.of_map _ h

theorem rows_out_ltK : (keepOpkSha256Rows.all fun r => decide (r.2.2 < 2 ^ 256)) = true := by
  decide +kernel

theorem rows_ltK : ∀ r ∈ keepOpkSha256Rows, r.2.2 < 2 ^ (8 * 32) := by
  intro r hr; have := List.all_eq_true.mp rows_out_ltK r hr; simpa using this

theorem rows_out_ne_ivK :
    (keepOpkSha256Rows.all fun r => r.2.2 != bytesToNat (shaStateBytes sha256IV)) = true := by
  decide +kernel

theorem rows_out_roundtripK :
    (keepOpkSha256Rows.all fun r => bytesToNat (shaStateBytes (shaStateOfBytes (leBytes 32 r.2.2))) == r.2.2) = true := by
  rw [List.all_eq_true]; intro r hr
  rw [shaStateBytes_shaStateOfBytes _ (leBytes_len 32 _), bytesToNat_leBytes 32 _ (rows_ltK r hr), beq_self_eq_true]

def rowOfTake8K (v : HwBytes) : Option (Nat × Nat × Nat) :=
  keepOpkSha256Rows.find? fun r => (digestOfOut r.2.2).take 8 == v
def rowByOutK (o : Nat) : Option (Nat × Nat × Nat) :=
  keepOpkSha256Rows.find? fun r => r.2.2 == o
def keyOfRow1K (r : Nat × Nat × Nat) : HwBytes :=
  ((leBytes 64 r.2.1).map (· ^^^ (0x5c : BitVec 8))).take 32
def keyOfTake8K (v : HwBytes) : Option HwBytes :=
  match rowOfTake8K v with
  | none => none
  | some r2 => match rowByOutK r2.1 with | none => none | some r1 => if r1.1 = ivNat then some (keyOfRow1K r1) else none

theorem row_stepK {s : ShaState} {b : HwBytes} (h : OnTabK s b) :
    ∃ r ∈ keepOpkSha256Rows, r.1 = bytesToNat (shaStateBytes s) ∧ r.2.1 = bytesToNat b ∧
      FK s b = shaStateOfBytes (leBytes 32 r.2.2) := by
  obtain ⟨_, _, _, r, hr, h1, h2, h3⟩ := keepOpkSha256_row_of_untagged h
  exact ⟨r, hr, h1, h2, by rw [FK_eq, h3]⟩

theorem keyOfTake8_hmacWithK (k m : HwBytes) (hk : k.length = 32)
    (h : (hmacWith FK k m).take 4 ≠ compTag4) :
    keyOfTake8K ((hmacWith FK k m).take 8) = some k := by
  have hk64 : k.length ≤ 64 := by omega
  have hx := kblk_length k 0x5c hk64
  have h1 := hmac_outer_first_onTabK k m hk64 h
  have hil : (sha256With FK (kblk k 0x36 ++ m)).length = 32 := sha256With_length FK _
  rw [hmacWith_eqK k m hk64] at h ⊢
  generalize sha256With FK (kblk k 0x36 ++ m) = inner at h hil ⊢
  have hch : chunks64 (sha256Pad (kblk k 0x5c ++ inner)) = [kblk k 0x5c] ++ padTail64 inner :: [] := by
    rw [sha256Pad_append64 _ _ hx, chunks64_append64 _ _ hx, chunks64_padTail64_32 inner hil]; rfl
  have h2' : OnTabK ([kblk k 0x5c].foldl FK sha256IV) (padTail64 inner) :=
    onTabK_of_sha256With_untagged _ h [kblk k 0x5c] (padTail64 inner) [] hch
  rw [List.foldl_cons, List.foldl_nil] at h2'
  obtain ⟨r1, hr1, hr1a, hr1b, hF1⟩ := row_stepK h1
  obtain ⟨r2, hr2, hr2a, _, hF2⟩ := row_stepK h2'
  have hsha : sha256With FK (kblk k 0x5c ++ inner) = digestOfOut r2.2.2 := by
    unfold sha256With digestOfOut; rw [hch, List.singleton_append, List.foldl_cons, List.foldl_cons, List.foldl_nil, hF2]
  have hr2r1 : r2.1 = r1.2.2 := by
    rw [hr2a, hF1]; exact beq_iff_eq.mp (List.all_eq_true.mp rows_out_roundtripK r1 hr1)
  have hblk : leBytes 64 r1.2.1 = kblk k 0x5c := by
    have hrt := leBytes_bytesToNat (kblk k 0x5c); rw [hx] at hrt; rw [hr1b, hrt]
  have hfind2 : rowOfTake8K ((digestOfOut r2.2.2).take 8) = some r2 :=
    find?_eq_some_of_nodup keepOpkSha256Rows (fun r => (digestOfOut r.2.2).take 8) _ rows_take8_nodupK r2 hr2 rfl
  have hfind1 : rowByOutK r2.1 = some r1 :=
    find?_eq_some_of_nodup keepOpkSha256Rows (fun r => r.2.2) r2.1 rows_out_nodupK r1 hr1 hr2r1.symm
  have hiv : r1.1 = ivNat := hr1a
  have hkey : keyOfRow1K r1 = k := by
    unfold keyOfRow1K; rw [hblk, kblk, map_xor_xor, hk]; exact List.take_left' hk
  rw [hsha]; unfold keyOfTake8K; simp only [hfind2, hfind1, hiv, ↓reduceIte, hkey]

theorem keepOpkSha256_inj_of_untagged {st₁ blk₁ st₂ blk₂ : HwBytes}
    (h₁ : (keepOpkSha256 st₁ blk₁).take 4 ≠ compTag4)
    (heq : keepOpkSha256 st₁ blk₁ = keepOpkSha256 st₂ blk₂) : st₁ = st₂ ∧ blk₁ = blk₂ := by
  have h₂ : (keepOpkSha256 st₂ blk₂).take 4 ≠ compTag4 := heq ▸ h₁
  obtain ⟨-, hs₁, hb₁, row₁, hm₁, hr₁s, hr₁b, he₁⟩ := keepOpkSha256_row_of_untagged h₁
  obtain ⟨-, hs₂, hb₂, row₂, hm₂, hr₂s, hr₂b, he₂⟩ := keepOpkSha256_row_of_untagged h₂
  have hout : row₁.2.2 = row₂.2.2 := by
    have hle : leBytes 32 row₁.2.2 = leBytes 32 row₂.2.2 := by rw [← he₁, ← he₂, heq]
    rw [← bytesToNat_leBytes 32 _ (rows_ltK row₁ hm₁), ← bytesToNat_leBytes 32 _ (rows_ltK row₂ hm₂), hle]
  have hrow : row₁ = row₂ := List.inj_on_of_nodup_map rows_out_nodupK hm₁ hm₂ hout; subst hrow
  refine ⟨eq_of_bytesToNat_eq (by rw [hs₁, hs₂]) (by rw [← hr₁s, hr₂s]),
          eq_of_bytesToNat_eq (by rw [hb₁, hb₂]) (by rw [← hr₁b, hr₂b])⟩

theorem FK_inj_of_untagged {s₁ s₂ : ShaState} {b₁ b₂ : HwBytes}
    (h₁ : OnTabK s₁ b₁) (heq : FK s₁ b₁ = FK s₂ b₂) : s₁ = s₂ ∧ b₁ = b₂ := by
  rw [FK_eq, FK_eq] at heq; have hc := congrArg shaStateBytes heq
  rw [shaStateBytes_shaStateOfBytes _ (keepOpkSha256_length _ _),
      shaStateBytes_shaStateOfBytes _ (keepOpkSha256_length _ _)] at hc
  obtain ⟨hs, hb⟩ := keepOpkSha256_inj_of_untagged h₁ hc
  refine ⟨?_, hb⟩; rw [← shaStateOfBytes_shaStateBytes' s₁, ← shaStateOfBytes_shaStateBytes' s₂, hs]

theorem FK_ne_iv {s : ShaState} {b : HwBytes} (h : OnTabK s b) : FK s b ≠ sha256IV := by
  intro hiv; obtain ⟨r, hr, -, -, hF⟩ := row_stepK h
  have h1 := congrArg (fun t => bytesToNat (shaStateBytes t)) (hF.symm.trans hiv)
  rw [shaStateBytes_shaStateOfBytes _ (leBytes_len 32 _), bytesToNat_leBytes 32 _ (rows_ltK r hr)] at h1
  have := List.all_eq_true.mp rows_out_ne_ivK r hr; simp [h1] at this

def AllUntaggedK (L : List HwBytes) : Prop :=
  ∀ l₁ b l₂, L = l₁ ++ b :: l₂ → OnTabK (l₁.foldl FK sha256IV) b

theorem AllUntaggedK.dropLast {L : List HwBytes} {a : HwBytes} (h : AllUntaggedK (L ++ [a])) : AllUntaggedK L :=
  fun l₁ b l₂ hL => h l₁ b (l₂ ++ [a]) (by rw [hL]; simp)
theorem AllUntaggedK.last {L : List HwBytes} {a : HwBytes} (h : AllUntaggedK (L ++ [a])) : OnTabK (L.foldl FK sha256IV) a :=
  h L a [] rfl

theorem fold_inj_auxK : ∀ (n : Nat) (A B : List HwBytes),
    A.length ≤ n → AllUntaggedK A → AllUntaggedK B → A.foldl FK sha256IV = B.foldl FK sha256IV → A = B := by
  intro n; induction n with
  | zero =>
    intro A B hn _ hB heq; have hA : A = [] := List.eq_nil_of_length_eq_zero (by omega); subst hA
    rcases eq_nil_or_snoc B with rfl | ⟨B', b, rfl⟩
    · rfl
    · exfalso; simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at heq; exact FK_ne_iv hB.last heq.symm
  | succ n ih =>
    intro A B hn hA hB heq
    rcases eq_nil_or_snoc A with rfl | ⟨A', a, rfl⟩
    · rcases eq_nil_or_snoc B with rfl | ⟨B', b, rfl⟩
      · rfl
      · exfalso; simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at heq; exact FK_ne_iv hB.last heq.symm
    · rcases eq_nil_or_snoc B with rfl | ⟨B', b, rfl⟩
      · exfalso; simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at heq; exact FK_ne_iv hA.last heq
      · simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at heq
        obtain ⟨hs, hb⟩ := FK_inj_of_untagged hA.last heq
        have hlen : A'.length ≤ n := by simp at hn; omega
        rw [ih A' B' hlen hA.dropLast hB.dropLast hs, hb]

theorem sha256With_inj_of_untaggedK {m₁ m₂ : HwBytes}
    (h₁ : (sha256With FK m₁).take 4 ≠ compTag4)
    (heq : sha256With FK m₁ = sha256With FK m₂) : m₁ = m₂ := by
  have ha₁ : AllUntaggedK (chunks64 (sha256Pad m₁)) := fun l₁ b l₂ hs => onTabK_of_sha256With_untagged m₁ h₁ l₁ b l₂ hs
  have ha₂ : AllUntaggedK (chunks64 (sha256Pad m₂)) := fun l₁ b l₂ hs => onTabK_of_sha256With_untagged m₂ (heq ▸ h₁) l₁ b l₂ hs
  unfold sha256With at heq
  have hc := fold_inj_auxK _ _ _ (Nat.le_refl _) ha₁ ha₂ (digest_inj heq)
  exact sha256Pad_inj (chunks64_inj (sha256Pad_length_mod m₁) (sha256Pad_length_mod m₂) hc)

def normKeyK (k : HwBytes) : HwBytes := if 64 < k.length then sha256With FK k else k

theorem normKeyK_length_le (k : HwBytes) : (normKeyK k).length ≤ 64 := by
  unfold normKeyK; split
  · rw [sha256With_length]; omega
  · omega

theorem hmacWith_eq_normKeyK (k m : HwBytes) : hmacWith FK k m = hmacWith FK (normKeyK k) m := by
  unfold normKeyK; split
  · rename_i h; have hle : ¬ 64 < (sha256With FK k).length := by rw [sha256With_length]; omega
    simp only [hmacWith, h, hle, ↓reduceIte]
  · rfl

private theorem kblk_36_of_5c (k₁ k₂ : HwBytes) (h : kblk k₁ 0x5c = kblk k₂ 0x5c) :
    kblk k₁ 0x36 = kblk k₂ 0x36 := by
  have hpad : k₁ ++ List.replicate (64 - k₁.length) 0 = k₂ ++ List.replicate (64 - k₂.length) 0 := by
    have h' := congrArg (List.map (· ^^^ (0x5c : BitVec 8))) h
    simpa only [kblk, map_xor_xor] using h'
  unfold kblk; rw [hpad]

theorem hmacWith_msg_inj_of_untaggedK {k₁ k₂ m₁ m₂ : HwBytes}
    (h₁ : (hmacWith FK k₁ m₁).take 4 ≠ compTag4)
    (heq : hmacWith FK k₁ m₁ = hmacWith FK k₂ m₂) : m₁ = m₂ := by
  rw [hmacWith_eq_normKeyK k₁ m₁] at h₁ heq
  rw [hmacWith_eq_normKeyK k₂ m₂] at heq
  have hk₁ := normKeyK_length_le k₁
  have hk₂ := normKeyK_length_le k₂
  have hin₁ := hmac_inner_untaggedK _ m₁ hk₁ h₁
  rw [hmacWith_eqK _ m₁ hk₁] at h₁ heq; rw [hmacWith_eqK _ m₂ hk₂] at heq
  have ho := sha256With_inj_of_untaggedK h₁ heq
  obtain ⟨hko, hino⟩ := List.append_inj ho (by rw [kblk_length _ 0x5c hk₁, kblk_length _ 0x5c hk₂])
  have hk36 := kblk_36_of_5c _ _ hko
  have hi := sha256With_inj_of_untaggedK hin₁ hino
  rw [hk36] at hi
  exact List.append_inj_right hi rfl

theorem hmacWith_inj_of_untaggedK {k₁ k₂ m₁ m₂ : HwBytes}
    (hl : k₁.length = k₂.length) (hk : k₁.length ≤ 64)
    (h₁ : (hmacWith FK k₁ m₁).take 4 ≠ compTag4)
    (heq : hmacWith FK k₁ m₁ = hmacWith FK k₂ m₂) : k₁ = k₂ ∧ m₁ = m₂ := by
  have hk₂ : k₂.length ≤ 64 := hl ▸ hk
  have hm := hmacWith_msg_inj_of_untaggedK h₁ heq
  rw [hmacWith_eqK k₁ m₁ hk] at h₁ heq; rw [hmacWith_eqK k₂ m₂ hk₂] at heq
  have ho := sha256With_inj_of_untaggedK h₁ heq
  obtain ⟨hko, -⟩ := List.append_inj ho (by rw [kblk_length _ 0x5c hk, kblk_length _ 0x5c hk₂])
  exact ⟨kblk_inj 0x5c hl hko, hm⟩

def keepOpkHmacKeys32 : List HwBytes :=
  keepOpkSha256Rows.filterMap fun r =>
    if r.1 = ivNat then
      if ((leBytes 64 r.2.1).map (· ^^^ (0x5c : BitVec 8))).drop 32 = List.replicate 32 0 then
        some (((leBytes 64 r.2.1).map (· ^^^ (0x5c : BitVec 8))).take 32)
      else none
    else none

theorem keepOpkHmacKeys32_untagged : (keepOpkHmacKeys32.all fun k => k.take 4 != compTag4) = true := by
  decide +kernel

theorem keyOfRow1K_untagged {r1 : Nat × Nat × Nat} (hr1 : r1 ∈ keepOpkSha256Rows)
    (hiv : r1.1 = ivNat) (hk : ((leBytes 64 r1.2.1).map (· ^^^ (0x5c : BitVec 8))).drop 32 = List.replicate 32 0) :
    (keyOfRow1K r1).take 4 ≠ compTag4 := by
  have hmem : keyOfRow1K r1 ∈ keepOpkHmacKeys32 := by
    unfold keepOpkHmacKeys32 keyOfRow1K; rw [List.mem_filterMap]
    exact ⟨r1, hr1, by simp only [hiv, hk, ↓reduceIte]⟩
  have h := List.all_eq_true.mp keepOpkHmacKeys32_untagged _ hmem
  simpa [bne_iff_ne] using h

theorem hmacWith_key_untagged_of_untaggedK {k m : HwBytes} (hk : k.length = 32)
    (h : (hmacWith FK k m).take 4 ≠ compTag4) : k.take 4 ≠ compTag4 := by
  have hx := kblk_length k 0x5c (by omega)
  obtain ⟨_, _, _, row, hrow, h1, h2, _⟩ := keepOpkSha256_row_of_untagged (hmac_outer_first_onTabK k m (by omega) h)
  have hrt := leBytes_bytesToNat (kblk k 0x5c); rw [hx] at hrt
  have hblk : leBytes 64 row.2.1 = kblk k 0x5c := by rw [h2, hrt]
  have hk0 : (leBytes 64 row.2.1).map (· ^^^ (0x5c : BitVec 8)) = k ++ List.replicate 32 0 := by
    rw [hblk, kblk, map_xor_xor, hk]
  have hdrop : ((leBytes 64 row.2.1).map (· ^^^ (0x5c : BitVec 8))).drop 32 = List.replicate 32 0 := by
    rw [hk0, List.drop_left' hk]
  have hkey : keyOfRow1K row = k := by unfold keyOfRow1K; rw [hk0, List.take_left' hk]
  rw [← hkey]; exact keyOfRow1K_untagged hrow h1 hdrop

theorem gamma_hmacK (S : OpaqueSymbolSemantics) (g : Ghost) (k m : DY.Bytes) :
    gamma keepOpkI0 S g (hmac k m) = hmacWith FK (gamma keepOpkI0 S g k) (gamma keepOpkI0 S g m) := by
  unfold gamma
  rw [show hmac k m = ({ salt := k, ikm := m } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack from rfl,
      ms_pack_kdf keepOpkI0 S g ⟨k, m⟩]
  rfl

theorem gamma_hmacK_length (S : OpaqueSymbolSemantics) (g : Ghost) (k m : DY.Bytes) :
    (gamma keepOpkI0 S g (hmac k m)).length = 32 := by
  rw [gamma_hmacK]; unfold hmacWith; split <;> exact sha256With_length FK _

theorem gamma_concatK (S : OpaqueSymbolSemantics) (g : Ghost) (a b : DY.Bytes) :
    gamma keepOpkI0 S g (DY.Concat.concat a b) = gamma keepOpkI0 S g a ++ gamma keepOpkI0 S g b := by
  unfold gamma
  rw [show DY.Concat.concat a b = ({ lhs := a, rhs := b } : DY.Concat.Concat.SubF DY.Bytes).pack from rfl,
      ms_pack_concat keepOpkI0 S g ⟨a, b⟩]
  rfl

theorem gamma_trunc8K (S : OpaqueSymbolSemantics) (g : Ghost) (x : DY.Bytes) :
    gamma keepOpkI0 S g (DY.Trunc.trunc8 x) = (gamma keepOpkI0 S g x).take 8 := by
  unfold gamma
  rw [show DY.Trunc.trunc8 x = ({ input := x } : DY.Trunc.Trunc8.SubF DY.Bytes).pack from rfl,
      ms_pack_trunc keepOpkI0 S g ⟨x⟩]
  rfl

theorem gamma_computeMacK (S : OpaqueSymbolSemantics) (g : Ghost) (mk sIk rIk w : DY.Bytes) :
    gamma keepOpkI0 S g (computeMac mk sIk rIk w) =
      (hmacWith FK (gamma keepOpkI0 S g mk)
        (gamma keepOpkI0 S g sIk ++ (gamma keepOpkI0 S g rIk ++ gamma keepOpkI0 S g w))).take 8 := by
  unfold computeMac; rw [gamma_trunc8K, gamma_hmacK, gamma_concatK, gamma_concatK]

theorem spqrKeyBytes_length (v : HwBytes) : (spqrKeyBytes v).length = 32 := by
  unfold spqrKeyBytes; simp

theorem gamma_spqrSendKey_length (S : OpaqueSymbolSemantics) (g : Ghost) (st c : DY.Bytes) :
    (gamma keepOpkI0 S g (({ st := st, coins := c } : DY.Spqr.SendKey.SubF DY.Bytes).pack)).length = 32 := by
  unfold gamma gamma'
  rw [DY.Bytes.rec_eq (gSpqrSendKey S) (gAll keepOpkI0 S g)]
  exact spqrKeyBytes_length _

theorem gamma_spqrRecvKey_length (S : OpaqueSymbolSemantics) (g : Ghost) (st m : DY.Bytes) :
    (gamma keepOpkI0 S g (({ st := st, msg := m } : DY.Spqr.RecvKey.SubF DY.Bytes).pack)).length = 32 := by
  unfold gamma gamma'
  rw [DY.Bytes.rec_eq (gSpqrRecvKey S) (gAll keepOpkI0 S g)]
  exact spqrKeyBytes_length _

theorem gamma_trMsgKeys_congr_prk {S₁ S₂ : OpaqueSymbolSemantics} {g₁ g₂ : Ghost}
    {salt₁ seed₁ salt₂ seed₂ : DY.Bytes}
    (hprk : gamma keepOpkI0 S₁ g₁ (hmac salt₁ seed₁) = gamma keepOpkI0 S₂ g₂ (hmac salt₂ seed₂)) :
    gamma keepOpkI0 S₁ g₁ (trMsgKeys salt₁ seed₁).cipherKey = gamma keepOpkI0 S₂ g₂ (trMsgKeys salt₂ seed₂).cipherKey ∧
    gamma keepOpkI0 S₁ g₁ (trMsgKeys salt₁ seed₁).macKey = gamma keepOpkI0 S₂ g₂ (trMsgKeys salt₂ seed₂).macKey ∧
    gamma keepOpkI0 S₁ g₁ (trMsgKeys salt₁ seed₁).iv = gamma keepOpkI0 S₂ g₂ (trMsgKeys salt₂ seed₂).iv := by
  have hlit : ∀ s, gamma keepOpkI0 S₁ g₁ (DY.Libsignal.TripleRatchet.lit s) = gamma keepOpkI0 S₂ g₂ (DY.Libsignal.TripleRatchet.lit s) := fun s => by
    unfold gamma DY.Libsignal.TripleRatchet.lit
    rw [show DY.Literal.literalToBytes s.toUTF8 = ({ lit := s.toUTF8 } : DY.Literal.Literal.SubF DY.Bytes).pack from rfl,
        ms_pack_lit keepOpkI0 S₁ g₁ ⟨s.toUTF8⟩, ms_pack_lit keepOpkI0 S₂ g₂ ⟨s.toUTF8⟩]
    rfl
  have hlb : ∀ b, gamma keepOpkI0 S₁ g₁ (DY.Libsignal.TripleRatchet.litByte b) = gamma keepOpkI0 S₂ g₂ (DY.Libsignal.TripleRatchet.litByte b) := fun b => by
    unfold gamma DY.Libsignal.TripleRatchet.litByte
    rw [show DY.Literal.literalToBytes ⟨#[b]⟩ = ({ lit := ⟨#[b]⟩ } : DY.Literal.Literal.SubF DY.Bytes).pack from rfl,
        ms_pack_lit keepOpkI0 S₁ g₁ ⟨⟨#[b]⟩⟩, ms_pack_lit keepOpkI0 S₂ g₂ ⟨⟨#[b]⟩⟩]
    rfl
  have hb1 : gamma keepOpkI0 S₁ g₁ (hkdfBlock1 (hmac salt₁ seed₁) (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")) =
             gamma keepOpkI0 S₂ g₂ (hkdfBlock1 (hmac salt₂ seed₂) (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")) := by
    unfold hkdfBlock1
    rw [gamma_hmacK S₁ g₁, gamma_hmacK S₂ g₂]
    simp only [gamma_concatK, hprk, hlit, hlb]
  have hb2 : gamma keepOpkI0 S₁ g₁ (hkdfBlock2 (hmac salt₁ seed₁) (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")) =
             gamma keepOpkI0 S₂ g₂ (hkdfBlock2 (hmac salt₂ seed₂) (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")) := by
    unfold hkdfBlock2
    rw [gamma_hmacK S₁ g₁, gamma_hmacK S₂ g₂]
    simp only [gamma_concatK, hprk, hb1, hlit, hlb]
  have hb3 : gamma keepOpkI0 S₁ g₁ (hkdfBlock3 (hmac salt₁ seed₁) (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")) =
             gamma keepOpkI0 S₂ g₂ (hkdfBlock3 (hmac salt₂ seed₂) (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")) := by
    unfold hkdfBlock3
    rw [gamma_hmacK S₁ g₁, gamma_hmacK S₂ g₂]
    simp only [gamma_concatK, hprk, hb2, hlit, hlb]
  exact ⟨hb1, hb2, hb3⟩

theorem computeMac_pins_macKey_prk_seed
    {S₁ S₂ : OpaqueSymbolSemantics} {g₁ g₂ : Ghost}
    {salt₁ seed₁ a₁ b₁ w₁ salt₂ seed₂ a₂ b₂ w₂ : DY.Bytes}
    (huntag : (gamma keepOpkI0 S₁ g₁ (computeMac (trMsgKeys salt₁ seed₁).macKey a₁ b₁ w₁)).take 4 ≠ compTag4)
    (heq : gamma keepOpkI0 S₁ g₁ (computeMac (trMsgKeys salt₁ seed₁).macKey a₁ b₁ w₁) =
           gamma keepOpkI0 S₂ g₂ (computeMac (trMsgKeys salt₂ seed₂).macKey a₂ b₂ w₂)) :
    gamma keepOpkI0 S₁ g₁ (trMsgKeys salt₁ seed₁).macKey = gamma keepOpkI0 S₂ g₂ (trMsgKeys salt₂ seed₂).macKey ∧
    gamma keepOpkI0 S₁ g₁ (hmac salt₁ seed₁) = gamma keepOpkI0 S₂ g₂ (hmac salt₂ seed₂) ∧
    gamma keepOpkI0 S₁ g₁ seed₁ = gamma keepOpkI0 S₂ g₂ seed₂ := by
  have hlen1 : (gamma keepOpkI0 S₁ g₁ (trMsgKeys salt₁ seed₁).macKey).length = 32 := gamma_hmacK_length _ _ _ _
  have hlen2 : (gamma keepOpkI0 S₂ g₂ (trMsgKeys salt₂ seed₂).macKey).length = 32 := gamma_hmacK_length _ _ _ _
  have huntag2 : (gamma keepOpkI0 S₂ g₂ (computeMac (trMsgKeys salt₂ seed₂).macKey a₂ b₂ w₂)).take 4 ≠ compTag4 := heq ▸ huntag
  rw [gamma_computeMacK] at huntag; rw [gamma_computeMacK] at huntag2
  rw [List.take_take, show min 4 8 = 4 by decide] at huntag huntag2
  have hk1 := keyOfTake8_hmacWithK _ _ hlen1 huntag
  have hk2 := keyOfTake8_hmacWithK _ _ hlen2 huntag2
  have ht8 := heq
  simp only [gamma_computeMacK] at ht8
  rw [ht8, hk2] at hk1; injection hk1 with hmk_rev
  have hmk := hmk_rev.symm
  have hmk_untag : (gamma keepOpkI0 S₁ g₁ (trMsgKeys salt₁ seed₁).macKey).take 4 ≠ compTag4 :=
    hmacWith_key_untagged_of_untaggedK hlen1 huntag
  have hprk_len1 : (gamma keepOpkI0 S₁ g₁ (hmac salt₁ seed₁)).length = 32 := gamma_hmacK_length _ _ _ _
  have hprk_len2 : (gamma keepOpkI0 S₂ g₂ (hmac salt₂ seed₂)).length = 32 := gamma_hmacK_length _ _ _ _
  have hmk_unfold1 : gamma keepOpkI0 S₁ g₁ (trMsgKeys salt₁ seed₁).macKey =
      hmacWith FK (gamma keepOpkI0 S₁ g₁ (hmac salt₁ seed₁))
        (gamma keepOpkI0 S₁ g₁ (DY.Concat.concat (hkdfBlock1 (hmac salt₁ seed₁) (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys"))
          (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") (DY.Libsignal.TripleRatchet.litByte 2)))) :=
    gamma_hmacK _ _ _ _
  have hmk_unfold2 : gamma keepOpkI0 S₂ g₂ (trMsgKeys salt₂ seed₂).macKey =
      hmacWith FK (gamma keepOpkI0 S₂ g₂ (hmac salt₂ seed₂))
        (gamma keepOpkI0 S₂ g₂ (DY.Concat.concat (hkdfBlock1 (hmac salt₂ seed₂) (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys"))
          (DY.Concat.concat (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") (DY.Libsignal.TripleRatchet.litByte 2)))) :=
    gamma_hmacK _ _ _ _
  have hmk' := hmk
  rw [hmk_unfold1, hmk_unfold2] at hmk'
  have hprk_inj := @hmacWith_inj_of_untaggedK
    (gamma keepOpkI0 S₁ g₁ (hmac salt₁ seed₁))
    (gamma keepOpkI0 S₂ g₂ (hmac salt₂ seed₂)) _ _
    (by rw [hprk_len1, hprk_len2]) (by omega) (hmk_unfold1 ▸ hmk_untag) hmk'
  have hprk := hprk_inj.1
  have hprk_untag : (gamma keepOpkI0 S₁ g₁ (hmac salt₁ seed₁)).take 4 ≠ compTag4 :=
    hmacWith_key_untagged_of_untaggedK hprk_len1 (hmk_unfold1 ▸ hmk_untag)
  have hprk' := hprk
  rw [gamma_hmacK S₁ g₁ salt₁ seed₁, gamma_hmacK S₂ g₂ salt₂ seed₂] at hprk'
  have hseed := hmacWith_msg_inj_of_untaggedK
    (gamma_hmacK S₁ g₁ salt₁ seed₁ ▸ hprk_untag) hprk'
  exact ⟨hmk, hprk, hseed⟩

theorem computeMac_pins_salt_and_seed
    {S₁ S₂ : OpaqueSymbolSemantics} {g₁ g₂ : Ghost}
    {salt₁ seed₁ a₁ b₁ w₁ salt₂ seed₂ a₂ b₂ w₂ : DY.Bytes}
    (hs₁ : (gamma keepOpkI0 S₁ g₁ salt₁).length = 32)
    (hs₂ : (gamma keepOpkI0 S₂ g₂ salt₂).length = 32)
    (huntag : (gamma keepOpkI0 S₁ g₁ (computeMac (trMsgKeys salt₁ seed₁).macKey a₁ b₁ w₁)).take 4 ≠ compTag4)
    (heq : gamma keepOpkI0 S₁ g₁ (computeMac (trMsgKeys salt₁ seed₁).macKey a₁ b₁ w₁) =
           gamma keepOpkI0 S₂ g₂ (computeMac (trMsgKeys salt₂ seed₂).macKey a₂ b₂ w₂)) :
    gamma keepOpkI0 S₁ g₁ salt₁ = gamma keepOpkI0 S₂ g₂ salt₂ ∧
    gamma keepOpkI0 S₁ g₁ seed₁ = gamma keepOpkI0 S₂ g₂ seed₂ := by
  obtain ⟨hmk, hprk, hseed⟩ := computeMac_pins_macKey_prk_seed huntag heq
  have hlen1 : (gamma keepOpkI0 S₁ g₁ (trMsgKeys salt₁ seed₁).macKey).length = 32 := gamma_hmacK_length _ _ _ _
  have huntag' : (hmacWith FK (gamma keepOpkI0 S₁ g₁ (trMsgKeys salt₁ seed₁).macKey)
      (gamma keepOpkI0 S₁ g₁ a₁ ++ (gamma keepOpkI0 S₁ g₁ b₁ ++ gamma keepOpkI0 S₁ g₁ w₁))).take 4 ≠ compTag4 := by
    rw [gamma_computeMacK, List.take_take, show min 4 8 = 4 by decide] at huntag; exact huntag
  have hmk_untag := hmacWith_key_untagged_of_untaggedK hlen1 huntag'
  have hprk_untag := hmacWith_key_untagged_of_untaggedK (gamma_hmacK_length _ _ _ _)
    (gamma_hmacK S₁ g₁ (hmac salt₁ seed₁) _ ▸ hmk_untag)
  have hprk' := hprk
  rw [gamma_hmacK S₁ g₁ salt₁ seed₁, gamma_hmacK S₂ g₂ salt₂ seed₂] at hprk'
  have hsalt := (@hmacWith_inj_of_untaggedK
    (gamma keepOpkI0 S₁ g₁ salt₁) (gamma keepOpkI0 S₂ g₂ salt₂)
    (gamma keepOpkI0 S₁ g₁ seed₁) (gamma keepOpkI0 S₂ g₂ seed₂)
    (by rw [hs₁, hs₂]) (by omega)
    (gamma_hmacK S₁ g₁ salt₁ seed₁ ▸ hprk_untag) hprk').1
  exact ⟨hsalt, hseed⟩

theorem not_macTagForgeryOrCollision_of_honest_mac
    {S : OpaqueSymbolSemantics} {g : Ghost} {known : DY.Bytes → Prop} {honest : List DY.Bytes}
    {msg : TRSignalMsg} {ctxs : List TrialCtx} {salt_h seed_h a_h b_h w_h : DY.Bytes}
    (hmem : salt_h ∈ honest)
    (hmac_eq : gamma keepOpkI0 S g msg.mac =
               gamma keepOpkI0 S g (computeMac (trMsgKeys salt_h seed_h).macKey a_h b_h w_h))
    (huntag : (gamma keepOpkI0 S g msg.mac).take 4 ≠ compTag4) :
    ¬ MacTagForgeryOrCollision keepOpkI0 S g known honest msg ctxs := by
  rintro (⟨ctx, _, seed, _, k_own, _, hmac1, _, hne⟩ |
          ⟨ctx, _, seed, _, k_own, _, hmac1, ctx₀, _, seed₀, _, hseed_ne, hcol⟩)
  · obtain ⟨-, hprk, hseed⟩ := computeMac_pins_macKey_prk_seed (hmac1.symm ▸ huntag) (hmac1.trans hmac_eq)
    have hprk' : gamma keepOpkI0 S g (hmac salt_h seed) = gamma keepOpkI0 S g (hmac k_own seed) := by
      rw [gamma_hmacK, hseed, ← gamma_hmacK, hprk.symm]
    obtain ⟨hc, hm, hiv⟩ := gamma_trMsgKeys_congr_prk hprk'
    exact hne salt_h hmem (Prod.ext hc (Prod.ext hm hiv))
  · rcases hcol with ⟨salt₀, _, hmac0⟩ | ⟨pIk₀, mIk₀, salt₀, w₀, hmsg_eq, _⟩
    · obtain ⟨-, -, hseed⟩ := computeMac_pins_macKey_prk_seed (hmac1.symm ▸ huntag) (hmac1.trans hmac0.symm)
      exact hseed_ne hseed
    · have hmac0 : gamma keepOpkI0 S g (computeMac (trMsgKeys salt₀ seed₀).macKey pIk₀ mIk₀ w₀) =
          gamma keepOpkI0 S g msg.mac := by rw [hmsg_eq]
      obtain ⟨-, -, hseed⟩ := computeMac_pins_macKey_prk_seed (hmac1.symm ▸ huntag) (hmac1.trans hmac0.symm)
      exact hseed_ne hseed

end Symbolic.BugInjection.Proofs.SyntheticKeepOpk.I0Laws
