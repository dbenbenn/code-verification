/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003
public import Symbolic.BugInjection.Proofs.Common.CompFitsPin
public import Symbolic.BugInjection.Proofs.Common443.CompRTag
public import Symbolic.Specifications.Refinement.ElfBinding
public import Symbolic.Proofs.SpecLemmas.ByteSpecs

/-!
# Algebraic Laws, Hook Agreement, and Unconditional SHA-256/HMAC Injectivity for `compI7003`

Proves `ExternContractsHoldCli compI7003`, `HooksMatchInterpretation compI7003 compHooks7003`,
`compI7003_kyberCorrectOn`, `not_kyberMismatch_compI7003`, and unconditional untagged
`sha256With`/`hmacWith` 8-byte truncation injectivity (`hmacWith_take8_inj_of_untagged`) for the
table-driven interpretation `compI7003`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003Laws

open ByteSpecs
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003
open Symbolic.BugInjection.Proofs.Common443.CompRTag
open CryptoProofLib.Refinement (ExternInterpretation ByteString)
open DY.X25519 (isLowOrderKey lowOrderUs uCoord leValue p25519)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (StubSymbol x25519PublicKeySymbol x25519AgreementSymbol
  x25519TorsionSymbol torsionShift aesCbcEncryptSymbol aesCbcDecryptSymbol
  sha256CompressSymbol sha256CompressFunction shaStateBytes shaStateOfBytes ExternCryptoLawsHold)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol kyberDecapsSymbol sha512CompressSymbol
  mlkem768FromSeedSymbol mlkem768Encaps1Symbol
  mlkem768Encaps2Symbol mlkem768DecapsSymbol mlkem768ValidatePkSymbol libcruxHmacSymbol
  X25519TorsionShiftsRejected)
open DY.Libsignal.Composed.Refinement (ProtocolSetup PreKeyFields KyberMismatch leBytes
  X25519PubCanonical)
open DY.Libsignal.Composed.Refinement.Cli (HooksMatchInterpretation ExternContractsHoldCli)
open CryptoVerification.SignalSession (CliHooks)

/-! ## 1. Basic Symbol Unfoldings -/

@[simp]
theorem leBytes_length (n v : Nat) : (leBytes n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [leBytes, ih (v / 256)]

theorem compI7003_publicKey (sk : HwBytes) :
    compI7003 x25519PublicKeySymbol [sk] = some (compLookupPub sk) := rfl

theorem compI7003_agreement (sk pk : HwBytes) :
    compI7003 x25519AgreementSymbol [sk, pk] = some (compLookupDh sk pk) := rfl

theorem compI7003_torsion (pt : HwBytes) (b : BitVec 8) :
    compI7003 x25519TorsionSymbol [pt, [b]] = compLookupTorsion pt b := rfl

theorem compI7003_aesEncrypt (text k iv : HwBytes) :
    compI7003 aesCbcEncryptSymbol [text, k, iv] = some (compAesPerm k iv text) := rfl

theorem compI7003_aesDecrypt (text k iv : HwBytes) :
    compI7003 aesCbcDecryptSymbol [text, k, iv] = compAesDec k iv text := rfl

theorem compI7003_kyberEncaps (pk e : HwBytes) :
    compI7003 kyberEncapsSymbol [pk, e] = some (compKyberEncaps e) := rfl

theorem compI7003_kyberDecaps (sk ct : HwBytes) :
    compI7003 kyberDecapsSymbol [sk, ct] = some (compKyberDecaps ct) := rfl

theorem compI7003_hmac (k d : HwBytes) :
    compI7003 libcruxHmacSymbol [k, d] = some (compDefaultHmac k d) := rfl

theorem compI7003_sha256Compress (st blk : HwBytes) :
    compI7003 sha256CompressSymbol [st, blk] = some (compSha256 st blk) := rfl

/-! ## 2. X25519 & Torsion Laws -/

theorem compPubOfOpt_length (o : Option (Fin 6)) : (compPubOfOpt o).length = 32 := by
  cases o with
  | none => decide
  | some i => revert i; decide

theorem compPubOfOpt_lt_p25519 (o : Option (Fin 6)) :
    leValue ((compPubOfOpt o).map BitVec.toNat) < p25519 := by
  cases o with
  | none => decide
  | some i => revert i; decide

theorem compPubOfOpt_not_lowOrder (o : Option (Fin 6)) :
    isLowOrderKey ((compPubOfOpt o).map BitVec.toNat) = false := by
  cases o with
  | none => decide
  | some i => revert i; decide

theorem compPointIdx_compPubOfOpt (o : Option (Fin 6)) : compPointIdx (compPubOfOpt o) = o := by
  cases o with
  | none => decide
  | some i => revert i; decide

theorem compDhByIdx_comm : ∀ i j : Fin 6, compDhByIdx i j = compDhByIdx j i := by decide
theorem compDhByIdx_length : ∀ i j : Fin 6, (compDhByIdx i j).length = 32 := by decide
theorem compDhByIdx_ne_zero : ∀ i j : Fin 6, compDhByIdx i j ≠ List.replicate 32 0#8 := by decide
theorem compDefaultDh_length : compDefaultDh.length = 32 := leBytes_length 32 _
theorem compDefaultDh_ne_zero : compDefaultDh ≠ List.replicate 32 0#8 := by decide

theorem compLookupPub_length (s : HwBytes) : (compLookupPub s).length = 32 :=
  compPubOfOpt_length (compSecretIdx s)

theorem compLookupPub_lt_p25519 (s : HwBytes) :
    leValue ((compLookupPub s).map BitVec.toNat) < p25519 :=
  compPubOfOpt_lt_p25519 (compSecretIdx s)

theorem compLookupPub_not_lowOrder (s : HwBytes) :
    isLowOrderKey ((compLookupPub s).map BitVec.toNat) = false :=
  compPubOfOpt_not_lowOrder (compSecretIdx s)

theorem compPointIdx_compLookupPub (s : HwBytes) :
    compPointIdx (compLookupPub s) = compSecretIdx s :=
  compPointIdx_compPubOfOpt (compSecretIdx s)

theorem compLookupDh_comm (a b : HwBytes) :
    compLookupDh a (compLookupPub b) = compLookupDh b (compLookupPub a) := by
  unfold compLookupDh
  rw [compLookupPub_not_lowOrder b, compLookupPub_not_lowOrder a]
  simp only [Bool.false_eq_true, ↓reduceIte, compPointIdx_compLookupPub]
  cases compSecretIdx a <;> cases compSecretIdx b <;> simp [compDhByIdx_comm]

theorem compLookupDh_length (s p : HwBytes) : (compLookupDh s p).length = 32 := by
  unfold compLookupDh
  split
  · simp
  · cases compSecretIdx s <;> cases compPointIdx p <;>
      simp [compDhByIdx_length, compDefaultDh_length]

theorem compLookupDh_ne_zero_of_not_lowOrder (s p : HwBytes)
    (hlo : isLowOrderKey (p.map BitVec.toNat) = false) :
    compLookupDh s p ≠ List.replicate 32 0#8 := by
  unfold compLookupDh; rw [hlo]; simp only [Bool.false_eq_true, ↓reduceIte]
  cases compSecretIdx s <;> cases compPointIdx p
  · exact compDefaultDh_ne_zero
  · exact compDefaultDh_ne_zero
  · exact compDefaultDh_ne_zero
  · next i j => exact compDhByIdx_ne_zero i j

@[simp]
theorem torsionShift_compI7003 (p : HwBytes) (t : Fin 8) :
    torsionShift compI7003 p t = p := by
  unfold torsionShift
  split
  · rfl
  · rw [compI7003_torsion]; rfl

theorem compLookupDh_torsionShift (s p : HwBytes) (t : Fin 8) :
    compLookupDh s (torsionShift compI7003 p t) = compLookupDh s p := by
  rw [torsionShift_compI7003]

/-! ## 3. AES-256-CBC Laws -/

private theorem compAesAB_disjoint :
    [compAesA0, compAesB0, compAesA1, compAesB1,
     compAesA2, compAesB2, compAesA3, compAesB3].Nodup ∧
    [compAesA4, compAesB4, compAesA5, compAesB5].Nodup := by decide

private theorem swapPair_involutive {α : Type} [BEq α] [LawfulBEq α]
    {a b : α} (g : α → α)
    (hab : a ≠ b)
    (hg : ∀ z, z ≠ a → z ≠ b → g z ≠ a ∧ g z ≠ b ∧ g (g z) = z)
    (x : α) :
    (if (if x == a then b else if x == b then a else g x) == a then b
     else if (if x == a then b else if x == b then a else g x) == b then a
     else g (if x == a then b else if x == b then a else g x)) = x := by
  by_cases hxa : x = a
  · subst hxa; simp [beq_false_of_ne hab.symm]
  · by_cases hxb : x = b
    · subst hxb; simp
    · obtain ⟨hga, hgb, hgg⟩ := hg x hxa hxb
      simp [beq_false_of_ne hxa, beq_false_of_ne hxb, beq_false_of_ne hga, beq_false_of_ne hgb, hgg]

private theorem swapChain2_involutive
    {a0 b0 a1 b1 : CryptoGames.CBC.Block}
    (hnd : [a0, b0, a1, b1].Nodup)
    (x : CryptoGames.CBC.Block) :
    let f := fun y =>
      if y == a0 then b0 else if y == b0 then a0
      else if y == a1 then b1 else if y == b1 then a1
      else y
    f (f x) = x := by
  intro f; dsimp only [f]
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  rcases hnd with ⟨⟨h01, h02, h03⟩, ⟨h12, h13⟩, h23, _⟩
  refine swapPair_involutive (fun y => if y == a1 then b1 else if y == b1 then a1 else y)
    h01 (fun z hz0 hzb0 => ⟨?_, ?_, ?_⟩) x
  · by_cases hza1 : z = a1; · subst hza1; simp [Ne.symm h03]
    by_cases hzb1 : z = b1; · subst hzb1; simp [beq_false_of_ne (Ne.symm h23), Ne.symm h02]
    simp [beq_false_of_ne hza1, beq_false_of_ne hzb1, hz0]
  · by_cases hza1 : z = a1; · subst hza1; simp [Ne.symm h13]
    by_cases hzb1 : z = b1; · subst hzb1; simp [beq_false_of_ne (Ne.symm h23), Ne.symm h12]
    simp [beq_false_of_ne hza1, beq_false_of_ne hzb1, hzb0]
  · exact swapPair_involutive id h23 (fun _ h1 h2 => ⟨h1, h2, rfl⟩) z

private theorem swapChain4_involutive
    {a0 b0 a1 b1 a2 b2 a3 b3 : CryptoGames.CBC.Block}
    (hnd : [a0, b0, a1, b1, a2, b2, a3, b3].Nodup)
    (x : CryptoGames.CBC.Block) :
    let f := fun y =>
      if y == a0 then b0 else if y == b0 then a0
      else if y == a1 then b1 else if y == b1 then a1
      else if y == a2 then b2 else if y == b2 then a2
      else if y == a3 then b3 else if y == b3 then a3
      else y
    f (f x) = x := by
  intro f; dsimp only [f]
  have hpreserve2 : ∀ {c0 d0 c1 d1 w : CryptoGames.CBC.Block},
      w ≠ c0 → w ≠ d0 → w ≠ c1 → w ≠ d1 →
      ∀ z, z ≠ w →
        (if z == c0 then d0 else if z == d0 then c0
         else if z == c1 then d1 else if z == d1 then c1 else z) ≠ w := by
    intro c0 d0 c1 d1 w hw1 hw2 hw3 hw4 z hzw
    by_cases h1 : z = c0; · subst h1; simp [hw2.symm]
    by_cases h2 : z = d0; · subst h2; simp [beq_false_of_ne h1, hw1.symm]
    by_cases h3 : z = c1; · subst h3; simp [beq_false_of_ne h1, beq_false_of_ne h2, hw4.symm]
    by_cases h4 : z = d1
    · subst h4
      simp [beq_false_of_ne h1, beq_false_of_ne h2, beq_false_of_ne h3, hw3.symm]
    · simp [beq_false_of_ne h1, beq_false_of_ne h2, beq_false_of_ne h3, beq_false_of_ne h4, hzw]
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  rcases hnd with ⟨h0, h1, h2, h3, h4567⟩
  have hnd23 : [a2, b2, a3, b3].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact h4567
  let g2 := fun y =>
    if y == a2 then b2 else if y == b2 then a2
    else if y == a3 then b3 else if y == b3 then a3 else y
  let f1 := fun y => if y == a1 then b1 else if y == b1 then a1 else g2 y
  have hg1 : ∀ z, f1 (f1 z) = z := fun z =>
    swapPair_involutive g2 h2.1
      (fun u hua1 hub1 =>
        ⟨hpreserve2 h2.2.1 h2.2.2.1 h2.2.2.2.1 h2.2.2.2.2 u hua1,
         hpreserve2 h3.1 h3.2.1 h3.2.2.1 h3.2.2.2 u hub1,
         swapChain2_involutive hnd23 u⟩) z
  have hf1_ne : ∀ {w : CryptoGames.CBC.Block},
      w ≠ a1 → w ≠ b1 → w ≠ a2 → w ≠ b2 → w ≠ a3 → w ≠ b3 →
      ∀ z, z ≠ w → f1 z ≠ w := by
    intro w hw1 hw2 hw3 hw4 hw5 hw6 z hzw
    dsimp only [f1]
    by_cases hza1 : z = a1; · subst hza1; simp [hw2.symm]
    by_cases hzb1 : z = b1; · subst hzb1; simp [beq_false_of_ne hza1, hw1.symm]
    simp [beq_false_of_ne hza1, beq_false_of_ne hzb1]
    exact hpreserve2 hw3 hw4 hw5 hw6 z hzw
  exact swapPair_involutive f1 h0.1
    (fun z hza0 hzb0 =>
      ⟨hf1_ne h0.2.1 h0.2.2.1 h0.2.2.2.1 h0.2.2.2.2.1 h0.2.2.2.2.2.1 h0.2.2.2.2.2.2 z hza0,
       hf1_ne h1.1 h1.2.1 h1.2.2.1 h1.2.2.2.1 h1.2.2.2.2.1 h1.2.2.2.2.2 z hzb0,
       hg1 z⟩) x

theorem compAesBlock_involutive (k : CryptoGames.CBC.AesKey) (b : CryptoGames.CBC.Block) :
    compAesBlock k (compAesBlock k b) = b := by
  obtain ⟨hndA, hndB⟩ := compAesAB_disjoint
  unfold compAesBlock
  cases k == CryptoGames.HKDF.bytesToKey32 compAesKA <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · cases k == CryptoGames.HKDF.bytesToKey32 compAesKB <;> simp only [Bool.false_eq_true, ↓reduceIte]
    exact swapChain2_involutive hndB b
  · exact swapChain4_involutive hndA b

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
    simp only [List.flatMap_cons, List.length_append, h16, length_flatMap_blockToBytesLE cs,
      List.length_cons]
    omega

private def cbcEncryptList (f : ByteSpecs.Block → ByteSpecs.Block) (iv : ByteSpecs.Block) :
    List ByteSpecs.Block → List ByteSpecs.Block
  | [] => []
  | b :: bs =>
    let c := f (b ^^^ iv)
    c :: cbcEncryptList f c bs

private theorem toList_cbcEncrypt (f : ByteSpecs.Block → ByteSpecs.Block) :
    ∀ (iv : ByteSpecs.Block) {n : Nat} (P : List.Vector ByteSpecs.Block n),
      (ByteSpecs.cbcEncrypt f iv P).toList = cbcEncryptList f iv P.toList
  | _, 0, P => by
    cases P with
    | mk l hl =>
      cases l with
      | nil => rfl
      | cons _ _ => cases hl
  | iv, _ + 1, P => by
    simp only [ByteSpecs.cbcEncrypt, List.Vector.toList_cons]
    rw [toList_cbcEncrypt f (f (P.head ^^^ iv)) P.tail]
    cases P with
    | mk l hl =>
      cases l with
      | nil => cases hl
      | cons b bs => rfl

private theorem cbcEncryptList_cbcDecryptBlocks {f : ByteSpecs.Block → ByteSpecs.Block}
    (hinv : ∀ b, f (f b) = b) :
    ∀ (iv : ByteSpecs.Block) (cs : List ByteSpecs.Block),
      cbcEncryptList f iv (ByteSpecs.cbcDecryptBlocks f iv cs) = cs
  | _, [] => rfl
  | iv, c :: cs => by
    have hxor : f ((f c ^^^ iv) ^^^ iv) = c := by
      rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, hinv]
    simp only [ByteSpecs.cbcDecryptBlocks, cbcEncryptList, hxor,
      cbcEncryptList_cbcDecryptBlocks hinv c cs]

private theorem flatMap_ofFn_chunks16 (m : Nat) :
    ∀ (bs : List (BitVec 8)), bs.length = 16 * m →
      (List.ofFn fun i : Fin m =>
        ByteSpecs.bytesToBlock ((bs.drop (16 * i.val)).take 16)).flatMap
          ByteSpecs.blockToBytesLE = bs := by
  induction m with
  | zero =>
    intro bs h
    simp only [Nat.mul_zero, List.length_eq_zero_iff] at h
    subst h; rfl
  | succ m ih =>
    intro bs h
    rw [List.ofFn_succ, List.flatMap_cons]
    simp only [Fin.val_zero, Nat.mul_zero, List.drop_zero, Fin.val_succ]
    rw [ByteSpecs.blockToBytesLE_bytesToBlock (bs.take 16) (by rw [List.length_take, h]; omega)]
    have hrest : (List.ofFn fun i : Fin m =>
        ByteSpecs.bytesToBlock ((bs.drop (16 * (i.val + 1))).take 16)) =
      List.ofFn fun i : Fin m =>
        ByteSpecs.bytesToBlock (((bs.drop 16).drop (16 * i.val)).take 16) := by
      congr 1; ext i; rw [List.drop_drop]
      have : 16 * (i.val + 1) = 16 + 16 * i.val := by omega
      rw [this]
    rw [hrest, ih (bs.drop 16) (by simp [h]; omega), List.take_append_drop]

private theorem flatMap_chunks16 (ct : List (BitVec 8)) (h : ct.length % 16 = 0) :
    (ByteSpecs.chunks16 ct).flatMap ByteSpecs.blockToBytesLE = ct := by
  unfold ByteSpecs.chunks16
  exact flatMap_ofFn_chunks16 (ct.length / 16) ct (by omega)

private theorem chunks16_pkcs7Bytes (p : List (BitVec 8)) :
    ByteSpecs.chunks16 (ByteSpecs.pkcs7Bytes (⟨p, rfl⟩ : ByteSpecs.Plain p.length)) =
      (ByteSpecs.pkcs7Blocks (⟨p, rfl⟩ : ByteSpecs.Plain p.length)).toList := by
  unfold ByteSpecs.chunks16 ByteSpecs.pkcs7Blocks
  rw [List.Vector.toList_ofFn]
  have hlen :
      (ByteSpecs.pkcs7Bytes (⟨p, rfl⟩ : ByteSpecs.Plain p.length)).length / 16 =
        ByteSpecs.nBlocks p.length := by
    simp only [ByteSpecs.pkcs7Bytes, List.length_append, List.Vector.toList_mk,
      List.length_replicate, ByteSpecs.padLen, ByteSpecs.nBlocks]
    omega
  refine List.ext_getElem ?_ fun i h1 h2 => ?_
  · simp [hlen]
  · simp

private theorem aesCbcEncrypt_of_decrypt
    {E : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block}
    (hinv : ∀ k b, E k (E k b) = b)
    (c p : List (BitVec 8)) (k : CryptoGames.CBC.AesKey) (iv : CryptoGames.CBC.Block)
    (hdec : CryptoGames.LibsignalSession.aesCbcDecrypt E k iv c = some p) :
    CryptoGames.LibsignalSession.aesCbcEncrypt E k iv p = c := by
  rw [aesCbcDecrypt_eq_byteSpecs] at hdec
  rw [aesCbcEncrypt_eq_byteSpecs]
  unfold ByteSpecs.cbcDecRaw at hdec
  split at hdec
  · cases hdec
  · rename_i hct
    push Not at hct
    obtain ⟨hcne, hmod⟩ := hct
    let m := c.length / 16
    have hclen : c.length = 16 * m := by dsimp [m]; omega
    set P := ByteSpecs.cbcDecryptBlocks (E k) iv (ByteSpecs.chunks16 c)
    set bs := P.flatMap ByteSpecs.blockToBytesLE
    have hPlen : P.length = m := by
      simp [P, length_cbcDecryptBlocks, ByteSpecs.chunks16, m]
    have hbslen : bs.length = 16 * m := by
      rw [show bs = P.flatMap ByteSpecs.blockToBytesLE from rfl,
        length_flatMap_blockToBytesLE, hPlen]
    unfold ByteSpecs.pkcs7Unpad at hdec
    cases hlast : bs.getLast? with
    | none => simp [hlast] at hdec
    | some last =>
      simp only [hlast] at hdec
      split at hdec
      · cases hdec
      · rename_i hbounds
        push Not at hbounds
        obtain ⟨hn0, hn16, hnlen⟩ := hbounds
        split at hdec
        · rename_i hall
          injection hdec with hp
          have hdrop_len : (bs.drop (bs.length - last.toNat)).length = last.toNat := by
            rw [List.length_drop]; omega
          have hdrop : bs.drop (bs.length - last.toNat) =
              List.replicate last.toNat last := by
            have := eq_replicate_of_all_beq _ _ hall
            rwa [hdrop_len] at this
          have hplen : p.length = 16 * m - last.toNat := by
            rw [← hp, List.length_take, hbslen]; omega
          have hpad : ByteSpecs.padLen p.length = last.toNat := by
            unfold ByteSpecs.padLen; rw [hplen]; omega
          have hlast_eq : BitVec.ofNat 8 (ByteSpecs.padLen p.length) = last := by
            rw [hpad]; simp
          have hbs_eq : bs = ByteSpecs.pkcs7Bytes (⟨p, rfl⟩ : ByteSpecs.Plain p.length) := by
            calc bs = bs.take (bs.length - last.toNat) ++ bs.drop (bs.length - last.toNat) :=
                  (List.take_append_drop _ _).symm
              _ = p ++ List.replicate last.toNat last := by rw [hp, hdrop]
              _ = p ++ List.replicate (ByteSpecs.padLen p.length)
                    (BitVec.ofNat 8 (ByteSpecs.padLen p.length)) := by rw [← hpad, hlast_eq]
              _ = ByteSpecs.pkcs7Bytes (⟨p, rfl⟩ : ByteSpecs.Plain p.length) := rfl
          have hP_eq : P = (ByteSpecs.pkcs7Blocks (⟨p, rfl⟩ : ByteSpecs.Plain p.length)).toList := by
            have hch := congrArg ByteSpecs.chunks16 hbs_eq
            simpa [bs, ByteSpecs.chunks16_flatMap, chunks16_pkcs7Bytes] using hch
          have henc : (ByteSpecs.cbcEncrypt (E k) iv
              (ByteSpecs.pkcs7Blocks (⟨p, rfl⟩ : ByteSpecs.Plain p.length))).toList =
              ByteSpecs.chunks16 c := by
            rw [toList_cbcEncrypt, ← hP_eq]
            exact cbcEncryptList_cbcDecryptBlocks (hinv k) iv (ByteSpecs.chunks16 c)
          rw [henc, flatMap_chunks16 c hmod]
        · cases hdec

theorem compAesDec_compAesPerm (k iv text : HwBytes) :
    compAesDec k iv (compAesPerm k iv text) = some text := by
  unfold compAesDec compAesPerm
  rw [aesCbcEncrypt_eq_byteSpecs, aesCbcDecrypt_eq_byteSpecs]
  exact ByteSpecs.cbcDecRaw_correct compAesBlock_involutive _ _
    (⟨text, rfl⟩ : ByteSpecs.Plain text.length)

theorem compAesPerm_of_compAesDec {k iv ct pt : HwBytes}
    (h : compAesDec k iv ct = some pt) :
    compAesPerm k iv pt = ct :=
  aesCbcEncrypt_of_decrypt compAesBlock_involutive ct pt _ _ h

theorem compAesPerm_injective (k iv : HwBytes) {t1 t2 : HwBytes}
    (h : compAesPerm k iv t1 = compAesPerm k iv t2) : t1 = t2 := by
  have h1 := compAesDec_compAesPerm k iv t1
  rw [h, compAesDec_compAesPerm] at h1
  exact (Option.some.inj h1).symm

theorem compAesPerm_length (k iv text : HwBytes) :
    (compAesPerm k iv text).length = 16 * (text.length / 16 + 1) := by
  unfold compAesPerm
  rw [aesCbcEncrypt_eq_byteSpecs, length_flatMap_blockToBytesLE, List.Vector.toList_length]
  rfl

theorem compDefaultHmac_length (k d : HwBytes) : (compDefaultHmac k d).length = 32 := by
  simp [compDefaultHmac, compTag4, compHmacMix28]

/-! ## 4. `ExternContractsHoldCli`, `compHooks7003`, and Kyber Correctness -/

theorem compI7003_cryptoEquationsHold : ExternCryptoLawsHold compI7003 where
  x25519_agreement_commutes a b := by
    simp only [compI7003_publicKey, compI7003_agreement, Option.getD_some]
    exact congrArg some (compLookupDh_comm a b)
  x25519_agreement_length a p := by simp [compI7003_agreement, compLookupDh_length]
  x25519_public_key_length a := by simp [compI7003_publicKey, compLookupPub_length]
  x25519_agreement_reads_u_coordinate a b b' hb hb' hu := by
    simp only [compI7003_agreement]; congr 1
    have hl : isLowOrderKey (b.map BitVec.toNat) = isLowOrderKey (b'.map BitVec.toNat) := by
      simp only [isLowOrderKey, List.length_map, hb, hb']
      exact congrArg (fun u => (32 == 32 && lowOrderUs.contains u)) hu
    have hp : compPointIdx b = compPointIdx b' := by simp only [compPointIdx, hb, hb', hu]
    unfold compLookupDh; rw [hl, hp]
  x25519_agreement_torsion_invariant secret point t := by
    simp only [compI7003_agreement]
    exact congrArg some (compLookupDh_torsionShift secret point t)
  x25519_agreement_zero_iff_low_order a b _ _ := by
    rw [compI7003_agreement, Option.getD_some]
    cases h : isLowOrderKey (b.map BitVec.toNat)
    · simp only [Bool.false_eq_true, iff_false]
      exact compLookupDh_ne_zero_of_not_lowOrder a b h
    · unfold compLookupDh; simp [h]
  x25519_public_key_not_low_order a _ := by simp [compI7003_publicKey, compLookupPub_not_lowOrder]
  aes_cbc_decrypt_inverts_encrypt plaintext key iv := by
    rw [compI7003_aesEncrypt, compI7003_aesDecrypt, Option.getD_some]
    exact compAesDec_compAesPerm key iv plaintext
  aes_cbc_encrypt_of_decrypt c k iv p _ _ h := by
    rw [compI7003_aesDecrypt] at h
    rw [compI7003_aesEncrypt]
    exact congrArg some (compAesPerm_of_compAesDec h)
  hmac_tag_length k d t h := by
    rw [compI7003_hmac, Option.some.injEq] at h
    rw [← h]; exact compDefaultHmac_length k d

theorem compI7003_pubCanonical : X25519PubCanonical compI7003 := by
  intro s
  rw [compI7003_publicKey, Option.getD_some]
  exact compLookupPub_lt_p25519 s

theorem compI7003_torsionShiftsRejected : X25519TorsionShiftsRejected compI7003 := by
  intro s t k _ hu hne _
  rw [torsionShift_compI7003] at hu
  exact hne hu

theorem compI7003_externContractsHoldCli : ExternContractsHoldCli compI7003 :=
  ⟨compI7003_cryptoEquationsHold, compI7003_pubCanonical, compI7003_torsionShiftsRejected⟩

private theorem compKyberCt0_length : compKyberCt0.length = 1568 := leBytes_length 1568 _
private theorem compDefaultKyberCt_length : compDefaultKyberCt.length = 1568 := List.length_replicate
private theorem compKyberSs0_length : compKyberSs0.length = 32 := leBytes_length 32 _
private theorem compDefaultKyberSs_length : compDefaultKyberSs.length = 32 := List.length_replicate

theorem compKyberEncaps_length (e : HwBytes) : (compKyberEncaps e).length = 1600 := by
  unfold compKyberEncaps
  split <;> simp [compKyberCt0_length, compDefaultKyberCt_length, compKyberSs0_length,
    compDefaultKyberSs_length]

theorem compKyberDecaps_length (ct : HwBytes) : (compKyberDecaps ct).length = 32 := by
  unfold compKyberDecaps
  split
  · exact compKyberSs0_length
  · exact compDefaultKyberSs_length

theorem compToEdwards_length (u : HwBytes) (sign : BitVec 8) :
    (compToEdwards u sign).length = 160 := by
  unfold compToEdwards compToEdBob0 compToEdBob1 compToEdAlice0 compToEdEk0
  repeat (first | exact leBytes_length 160 _ | exact List.length_replicate | split)

def compMlKem7003 : CryptoVerification.LibsignalSpqrV1.MlKem where
  keyPair _ := List.Vector.replicate 2400 0#8
  encaps1 _ _ :=
    some (List.Vector.replicate 960 0#8,
          List.Vector.replicate 2080 0#8,
          List.Vector.replicate 32 0#8)
  encaps2 _ _ := List.Vector.replicate 128 0#8
  decaps _ _ _ := List.Vector.replicate 32 0#8
  validPk _ _ := true

def compHooks7003 : CliHooks where
  C :=
    { F := sha256CompressFunction compI7003
      E := compAesBlock
      D := compAesBlock
      X := fun a b => ⟨compLookupDh a.toList b.toList, compLookupDh_length a.toList b.toList⟩
      pubKey := fun a => ⟨compLookupPub a.toList, compLookupPub_length a.toList⟩ }
  Q :=
    { F512 := fun st _ => st
      encaps := fun _ rand =>
        (⟨(compKyberEncaps rand.toList).take 1568, by
            rw [List.length_take, compKyberEncaps_length]; rfl⟩,
         ⟨(compKyberEncaps rand.toList).drop 1568, by
            rw [List.length_drop, compKyberEncaps_length]⟩)
      decaps := fun _ ct => ⟨compKyberDecaps ct.toList, compKyberDecaps_length ct.toList⟩
      K := compMlKem7003 }

theorem compI7003_hooksMatch : HooksMatchInterpretation compI7003 compHooks7003 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p k iv _ _; rfl
  · intro c k iv _ _; rfl
  · intro a b; rfl
  · intro a; rfl
  · intro pk rand
    rw [compI7003_kyberEncaps]
    exact congrArg some (List.take_append_drop 1568 (compKyberEncaps rand.toList)).symm
  · intro sk ct; rfl

private theorem compDefaultKyberCt_beq_ct0 : (compDefaultKyberCt == compKyberCt0) = false := by
  exact Bool.eq_false_iff.mpr (fun h => by
    have := congrArg List.head? (eq_of_beq h)
    revert this; decide)

private theorem take_append_of_eq_length {α : Type} {l1 l2 : List α} {n : Nat}
    (h : l1.length = n) : (l1 ++ l2).take n = l1 := by subst h; exact List.take_left

private theorem drop_append_of_eq_length {α : Type} {l1 l2 : List α} {n : Nat}
    (h : l1.length = n) : (l1 ++ l2).drop n = l2 := by subst h; exact List.drop_left

theorem compI7003_kyberCorrectOn (r : ProtocolSetup) (cts : List HwBytes) :
    ∀ ct ∈ cts, ∀ e ss, e.length = 32 →
      DY.Libsignal.Composed.Refinement.kyberEncapsBytes compI7003 r e = some (ct, ss) →
      DY.Libsignal.Composed.Refinement.kyberDecapsBytes compI7003 r ct = some ss := by
  intro ct _ e ss _ he
  unfold DY.Libsignal.Composed.Refinement.kyberEncapsBytes at he
  rw [compI7003_kyberEncaps, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨hct, hss⟩ := he
  unfold DY.Libsignal.Composed.Refinement.kyberDecapsBytes
  rw [compI7003_kyberDecaps, Option.some.injEq]
  unfold compKyberEncaps at hct hss
  split at hct <;> rename_i h0
  · simp only [h0, ↓reduceIte] at hss
    rw [take_append_of_eq_length compKyberCt0_length] at hct
    rw [drop_append_of_eq_length compKyberCt0_length] at hss
    rw [← hct, ← hss]; simp [compKyberDecaps]
  · simp only [h0, Bool.false_eq_true, ↓reduceIte] at hss
    rw [take_append_of_eq_length compDefaultKyberCt_length] at hct
    rw [drop_append_of_eq_length compDefaultKyberCt_length] at hss
    rw [← hct, ← hss]; simp [compKyberDecaps, compDefaultKyberCt_beq_ct0]

theorem not_kyberMismatch_compI7003 (r : ProtocolSetup) (p : PreKeyFields) :
    ¬ KyberMismatch compI7003 r p := by
  rintro ⟨e, ct, ss, he, _, henc, hdec⟩
  exact hdec (compI7003_kyberCorrectOn r [ct] ct (List.mem_singleton_self ct) e ss he henc)

/-! ## 5. Unconditional SHA-256 and HMAC-SHA256 Truncation Injectivity (`F7`) -/

abbrev F7 : ShaState → HwBytes → ShaState := sha256CompressFunction compI7003

def OnTab7 (s : ShaState) (b : HwBytes) : Prop :=
  (compSha256 (shaStateBytes s) b).take 4 ≠ compTag4

def tagW : BitVec 32 := 0xd7d7d7d7#32

private theorem shaStateOfBytes_head_eq_take4 (bytes : HwBytes) :
    (shaStateOfBytes bytes).head = (shaStateOfBytes (bytes.take 4)).head := by
  rcases bytes with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, bs⟩⟩⟩⟩ <;> rfl

theorem sha256CompressFunction_compI7003_head (st : ShaState) (blk : HwBytes) :
    (F7 st blk).head = (shaStateOfBytes ((compSha256 (shaStateBytes st) blk).take 4)).head := by
  unfold F7 sha256CompressFunction
  rw [compI7003_sha256Compress, Option.getD_some, shaStateOfBytes_head_eq_take4]

theorem compDefaultSha256_take4 (st blk : HwBytes) :
    (compDefaultSha256 st blk).take 4 = compTag4 := by
  simp [compDefaultSha256, compTag4]

theorem compSha256_row_of_untagged {st blk : HwBytes}
    (h : (compSha256 st blk).take 4 ≠ compTag4) :
    st.take 4 ≠ compTag4 ∧ st.length = 32 ∧ blk.length = 64 ∧
      ∃ row ∈ compSha256Rows,
        row.1 = bytesToNat st ∧ row.2.1 = bytesToNat blk ∧ compSha256 st blk = leBytes 32 row.2.2 := by
  unfold compSha256 at h ⊢
  by_cases htag : (st.take 4 == compTag4 || blk.take 4 == compTag4 ||
      blk.take 4 == compTag4Ipad || blk.take 4 == compTag4Opad) = true
  · simp only [htag, ↓reduceIte] at h; exact absurd (compDefaultSha256_take4 st blk) h
  · have hst : st.take 4 ≠ compTag4 := fun he => by apply htag; simp [he]
    simp only [htag, ↓reduceIte, Bool.false_eq_true] at h ⊢
    by_cases hlen : (st.length == 32 && blk.length == 64) = true
    · simp only [hlen, ↓reduceIte] at h ⊢
      simp only [Bool.and_eq_true, beq_iff_eq] at hlen
      cases hf : List.find? (fun r => r.1 == bytesToNat st && r.2.1 == bytesToNat blk) compSha256Rows with
      | none => simp only [hf] at h; exact absurd (compDefaultSha256_take4 st blk) h
      | some row =>
        rcases row with ⟨r1, r2, r3⟩
        have hmem := List.mem_of_find?_eq_some hf
        have hp := List.find?_some hf
        simp only [Bool.and_eq_true, beq_iff_eq] at hp
        exact ⟨hst, hlen.1, hlen.2, ⟨r1, r2, r3⟩, hmem, hp.1, hp.2, rfl⟩
    · simp only [hlen, ↓reduceIte, Bool.false_eq_true] at h
      exact absurd (compDefaultSha256_take4 st blk) h

theorem leBytes_bytesToNat : ∀ bs : HwBytes, leBytes bs.length (bytesToNat bs) = bs
  | [] => rfl
  | b :: bs => by
    have hb : b.toNat < 256 := b.isLt
    have h1 : (b.toNat + 256 * bytesToNat bs) / 256 = bytesToNat bs := by omega
    simp only [List.length_cons, leBytes, bytesToNat, h1, leBytes_bytesToNat bs]
    congr 1; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega

theorem bytesToNat_leBytes : ∀ (k n : Nat), n < 2 ^ (8 * k) → bytesToNat (leBytes k n) = n
  | 0, n, h => by
    have : n = 0 := by simpa using h
    subst this; rfl
  | k + 1, n, h => by
    have hpow : 2 ^ (8 * (k + 1)) = 2 ^ (8 * k) * 256 := by
      rw [show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add]
    have hk : n / 256 < 2 ^ (8 * k) := by rw [Nat.div_lt_iff_lt_mul (by decide)]; omega
    simp only [leBytes, bytesToNat, BitVec.toNat_ofNat, bytesToNat_leBytes k (n / 256) hk]; omega

theorem toBEBytes_tagW : toBEBytes 4 tagW = compTag4 := by decide
theorem shaStateOfBytes_compTag4_head : (shaStateOfBytes compTag4).head = tagW := by decide

theorem hstep7 : ∀ s b, ¬ OnTab7 s b → (F7 s b).head = tagW := by
  intro s b h
  rw [sha256CompressFunction_compI7003_head, Classical.not_not.mp h, shaStateOfBytes_compTag4_head]

theorem shaStateBytes_take4_of_head (s : ShaState) (hs : s.head = tagW) :
    (shaStateBytes s).take 4 = compTag4 := by
  obtain ⟨l, hl⟩ := s
  match l, hl with
  | w :: _, _ =>
    have hw : w = tagW := hs; subst hw
    simp only [shaStateBytes, List.Vector.toList, List.flatMap_cons]
    rw [List.take_append_of_le_length (by simp)]; decide

theorem hT1_7 : ∀ s b, s.head = tagW → ¬ OnTab7 s b := by
  intro s b hs h; apply h
  have hst := shaStateBytes_take4_of_head s hs
  unfold compSha256
  simp only [hst, beq_self_eq_true, Bool.true_or, ↓reduceIte]
  exact compDefaultSha256_take4 _ _

theorem hT2_7 : ∀ s b, b.take 4 = toBEBytes 4 tagW → ¬ OnTab7 s b := by
  intro s b hb h; rw [toBEBytes_tagW] at hb; apply h
  unfold compSha256
  simp only [hb, beq_self_eq_true, Bool.true_or, Bool.or_true, ↓reduceIte]
  exact compDefaultSha256_take4 _ _

theorem onTab_of_sha256With_untagged (m : HwBytes) (h : (sha256With F7 m).take 4 ≠ compTag4)
    (l₁ : List HwBytes) (b : HwBytes) (l₂ : List HwBytes)
    (hsplit : chunks64 (sha256Pad m) = l₁ ++ b :: l₂) :
    OnTab7 (l₁.foldl F7 sha256IV) b := by
  intro hoff; apply h
  rw [sha256With_take4_of_offTable OnTab7 tagW F7 hstep7 hT1_7 m l₁ b l₂ hsplit
    (fun h' => h' hoff), toBEBytes_tagW]

def kblk (k : HwBytes) (pad : BitVec 8) : HwBytes :=
  (k ++ List.replicate (64 - k.length) 0).map (· ^^^ pad)

theorem kblk_length (k : HwBytes) (pad : BitVec 8) (hk : k.length ≤ 64) :
    (kblk k pad).length = 64 := by
  simp only [kblk, List.length_map, List.length_append, List.length_replicate]; omega

theorem hmacWith_eq (k m : HwBytes) (hk : k.length ≤ 64) :
    hmacWith F7 k m = sha256With F7 (kblk k 0x5c ++ sha256With F7 (kblk k 0x36 ++ m)) := by
  have hk' : ¬ 64 < k.length := by omega
  simp only [hmacWith, hk', ↓reduceIte, kblk]

theorem hmac_inner_untagged (k m : HwBytes) (hk : k.length ≤ 64)
    (h : (hmacWith F7 k m).take 4 ≠ compTag4) :
    (sha256With F7 (kblk k 0x36 ++ m)).take 4 ≠ compTag4 := by
  intro hin; apply h
  rw [hmacWith_take4_of_inner OnTab7 tagW F7 hstep7 hT1_7 hT2_7 k m hk
    (by rw [toBEBytes_tagW]; exact hin), toBEBytes_tagW]

def ivNat : Nat := bytesToNat (shaStateBytes sha256IV)
def digestOfOut (o : Nat) : HwBytes := (shaStateOfBytes (leBytes 32 o)).toList.flatMap (toBEBytes 4)

def natElem (a : Nat) : List Nat → Bool
  | [] => false
  | b :: bs => match Nat.beq a b with | true => true | false => natElem a bs

def natNodup : List Nat → Bool
  | [] => true
  | x :: xs => match natElem x xs with | true => false | false => natNodup xs

theorem not_mem_of_natElem_false {a : Nat} : ∀ {l : List Nat}, natElem a l = false → a ∉ l
  | [], _, hmem => nomatch hmem
  | b :: bs, h, hmem => by
    unfold natElem at h; cases hbeq : Nat.beq a b
    · rw [hbeq] at h; rcases List.mem_cons.mp hmem with rfl | hbs
      · rw [Nat.beq_eq.mpr rfl] at hbeq; nomatch hbeq
      · exact not_mem_of_natElem_false h hbs
    · rw [hbeq] at h; nomatch h

theorem nodup_of_natNodup : ∀ {l : List Nat}, natNodup l = true → l.Nodup
  | [], _ => List.Pairwise.nil
  | x :: xs, h => by
    unfold natNodup at h; cases he : natElem x xs
    · rw [he] at h
      exact List.Pairwise.cons (fun y hy hxy => not_mem_of_natElem_false he (hxy ▸ hy))
        (nodup_of_natNodup h)
    · rw [he] at h; nomatch h

def low16Bytes (v : HwBytes) : Nat := (v.getD 3 0#8).toNat + 256 * (v.getD 2 0#8).toNat

private theorem ext0 (a b c d : BitVec 8) :
    (BitVec.ofNat 32 (a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat)).extractLsb' 0 8 = a := by
  apply BitVec.eq_of_toNat_eq
  have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega

private theorem ext8 (a b c d : BitVec 8) :
    (BitVec.ofNat 32 (a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat)).extractLsb' 8 8 = b := by
  apply BitVec.eq_of_toNat_eq
  have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega

private theorem ext16 (a b c d : BitVec 8) :
    (BitVec.ofNat 32 (a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat)).extractLsb' 16 8 = c := by
  apply BitVec.eq_of_toNat_eq
  have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega

private theorem ext24 (a b c d : BitVec 8) :
    (BitVec.ofNat 32 (a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat)).extractLsb' 24 8 = d := by
  apply BitVec.eq_of_toNat_eq
  have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega

private theorem reassemble_word32 (w : BitVec 32) :
    BitVec.ofNat 32
      ((w.extractLsb' 0 8).toNat + 256 * (w.extractLsb' 8 8).toNat +
       65536 * (w.extractLsb' 16 8).toNat + 16777216 * (w.extractLsb' 24 8).toNat) = w := by
  apply BitVec.eq_of_toNat_eq
  have := w.isLt
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

theorem shaStateBytes_length (s : ShaState) : (shaStateBytes s).length = 32 := by
  obtain ⟨l, hl⟩ := s
  match l, hl with
  | [_, _, _, _, _, _, _, _], _ => rfl

theorem shaStateOfBytes_shaStateBytes (s : ShaState) : shaStateOfBytes (shaStateBytes s) = s := by
  obtain ⟨l, hl⟩ := s
  match l, hl with
  | [w0, w1, w2, w3, w4, w5, w6, w7], _ =>
    apply List.Vector.eq
    simp only [shaStateBytes, shaStateOfBytes, List.Vector.toList_mk, List.Vector.toList_ofFn,
      List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ, List.flatMap_cons,
      List.flatMap_nil, List.cons_append, List.nil_append, Nat.mul_zero, Nat.zero_add,
      List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
      reassemble_word32]

theorem shaStateBytes_shaStateOfBytes (x : HwBytes) (hx : x.length = 32) :
    shaStateBytes (shaStateOfBytes x) = x := by
  match x, hx with
  | [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15,
     x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31], _ =>
    simp only [shaStateOfBytes, shaStateBytes, List.Vector.toList_ofFn, List.ofFn_succ,
      List.ofFn_zero, Fin.val_zero, Fin.val_succ, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.nil_append, List.cons_append, Nat.mul_zero, Nat.zero_add,
      List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
      ext0, ext8, ext16, ext24]

theorem low16Bytes_digestOfOut_take8 (o : Nat) :
    low16Bytes ((digestOfOut o).take 8) = o % 65536 := by
  let b0 : BitVec 8 := BitVec.ofNat 8 o
  let b1 : BitVec 8 := BitVec.ofNat 8 (o / 256)
  let b2 : BitVec 8 := BitVec.ofNat 8 (o / 256 / 256)
  let b3 : BitVec 8 := BitVec.ofNat 8 (o / 256 / 256 / 256)
  have hle : leBytes 32 o = b0 :: b1 :: b2 :: b3 :: leBytes 28 (o / 256 / 256 / 256 / 256) := rfl
  unfold low16Bytes digestOfOut; rw [hle]
  simp only [shaStateOfBytes, List.Vector.toList_ofFn, List.ofFn_succ, List.ofFn_zero,
    Fin.val_zero, Fin.val_succ, Nat.mul_zero, Nat.zero_add, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.flatMap_cons, toBEBytes, List.cons_append,
    List.nil_append, List.take_succ_cons, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, ext0, ext8]
  simp only [b0, b1, BitVec.toNat_ofNat]; omega

theorem rows_mod65536_nodup : (compSha256Rows.map fun r => r.2.2 % 65536).Nodup := by
  apply nodup_of_natNodup; decide +kernel

theorem rows_out_nodup : (compSha256Rows.map fun r => r.2.2).Nodup := by
  have h := rows_mod65536_nodup
  have hfun : (fun r : Nat × Nat × Nat => r.2.2 % 65536) =
      ((fun x : Nat => x % 65536) ∘ fun r : Nat × Nat × Nat => r.2.2) := rfl
  rw [hfun, ← List.map_map] at h
  exact List.Nodup.of_map _ h

theorem rows_take8_nodup : (compSha256Rows.map fun r => (digestOfOut r.2.2).take 8).Nodup := by
  have h := rows_mod65536_nodup
  have hfun : (fun r : Nat × Nat × Nat => r.2.2 % 65536) =
      (low16Bytes ∘ fun r : Nat × Nat × Nat => (digestOfOut r.2.2).take 8) := by
    funext r; exact (low16Bytes_digestOfOut_take8 r.2.2).symm
  rw [hfun, ← List.map_map] at h
  exact List.Nodup.of_map _ h

theorem ivNat_not_mem_rows_out : ivNat ∉ compSha256Rows.map (·.2.2) :=
  not_mem_of_natElem_false (by decide +kernel)

theorem sha256IV_head_ne_tagW : sha256IV.head ≠ tagW := by decide

theorem rows_out_lt : (compSha256Rows.all fun r => Nat.ble r.2.2 (2 ^ 256 - 1)) = true := by
  decide +kernel

theorem rows_lt : ∀ r ∈ compSha256Rows, r.2.2 < 2 ^ (8 * 32) := by
  intro r hr
  have h := Nat.le_of_ble_eq_true (List.all_eq_true.mp rows_out_lt r hr)
  omega

theorem rows_out_roundtrip :
    (compSha256Rows.all fun r =>
      bytesToNat (shaStateBytes (shaStateOfBytes (leBytes 32 r.2.2))) == r.2.2) = true := by
  rw [List.all_eq_true]; intro r hr
  rw [shaStateBytes_shaStateOfBytes _ (leBytes_length 32 _), bytesToNat_leBytes 32 _ (rows_lt r hr),
    beq_self_eq_true]

theorem F7_eq (s : ShaState) (b : HwBytes) :
    F7 s b = shaStateOfBytes (compSha256 (shaStateBytes s) b) := by
  unfold F7 sha256CompressFunction
  rw [compI7003_sha256Compress, Option.getD_some]

theorem row_step7 {s : ShaState} {b : HwBytes} (h : OnTab7 s b) :
    b.length = 64 ∧
      ∃ r ∈ compSha256Rows,
        r.1 = bytesToNat (shaStateBytes s) ∧
        r.2.1 = bytesToNat b ∧
        F7 s b = shaStateOfBytes (leBytes 32 r.2.2) := by
  obtain ⟨_, _, hbl, r, hr, h1, h2, h3⟩ := compSha256_row_of_untagged h
  exact ⟨hbl, r, hr, h1, h2, by rw [F7_eq, h3]⟩

theorem F7_ne_sha256IV (s : ShaState) (b : HwBytes) : F7 s b ≠ sha256IV := by
  intro heq
  have hon : OnTab7 s b := by
    intro hoff
    have hh := hstep7 s b (fun h' => h' hoff)
    rw [heq] at hh
    exact sha256IV_head_ne_tagW hh
  obtain ⟨_, r, hr, _, _, hF⟩ := row_step7 hon
  rw [heq] at hF
  have hout : r.2.2 = ivNat := by
    have hrt := beq_iff_eq.mp (List.all_eq_true.mp rows_out_roundtrip r hr)
    rw [← hF] at hrt
    exact hrt.symm
  exact ivNat_not_mem_rows_out (List.mem_map.mpr ⟨r, hr, hout⟩)

theorem F7_inj_of_head_ne_tagW {s₁ s₂ : ShaState} {b₁ b₂ : HwBytes}
    (hhead : (F7 s₂ b₂).head ≠ tagW)
    (heq : F7 s₁ b₁ = F7 s₂ b₂) :
    s₁ = s₂ ∧ b₁ = b₂ := by
  have hon₂ : OnTab7 s₂ b₂ := fun hoff => hhead (hstep7 s₂ b₂ (fun h' => h' hoff))
  have hon₁ : OnTab7 s₁ b₁ := fun hoff => hhead (heq ▸ hstep7 s₁ b₁ (fun h' => h' hoff))
  obtain ⟨hbl₁, r₁, hr₁, hs₁, hb₁, hF₁⟩ := row_step7 hon₁
  obtain ⟨hbl₂, r₂, hr₂, hs₂, hb₂, hF₂⟩ := row_step7 hon₂
  have hout : r₁.2.2 = r₂.2.2 := by
    have hrt₁ := beq_iff_eq.mp (List.all_eq_true.mp rows_out_roundtrip r₁ hr₁)
    have hrt₂ := beq_iff_eq.mp (List.all_eq_true.mp rows_out_roundtrip r₂ hr₂)
    rw [← hF₁, heq, hF₂] at hrt₁
    exact hrt₁.symm.trans hrt₂
  have hr_eq : r₁ = r₂ := List.inj_on_of_nodup_map rows_out_nodup hr₁ hr₂ hout
  subst hr_eq
  have hsb_eq : shaStateBytes s₁ = shaStateBytes s₂ := by
    have hrt₁ := leBytes_bytesToNat (shaStateBytes s₁)
    have hrt₂ := leBytes_bytesToNat (shaStateBytes s₂)
    rw [shaStateBytes_length] at hrt₁ hrt₂
    rw [← hrt₁, ← hrt₂, ← hs₁, hs₂]
  have hb_eq : b₁ = b₂ := by
    have hrt₁ := leBytes_bytesToNat b₁
    have hrt₂ := leBytes_bytesToNat b₂
    rw [hbl₁] at hrt₁; rw [hbl₂] at hrt₂
    rw [← hrt₁, ← hrt₂, ← hb₁, hb₂]
  refine ⟨?_, hb_eq⟩
  rw [← shaStateOfBytes_shaStateBytes s₁, ← shaStateOfBytes_shaStateBytes s₂, hsb_eq]

theorem foldl_F7_inj :
    ∀ (l₁ l₂ : List HwBytes),
      (l₂.foldl F7 sha256IV).head ≠ tagW →
      l₁.foldl F7 sha256IV = l₂.foldl F7 sha256IV →
      l₁ = l₂ := by
  intro l₁
  induction l₁ using List.reverseRecOn with
  | nil =>
    intro l₂ _ heq
    induction l₂ using List.reverseRecOn with
    | nil => rfl
    | append_singleton ys y _ =>
      rw [List.foldl_nil, List.foldl_append, List.foldl_cons, List.foldl_nil] at heq
      exact absurd heq.symm (F7_ne_sha256IV _ _)
  | append_singleton xs x ih =>
    intro l₂ hhead heq
    induction l₂ using List.reverseRecOn with
    | nil =>
      rw [List.foldl_nil, List.foldl_append, List.foldl_cons, List.foldl_nil] at heq
      exact absurd heq (F7_ne_sha256IV _ _)
    | append_singleton ys y _ =>
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at heq hhead
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at heq
      obtain ⟨hs, hb⟩ := F7_inj_of_head_ne_tagW hhead heq
      have hys_nt : (ys.foldl F7 sha256IV).head ≠ tagW := by
        intro htag
        exact hhead (hstep7 _ y (hT1_7 _ y htag))
      rw [ih ys hys_nt hs, hb]

private theorem flatten_ofFn_chunks64 (m : Nat) :
    ∀ (bs : HwBytes), bs.length = 64 * m →
      (List.ofFn fun i : Fin m => (bs.drop (64 * i.val)).take 64).flatten = bs := by
  induction m with
  | zero =>
    intro bs h
    simp only [Nat.mul_zero, List.length_eq_zero_iff] at h
    subst h; rfl
  | succ m ih =>
    intro bs h
    rw [List.ofFn_succ, List.flatten_cons]
    simp only [Fin.val_zero, Nat.mul_zero, List.drop_zero, Fin.val_succ]
    have hrest : (List.ofFn fun i : Fin m => (bs.drop (64 * (i.val + 1))).take 64) =
        List.ofFn fun i : Fin m => ((bs.drop 64).drop (64 * i.val)).take 64 := by
      congr 1; ext i; rw [List.drop_drop]
      rw [show 64 * (i.val + 1) = 64 + 64 * i.val by omega]
    rw [hrest, ih (bs.drop 64) (by simp [h]; omega), List.take_append_drop]

private theorem chunks64_flatten (bs : HwBytes) (h : bs.length % 64 = 0) :
    (chunks64 bs).flatten = bs :=
  flatten_ofFn_chunks64 (bs.length / 64) bs (by omega)

private theorem append_80_zeros_inj :
    ∀ {m₁ m₂ : HwBytes} {z₁ z₂ : Nat},
      m₁ ++ (0x80#8 :: List.replicate z₁ 0#8) = m₂ ++ (0x80#8 :: List.replicate z₂ 0#8) →
      m₁ = m₂
  | [], [], _, _, _ => rfl
  | [], b :: ms, z₁, z₂, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    have hmem : 0x80#8 ∈ List.replicate z₁ 0#8 := by
      rw [h.2]; exact List.mem_append_right _ List.mem_cons_self
    have heq := List.eq_of_mem_replicate hmem
    exact absurd heq (by decide)
  | a :: as, [], z₁, z₂, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    have hmem : 0x80#8 ∈ List.replicate z₂ 0#8 := by
      rw [← h.2]; exact List.mem_append_right _ List.mem_cons_self
    have heq := List.eq_of_mem_replicate hmem
    exact absurd heq (by decide)
  | a :: as, b :: bs, z₁, z₂, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    exact congrArg₂ List.cons h.1 (append_80_zeros_inj h.2)

theorem sha256Pad_inj {m₁ m₂ : HwBytes} (h : sha256Pad m₁ = sha256Pad m₂) : m₁ = m₂ := by
  have htake : ∀ m : HwBytes,
      (sha256Pad m).take ((sha256Pad m).length - 8) =
        m ++ (0x80#8 :: List.replicate ((119 - m.length % 64) % 64) 0#8) := by
    intro m
    let pre := m ++ (0x80#8 :: List.replicate ((119 - m.length % 64) % 64) 0#8)
    have hp : sha256Pad m = pre ++ toBEBytes 8 (BitVec.ofNat 64 (8 * m.length)) := by
      simp [sha256Pad, pre, List.append_assoc]
    have hl : (sha256Pad m).length - 8 = pre.length := by
      rw [hp, List.length_append, toBEBytes_length]; omega
    rw [hl, hp, List.take_left]
  have h1 := htake m₁
  rw [h, htake m₂] at h1
  exact append_80_zeros_inj h1.symm

theorem sha256With_row_of_untagged (m : HwBytes) (h : (sha256With F7 m).take 4 ≠ compTag4) :
    ∃ r ∈ compSha256Rows,
      (chunks64 (sha256Pad m)).foldl F7 sha256IV = shaStateOfBytes (leBytes 32 r.2.2) ∧
      sha256With F7 m = digestOfOut r.2.2 := by
  have hne := chunks64_sha256Pad_ne_nil m
  have hsplit := (dropLast_append_getLast hne).symm
  have hon : OnTab7 ((chunks64 (sha256Pad m)).dropLast.foldl F7 sha256IV)
      ((chunks64 (sha256Pad m)).getLast hne) :=
    onTab_of_sha256With_untagged m h _ _ [] hsplit
  obtain ⟨_, r, hr, _, _, hF⟩ := row_step7 hon
  have hfold : (chunks64 (sha256Pad m)).foldl F7 sha256IV = shaStateOfBytes (leBytes 32 r.2.2) := by
    rw [foldl_eq_getLast F7 sha256IV _ hne, hF]
  exact ⟨r, hr, hfold, by unfold sha256With digestOfOut; rw [hfold]⟩

theorem sha256With_take8_inj_of_untagged {m₁ m₂ : HwBytes}
    (h₂ : (sha256With F7 m₂).take 4 ≠ compTag4)
    (heq : (sha256With F7 m₁).take 8 = (sha256With F7 m₂).take 8) :
    m₁ = m₂ := by
  have h₁ : (sha256With F7 m₁).take 4 ≠ compTag4 := by
    have ht : (sha256With F7 m₁).take 4 = (sha256With F7 m₂).take 4 := by
      calc (sha256With F7 m₁).take 4 = ((sha256With F7 m₁).take 8).take 4 := by
            rw [List.take_take]; rfl
        _ = ((sha256With F7 m₂).take 8).take 4 := by rw [heq]
        _ = (sha256With F7 m₂).take 4 := by rw [List.take_take]; rfl
    rwa [ht]
  obtain ⟨r₁, hr₁, hf₁, hs₁⟩ := sha256With_row_of_untagged m₁ h₁
  obtain ⟨r₂, hr₂, hf₂, hs₂⟩ := sha256With_row_of_untagged m₂ h₂
  rw [hs₁, hs₂] at heq
  have hr_eq : r₁ = r₂ := List.inj_on_of_nodup_map rows_take8_nodup hr₁ hr₂ heq
  subst hr_eq
  have hhead : ((chunks64 (sha256Pad m₂)).foldl F7 sha256IV).head ≠ tagW := by
    intro htag
    apply h₂
    rw [sha256With_take4_fold, htag, toBEBytes_tagW]
  have hch := foldl_F7_inj _ _ hhead (hf₁.trans hf₂.symm)
  have hpad : sha256Pad m₁ = sha256Pad m₂ := by
    rw [← chunks64_flatten (sha256Pad m₁) (sha256Pad_length_mod m₁),
      ← chunks64_flatten (sha256Pad m₂) (sha256Pad_length_mod m₂), hch]
  exact sha256Pad_inj hpad

theorem map_xor_xor (l : HwBytes) (p : BitVec 8) : (l.map (· ^^^ p)).map (· ^^^ p) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem hmacWith_take8_inj_of_untagged {k₁ k₂ m₁ m₂ : HwBytes}
    (hk₁ : k₁.length = 32) (hk₂ : k₂.length = 32)
    (h₂ : (hmacWith F7 k₂ m₂).take 4 ≠ compTag4)
    (heq : (hmacWith F7 k₁ m₁).take 8 = (hmacWith F7 k₂ m₂).take 8) :
    k₁ = k₂ ∧ m₁ = m₂ := by
  have hk₁64 : k₁.length ≤ 64 := by omega
  have hk₂64 : k₂.length ≤ 64 := by omega
  have hin₂ : (sha256With F7 (kblk k₂ 0x36 ++ m₂)).take 4 ≠ compTag4 :=
    hmac_inner_untagged k₂ m₂ hk₂64 h₂
  rw [hmacWith_eq k₁ m₁ hk₁64] at heq
  rw [hmacWith_eq k₂ m₂ hk₂64] at h₂ heq
  have hout_eq := sha256With_take8_inj_of_untagged h₂ heq
  have hx₁ := kblk_length k₁ 0x5c hk₁64
  have hx₂ := kblk_length k₂ 0x5c hk₂64
  have hkb_eq : kblk k₁ 0x5c = kblk k₂ 0x5c := by
    have := congrArg (List.take 64) hout_eq
    rwa [List.take_left' hx₁, List.take_left' hx₂] at this
  have hk_eq : k₁ = k₂ := by
    have hpad := congrArg (fun l : HwBytes => (l.map (· ^^^ (0x5c : BitVec 8))).take 32) hkb_eq
    have hsimp : ∀ k : HwBytes, k.length = 32 →
        ((kblk k 0x5c).map (· ^^^ (0x5c : BitVec 8))).take 32 = k := by
      intro k hk
      unfold kblk
      rw [List.map_append, List.map_append, map_xor_xor, List.take_left' hk]
    rwa [hsimp k₁ hk₁, hsimp k₂ hk₂] at hpad
  have hin_eq : sha256With F7 (kblk k₁ 0x36 ++ m₁) = sha256With F7 (kblk k₂ 0x36 ++ m₂) := by
    have := congrArg (List.drop 64) hout_eq
    rwa [List.drop_left' hx₁, List.drop_left' hx₂] at this
  have hm_full := sha256With_take8_inj_of_untagged hin₂ (congrArg (List.take 8) hin_eq)
  have hy₁ := kblk_length k₁ 0x36 hk₁64
  have hy₂ := kblk_length k₂ 0x36 hk₂64
  have hm_eq : m₁ = m₂ := by
    have := congrArg (List.drop 64) hm_full
    rwa [List.drop_left' hy₁, List.drop_left' hy₂] at this
  exact ⟨hk_eq, hm_eq⟩

end Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003Laws
