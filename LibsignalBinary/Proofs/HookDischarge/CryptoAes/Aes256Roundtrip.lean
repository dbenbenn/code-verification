/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Spec.Aes256
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession
import LibsignalBinary.Proofs.CryptoGames.AEAD.CBCProof.CBCDec

/-!
# Roundtrip Proofs for FIPS 197 AES-256 and AES-256-CBC (`CryptoAes.Aes256Roundtrip`)

Proves `0-sorry`, `bv_decide`-free inversion laws for `Spec.Aes256`:
- `aes256InvCipher_aes256Cipher` and `aes256Cipher_aes256InvCipher` on 16-byte `State`s;
- `aes256Dec_aes256Enc` and `aes256Enc_aes256Dec` on little-endian `CBC.AesKey` / `CBC.Block`;
- `aesCbcDecrypt_aes256Enc` and `aesCbcEncrypt_of_aesCbcDecrypt` for PKCS#7-padded AES-256-CBC
  (discharging both `aes_cbc_decrypt_inverts_encrypt` and `aes_cbc_encrypt_of_decrypt`).
-/

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.Aes256Roundtrip

open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Spec.Aes256
  (State Word sbox invSbox xtime gfMul subBytes invSubBytes shiftRows invShiftRows
   mixColumn mixColumns invMixColumn invMixColumns addRoundKey xorWord
   expandKey256 roundKey aes256Cipher aes256InvCipher aes256Enc aes256Dec)
open CryptoGames.CBC
  (AesKey Block Plain cbcEncrypt cbcDecryptBlocks cbcDecRaw cbcPkcs7EncryptOnly cbcScheme
   chunks16 pkcs7Unpad pkcs7Bytes pkcs7Blocks padLen nBlocks blockToBytesLE bytesToBlock
   bytesToBlock_blockToBytesLE blockToBytesLE_bytesToBlock chunks16_flatMap
   cbcDecRaw_correct)
open CryptoGames.LibsignalSession (aesCbcEncrypt aesCbcDecrypt)

/-! ## Length Invariants and 16-Byte State Extensionality -/

@[simp] theorem length_subBytes (s : State) : (subBytes s).length = s.length := by
  simp [subBytes]

@[simp] theorem length_invSubBytes (s : State) : (invSubBytes s).length = s.length := by
  simp [invSubBytes]

@[simp] theorem length_shiftRows (s : State) : (shiftRows s).length = 16 := by
  simp [shiftRows]

@[simp] theorem length_invShiftRows (s : State) : (invShiftRows s).length = 16 := by
  simp [invShiftRows]

@[simp] theorem length_mixColumns (s : State) : (mixColumns s).length = 16 := by
  simp [mixColumns, mixColumn, List.ofFn_succ, List.ofFn_zero]

@[simp] theorem length_invMixColumns (s : State) : (invMixColumns s).length = 16 := by
  simp [invMixColumns, invMixColumn, List.ofFn_succ, List.ofFn_zero]

@[simp] theorem length_addRoundKey (s rk : State) : (addRoundKey s rk).length = 16 := by
  simp [addRoundKey]

@[simp] theorem length_roundKey (w : List Word) (r : Nat) : (roundKey w r).length = 16 := by
  simp [roundKey]

@[simp] theorem length_aes256Cipher (key : List (BitVec 8)) (input : State) :
    (aes256Cipher key input).length = 16 := by
  simp [aes256Cipher]

@[simp] theorem length_aes256InvCipher (key : List (BitVec 8)) (input : State) :
    (aes256InvCipher key input).length = 16 := by
  simp [aes256InvCipher]

private theorem getD_ofFn {α : Type} {n : Nat} (f : Fin n → α) (d : α) (i : Nat) (hi : i < n) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  have hlen : i < (List.ofFn f).length := by simpa using hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
  simp

private theorem state_eq_of_getD {s t : State} (hs : s.length = 16) (ht : t.length = 16)
    (h : ∀ i : Fin 16, s.getD i.val 0#8 = t.getD i.val 0#8) : s = t := by
  apply List.ext_getElem (by omega)
  intro i hi1 hi2
  have hi : i < 16 := by omega
  have hsi : s.getD i 0#8 = s[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1]; rfl
  have hti : t.getD i 0#8 = t[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2]; rfl
  exact hsi.symm.trans ((h ⟨i, hi⟩).trans hti)

private theorem state_eta16 {s : State} (hs : s.length = 16) :
    s = [s.getD 0 0#8, s.getD 1 0#8, s.getD 2 0#8, s.getD 3 0#8,
         s.getD 4 0#8, s.getD 5 0#8, s.getD 6 0#8, s.getD 7 0#8,
         s.getD 8 0#8, s.getD 9 0#8, s.getD 10 0#8, s.getD 11 0#8,
         s.getD 12 0#8, s.getD 13 0#8, s.getD 14 0#8, s.getD 15 0#8] := by
  apply state_eq_of_getD hs rfl
  intro ⟨i, hi⟩
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _
  | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ => rfl
  | _ + 16, hi => omega

/-! ## S-Box, `SubBytes`, `ShiftRows`, and `AddRoundKey` Inverses -/

theorem invSbox_sbox : ∀ b : BitVec 8, invSbox (sbox b) = b := by decide

theorem sbox_invSbox : ∀ b : BitVec 8, sbox (invSbox b) = b := by decide

theorem invSubBytes_subBytes (s : State) : invSubBytes (subBytes s) = s := by
  simp [invSubBytes, subBytes, Function.comp_def, invSbox_sbox]

theorem subBytes_invSubBytes (s : State) : subBytes (invSubBytes s) = s := by
  simp [subBytes, invSubBytes, Function.comp_def, sbox_invSbox]

theorem invShiftRows_shiftRows {s : State} (hs : s.length = 16) :
    invShiftRows (shiftRows s) = s := by
  rw [state_eta16 hs]
  rfl

theorem shiftRows_invShiftRows {s : State} (hs : s.length = 16) :
    shiftRows (invShiftRows s) = s := by
  rw [state_eta16 hs]
  rfl

private theorem xor8_cancel_right (a b : BitVec 8) : (a ^^^ b) ^^^ b = a := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem addRoundKey_involutive {s : State} (hs : s.length = 16) (rk : State) :
    addRoundKey (addRoundKey s rk) rk = s := by
  apply state_eq_of_getD (length_addRoundKey _ _) hs
  intro ⟨i, hi⟩
  simp only [addRoundKey]
  rw [getD_ofFn _ _ i hi, getD_ofFn _ _ i hi, xor8_cancel_right]

/-! ## $\mathrm{GF}(2^8)$ Linearity and `MixColumns` / `InvMixColumns` Inverses -/

private theorem xor8_4 (a b c d : BitVec 8) :
    (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  ext k hk
  simp only [BitVec.getElem_xor]
  cases a[k] <;> cases b[k] <;> cases c[k] <;> cases d[k] <;> rfl

private theorem xor8_8 (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 8) :
    (a0 ^^^ b0) ^^^ (a1 ^^^ b1) ^^^ (a2 ^^^ b2) ^^^ (a3 ^^^ b3) =
      (a0 ^^^ a1 ^^^ a2 ^^^ a3) ^^^ (b0 ^^^ b1 ^^^ b2 ^^^ b3) := by
  ext k hk
  simp only [BitVec.getElem_xor]
  cases a0[k] <;> cases a1[k] <;> cases a2[k] <;> cases a3[k] <;>
    cases b0[k] <;> cases b1[k] <;> cases b2[k] <;> cases b3[k] <;> rfl

private theorem xtime_xor (a b : BitVec 8) : xtime (a ^^^ b) = xtime a ^^^ xtime b := by
  unfold xtime
  rw [BitVec.msb_xor, BitVec.shiftLeft_xor_distrib]
  cases a.msb <;> cases b.msb <;> simp
  · rw [BitVec.xor_assoc]
  · ext k hk
    simp only [BitVec.getElem_xor]
    cases (a <<< 1)[k] <;> cases (b <<< 1)[k] <;> cases (0x1b#8)[k] <;> rfl
  · rw [xor8_4, BitVec.xor_self, BitVec.xor_zero]

private def gfStep (p : Bool) (st : BitVec 8 × BitVec 8) : BitVec 8 × BitVec 8 :=
  (if p then st.1 ^^^ st.2 else st.1, xtime st.2)

private theorem gfStep_xor (p : Bool) (a1 a2 c1 c2 : BitVec 8) :
    gfStep p (a1 ^^^ a2, c1 ^^^ c2) =
      ((gfStep p (a1, c1)).1 ^^^ (gfStep p (a2, c2)).1,
       (gfStep p (a1, c1)).2 ^^^ (gfStep p (a2, c2)).2) := by
  cases p <;> simp [gfStep, xtime_xor, xor8_4]

private theorem foldl_gfStep_xor (n : Nat) (f : Fin n → Bool) (a1 a2 c1 c2 : BitVec 8) :
    Fin.foldl n (fun st i => gfStep (f i) st) (a1 ^^^ a2, c1 ^^^ c2) =
      ((Fin.foldl n (fun st i => gfStep (f i) st) (a1, c1)).1 ^^^
        (Fin.foldl n (fun st i => gfStep (f i) st) (a2, c2)).1,
       (Fin.foldl n (fun st i => gfStep (f i) st) (a1, c1)).2 ^^^
        (Fin.foldl n (fun st i => gfStep (f i) st) (a2, c2)).2) := by
  induction n generalizing a1 a2 c1 c2 with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    simp only [Fin.foldl_succ, gfStep_xor]
    exact ih (fun i => f i.succ) _ _ _ _

theorem gfMul_xor_right (c a b : BitVec 8) : gfMul c (a ^^^ b) = gfMul c a ^^^ gfMul c b := by
  have h := congrArg Prod.fst
    (foldl_gfStep_xor 8 (fun i => c.getLsbD i.val) 0#8 0#8 a b)
  simpa [gfMul, gfStep] using h

private def mixCol4 (w : Word) : Word :=
  mixColumn (w.getD 0 0#8) (w.getD 1 0#8) (w.getD 2 0#8) (w.getD 3 0#8)

private def invMixCol4 (w : Word) : Word :=
  invMixColumn (w.getD 0 0#8) (w.getD 1 0#8) (w.getD 2 0#8) (w.getD 3 0#8)

private theorem mixCol4_xorWord (u v : Word) :
    mixCol4 (xorWord u v) = xorWord (mixCol4 u) (mixCol4 v) := by
  simp only [mixCol4, mixColumn, xorWord, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ,
    Nat.reduceAdd, List.getD_cons_zero, List.getD_cons_succ, gfMul_xor_right]
  refine congrArg₂ List.cons (xor8_8 _ _ _ _ _ _ _ _)
    (congrArg₂ List.cons (xor8_8 _ _ _ _ _ _ _ _)
      (congrArg₂ List.cons (xor8_8 _ _ _ _ _ _ _ _)
        (congrArg₂ List.cons (xor8_8 _ _ _ _ _ _ _ _) rfl)))

private theorem invMixCol4_xorWord (u v : Word) :
    invMixCol4 (xorWord u v) = xorWord (invMixCol4 u) (invMixCol4 v) := by
  simp only [invMixCol4, invMixColumn, xorWord, List.ofFn_succ, List.ofFn_zero, Fin.val_zero,
    Fin.val_succ, Nat.reduceAdd, List.getD_cons_zero, List.getD_cons_succ, gfMul_xor_right]
  refine congrArg₂ List.cons (xor8_8 _ _ _ _ _ _ _ _)
    (congrArg₂ List.cons (xor8_8 _ _ _ _ _ _ _ _)
      (congrArg₂ List.cons (xor8_8 _ _ _ _ _ _ _ _)
        (congrArg₂ List.cons (xor8_8 _ _ _ _ _ _ _ _) rfl)))

private theorem word4_decomp (a b c d : BitVec 8) :
    [a, b, c, d] = xorWord
      (xorWord [a, 0#8, 0#8, 0#8] [0#8, b, 0#8, 0#8])
      (xorWord [0#8, 0#8, c, 0#8] [0#8, 0#8, 0#8, d]) := by
  simp [xorWord, List.ofFn_succ, List.ofFn_zero]

private theorem byte_bit_decomp : ∀ b : BitVec 8,
    b = (((if b.getLsbD 0 then 0x01#8 else 0#8) ^^^ (if b.getLsbD 1 then 0x02#8 else 0#8)) ^^^
         ((if b.getLsbD 2 then 0x04#8 else 0#8) ^^^ (if b.getLsbD 3 then 0x08#8 else 0#8))) ^^^
        (((if b.getLsbD 4 then 0x10#8 else 0#8) ^^^ (if b.getLsbD 5 then 0x20#8 else 0#8)) ^^^
         ((if b.getLsbD 6 then 0x40#8 else 0#8) ^^^ (if b.getLsbD 7 then 0x80#8 else 0#8))) := by
  decide

private theorem word_linear_of_basis (F G : BitVec 8 → Word)
    (hF0 : F 0#8 = [0#8, 0#8, 0#8, 0#8]) (hG0 : G 0#8 = [0#8, 0#8, 0#8, 0#8])
    (hFx : ∀ a b, F (a ^^^ b) = xorWord (F a) (F b))
    (hGx : ∀ a b, G (a ^^^ b) = xorWord (G a) (G b))
    (hb : ∀ j : Fin 8, F (0x01#8 <<< j.val) = G (0x01#8 <<< j.val)) (b : BitVec 8) :
    F b = G b := by
  have hbit : ∀ (p : Bool) (j : Fin 8),
      F (if p then 0x01#8 <<< j.val else 0#8) = G (if p then 0x01#8 <<< j.val else 0#8) := by
    intro p j; cases p <;> simp [hF0, hG0, hb j]
  have h0 : F (if b.getLsbD 0 then 0x01#8 else 0#8) = G (if b.getLsbD 0 then 0x01#8 else 0#8) :=
    hbit (b.getLsbD 0) ⟨0, by omega⟩
  have h1 : F (if b.getLsbD 1 then 0x02#8 else 0#8) = G (if b.getLsbD 1 then 0x02#8 else 0#8) :=
    hbit (b.getLsbD 1) ⟨1, by omega⟩
  have h2 : F (if b.getLsbD 2 then 0x04#8 else 0#8) = G (if b.getLsbD 2 then 0x04#8 else 0#8) :=
    hbit (b.getLsbD 2) ⟨2, by omega⟩
  have h3 : F (if b.getLsbD 3 then 0x08#8 else 0#8) = G (if b.getLsbD 3 then 0x08#8 else 0#8) :=
    hbit (b.getLsbD 3) ⟨3, by omega⟩
  have h4 : F (if b.getLsbD 4 then 0x10#8 else 0#8) = G (if b.getLsbD 4 then 0x10#8 else 0#8) :=
    hbit (b.getLsbD 4) ⟨4, by omega⟩
  have h5 : F (if b.getLsbD 5 then 0x20#8 else 0#8) = G (if b.getLsbD 5 then 0x20#8 else 0#8) :=
    hbit (b.getLsbD 5) ⟨5, by omega⟩
  have h6 : F (if b.getLsbD 6 then 0x40#8 else 0#8) = G (if b.getLsbD 6 then 0x40#8 else 0#8) :=
    hbit (b.getLsbD 6) ⟨6, by omega⟩
  have h7 : F (if b.getLsbD 7 then 0x80#8 else 0#8) = G (if b.getLsbD 7 then 0x80#8 else 0#8) :=
    hbit (b.getLsbD 7) ⟨7, by omega⟩
  conv_lhs => rw [byte_bit_decomp b]
  conv_rhs => rw [byte_bit_decomp b]
  simp only [hFx, hGx, h0, h1, h2, h3, h4, h5, h6, h7]

private theorem invMix_mix_e0 (b : BitVec 8) :
    invMixCol4 (mixCol4 [b, 0#8, 0#8, 0#8]) = [b, 0#8, 0#8, 0#8] :=
  word_linear_of_basis (fun x => invMixCol4 (mixCol4 [x, 0#8, 0#8, 0#8]))
    (fun x => [x, 0#8, 0#8, 0#8]) (by decide) rfl
    (fun a c => by
      have h : [a ^^^ c, 0#8, 0#8, 0#8] = xorWord [a, 0#8, 0#8, 0#8] [c, 0#8, 0#8, 0#8] := by
        simp [xorWord, List.ofFn_succ, List.ofFn_zero]
      rw [h, mixCol4_xorWord, invMixCol4_xorWord])
    (fun a c => by simp [xorWord, List.ofFn_succ, List.ofFn_zero]) (by decide) b

private theorem invMix_mix_e1 (b : BitVec 8) :
    invMixCol4 (mixCol4 [0#8, b, 0#8, 0#8]) = [0#8, b, 0#8, 0#8] :=
  word_linear_of_basis (fun x => invMixCol4 (mixCol4 [0#8, x, 0#8, 0#8]))
    (fun x => [0#8, x, 0#8, 0#8]) (by decide) rfl
    (fun a c => by
      have h : [0#8, a ^^^ c, 0#8, 0#8] = xorWord [0#8, a, 0#8, 0#8] [0#8, c, 0#8, 0#8] := by
        simp [xorWord, List.ofFn_succ, List.ofFn_zero]
      rw [h, mixCol4_xorWord, invMixCol4_xorWord])
    (fun a c => by simp [xorWord, List.ofFn_succ, List.ofFn_zero]) (by decide) b

private theorem invMix_mix_e2 (b : BitVec 8) :
    invMixCol4 (mixCol4 [0#8, 0#8, b, 0#8]) = [0#8, 0#8, b, 0#8] :=
  word_linear_of_basis (fun x => invMixCol4 (mixCol4 [0#8, 0#8, x, 0#8]))
    (fun x => [0#8, 0#8, x, 0#8]) (by decide) rfl
    (fun a c => by
      have h : [0#8, 0#8, a ^^^ c, 0#8] = xorWord [0#8, 0#8, a, 0#8] [0#8, 0#8, c, 0#8] := by
        simp [xorWord, List.ofFn_succ, List.ofFn_zero]
      rw [h, mixCol4_xorWord, invMixCol4_xorWord])
    (fun a c => by simp [xorWord, List.ofFn_succ, List.ofFn_zero]) (by decide) b

private theorem invMix_mix_e3 (b : BitVec 8) :
    invMixCol4 (mixCol4 [0#8, 0#8, 0#8, b]) = [0#8, 0#8, 0#8, b] :=
  word_linear_of_basis (fun x => invMixCol4 (mixCol4 [0#8, 0#8, 0#8, x]))
    (fun x => [0#8, 0#8, 0#8, x]) (by decide) rfl
    (fun a c => by
      have h : [0#8, 0#8, 0#8, a ^^^ c] = xorWord [0#8, 0#8, 0#8, a] [0#8, 0#8, 0#8, c] := by
        simp [xorWord, List.ofFn_succ, List.ofFn_zero]
      rw [h, mixCol4_xorWord, invMixCol4_xorWord])
    (fun a c => by simp [xorWord, List.ofFn_succ, List.ofFn_zero]) (by decide) b

private theorem mix_invMix_e0 (b : BitVec 8) :
    mixCol4 (invMixCol4 [b, 0#8, 0#8, 0#8]) = [b, 0#8, 0#8, 0#8] :=
  word_linear_of_basis (fun x => mixCol4 (invMixCol4 [x, 0#8, 0#8, 0#8]))
    (fun x => [x, 0#8, 0#8, 0#8]) (by decide) rfl
    (fun a c => by
      have h : [a ^^^ c, 0#8, 0#8, 0#8] = xorWord [a, 0#8, 0#8, 0#8] [c, 0#8, 0#8, 0#8] := by
        simp [xorWord, List.ofFn_succ, List.ofFn_zero]
      rw [h, invMixCol4_xorWord, mixCol4_xorWord])
    (fun a c => by simp [xorWord, List.ofFn_succ, List.ofFn_zero]) (by decide) b

private theorem mix_invMix_e1 (b : BitVec 8) :
    mixCol4 (invMixCol4 [0#8, b, 0#8, 0#8]) = [0#8, b, 0#8, 0#8] :=
  word_linear_of_basis (fun x => mixCol4 (invMixCol4 [0#8, x, 0#8, 0#8]))
    (fun x => [0#8, x, 0#8, 0#8]) (by decide) rfl
    (fun a c => by
      have h : [0#8, a ^^^ c, 0#8, 0#8] = xorWord [0#8, a, 0#8, 0#8] [0#8, c, 0#8, 0#8] := by
        simp [xorWord, List.ofFn_succ, List.ofFn_zero]
      rw [h, invMixCol4_xorWord, mixCol4_xorWord])
    (fun a c => by simp [xorWord, List.ofFn_succ, List.ofFn_zero]) (by decide) b

private theorem mix_invMix_e2 (b : BitVec 8) :
    mixCol4 (invMixCol4 [0#8, 0#8, b, 0#8]) = [0#8, 0#8, b, 0#8] :=
  word_linear_of_basis (fun x => mixCol4 (invMixCol4 [0#8, 0#8, x, 0#8]))
    (fun x => [0#8, 0#8, x, 0#8]) (by decide) rfl
    (fun a c => by
      have h : [0#8, 0#8, a ^^^ c, 0#8] = xorWord [0#8, 0#8, a, 0#8] [0#8, 0#8, c, 0#8] := by
        simp [xorWord, List.ofFn_succ, List.ofFn_zero]
      rw [h, invMixCol4_xorWord, mixCol4_xorWord])
    (fun a c => by simp [xorWord, List.ofFn_succ, List.ofFn_zero]) (by decide) b

private theorem mix_invMix_e3 (b : BitVec 8) :
    mixCol4 (invMixCol4 [0#8, 0#8, 0#8, b]) = [0#8, 0#8, 0#8, b] :=
  word_linear_of_basis (fun x => mixCol4 (invMixCol4 [0#8, 0#8, 0#8, x]))
    (fun x => [0#8, 0#8, 0#8, x]) (by decide) rfl
    (fun a c => by
      have h : [0#8, 0#8, 0#8, a ^^^ c] = xorWord [0#8, 0#8, 0#8, a] [0#8, 0#8, 0#8, c] := by
        simp [xorWord, List.ofFn_succ, List.ofFn_zero]
      rw [h, invMixCol4_xorWord, mixCol4_xorWord])
    (fun a c => by simp [xorWord, List.ofFn_succ, List.ofFn_zero]) (by decide) b

private theorem invMixCol4_mixColumn (a b c d : BitVec 8) :
    invMixCol4 (mixColumn a b c d) = [a, b, c, d] := by
  change invMixCol4 (mixCol4 [a, b, c, d]) = [a, b, c, d]
  conv_lhs => rw [word4_decomp a b c d]
  rw [mixCol4_xorWord, mixCol4_xorWord, mixCol4_xorWord,
      invMixCol4_xorWord, invMixCol4_xorWord, invMixCol4_xorWord,
      invMix_mix_e0, invMix_mix_e1, invMix_mix_e2, invMix_mix_e3, ← word4_decomp a b c d]

private theorem mixCol4_invMixColumn (a b c d : BitVec 8) :
    mixCol4 (invMixColumn a b c d) = [a, b, c, d] := by
  change mixCol4 (invMixCol4 [a, b, c, d]) = [a, b, c, d]
  conv_lhs => rw [word4_decomp a b c d]
  rw [invMixCol4_xorWord, invMixCol4_xorWord, invMixCol4_xorWord,
      mixCol4_xorWord, mixCol4_xorWord, mixCol4_xorWord,
      mix_invMix_e0, mix_invMix_e1, mix_invMix_e2, mix_invMix_e3, ← word4_decomp a b c d]

private theorem invMixColumns_mixColumns_16
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : BitVec 8) :
    invMixColumns (mixColumns
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15]) =
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] := by
  have hc0 := invMixCol4_mixColumn a0 a1 a2 a3
  have hc1 := invMixCol4_mixColumn a4 a5 a6 a7
  have hc2 := invMixCol4_mixColumn a8 a9 a10 a11
  have hc3 := invMixCol4_mixColumn a12 a13 a14 a15
  simp only [invMixCol4] at hc0 hc1 hc2 hc3
  simp only [mixColumns, invMixColumns, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ,
    Nat.reduceAdd, Nat.mul_zero, List.flatten_cons, List.flatten_nil, List.append_nil]
  simp only [mixColumn, List.cons_append, List.nil_append,
    List.getD_cons_zero, List.getD_cons_succ] at hc0 hc1 hc2 hc3 ⊢
  rw [hc0, hc1, hc2, hc3]
  rfl

private theorem mixColumns_invMixColumns_16
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : BitVec 8) :
    mixColumns (invMixColumns
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15]) =
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] := by
  have hc0 := mixCol4_invMixColumn a0 a1 a2 a3
  have hc1 := mixCol4_invMixColumn a4 a5 a6 a7
  have hc2 := mixCol4_invMixColumn a8 a9 a10 a11
  have hc3 := mixCol4_invMixColumn a12 a13 a14 a15
  simp only [mixCol4] at hc0 hc1 hc2 hc3
  simp only [invMixColumns, mixColumns, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ,
    Nat.reduceAdd, Nat.mul_zero, List.flatten_cons, List.flatten_nil, List.append_nil]
  simp only [invMixColumn, List.cons_append, List.nil_append,
    List.getD_cons_zero, List.getD_cons_succ] at hc0 hc1 hc2 hc3 ⊢
  rw [hc0, hc1, hc2, hc3]
  rfl

theorem invMixColumns_mixColumns {s : State} (hs : s.length = 16) :
    invMixColumns (mixColumns s) = s := by
  rw [state_eta16 hs]
  exact invMixColumns_mixColumns_16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem mixColumns_invMixColumns {s : State} (hs : s.length = 16) :
    mixColumns (invMixColumns s) = s := by
  rw [state_eta16 hs]
  exact mixColumns_invMixColumns_16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-! ## 14-Round `aes256Cipher` / `aes256InvCipher` Roundtrip -/

private theorem invStep_encStep (s rk : State) :
    invMixColumns (addRoundKey (invSubBytes (invShiftRows
      (shiftRows (subBytes (addRoundKey (mixColumns (shiftRows (subBytes s))) rk))))) rk) =
      shiftRows (subBytes s) := by
  rw [invShiftRows_shiftRows (by simp), invSubBytes_subBytes,
      addRoundKey_involutive (by simp), invMixColumns_mixColumns (by simp)]

private theorem encStep_invStep (d rk : State) :
    addRoundKey (mixColumns (shiftRows (subBytes
      (invSubBytes (invShiftRows (invMixColumns (addRoundKey (invSubBytes (invShiftRows d)) rk))))))) rk =
      invSubBytes (invShiftRows d) := by
  rw [subBytes_invSubBytes, shiftRows_invShiftRows (by simp),
      mixColumns_invMixColumns (by simp), addRoundKey_involutive (by simp)]

/-- FIPS 197 `InvCipher` inverts `Cipher` for every key and 16-byte state. -/
theorem aes256InvCipher_aes256Cipher (key : List (BitVec 8)) {input : State}
    (hin : input.length = 16) :
    aes256InvCipher key (aes256Cipher key input) = input := by
  unfold aes256InvCipher aes256Cipher
  dsimp only
  simp only [Fin.foldl_succ, Fin.foldl_zero, Fin.val_zero, Fin.val_succ]
  rw [addRoundKey_involutive (by simp)]
  repeat rw [invStep_encStep]
  rw [invShiftRows_shiftRows (by simp), invSubBytes_subBytes, addRoundKey_involutive hin]

/-- FIPS 197 `Cipher` inverts `InvCipher` for every key and 16-byte state. -/
theorem aes256Cipher_aes256InvCipher (key : List (BitVec 8)) {input : State}
    (hin : input.length = 16) :
    aes256Cipher key (aes256InvCipher key input) = input := by
  unfold aes256Cipher aes256InvCipher
  dsimp only
  simp only [Fin.foldl_succ, Fin.foldl_zero, Fin.val_zero, Fin.val_succ]
  rw [addRoundKey_involutive (by simp)]
  repeat rw [encStep_invStep]
  rw [subBytes_invSubBytes, shiftRows_invShiftRows (by simp), addRoundKey_involutive hin]

/-! ## Little-Endian `CBC.Block` / `CBC.AesKey` Roundtrip -/

/-- `aes256Dec k` inverts `aes256Enc k` on all 256-bit keys and 128-bit blocks. -/
@[simp]
theorem aes256Dec_aes256Enc (k : AesKey) (b : Block) :
    aes256Dec k (aes256Enc k b) = b := by
  have hlen : (blockToBytesLE b).length = 16 := by simp [blockToBytesLE]
  unfold aes256Dec aes256Enc
  rw [blockToBytesLE_bytesToBlock _ (length_aes256Cipher _ _),
      aes256InvCipher_aes256Cipher _ hlen, bytesToBlock_blockToBytesLE]

/-- `aes256Enc k` inverts `aes256Dec k` on all 256-bit keys and 128-bit blocks. -/
@[simp]
theorem aes256Enc_aes256Dec (k : AesKey) (b : Block) :
    aes256Enc k (aes256Dec k b) = b := by
  have hlen : (blockToBytesLE b).length = 16 := by simp [blockToBytesLE]
  unfold aes256Enc aes256Dec
  rw [blockToBytesLE_bytesToBlock _ (length_aes256InvCipher _ _),
      aes256Cipher_aes256InvCipher _ hlen, bytesToBlock_blockToBytesLE]

/-! ## PKCS#7-Padded AES-256-CBC Roundtrip (`aesCbcDecrypt` / `aesCbcEncrypt`) -/

/-- `aesCbcDecrypt aes256Dec` recovers every plaintext encrypted by `aesCbcEncrypt aes256Enc`. -/
theorem aesCbcDecrypt_aes256Enc (key : AesKey) (iv : Block) (ptext : List (BitVec 8)) :
    aesCbcDecrypt aes256Dec key iv (aesCbcEncrypt aes256Enc key iv ptext) = some ptext := by
  unfold aesCbcDecrypt aesCbcEncrypt cbcPkcs7EncryptOnly cbcScheme
  exact cbcDecRaw_correct aes256Dec_aes256Enc key iv ⟨ptext, rfl⟩

private theorem all_beq_eq_replicate {bs : List (BitVec 8)} {x : BitVec 8}
    (h : bs.all (· == x) = true) : bs = List.replicate bs.length x := by
  induction bs with
  | nil => rfl
  | cons b tl ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl, htl⟩
    rw [List.length_cons, List.replicate_succ, ← ih htl]

private theorem cbcEncrypt_cbcDecryptBlocks {f g : Block → Block} (hfg : ∀ x, f (g x) = x)
    (prev : Block) (cs : List Block) :
    ∀ {n : Nat} (V : List.Vector Block n), V.toList = cbcDecryptBlocks g prev cs →
      (cbcEncrypt f prev V).toList = cs := by
  induction cs generalizing prev with
  | nil =>
    intro n V hV
    cases n with
    | zero => simp [cbcEncrypt]
    | succ n =>
      have hlen := V.toList_length
      rw [hV] at hlen
      simp [cbcDecryptBlocks] at hlen
  | cons c cs ih =>
    intro n V hV
    cases n with
    | zero =>
      have hlen := V.toList_length
      rw [hV] at hlen
      simp [cbcDecryptBlocks] at hlen
    | succ n =>
      have hht : V.head :: V.tail.toList = V.toList := by
        rcases V with ⟨_ | ⟨v, vs⟩, hlen⟩
        · simp at hlen
        · rfl
      have hcons : V.head :: V.tail.toList = (g c ^^^ prev) :: cbcDecryptBlocks g c cs := by
        simpa [cbcDecryptBlocks] using hht.trans hV
      injection hcons with hhead htail
      have hxor : (g c ^^^ prev) ^^^ prev = g c := by
        rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
      simp only [cbcEncrypt, List.Vector.toList_cons, hhead, hxor, hfg c]
      congr 1
      exact ih c V.tail htail

private theorem ofFn_cast_len {α : Type} {m n : Nat} (h : m = n) (f : Nat → α) :
    (List.ofFn fun i : Fin m => f i.val) = (List.ofFn fun i : Fin n => f i.val) := by
  subst h; rfl

private theorem flatMap_chunks16_of_dvd {bs : List (BitVec 8)} (h : bs.length % 16 = 0) :
    (chunks16 bs).flatMap blockToBytesLE = bs := by
  have hk : bs.length = 16 * (bs.length / 16) := by omega
  have go : ∀ (k : Nat) (xs : List (BitVec 8)), xs.length = 16 * k →
       (List.ofFn fun i : Fin k => bytesToBlock ((xs.drop (16 * i.val)).take 16)).flatMap
        blockToBytesLE = xs := by
    intro k
    induction k with
    | zero =>
      intro xs hxs
      have h0 : xs.length = 0 := by omega
      rw [List.eq_nil_of_length_eq_zero h0]; rfl
    | succ k ih =>
      intro xs hxs
      rw [List.ofFn_succ, List.flatMap_cons]
      simp only [Fin.val_zero, Nat.mul_zero, List.drop_zero, Fin.val_succ]
      rw [blockToBytesLE_bytesToBlock (xs.take 16) (by simp [hxs])]
      have hrest : (List.ofFn fun i : Fin k =>
          bytesToBlock ((xs.drop (16 * (i.val + 1))).take 16)) =
        List.ofFn fun i : Fin k =>
          bytesToBlock (((xs.drop 16).drop (16 * i.val)).take 16) := by
        congr 1; ext i; rw [List.drop_drop]
        have : 16 * (i.val + 1) = 16 + 16 * i.val := by omega
        rw [this]
      rw [hrest, ih (xs.drop 16) (by simp [hxs]; omega), List.take_append_drop]
  exact go (bs.length / 16) bs hk

private theorem length_cbcDecryptBlocks (g : Block → Block) (prev : Block) (cs : List Block) :
    (cbcDecryptBlocks g prev cs).length = cs.length := by
  induction cs generalizing prev with
  | nil => rfl
  | cons c cs ih => simp [cbcDecryptBlocks, ih]

private theorem length_flatMap_blockToBytesLE' (bs : List Block) :
    (bs.flatMap blockToBytesLE).length = 16 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hb : (blockToBytesLE b).length = 16 := by simp [blockToBytesLE]
    simp [List.flatMap_cons, hb, ih]
    omega

/-- Whenever `aesCbcDecrypt aes256Dec` accepts `ctext` with output `ptext`, re-encrypting `ptext`
under `(key, iv)` with `aesCbcEncrypt aes256Enc` yields `ctext` (`aes_cbc_encrypt_of_decrypt`). -/
theorem aesCbcEncrypt_of_aesCbcDecrypt {key : AesKey} {iv : Block}
    {ctext ptext : List (BitVec 8)}
    (hdec : aesCbcDecrypt aes256Dec key iv ctext = some ptext) :
    aesCbcEncrypt aes256Enc key iv ptext = ctext := by
  unfold aesCbcDecrypt cbcDecRaw at hdec
  split at hdec
  · simp at hdec
  · rename_i hct
    simp only [not_or, ne_eq, not_not] at hct
    rcases hct with ⟨hct_ne, hct_mod⟩
    set decBlocks := cbcDecryptBlocks (aes256Dec key) iv (chunks16 ctext)
    set bs := decBlocks.flatMap blockToBytesLE
    have hct_pos : 0 < ctext.length := List.length_pos_iff.mpr hct_ne
    have hm_pos : 1 ≤ ctext.length / 16 := by omega
    have hbs_len : bs.length = 16 * (ctext.length / 16) := by
      rw [length_flatMap_blockToBytesLE', length_cbcDecryptBlocks]
      simp [chunks16]
    unfold pkcs7Unpad at hdec
    cases hlast : bs.getLast? with
    | none => simp [hlast] at hdec
    | some last =>
      simp only [hlast] at hdec
      split at hdec
      · simp at hdec
      · rename_i hbounds
        split at hdec
        · rename_i hall
          injection hdec with hpt_eq
          subst hpt_eq
          have hn1 : 1 ≤ last.toNat := by omega
          have hn16 : last.toNat ≤ 16 := by omega
          have hn_le : last.toNat ≤ bs.length := by omega
          have hpt_len : (bs.take (bs.length - last.toNat)).length = bs.length - last.toNat := by
            simp
          have hpad : padLen (bs.take (bs.length - last.toNat)).length = last.toNat := by
            rw [hpt_len]; unfold padLen; omega
          have hnBlocks : nBlocks (bs.take (bs.length - last.toNat)).length = ctext.length / 16 := by
            rw [hpt_len]; unfold nBlocks; omega
          have hdrop_len : (bs.drop (bs.length - last.toNat)).length = last.toNat := by
            simp; omega
          have hdrop_rep : bs.drop (bs.length - last.toNat) = List.replicate last.toNat last := by
            have := all_beq_eq_replicate hall
            rwa [hdrop_len] at this
          have hlast_bv : BitVec.ofNat 8 last.toNat = last := by simp
          have hpkcs7Bytes :
              pkcs7Bytes ⟨bs.take (bs.length - last.toNat), rfl⟩ = bs := by
            simp only [pkcs7Bytes, hpad, hlast_bv, ← hdrop_rep]
            exact List.take_append_drop (bs.length - last.toNat) bs
          have hblocks_list :
              (pkcs7Blocks ⟨bs.take (bs.length - last.toNat), rfl⟩).toList = decBlocks := by
            unfold pkcs7Blocks
            rw [List.Vector.toList_ofFn, hpkcs7Bytes]
            have hdiv : nBlocks (bs.take (bs.length - last.toNat)).length = bs.length / 16 := by
              omega
            have hfn :
                (List.ofFn fun i : Fin (nBlocks (bs.take (bs.length - last.toNat)).length) =>
                  bytesToBlock ((bs.drop (16 * i.val)).take 16)) = chunks16 bs :=
              ofFn_cast_len hdiv (fun k => bytesToBlock ((bs.drop (16 * k)).take 16))
            rw [hfn]
            exact chunks16_flatMap decBlocks
          unfold aesCbcEncrypt cbcPkcs7EncryptOnly cbcScheme
          dsimp only
          have hcbc :
              (cbcEncrypt (aes256Enc key) iv
                (pkcs7Blocks ⟨bs.take (bs.length - last.toNat), rfl⟩)).toList =
                chunks16 ctext :=
            cbcEncrypt_cbcDecryptBlocks (aes256Enc_aes256Dec key) iv (chunks16 ctext) _
              hblocks_list
          rw [hcbc]
          exact flatMap_chunks16_of_dvd hct_mod
        · simp at hdec

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.Aes256Roundtrip
