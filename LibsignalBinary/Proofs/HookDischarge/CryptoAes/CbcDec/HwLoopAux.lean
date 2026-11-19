/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import ProofLib.SepLogic.WP
public import ProofLib.StdStartup.MemOps
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Spec.Aes256
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDec
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDecPar17
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.BV.Bits
import ProofLib.Hoare.Model
import ProofLib.SepLogic.Bytes
import ProofLib.SepLogic.Model
import ProofLib.SepLogic.Region
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.CryptoGames.AEAD.CBCProof.CBCDec
import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Pure.CipherEquiv

/-!
# Shared Arithmetic, Pure CBC Chaining & Call Helpers (`CbcDec.HwLoopAux`)
-/

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.HwLoopAux

open Arm64 ProofLib SepProp
open ProofLib.StdStartup (hasInstrs)
open CryptoGames.CBC
  (Block bytesToBlock blockToBytesLE blockToBytesLE_bytesToBlock chunks16 cbcDecryptBlocks)
open CryptoGames.HKDF (bytesToKey32)
open LibsignalBinary.Heap (AllocCallPreserved VmPreserved)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (PureStepPreserved pureStepProj hasInstrs_prefix)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
  (bytesToU128LE u128ToBytesLE armv8ExpandKey armv8InvExpandedKeys
   armv8Decrypt15 armv8DecryptPar17 blocks17Bytes roundKeys15At)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDec (decrypt15InplaceSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDecPar17
  (decryptPar17InplaceBytesSpec bytesToBlocks17 Par17Anchor)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.BlockDecPar17Aux
  (blocks17Bytes_bytesToBlocks17)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Pure.CipherEquiv
  (u128ToBytesLE_armv8Decrypt15_bytes blocks17Bytes_armv8DecryptPar17_of_bytes)

attribute [local irreducible]
  Spec.Aes256.aes256Dec armv8ExpandKey armv8InvExpandedKeys
  armv8Decrypt15 armv8DecryptPar17 blocks17Bytes bytesToBlocks17

public section

/-! ## 1. Segment-Stepping, Magic Division by `272` & `BitVec 64` Arithmetic -/

theorem hasInstrs_step {P : Program} {pc1 pc2 : BitVec 64} {xs ys : List Instr}
    (h : hasInstrs P pc1 (xs ++ ys))
    (hoff : pc1 + BitVec.ofNat 64 (4 * xs.length) = pc2) :
    hasInstrs P pc1 xs ∧ hasInstrs P pc2 ys := by
  refine ⟨hasInstrs_prefix h, fun i hi => ?_⟩
  have hf := h (xs.length + i) (by rw [List.length_append]; omega)
  rw [List.getElem_append_right (Nat.le_add_right _ _)] at hf
  simp only [Nat.add_sub_cancel_left] at hf
  have had : pc2 + BitVec.ofNat 64 (4 * i) = pc1 + BitVec.ofNat 64 (4 * (xs.length + i)) := by
    rw [← hoff, BitVec.add_assoc]; congr 1
    rw [← BitVec.ofNat_add]; congr 1; omega
  rwa [had]

theorem umulh_magic272_lsr8 {n : Nat} (hn : n < 2 ^ 64) :
    ((((BitVec.ofNat 64 n).zeroExtend 128 * (0xf0f0f0f0f0f0f0f1#64).zeroExtend 128) >>> 64).truncate 64) >>> 8 =
      BitVec.ofNat 64 (n / 272) := by
  apply BitVec.eq_of_toNat_eq
  have hn128 : ((BitVec.ofNat 64 n).zeroExtend 128).toNat = n := by
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  have hm128 : ((0xf0f0f0f0f0f0f0f1#64).zeroExtend 128).toNat = 0xf0f0f0f0f0f0f0f1 := rfl
  have hmul : ((BitVec.ofNat 64 n).zeroExtend 128 * (0xf0f0f0f0f0f0f0f1#64).zeroExtend 128).toNat =
      n * 0xf0f0f0f0f0f0f0f1 := by
    rw [BitVec.toNat_mul, hn128, hm128, Nat.mod_eq_of_lt (by omega)]
  have hhi : ((((BitVec.ofNat 64 n).zeroExtend 128 * (0xf0f0f0f0f0f0f0f1#64).zeroExtend 128) >>> 64).truncate 64).toNat =
      (n * 0xf0f0f0f0f0f0f0f1) / 2 ^ 64 := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, hmul, Nat.shiftRight_eq_div_pow,
        Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_ushiftRight, hhi, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmagic : 272 * 0xf0f0f0f0f0f0f0f1 = 2 ^ 72 + 16 := by decide
  omega

theorem add_lsl4_ofNat (q : Nat) :
    BitVec.ofNat 64 q + (BitVec.ofNat 64 q <<< 4) = BitVec.ofNat 64 (17 * q) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega

theorem lsl4_ofNat (q : Nat) : (BitVec.ofNat 64 q) <<< 4 = BitVec.ofNat 64 (16 * q) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega

theorem madd_272_ofNat (ptr : BitVec 64) (k : Nat) :
    ptr + BitVec.ofNat 64 k * 0x110#64 = ptr + BitVec.ofNat 64 (272 * k) := by
  congr 1; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]; omega

/-! ## 2. Pure CBC Block-Chaining & 1-Block / 17-Block Step Lemmas -/

private def cbcLastBlock (prev : Block) : List Block → Block
  | [] => prev
  | c :: cs => cbcLastBlock c cs

private theorem cbcDecryptBlocks_append (g : Block → Block) (prev : Block) (xs ys : List Block) :
    cbcDecryptBlocks g prev (xs ++ ys) =
      cbcDecryptBlocks g prev xs ++ cbcDecryptBlocks g (cbcLastBlock prev xs) ys := by
  induction xs generalizing prev with
  | nil => rfl
  | cons c xs ih => simp only [List.cons_append, cbcDecryptBlocks, cbcLastBlock, ih c]

private theorem cbcLastBlock_snoc (prev c : Block) (xs : List Block) :
    cbcLastBlock prev (xs ++ [c]) = c := by
  induction xs generalizing prev with
  | nil => rfl
  | cons x xs ih => exact ih x

/-- Active 16-byte CBC feedback block before block index `m` (`iv` at `m = 0`, else `ct[16*(m-1)..16*m)`). -/
@[expose] def cbcChainAt (iv ct : List (BitVec 8)) (m : Nat) : List (BitVec 8) :=
  if m = 0 then iv else (ct.drop (16 * (m - 1))).take 16

theorem cbcChainAt_zero (iv ct : List (BitVec 8)) : cbcChainAt iv ct 0 = iv := rfl

theorem cbcChainAt_succ (iv ct : List (BitVec 8)) (m : Nat) :
    cbcChainAt iv ct (m + 1) = (ct.drop (16 * m)).take 16 := by simp [cbcChainAt]

theorem cbcChainAt_length {iv ct : List (BitVec 8)} {m : Nat}
    (hiv : iv.length = 16) (hm : 16 * m ≤ ct.length) :
    (cbcChainAt iv ct m).length = 16 := by
  unfold cbcChainAt; split
  · exact hiv
  · rw [List.length_take, List.length_drop]; omega

/-- Raw decrypted plaintext bytes for the first `m` 16-byte ciphertext blocks. -/
@[expose] def cbcPrefixBytes (key iv ct : List (BitVec 8)) (m : Nat) : List (BitVec 8) :=
  (cbcDecryptBlocks (Spec.Aes256.aes256Dec (bytesToKey32 key)) (bytesToBlock iv)
    ((chunks16 ct).take m)).flatMap blockToBytesLE

theorem cbcPrefixBytes_zero (key iv ct : List (BitVec 8)) :
    cbcPrefixBytes key iv ct 0 = [] := by
  simp [cbcPrefixBytes, cbcDecryptBlocks]

private theorem chunks16_length (ct : List (BitVec 8)) :
    (chunks16 ct).length = ct.length / 16 := by simp [chunks16]

private theorem chunks16_take_succ {ct : List (BitVec 8)} {m : Nat} (hm : m < ct.length / 16) :
    (chunks16 ct).take (m + 1) =
      (chunks16 ct).take m ++ [bytesToBlock ((ct.drop (16 * m)).take 16)] := by
  have hm' : m < (chunks16 ct).length := by rw [chunks16_length]; exact hm
  rw [List.take_add_one, List.getElem?_eq_getElem hm', Option.toList_some]; simp [chunks16]

private theorem cbcLastBlock_chunks16_take {iv ct : List (BitVec 8)} {m : Nat}
    (hm : m ≤ ct.length / 16) :
    cbcLastBlock (bytesToBlock iv) ((chunks16 ct).take m) =
      bytesToBlock (cbcChainAt iv ct m) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [chunks16_take_succ (by omega), cbcLastBlock_snoc, cbcChainAt_succ]

private theorem cbcDecryptBlocks_length (g : Block → Block) (prev : Block) (xs : List Block) :
    (cbcDecryptBlocks g prev xs).length = xs.length := by
  induction xs generalizing prev with
  | nil => rfl
  | cons c xs ih => simp [cbcDecryptBlocks, ih c]

private theorem length_blockToBytesLE (b : Block) : (blockToBytesLE b).length = 16 := by
  simp [blockToBytesLE]

private theorem length_flatMap_blockToBytesLE (cs : List Block) :
    (cs.flatMap blockToBytesLE).length = 16 * cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [List.flatMap_cons, length_blockToBytesLE, ih]; omega

theorem cbcPrefixBytes_length {key iv ct : List (BitVec 8)} {m : Nat}
    (hm : m ≤ ct.length / 16) :
    (cbcPrefixBytes key iv ct m).length = 16 * m := by
  unfold cbcPrefixBytes
  rw [length_flatMap_blockToBytesLE, cbcDecryptBlocks_length,
      List.length_take, chunks16_length, Nat.min_eq_left hm, Nat.mul_comm]

theorem cbcPrefixBytes_full (key iv ct : List (BitVec 8)) :
    cbcPrefixBytes key iv ct (ct.length / 16) =
      (cbcDecryptBlocks (Spec.Aes256.aes256Dec (bytesToKey32 key)) (bytesToBlock iv)
        (chunks16 ct)).flatMap blockToBytesLE := by
  unfold cbcPrefixBytes; rw [← chunks16_length ct, List.take_length]

private theorem blockToBytesLE_xor (b1 b2 : Block) :
    blockToBytesLE (b1 ^^^ b2) = List.zipWith (· ^^^ ·) (blockToBytesLE b1) (blockToBytesLE b2) := by
  apply List.ext_getElem
  · simp [blockToBytesLE]
  · intro i h1 h2
    simp only [blockToBytesLE, List.getElem_zipWith, List.getElem_ofFn]
    apply BitVec.eq_of_getLsbD_eq; intro k hk; simp [hk]

private theorem zipWith_xor_blockToBytesLE (b : Block) {ps : List (BitVec 8)} (hps : ps.length = 16) :
    List.zipWith (· ^^^ ·) (blockToBytesLE b) ps =
      blockToBytesLE (b ^^^ bytesToBlock ps) := by
  rw [blockToBytesLE_xor, blockToBytesLE_bytesToBlock ps hps]

theorem zipWith_append_eq {α β γ : Type} (f : α → β → γ)
    {a1 a2 : List α} {b1 b2 : List β} (hlen : a1.length = b1.length) :
    List.zipWith f (a1 ++ a2) (b1 ++ b2) = List.zipWith f a1 b1 ++ List.zipWith f a2 b2 := by
  induction a1 generalizing b1 with
  | nil => cases b1 <;> [rfl; simp at hlen]
  | cons x xs ih =>
    cases b1 with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.cons_append, List.zipWith_cons_cons, ih hlen]

/-- 1-block hardware CBC decryption step (`decrypt::<15>` + 16-byte XOR). -/
theorem cbcPrefixBytes_step1 {key iv ct : List (BitVec 8)} {m : Nat}
    (hkey : key.length = 32) (hiv : iv.length = 16) (hm : m < ct.length / 16) :
    cbcPrefixBytes key iv ct m ++
        List.zipWith (· ^^^ ·)
          (u128ToBytesLE (armv8Decrypt15 (armv8InvExpandedKeys (armv8ExpandKey key))
            (bytesToU128LE ((ct.drop (16 * m)).take 16))))
          (cbcChainAt iv ct m) =
      cbcPrefixBytes key iv ct (m + 1) := by
  have hc0_len : ((ct.drop (16 * m)).take 16).length = 16 := by
    rw [List.length_take, List.length_drop]; omega
  have hprev_len : (cbcChainAt iv ct m).length = 16 := cbcChainAt_length hiv (by omega)
  rw [u128ToBytesLE_armv8Decrypt15_bytes hkey hc0_len, zipWith_xor_blockToBytesLE _ hprev_len]
  unfold cbcPrefixBytes
  rw [chunks16_take_succ hm, cbcDecryptBlocks_append, List.flatMap_append,
      cbcLastBlock_chunks16_take (Nat.le_of_lt hm)]
  simp [cbcDecryptBlocks]

private theorem ofFn_succ_snoc {α : Type} {n : Nat} (f : Fin (n + 1) → α) :
    List.ofFn f = (List.ofFn fun i : Fin n => f i.castSucc) ++ [f (Fin.last n)] := by
  apply List.ext_getElem (by simp)
  intro k hk1 hk2
  rw [List.getElem_ofFn]
  by_cases hk : k < n
  · rw [List.getElem_append_left (by simp [hk]), List.getElem_ofFn]; rfl
  · have hkeq : k = n := by simp at hk1; omega
    subst hkeq; rw [List.getElem_append_right (by simp)]; simp [Fin.last]

private theorem length_flatten_ofFn_block {k : Nat} (f : Fin k → Block) :
    ((List.ofFn fun i => blockToBytesLE (f i)).flatten).length = 16 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [ofFn_succ_snoc, List.flatten_append, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.length_append, ih (fun i => f i.castSucc), length_blockToBytesLE]
    omega

private theorem list_zipWith_xor_blocks (g : Block → Block) (iv ct : List (BitVec 8))
    (hiv : iv.length = 16) (m n : Nat) (hmn : m + n ≤ ct.length / 16) :
    List.zipWith (· ^^^ ·)
      ((List.ofFn fun i : Fin n =>
        blockToBytesLE (g (bytesToBlock ((ct.drop (16 * (m + i.val))).take 16)))).flatten)
      ((if n = 0 then [] else cbcChainAt iv ct m ++ (ct.drop (16 * m)).take (16 * (n - 1)))) =
    (cbcDecryptBlocks g (bytesToBlock (cbcChainAt iv ct m))
      (List.ofFn fun i : Fin n => bytesToBlock ((ct.drop (16 * (m + i.val))).take 16))).flatMap
        blockToBytesLE := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ofFn_succ_snoc, ofFn_succ_snoc, List.flatten_append, List.flatten_cons, List.flatten_nil,
        List.append_nil, cbcDecryptBlocks_append, List.flatMap_append]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel,
      Fin.val_castSucc, Fin.val_last]
    cases n with
    | zero =>
      simp only [List.ofFn_zero, List.flatten_nil, List.nil_append, Nat.mul_zero, List.take_zero,
        List.append_nil, Nat.add_zero, cbcLastBlock, cbcDecryptBlocks, List.flatMap_nil,
        List.flatMap_cons]
      exact zipWith_xor_blockToBytesLE _ (cbcChainAt_length hiv (by omega))
    | succ n' =>
      have htake_split :
          (ct.drop (16 * m)).take (16 * (n' + 1)) =
            (ct.drop (16 * m)).take (16 * n') ++ (ct.drop (16 * (m + n'))).take 16 := by
        rw [show 16 * (n' + 1) = 16 * n' + 16 by omega, List.take_add, List.drop_drop,
            show 16 * m + 16 * n' = 16 * (m + n') by omega]
      have hlen_lhs :
          ((List.ofFn fun i : Fin (n' + 1) =>
            blockToBytesLE (g (bytesToBlock ((ct.drop (16 * (m + i.val))).take 16)))).flatten).length =
            (cbcChainAt iv ct m ++ (ct.drop (16 * m)).take (16 * n')).length := by
        rw [length_flatten_ofFn_block, List.length_append, cbcChainAt_length hiv (by omega),
            List.length_take, List.length_drop]
        omega
      rw [htake_split, ← List.append_assoc, zipWith_append_eq _ hlen_lhs]
      have ih' := ih (by omega)
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel] at ih'
      rw [ih']
      congr 1
      have hfn_split := ofFn_succ_snoc (n := n')
        (fun i : Fin (n' + 1) => bytesToBlock ((ct.drop (16 * (m + i.val))).take 16))
      have hlast :
          cbcLastBlock (bytesToBlock (cbcChainAt iv ct m))
            (List.ofFn fun i : Fin (n' + 1) =>
              bytesToBlock ((ct.drop (16 * (m + i.val))).take 16)) =
            bytesToBlock ((ct.drop (16 * (m + n'))).take 16) := by
        rw [hfn_split, cbcLastBlock_snoc]; rfl
      have hc_len : ((ct.drop (16 * (m + n'))).take 16).length = 16 := by
        rw [List.length_take, List.length_drop]; omega
      simp only [cbcDecryptBlocks, List.flatMap_cons, List.flatMap_nil, List.append_nil, hlast]
      exact zipWith_xor_blockToBytesLE _ hc_len

/-- 17-block parallel hardware CBC decryption step (`decrypt_par::<15, U17>` + 272-byte XOR). -/
theorem cbcPrefixBytes_step17 {key iv ct ctChunk : List (BitVec 8)} {m : Nat}
    (hkey : key.length = 32) (hiv : iv.length = 16) (hm : m + 17 ≤ ct.length / 16)
    (hchunk : ctChunk = (ct.drop (16 * m)).take 272) :
    cbcPrefixBytes key iv ct m ++
        List.zipWith (· ^^^ ·)
          (blocks17Bytes (armv8DecryptPar17 (armv8InvExpandedKeys (armv8ExpandKey key))
            (bytesToBlocks17 ctChunk)))
          (cbcChainAt iv ct m ++ ctChunk.take 256) =
      cbcPrefixBytes key iv ct (m + 17) := by
  have hchunk_len : ctChunk.length = 272 := by
    rw [hchunk, List.length_take, List.length_drop]; omega
  have hblks : blocks17Bytes (bytesToBlocks17 ctChunk) = ctChunk :=
    blocks17Bytes_bytesToBlocks17 hchunk_len
  have ⟨_, hdec⟩ := blocks17Bytes_armv8DecryptPar17_of_bytes hkey hblks
  have hslice : ∀ i : Fin 17,
      (ctChunk.drop (16 * i.val)).take 16 = (ct.drop (16 * (m + i.val))).take 16 := by
    intro i; rw [hchunk, List.drop_take, List.drop_drop, List.take_take,
        Nat.min_eq_left (by omega : 16 ≤ 272 - 16 * i.val),
        show 16 * m + 16 * i.val = 16 * (m + i.val) by omega]
  have hdec' :
      blocks17Bytes (armv8DecryptPar17 (armv8InvExpandedKeys (armv8ExpandKey key))
        (bytesToBlocks17 ctChunk)) =
      (List.ofFn fun i : Fin 17 =>
        blockToBytesLE (Spec.Aes256.aes256Dec (bytesToKey32 key)
          (bytesToBlock ((ct.drop (16 * (m + i.val))).take 16)))).flatten := by
    rw [hdec]; congr 2; funext i; rw [hslice i]
  have htake256 : ctChunk.take 256 = (ct.drop (16 * m)).take (16 * 16) := by
    rw [hchunk, List.take_take, Nat.min_eq_left (by decide)]
  rw [hdec', htake256]
  have hzip := list_zipWith_xor_blocks (Spec.Aes256.aes256Dec (bytesToKey32 key)) iv ct hiv m 17 hm
  simp only [Nat.reduceEqDiff, ↓reduceIte] at hzip
  rw [hzip]
  unfold cbcPrefixBytes
  have htake_add : ∀ n : Nat, m + n ≤ ct.length / 16 →
      (chunks16 ct).take (m + n) =
        (chunks16 ct).take m ++
          List.ofFn fun i : Fin n => bytesToBlock ((ct.drop (16 * (m + i.val))).take 16) := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show m + (n + 1) = (m + n) + 1 by omega, chunks16_take_succ (by omega),
          ih (by omega), ofFn_succ_snoc, ← List.append_assoc]
      rfl
  rw [htake_add 17 hm, cbcDecryptBlocks_append, List.flatMap_append,
      cbcLastBlock_chunks16_take (by omega)]

/-! ## 3. `bytes16At`, Post-Indexed `↦₁₂₈` Load/Store & `BL` Call Combinators -/

@[expose] def bytes16At (p : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) : SepProp :=
  (p ↦₈ b0) ∗ ((p + 1#64) ↦₈ b1) ∗ ((p + 2#64) ↦₈ b2) ∗ ((p + 3#64) ↦₈ b3) ∗
  ((p + 4#64) ↦₈ b4) ∗ ((p + 5#64) ↦₈ b5) ∗ ((p + 6#64) ↦₈ b6) ∗ ((p + 7#64) ↦₈ b7) ∗
  ((p + 8#64) ↦₈ b8) ∗ ((p + 9#64) ↦₈ b9) ∗ ((p + 10#64) ↦₈ b10) ∗ ((p + 11#64) ↦₈ b11) ∗
  ((p + 12#64) ↦₈ b12) ∗ ((p + 13#64) ↦₈ b13) ∗ ((p + 14#64) ↦₈ b14) ∗ ((p + 15#64) ↦₈ b15)

theorem pointsToBytes16_eq_bytes16At (p : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    (p ↦ₛ [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]) =
      bytes16At p b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 := by
  simp only [bytes16At, pointsToBytes_cons_def, pointsToBytes_nil_def, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem exists_bytes16 {bs : List (BitVec 8)} (h : bs.length = 16) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15,
      bs = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals simp at h
  exact ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, rfl⟩

theorem sepWP_weaken_pre {P : Program} {pc : BitVec 64} {s : State}
    {P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : P1 ⊢ P2) (hw : SepWP P pc s P2 post oom) :
    SepWP P pc s P1 post oom :=
  SepWP.of_reaches_pc fun _ hm => hw.to_reaches_pc (Satisfies.mono (sepConj_mono_left h) hm)

theorem sepWP_checkpoint {P : Program} {pc : BitVec 64} {s : State}
    {Spatial : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {φ : State → Prop} (hφ : φ s)
    (hk : ∀ sM : State, φ sM → SepWP P pc sM Spatial post oom) :
    SepWP P pc s Spatial post oom := hk s hφ

theorem cs_refl (s : State) : CalleeSavedPreserved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem cs_trans {s0 s1 s2 : State}
    (h1 : CalleeSavedPreserved s0 s1) (h2 : CalleeSavedPreserved s1 s2) :
    CalleeSavedPreserved s0 s2 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
   h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.1.trans h1.2.2.2.2.1,
   h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1, h2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.1, h2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Post-indexed 128-bit SIMD load (`LDR Qt, [Xn], #imm`) over `(ea ↦₁₂₈ v) ∗ F`. -/
theorem step_ldr128_post {prog : Program} {target_pc pc ea : BitVec 64} {v : BitVec 128}
    {s : State} {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {vt rn : BitVec 5} {imm : BitVec 64}
    (hfetch : prog.fetch pc = some (.ldrSimd .Q128 vt (.PostIndex (.gpr rn) imm)))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (haddr : s.readReg64 (.gpr rn) = ea)
    (hP : P = (ea ↦₁₂₈ v) ∗ F)
    (hnext : SepWP prog target_pc
      (((s.writeReg64 (.gpr rn) (ea + imm)).writeVReg128 vt v).setPC (pc + 4#64)) P post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hm0 : s.mem ⊨ (ea ↦₁₂₈ v) ∗ (F ∗ R) := by rwa [hP, sepConj_assoc] at hm
  have hread : s.mem.read128 ea = v := (IsBlock.pointsTo128 ea v).read hm0
  have hcan : s.mem.canRead ea 16 = true := (IsBlock.pointsTo128 ea v).canRead (by decide) hm0
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.ldrSimd .Q128 vt (.PostIndex (.gpr rn) imm)) s =
      (((s.writeReg64 (.gpr rn) (ea + imm)).writeVReg128 vt v).setPC (pc + 4#64)) := by
    simp [Program.evalInst, execInstWithSvc, checkAddrSPAligned, checkRegSPAligned,
      AddrMode.baseReg, evalAddrMode, Memory.readSimdSized, State.advancePC,
      State.setPC, State.writeVReg128, SimdMemSize.bytes, haddr, hread, hcan, hpc]
  rw [hstep]
  exact SepWP.to_reaches_pc hnext hm

/-- Permission-preserving post-indexed 128-bit SIMD store (`STR Qt, [Xn], #imm`) over `↦₁₂₈`. -/
theorem step_str128_post_perm {prog : Program} {target_pc pc ea : BitVec 64} {old val : BitVec 128}
    {s : State} {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {vt rn : BitVec 5} {imm : BitVec 64}
    (hfetch : prog.fetch pc = some (.strSimd .Q128 vt (.PostIndex (.gpr rn) imm)))
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (haddr : s.readReg64 (.gpr rn) = ea)
    (hval : s.readVReg128 vt = val)
    (hP : P = (ea ↦₁₂₈ old) ∗ F)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm →
      SepWP prog target_pc (((s.writeReg64 (.gpr rn) (ea + imm)).setPC (pc + 4#64)).setMem m')
        ((ea ↦₁₂₈ val) ∗ F) post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hm0 : s.mem ⊨ (ea ↦₁₂₈ old) ∗ (F ∗ R) := by rwa [hP, sepConj_assoc] at hm
  have hcan : s.mem.canWrite ea 16 = true := (IsBlock.pointsTo128 ea old).canWrite (by decide) hm0
  let m1 := s.mem.write128 ea val
  have hm1 : m1 ⊨ ((ea ↦₁₂₈ val) ∗ F) ∗ R := by
    rw [sepConj_assoc]; exact IsBlock.write128 (IsBlock.pointsTo128 ea old) hm0 val
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.strSimd .Q128 vt (.PostIndex (.gpr rn) imm)) s =
      (((s.writeReg64 (.gpr rn) (ea + imm)).setPC (pc + 4#64)).setMem m1) := by
    simp [Program.evalInst, execInstWithSvc, checkAddrSPAligned, checkRegSPAligned,
      AddrMode.baseReg, evalAddrMode, Memory.writeSimdSized, State.advancePC,
      State.setPC, State.setMem, State.writeReg64, SimdMemSize.bytes, haddr, hval, hcan, hpc, m1]
  rw [hstep]
  exact SepWP.to_reaches_pc (hnext m1 (Memory.perm_write128 _ _ _)) hm1

private theorem step_bl_call {α : Type} {P : Program}
    {blPc calleeAddr target_pc : BitVec 64} {spec : Spec α}
    (hbl : hasInstrs P blPc [.bl (calleeAddr - blPc)])
    (hcall : subroutine_ok P calleeAddr spec) (x : α)
    {s : State} {Full A A' F : SepProp} {φ : Prop} {ψ : State → Prop}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = blPc) (hrun : s.status = .Running) (hsp_al : s.spAligned = true)
    (hpre_eq : spec.pre x ((s.writeReg64 .lr (blPc + 4#64)).setPC calleeAddr) = (⌜φ⌝ ∗ A))
    (hpost_eq : ∀ sf, spec.post x ((s.writeReg64 .lr (blPc + 4#64)).setPC calleeAddr) sf = (⌜ψ sf⌝ ∗ A'))
    (hFull : Full = A ∗ F) (hφ : φ)
    (hnext : ∀ sf : State, sf.pc = blPc + 4#64 → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → ψ sf → SepWP P target_pc sf (A' ∗ F) post oom)
    (hno : ∀ se, spec.onPanic x se = (fun _ => ⌜False⌝) := by intro _; exact rfl)
    (h_no_exit : spec.onExit x = (fun _ _ _ => ⌜False⌝) := by exact rfl)
    (h_no_oom : ∀ se sf, spec.onOom x se sf = ⌜False⌝ := by intro _ _; exact rfl) :
    SepWP P target_pc s Full post oom := by
  have hf : P.fetch s.pc = some (.bl (calleeAddr - blPc)) := by
    rw [hpc]; simpa [hasInstrs] using hbl 0 (Nat.zero_lt_succ 0)
  apply SepWP.of_reaches_pc; intro R hm; apply reaches_pc_step hrun hf
  let s' : State := (s.writeReg64 .lr (blPc + 4#64)).setPC calleeAddr
  have hadd : blPc + (calleeAddr - blPc) = calleeAddr := by bv_lin
  have heval : P.evalInst (.bl (calleeAddr - blPc)) s = s' := by
    simp [Program.evalInst, execInstWithSvc, State.setPC, State.writeReg64, hpc, hadd, s']
  rw [heval]
  have hm' : s'.mem ⊨ Full ∗ R := by
    have : s'.mem = s.mem := by cases s; rfl
    rw [this]; exact hm
  refine SepWP.to_reaches_pc ?_ hm'
  refine SepWP.call_framed_mut hcall x hpre_eq hpost_eq hFull hφ
    (by cases s; rfl) (by cases s; exact hrun) (by cases s; exact hsp_al) (by cases s; rfl)
    ?_ (hno s') h_no_exit ?_
  · intro sf hpc' hrun' hsp' hcs' hψ
    have hsp_s : sf.sp = s.sp := hsp'.trans (by cases s; rfl)
    have hcs_s : CalleeSavedPreserved s sf :=
      (show CalleeSavedPreserved s' sf ↔ CalleeSavedPreserved s sf by cases s; rfl).mp hcs'
    exact hnext sf hpc' hrun' hsp_s hcs_s hψ
  · intro R' sf _ hsat; rw [h_no_oom s' sf] at hsat; exact False.elim (not_satisfies_false_sepConj hsat)

private theorem pureStepPreserved_bl {s sf : State} {retPc calleeAddr : BitVec 64}
    (h : PureStepPreserved ((s.writeReg64 .lr retPc).setPC calleeAddr) sf) :
    PureStepPreserved s sf :=
  (PureStepPreserved.of_proj_perm (by simp [arm64_norm]) (by simp [arm64_norm])).trans h

/-- Step `BL memcpy` (`allocMemcpyVmSpec`), yielding `CalleeSavedPreserved` and `PureStepPreserved`. -/
theorem step_bl_memcpy {P : Program} {blPc calleeAddr target_pc sp dst src : BitVec 64}
    {bs : List (BitVec 8)}
    (hbl : hasInstrs P blPc [.bl (calleeAddr - blPc)])
    (hcall : subroutine_ok P calleeAddr allocMemcpyVmSpec)
    {s : State} {Full F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = blPc) (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_al : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length) (hlen : bs.length < 2 ^ 64)
    (hFull : Full = (memRegion dst bs.length ∗ (src ↦ₛ bs)) ∗ F)
    (hnext : ∀ sf : State, sf.pc = blPc + 4#64 → sf.status = .Running → sf.sp = sp →
      CalleeSavedPreserved s sf → PureStepPreserved s sf →
      SepWP P target_pc sf (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ F) post oom) :
    SepWP P target_pc s Full post oom :=
  let s' := (s.writeReg64 .lr (blPc + 4#64)).setPC calleeAddr
  step_bl_call hbl hcall (dst, src, bs)
    (φ := s'.readReg64 .x0 = dst ∧ s'.readReg64 .x1 = src ∧
          s'.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧ bs.length < 2 ^ 64)
    (ψ := fun sf => sf.readReg64 .x0 = dst ∧ AllocCallPreserved s' sf ∧ VmPreserved s' sf)
    hpc hrun hsp_al rfl (fun _ => rfl) hFull
    ⟨by simp [s', arm64_norm, hx0], by simp [s', arm64_norm, hx1],
     by simp [s', arm64_norm, hx2], hlen⟩
    fun sf hpc' hrun' hsp' hcs ⟨_, ha, hv⟩ =>
      hnext sf hpc' hrun' (hsp'.trans hsp) hcs (pureStepPreserved_bl ⟨ha, hv⟩)

/-- Step `BL decrypt_par::<15, U17>` (`decryptPar17InplaceBytesSpec`). -/
theorem step_bl_decryptPar17 {P : Program} {blPc calleeAddr target_pc sp dkPtr bufPtr : BitVec 64}
    {dk : Vector (BitVec 128) 15} {bs : List (BitVec 8)}
    (hbl : hasInstrs P blPc [.bl (calleeAddr - blPc)])
    (hcall : subroutine_ok P calleeAddr decryptPar17InplaceBytesSpec)
    {s : State} {Full F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = blPc) (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_al : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = dkPtr) (hx1 : s.readReg64 .x1 = bufPtr) (hx2 : s.readReg64 .x2 = bufPtr)
    (hlen : bs.length = 272)
    (hFull : Full = (roundKeys15At dkPtr dk ∗ (bufPtr ↦ₛ bs)) ∗ F)
    (hnext : ∀ sf : State, sf.pc = blPc + 4#64 → sf.status = .Running → sf.sp = sp →
      CalleeSavedPreserved s sf → PureStepPreserved s sf →
      SepWP P target_pc sf
        ((roundKeys15At dkPtr dk ∗
          (bufPtr ↦ₛ blocks17Bytes (armv8DecryptPar17 dk (bytesToBlocks17 bs)))) ∗ F)
        post oom) :
    SepWP P target_pc s Full post oom :=
  let s' := (s.writeReg64 .lr (blPc + 4#64)).setPC calleeAddr
  step_bl_call hbl hcall (dkPtr, bufPtr, dk, bs)
    (φ := s'.readReg64 .x0 = dkPtr ∧ s'.readReg64 .x1 = bufPtr ∧
          s'.readReg64 .x2 = bufPtr ∧ bs.length = 272)
    (ψ := fun sf => Par17Anchor s' sf)
    hpc hrun hsp_al rfl (fun _ => rfl) hFull
    ⟨by simp [s', arm64_norm, hx0], by simp [s', arm64_norm, hx1],
     by simp [s', arm64_norm, hx2], hlen⟩
    fun sf hpc' hrun' hsp' hcs ha =>
      hnext sf hpc' hrun' (hsp'.trans hsp) hcs (pureStepPreserved_bl ha.pres)

/-- Step `BL decrypt::<15>` (`decrypt15InplaceSpec`). -/
theorem step_bl_decrypt15 {P : Program} {blPc calleeAddr target_pc sp dkPtr blkPtr : BitVec 64}
    {dk : Vector (BitVec 128) 15} {blk : BitVec 128}
    (hbl : hasInstrs P blPc [.bl (calleeAddr - blPc)])
    (hcall : subroutine_ok P calleeAddr decrypt15InplaceSpec)
    {s : State} {Full F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = blPc) (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_al : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = dkPtr) (hx1 : s.readReg64 .x1 = blkPtr) (hx2 : s.readReg64 .x2 = blkPtr)
    (hFull : Full = (roundKeys15At dkPtr dk ∗ (blkPtr ↦₁₂₈ blk)) ∗ F)
    (hnext : ∀ sf : State, sf.pc = blPc + 4#64 → sf.status = .Running → sf.sp = sp →
      CalleeSavedPreserved s sf → PureStepPreserved s sf →
      SepWP P target_pc sf
        ((roundKeys15At dkPtr dk ∗ (blkPtr ↦₁₂₈ armv8Decrypt15 dk blk)) ∗ F)
        post oom) :
    SepWP P target_pc s Full post oom :=
  let s' := (s.writeReg64 .lr (blPc + 4#64)).setPC calleeAddr
  step_bl_call hbl hcall (dkPtr, blkPtr, dk, blk)
    (φ := s'.readReg64 .x0 = dkPtr ∧ s'.readReg64 .x1 = blkPtr ∧ s'.readReg64 .x2 = blkPtr)
    (ψ := fun sf => PureStepPreserved s' sf ∧ sf.regs = s'.regs)
    hpc hrun hsp_al rfl (fun _ => rfl) hFull
    ⟨by simp [s', arm64_norm, hx0], by simp [s', arm64_norm, hx1], by simp [s', arm64_norm, hx2]⟩
    fun sf hpc' hrun' hsp' hcs ⟨hpure, _⟩ =>
      hnext sf hpc' hrun' (hsp'.trans hsp) hcs (pureStepPreserved_bl hpure)

end

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.HwLoopAux
