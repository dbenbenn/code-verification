/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Hoare.Model
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.AesDecErrRoBudget
public import LibsignalBinary.Heap.IfaceBudgetBase
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Spec.Aes256
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.KeySchedule
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.BlockDec
import ProofLib.BV.Bits
import LibsignalBinary.Proofs.CryptoGames.AEAD.CBCProof.CBCDec

/-!
# Consumer Specifications & Pure CBC / PKCS#7 Lemmas for `aes_256_cbc_decrypt`
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PureLemmas

open Arm64 ProofLib SepProp
open CryptoGames.CBC
  (AesKey Block bytesToBlock blockToBytesLE blockToBytesLE_bytesToBlock
   chunks16 cbcDecryptBlocks pkcs7Unpad cbcDecRaw)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.LibsignalSession (aesCbcDecrypt)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.LibsignalTripleRatchetRepr (errTag)
open CryptoVerification.LibsignalTripleRatchet (AesCall extHookStack)
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget AllocCallPreserved
   OomPreserved NullAllowed FitsEvents fitsEvents_append rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (AesDecEnv)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model
  (aes256KeyScheduleFs aes256DecryptFs)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon (blocks4Bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.BlockDec
  (blocks4Bytes_aes256DecryptFs_single blocks4Bytes_aes256DecryptFs_quad)

/-! ## 1. Consumer Specifications (`Spec.Aes256.aes256Dec`) -/

/-- Exact deterministic allocator event list of `signal_crypto::aes_cbc::aes_256_cbc_decrypt`. -/
@[expose] def aesDecEvents (D : AesKey → Block → Block) (x : AesCall) : List AllocEvent :=
  if x.input.length = 0 ∨ x.input.length % 16 ≠ 0 then
    []
  else if (aesCbcDecrypt D (bytesToKey32 x.key) (bytesToBlock x.iv) x.input).isSome then
    rustAllocEvents x.input.length 1
  else
    rustAllocEvents x.input.length 1 ++ rustDeallocEvents x.input.length 1

theorem aesDecEnv_aesDecEvents (D : AesKey → Block → Block) (x : AesCall) :
    AesDecEnv x (aesDecEvents D x) := by
  unfold AesDecEnv aesDecEvents
  split
  · rfl
  · split
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem fitsAllocEvents_of_fitsAesDecEvents {D : AesKey → Block → Block}
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} {x : AesCall}
    (hnb : ¬ (x.input.length = 0 ∨ x.input.length % 16 ≠ 0))
    (hfit : FitsEvents M lim st (aesDecEvents D x)) :
    FitsEvents M lim st (rustAllocEvents x.input.length 1) := by
  unfold aesDecEvents at hfit
  simp only [hnb, ↓reduceIte] at hfit
  split at hfit
  · exact hfit
  · rw [fitsEvents_append] at hfit
    exact hfit.1

/-- Conditional-OOM budget-threaded contract for `signal_crypto::aes_cbc::aes_256_cbc_decrypt`. -/
@[expose] def aesDecBudgetCondSpec (D : AesKey → Block → Block)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AesCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.inA ∧ (s.readReg64 .x1).toNat = x.input.length ∧ s.readReg64 .x2 = x.keyA ∧
      s.readReg64 .x3 = 32#64 ∧ s.readReg64 .x4 = x.ivA ∧ s.readReg64 .x5 = 16#64 ∧
      s.readReg64 .x8 = x.ret ∧ x.key.length = 32 ∧ x.iv.length = 16 ∧ x.input.length < 2 ^ 40⌝ ∗
      (x.inA ↦ₛ x.input) ∗ (x.keyA ↦ₛ x.key) ∗ (x.ivA ↦ₛ x.iv) ∗ memRegion x.ret 24 ∗
      A.pool lim st s ∗ stackAt s.sp extHookStack
  post := fun (x, st) s0 sf =>
    ⌜AllocCallPreserved s0 sf⌝ ∗ x.frame ∗
      (match aesCbcDecrypt D (bytesToKey32 x.key) (bytesToBlock x.iv) x.input with
       | some pt => vecU8 A.repAlloc x.ret pt
       | none => (x.ret ↦₆₄ errTag) ∗
           (∃∗ p : BitVec 64, ⌜p ≠ 0⌝ ∗ ((x.ret + 8#64) ↦₆₄ p)) ∗ memRegion (x.ret + 16#64) 8) ∗
      A.pool lim (M.stepEvents (aesDecEvents D x) st) sf ∗ stackAt s0.sp extHookStack
  onPanic := fun (x, _) s0 sf =>
    ⌜¬ (x.input.length = 0 ∨ x.input.length % 16 ≠ 0) ∧ NullAllowed x.input.length 1 ∧
      sf.fs = s0.fs ∧ sf.trace = s0.trace⌝ ∗ anyHeap
  onOom := fun (x, st) s0 sf =>
    ⌜¬ FitsEvents M lim st (aesDecEvents D x) ∧ OomPreserved s0 sf⌝

/-- Deterministic-event `NoOom` specialization of `aesDecBudgetCondSpec`. -/
@[expose] def aesDecNoOomSpec (D : AesKey → Block → Block)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AesCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.inA ∧ (s.readReg64 .x1).toNat = x.input.length ∧ s.readReg64 .x2 = x.keyA ∧
      s.readReg64 .x3 = 32#64 ∧ s.readReg64 .x4 = x.ivA ∧ s.readReg64 .x5 = 16#64 ∧
      s.readReg64 .x8 = x.ret ∧ x.key.length = 32 ∧ x.iv.length = 16 ∧ x.input.length < 2 ^ 40 ∧
      FitsEvents M lim st (aesDecEvents D x)⌝ ∗
      (x.inA ↦ₛ x.input) ∗ (x.keyA ↦ₛ x.key) ∗ (x.ivA ↦ₛ x.iv) ∗ memRegion x.ret 24 ∗
      A.pool lim st s ∗ stackAt s.sp extHookStack
  post := (aesDecBudgetCondSpec D M A lim).post
  onPanic := fun _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- Concrete `.rodata` error-string strengthening of `aesDecBudgetCondSpec`. -/
@[expose] def aesDecBudgetCondSpecErrRo (D : AesKey → Block → Block)
    (errStr1Addr errStr2Addr : BitVec 64)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AesCall × M.σ) where
  pre := (aesDecBudgetCondSpec D M A lim).pre
  post := fun (x, st) s0 sf =>
    ⌜AllocCallPreserved s0 sf⌝ ∗ x.frame ∗
      (match aesCbcDecrypt D (bytesToKey32 x.key) (bytesToBlock x.iv) x.input with
       | some pt => vecU8 A.repAlloc x.ret pt
       | none => (x.ret ↦₆₄ errTag) ∗
           (∃∗ p : BitVec 64, ∃∗ len : BitVec 64,
             ⌜(p = errStr1Addr ∧ len = 0x33#64) ∨ (p = errStr2Addr ∧ len = 0x11#64)⌝ ∗
             ((x.ret + 8#64) ↦₆₄ p) ∗ ((x.ret + 16#64) ↦₆₄ len))) ∗
      A.pool lim (M.stepEvents (aesDecEvents D x) st) sf ∗ stackAt s0.sp extHookStack
  onPanic := (aesDecBudgetCondSpec D M A lim).onPanic
  onOom := (aesDecBudgetCondSpec D M A lim).onOom

/-- Deterministic-event `NoOom` specialization of `aesDecBudgetCondSpecErrRo`. -/
@[expose] def aesDecNoOomSpecErrRo (D : AesKey → Block → Block)
    (errStr1Addr errStr2Addr : BitVec 64)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AesCall × M.σ) where
  pre := (aesDecNoOomSpec D M A lim).pre
  post := (aesDecBudgetCondSpecErrRo D errStr1Addr errStr2Addr M A lim).post
  onPanic := fun _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-! ## 2. Pure CBC Block-Chaining & PKCS#7 Unpadding Lemmas -/

theorem aesCbcDecrypt_of_badLen (D : AesKey → Block → Block) (k : AesKey) (iv : Block)
    {ct : List (BitVec 8)} (hbad : ct.length = 0 ∨ ct.length % 16 ≠ 0) :
    aesCbcDecrypt D k iv ct = none := by
  unfold aesCbcDecrypt cbcDecRaw
  have hbad' : ct = [] ∨ ct.length % 16 ≠ 0 := by
    rcases hbad with h0 | hmod
    · exact Or.inl (List.eq_nil_of_length_eq_zero h0)
    · exact Or.inr hmod
  simp only [hbad', ↓reduceIte]

theorem aesCbcDecrypt_of_aligned (D : AesKey → Block → Block) (k : AesKey) (iv : Block)
    {ct : List (BitVec 8)} (hnb : ¬ (ct.length = 0 ∨ ct.length % 16 ≠ 0)) :
    aesCbcDecrypt D k iv ct =
      pkcs7Unpad ((cbcDecryptBlocks (D k) iv (chunks16 ct)).flatMap blockToBytesLE) := by
  unfold aesCbcDecrypt cbcDecRaw
  have hnb' : ¬ (ct = [] ∨ ct.length % 16 ≠ 0) := by
    rintro (rfl | hmod)
    · exact hnb (Or.inl rfl)
    · exact hnb (Or.inr hmod)
  simp only [hnb', ↓reduceIte]

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

@[expose] def cbcChainAt (iv ct : List (BitVec 8)) (m : Nat) : List (BitVec 8) :=
  if m = 0 then iv else (ct.drop (16 * (m - 1))).take 16

theorem cbcChainAt_zero (iv ct : List (BitVec 8)) : cbcChainAt iv ct 0 = iv := rfl

theorem cbcChainAt_succ (iv ct : List (BitVec 8)) (m : Nat) :
    cbcChainAt iv ct (m + 1) = (ct.drop (16 * m)).take 16 := by
  simp [cbcChainAt]

theorem cbcChainAt_length {iv ct : List (BitVec 8)} {m : Nat}
    (hiv : iv.length = 16) (hm : 16 * m ≤ ct.length) :
    (cbcChainAt iv ct m).length = 16 := by
  unfold cbcChainAt
  split
  · exact hiv
  · next hne =>
    rw [List.length_take, List.length_drop]
    omega

private theorem chunks16_length (ct : List (BitVec 8)) :
    (chunks16 ct).length = ct.length / 16 := by
  simp [chunks16]

private theorem chunks16_getElem (ct : List (BitVec 8)) (i : Nat) (hi : i < (chunks16 ct).length) :
    (chunks16 ct)[i] = bytesToBlock ((ct.drop (16 * i)).take 16) := by
  simp [chunks16]

private theorem chunks16_take_succ {ct : List (BitVec 8)} {m : Nat} (hm : m < ct.length / 16) :
    (chunks16 ct).take (m + 1) =
      (chunks16 ct).take m ++ [bytesToBlock ((ct.drop (16 * m)).take 16)] := by
  have hm' : m < (chunks16 ct).length := by rw [chunks16_length]; exact hm
  rw [List.take_add_one, List.getElem?_eq_getElem hm', Option.toList_some, chunks16_getElem ct m hm']

private theorem cbcLastBlock_chunks16_take {iv ct : List (BitVec 8)} {m : Nat}
    (hm : m ≤ ct.length / 16) :
    cbcLastBlock (bytesToBlock iv) ((chunks16 ct).take m) =
      bytesToBlock (cbcChainAt iv ct m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [chunks16_take_succ (by omega), cbcLastBlock_snoc, cbcChainAt_succ]

private theorem blockToBytesLE_xor (b1 b2 : Block) :
    blockToBytesLE (b1 ^^^ b2) = List.zipWith (· ^^^ ·) (blockToBytesLE b1) (blockToBytesLE b2) := by
  apply List.ext_getElem
  · simp [blockToBytesLE]
  · intro i h1 h2
    simp only [blockToBytesLE, List.getElem_zipWith, List.getElem_ofFn]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp [hk]

private theorem zipWith_xor_blockToBytesLE (b : Block) {ps : List (BitVec 8)} (hps : ps.length = 16) :
    List.zipWith (· ^^^ ·) (blockToBytesLE b) ps =
      blockToBytesLE (b ^^^ bytesToBlock ps) := by
  rw [blockToBytesLE_xor, blockToBytesLE_bytesToBlock ps hps]

private theorem zipWith_append_eq {α β γ : Type} (f : α → β → γ)
    {a1 a2 : List α} {b1 b2 : List β} (hlen : a1.length = b1.length) :
    List.zipWith f (a1 ++ a2) (b1 ++ b2) = List.zipWith f a1 b1 ++ List.zipWith f a2 b2 := by
  induction a1 generalizing b1 with
  | nil =>
    cases b1 with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases b1 with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.cons_append, List.zipWith_cons_cons, ih hlen]

@[expose] def cbcPrefixBytes (key iv ct : List (BitVec 8)) (m : Nat) : List (BitVec 8) :=
  (cbcDecryptBlocks (Spec.Aes256.aes256Dec (bytesToKey32 key)) (bytesToBlock iv)
    ((chunks16 ct).take m)).flatMap blockToBytesLE

theorem cbcPrefixBytes_zero (key iv ct : List (BitVec 8)) :
    cbcPrefixBytes key iv ct 0 = [] := rfl

private theorem cbcDecryptBlocks_length (g : Block → Block) (prev : Block) (xs : List Block) :
    (cbcDecryptBlocks g prev xs).length = xs.length := by
  induction xs generalizing prev with
  | nil => rfl
  | cons c xs ih => simp [cbcDecryptBlocks, ih c]

private theorem length_blockToBytesLE (b : Block) : (blockToBytesLE b).length = 16 := by
  simp [blockToBytesLE]

theorem length_flatMap_blockToBytesLE (cs : List Block) :
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
  unfold cbcPrefixBytes
  rw [List.take_of_length_le (by rw [chunks16_length])]

theorem cbcPrefixBytes_step1 {key iv ct : List (BitVec 8)} {m : Nat}
    (hkey : key.length = 32) (hiv : iv.length = 16) (hm : m < ct.length / 16)
    {b1 b2 b3 : List (BitVec 8)} (hb1 : b1.length = 16) (hb2 : b2.length = 16) (hb3 : b3.length = 16) :
    cbcPrefixBytes key iv ct m ++
        List.zipWith (· ^^^ ·)
          ((blocks4Bytes (aes256DecryptFs (aes256KeyScheduleFs key)
            ⟨(ct.drop (16 * m)).take 16, b1, b2, b3⟩)).take 16)
          (cbcChainAt iv ct m) =
      cbcPrefixBytes key iv ct (m + 1) := by
  let c0 := (ct.drop (16 * m)).take 16
  have hc0_len : c0.length = 16 := by dsimp [c0]; rw [List.length_take, List.length_drop]; omega
  have hc0_blk : blockToBytesLE (bytesToBlock c0) = c0 := blockToBytesLE_bytesToBlock c0 hc0_len
  have hsingle :
      (blocks4Bytes (aes256DecryptFs (aes256KeyScheduleFs key)
        ⟨c0, b1, b2, b3⟩)).take 16 =
        blockToBytesLE (Spec.Aes256.aes256Dec (bytesToKey32 key) (bytesToBlock c0)) := by
    conv => lhs; rw [← hc0_blk]
    exact blocks4Bytes_aes256DecryptFs_single hkey (bytesToBlock c0) hb1 hb2 hb3
  have hprev_len : (cbcChainAt iv ct m).length = 16 := cbcChainAt_length hiv (by omega)
  change cbcPrefixBytes key iv ct m ++
      List.zipWith (· ^^^ ·)
        ((blocks4Bytes (aes256DecryptFs (aes256KeyScheduleFs key) ⟨c0, b1, b2, b3⟩)).take 16)
        (cbcChainAt iv ct m) = _
  rw [hsingle, zipWith_xor_blockToBytesLE _ hprev_len]
  unfold cbcPrefixBytes
  rw [chunks16_take_succ hm, cbcDecryptBlocks_append, List.flatMap_append,
      cbcLastBlock_chunks16_take (Nat.le_of_lt hm)]
  simp [cbcDecryptBlocks, c0]

theorem cbcPrefixBytes_step4 {key iv ct : List (BitVec 8)} {m : Nat}
    (hkey : key.length = 32) (hiv : iv.length = 16) (hm : m + 4 ≤ ct.length / 16) :
    let c0 := (ct.drop (16 * m)).take 16
    let c1 := (ct.drop (16 * (m + 1))).take 16
    let c2 := (ct.drop (16 * (m + 2))).take 16
    let c3 := (ct.drop (16 * (m + 3))).take 16
    cbcPrefixBytes key iv ct m ++
        List.zipWith (· ^^^ ·)
          (blocks4Bytes (aes256DecryptFs (aes256KeyScheduleFs key) ⟨c0, c1, c2, c3⟩))
          (cbcChainAt iv ct m ++ c0 ++ c1 ++ c2) =
      cbcPrefixBytes key iv ct (m + 4) := by
  intro c0 c1 c2 c3
  have hc0_len : c0.length = 16 := by dsimp [c0]; rw [List.length_take, List.length_drop]; omega
  have hc1_len : c1.length = 16 := by dsimp [c1]; rw [List.length_take, List.length_drop]; omega
  have hc2_len : c2.length = 16 := by dsimp [c2]; rw [List.length_take, List.length_drop]; omega
  have hc3_len : c3.length = 16 := by dsimp [c3]; rw [List.length_take, List.length_drop]; omega
  have hc0_b := blockToBytesLE_bytesToBlock c0 hc0_len
  have hc1_b := blockToBytesLE_bytesToBlock c1 hc1_len
  have hc2_b := blockToBytesLE_bytesToBlock c2 hc2_len
  have hc3_b := blockToBytesLE_bytesToBlock c3 hc3_len
  have hprev_len : (cbcChainAt iv ct m).length = 16 := cbcChainAt_length hiv (by omega)
  have hquad :
      blocks4Bytes (aes256DecryptFs (aes256KeyScheduleFs key) ⟨c0, c1, c2, c3⟩) =
        blockToBytesLE (Spec.Aes256.aes256Dec (bytesToKey32 key) (bytesToBlock c0)) ++
        blockToBytesLE (Spec.Aes256.aes256Dec (bytesToKey32 key) (bytesToBlock c1)) ++
        blockToBytesLE (Spec.Aes256.aes256Dec (bytesToKey32 key) (bytesToBlock c2)) ++
        blockToBytesLE (Spec.Aes256.aes256Dec (bytesToKey32 key) (bytesToBlock c3)) := by
    conv => lhs; rw [← hc0_b, ← hc1_b, ← hc2_b, ← hc3_b]
    exact blocks4Bytes_aes256DecryptFs_quad hkey _ _ _ _
  have hbl := length_blockToBytesLE
  rw [hquad]
  simp only [List.append_assoc]
  rw [zipWith_append_eq _ (by rw [hbl, hprev_len]),
      zipWith_append_eq _ (by rw [hbl, hc0_len]),
      zipWith_append_eq _ (by rw [hbl, hc1_len]),
      zipWith_xor_blockToBytesLE _ hprev_len,
      zipWith_xor_blockToBytesLE _ hc0_len,
      zipWith_xor_blockToBytesLE _ hc1_len,
      zipWith_xor_blockToBytesLE _ hc2_len]
  unfold cbcPrefixBytes
  have htake4 : (chunks16 ct).take (m + 4) =
      (chunks16 ct).take m ++
        [bytesToBlock c0, bytesToBlock c1, bytesToBlock c2, bytesToBlock c3] := by
    rw [show m + 4 = (((m + 1) + 1) + 1) + 1 from by omega,
        chunks16_take_succ (by omega), chunks16_take_succ (by omega),
        chunks16_take_succ (by omega), chunks16_take_succ (by omega)]
    simp only [List.append_assoc, List.cons_append, List.nil_append, c0, c1, c2, c3]
  rw [htake4, cbcDecryptBlocks_append, List.flatMap_append,
      cbcLastBlock_chunks16_take (by omega)]
  simp only [cbcDecryptBlocks, List.flatMap_cons, List.flatMap_nil, List.append_nil]

private theorem getLast?_eq_getD_last {bs : List (BitVec 8)} (hpos : 0 < bs.length) :
    bs.getLast? = some (bs.getD (bs.length - 1) 0#8) := by
  have hne : bs ≠ [] := List.ne_nil_of_length_pos hpos
  rw [List.getLast?_eq_some_getLast hne, List.getLast_eq_getElem hne,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

theorem pkcs7Unpad_of_bad_last {bs : List (BitVec 8)} {numBlocks : Nat}
    (hlen : bs.length = 16 * numBlocks) (hpos : 0 < numBlocks)
    (hbad : ¬ (1 ≤ (bs.getD (16 * (numBlocks - 1) + 15) 0#8).toNat ∧
               (bs.getD (16 * (numBlocks - 1) + 15) 0#8).toNat ≤ 16)) :
    pkcs7Unpad bs = none := by
  have hidx : bs.length - 1 = 16 * (numBlocks - 1) + 15 := by omega
  unfold pkcs7Unpad
  rw [getLast?_eq_getD_last (by omega), hidx]
  dsimp only
  have hor : (bs.getD (16 * (numBlocks - 1) + 15) 0#8).toNat = 0 ∨
      16 < (bs.getD (16 * (numBlocks - 1) + 15) 0#8).toNat ∨
      bs.length < (bs.getD (16 * (numBlocks - 1) + 15) 0#8).toNat := by omega
  simp only [hor, ite_true]

theorem pkcs7Unpad_of_mismatch {bs : List (BitVec 8)} {numBlocks j : Nat}
    (hlen : bs.length = 16 * numBlocks) (hpos : 0 < numBlocks)
    (hlo : 1 ≤ (bs.getD (16 * (numBlocks - 1) + 15) 0#8).toNat)
    (hhi : (bs.getD (16 * (numBlocks - 1) + 15) 0#8).toNat ≤ 16)
    (hj1 : 16 - (bs.getD (16 * (numBlocks - 1) + 15) 0#8).toNat ≤ j) (hj2 : j < 15)
    (hne : bs.getD (16 * (numBlocks - 1) + j) 0#8 ≠ bs.getD (16 * (numBlocks - 1) + 15) 0#8) :
    pkcs7Unpad bs = none := by
  have hidx : bs.length - 1 = 16 * (numBlocks - 1) + 15 := by omega
  unfold pkcs7Unpad
  rw [getLast?_eq_getD_last (by omega), hidx]
  dsimp only
  set last := bs.getD (16 * (numBlocks - 1) + 15) 0#8
  have hnor : ¬ (last.toNat = 0 ∨ 16 < last.toNat ∨ bs.length < last.toNat) := by omega
  simp only [hnor, ite_false]
  have hall_false : (bs.drop (bs.length - last.toNat)).all (· == last) = false := by
    rw [List.all_eq_false]
    have hmem : bs[16 * (numBlocks - 1) + j]'(by omega) ∈ bs.drop (bs.length - last.toNat) := by
      have hlt : j - (16 - last.toNat) < (bs.drop (bs.length - last.toNat)).length := by
        rw [List.length_drop]; omega
      have heq : (bs.drop (bs.length - last.toNat))[j - (16 - last.toNat)]'hlt =
          bs[16 * (numBlocks - 1) + j]'(by omega) := by
        rw [List.getElem_drop]; congr 1; omega
      rw [← heq]; exact List.getElem_mem hlt
    refine ⟨bs[16 * (numBlocks - 1) + j]'(by omega), hmem, ?_⟩
    simp only [Bool.not_eq_true, beq_eq_false_iff_ne]
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some] at hne
  rw [hall_false]; rfl

theorem pkcs7Unpad_of_all_eq {bs : List (BitVec 8)} {numBlocks : Nat}
    (hlen : bs.length = 16 * numBlocks) (hpos : 0 < numBlocks)
    (hlo : 1 ≤ (bs.getD (16 * (numBlocks - 1) + 15) 0#8).toNat)
    (hhi : (bs.getD (16 * (numBlocks - 1) + 15) 0#8).toNat ≤ 16)
    (hall : ∀ j, 16 - (bs.getD (16 * (numBlocks - 1) + 15) 0#8).toNat ≤ j → j < 15 →
      bs.getD (16 * (numBlocks - 1) + j) 0#8 = bs.getD (16 * (numBlocks - 1) + 15) 0#8) :
    pkcs7Unpad bs =
      some (bs.take (16 * numBlocks - (bs.getD (16 * (numBlocks - 1) + 15) 0#8).toNat)) := by
  have hidx : bs.length - 1 = 16 * (numBlocks - 1) + 15 := by omega
  unfold pkcs7Unpad
  rw [getLast?_eq_getD_last (by omega), hidx]
  dsimp only
  set last := bs.getD (16 * (numBlocks - 1) + 15) 0#8
  have hnor : ¬ (last.toNat = 0 ∨ 16 < last.toNat ∨ bs.length < last.toNat) := by omega
  simp only [hnor, ite_false]
  have hall_true : (bs.drop (bs.length - last.toNat)).all (· == last) = true := by
    rw [List.all_eq_true]
    intro b hb
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
    rw [List.length_drop] at hk
    rw [List.getElem_drop, beq_iff_eq]
    set j := (16 - last.toNat) + k
    have hj_eq : (bs.length - last.toNat) + k = 16 * (numBlocks - 1) + j := by omega
    have hj_lt16 : j < 16 := by omega
    have hget : bs[(bs.length - last.toNat) + k]'(by omega) = bs.getD (16 * (numBlocks - 1) + j) 0#8 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      congr 1
    rw [hget]
    by_cases hj15 : j = 15
    · rw [hj15]
    · exact hall j (by omega) (by omega)
  rw [hall_true, hlen]; rfl

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcDec.PureLemmas
