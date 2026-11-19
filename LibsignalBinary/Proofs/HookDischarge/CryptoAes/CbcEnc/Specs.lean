/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs
import LibsignalBinary.Proofs.CryptoGames.AEAD.CBCProof.CBCDec

/-!
# Consumer Budget Specifications & Pure CBC-PKCS#7 Lemmas (`CbcEnc.Specs`)

Shared consumer specifications (`aesEncBudgetCondSpec`, `aesEncNoOomSpec`, `withRoData` weakening
ladder) and pure CBC / PKCS#7 block-prefix decomposition lemmas for `aes_256_cbc_encrypt`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Specs

open Arm64 ProofLib SepProp
open ProofLib.SepLogic
open CryptoGames.CBC
  (AesKey Block Plain cbcEncrypt nBlocks padLen pkcs7Bytes pkcs7Blocks bytesToBlock blockToBytesLE)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.LibsignalSession (aesCbcEncrypt)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.LibsignalTripleRatchet (AesCall extHookStack)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget FitsEvents FitsEnv NullAllowed
   RustLayoutOk OomPreserved AllocCallPreserved rustAllocEvents not_nullAllowed_of_fitsAllocEvents)
open LibsignalBinary.Heap.SpecBudget
  (AesEncEnv aesCallPreBudget aesEncBudgetSpec)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common
  (keepsFs subroutine_ok_drop_keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common
  (RoDataAt SpecSimulates withRoData withRoDataSep keepsFs_withRoData)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.Defs (aesRconBytes)

/-! ## 1. Consumer Budget Specifications & `withRoData` Weakening Ladder -/

/-- Deterministic allocator event list of `aes_256_cbc_encrypt(x)`: one alignment-1 allocation of
    PKCS#7-padded length `(x.input.length / 16 + 1) * 16`. -/
@[expose] def aesEncEvents (x : AesCall) : List AllocEvent :=
  rustAllocEvents ((x.input.length / 16 + 1) * 16) 1

theorem aesEncEnv_events (x : AesCall) : AesEncEnv x (aesEncEvents x) := rfl

theorem fitsEvents_aesEnc_of_fitsEnv (M : AllocCostModel) (lim : BudgetLimits)
    (st : M.σ) (x : AesCall) (h : FitsEnv M lim st (AesEncEnv x)) :
    FitsEvents M lim st (aesEncEvents x) :=
  h (aesEncEvents x) rfl

/-- Conditional-OOM / null-panic budget-threaded contract for `aes_256_cbc_encrypt` over an
    abstract block cipher `E : AesKey → Block → Block` (requiring no `FitsEnv` in `pre`). -/
@[expose] def aesEncBudgetCondSpec (E : AesKey → Block → Block)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AesCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.inA ∧ (s.readReg64 .x1).toNat = x.input.length ∧
      s.readReg64 .x2 = x.keyA ∧ s.readReg64 .x3 = 32#64 ∧
      s.readReg64 .x4 = x.ivA ∧ s.readReg64 .x5 = 16#64 ∧
      s.readReg64 .x8 = x.ret ∧ x.key.length = 32 ∧ x.iv.length = 16 ∧
      x.input.length < 2 ^ 40⌝ ∗
      (x.inA ↦ₛ x.input) ∗ (x.keyA ↦ₛ x.key) ∗ (x.ivA ↦ₛ x.iv) ∗ memRegion x.ret 24 ∗
      A.pool lim st s ∗ stackAt s.sp extHookStack
  post := fun (x, st) s0 sf =>
    ⌜AllocCallPreserved s0 sf⌝ ∗ x.frame ∗
      vecU8 A.repAlloc x.ret (aesCbcEncrypt E (bytesToKey32 x.key) (bytesToBlock x.iv) x.input) ∗
      A.pool lim (M.stepEvents (aesEncEvents x) st) sf ∗ stackAt s0.sp extHookStack
  onPanic := fun (x, _) s0 sf =>
    ⌜NullAllowed ((x.input.length / 16 + 1) * 16) 1 ∧
      sf.fs = s0.fs ∧ sf.trace = s0.trace⌝ ∗ anyHeap
  onOom := fun (x, st) s0 sf =>
    ⌜¬ FitsEvents M lim st (aesEncEvents x) ∧ OomPreserved s0 sf⌝

/-- Deterministic-event `NoOom` specialization of `aesEncBudgetCondSpec` under
    `FitsEvents M lim st (aesEncEvents x)` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
@[expose] def aesEncNoOomSpec (E : AesKey → Block → Block)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AesCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.inA ∧ (s.readReg64 .x1).toNat = x.input.length ∧
      s.readReg64 .x2 = x.keyA ∧ s.readReg64 .x3 = 32#64 ∧
      s.readReg64 .x4 = x.ivA ∧ s.readReg64 .x5 = 16#64 ∧
      s.readReg64 .x8 = x.ret ∧ x.key.length = 32 ∧ x.iv.length = 16 ∧
      x.input.length < 2 ^ 40 ∧ FitsEvents M lim st (aesEncEvents x)⌝ ∗
      (x.inA ↦ₛ x.input) ∗ (x.keyA ↦ₛ x.key) ∗ (x.ivA ↦ₛ x.iv) ∗ memRegion x.ret 24 ∗
      A.pool lim st s ∗ stackAt s.sp extHookStack
  post := fun (x, st) s0 sf =>
    ⌜AllocCallPreserved s0 sf⌝ ∗ x.frame ∗
      vecU8 A.repAlloc x.ret (aesCbcEncrypt E (bytesToKey32 x.key) (bytesToBlock x.iv) x.input) ∗
      A.pool lim (M.stepEvents (aesEncEvents x) st) sf ∗ stackAt s0.sp extHookStack

theorem aesRconBytes_length_le : aesRconBytes.length ≤ 2 ^ 64 := by decide

theorem subroutine_ok_roData_cond_of_sep {E : AesKey → Block → Block}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry rconAddr : BitVec 64}
    (h : subroutine_ok P entry (withRoDataSep rconAddr aesRconBytes (aesEncBudgetCondSpec E M A lim))) :
    subroutine_ok P entry (withRoData rconAddr aesRconBytes (aesEncBudgetCondSpec E M A lim)) :=
  (SpecSimulates.withRoData_of_sep aesRconBytes_length_le).subroutine_ok h

theorem subroutine_ok_roData_noOom_of_cond {E : AesKey → Block → Block}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry rconAddr : BitVec 64}
    (h : subroutine_ok P entry (withRoData rconAddr aesRconBytes (aesEncBudgetCondSpec E M A lim))) :
    subroutine_ok P entry (withRoData rconAddr aesRconBytes (aesEncNoOomSpec E M A lim)) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp _
  dsimp only [withRoData, aesEncNoOomSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hro, hpre⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
      sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx8, hk, hiv, hin, hFit⟩, hrest⟩
  have hpreC : s0.mem ⊨ (withRoData rconAddr aesRconBytes (aesEncBudgetCondSpec E M A lim)).pre (x, st) s0 ∗ R := by
    dsimp only [withRoData, aesEncBudgetCondSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hro, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
        sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx8, hk, hiv, hin⟩, hrest⟩
  refine subroutine_ok.mono_outcome h (x, st) R s0 hpc hrun hpreC hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · exact Or.inl ⟨hret, hcc, hpost⟩
  · exfalso
    dsimp only [withRoData, aesEncBudgetCondSpec] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    rcases hpan with ⟨⟨hna, _, _⟩, _⟩
    have hLay : RustLayoutOk ((x.input.length / 16 + 1) * 16) 1 :=
      ⟨⟨by omega, ⟨0, rfl⟩, by omega⟩, by decide⟩
    exact not_nullAllowed_of_fitsAllocEvents hLay hFit hna
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exfalso
    dsimp only [withRoData, aesEncBudgetCondSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact hoom.1.1 hFit

theorem subroutine_ok_roData_keepsFs_of_noOom {E : AesKey → Block → Block}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry rconAddr : BitVec 64}
    (h : subroutine_ok P entry (withRoData rconAddr aesRconBytes (aesEncNoOomSpec E M A lim))) :
    subroutine_ok P entry (withRoData rconAddr aesRconBytes (keepsFs (aesEncBudgetSpec E M A lim))) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp _
  dsimp only [withRoData, keepsFs, aesEncBudgetSpec, aesCallPreBudget] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hro, hpre⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
      sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx8, hk, hiv, hin, hEnv⟩, hrest⟩
  have hFit : FitsEvents M lim st (aesEncEvents x) :=
    fitsEvents_aesEnc_of_fitsEnv M lim st x hEnv
  have hpreN : s0.mem ⊨ (withRoData rconAddr aesRconBytes (aesEncNoOomSpec E M A lim)).pre (x, st) s0 ∗ R := by
    dsimp only [withRoData, aesEncNoOomSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hro, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
        sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx8, hk, hiv, hin, hFit⟩, hrest⟩
  refine subroutine_ok.mono_outcome h (x, st) R s0 hpc hrun hpreN hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withRoData, aesEncNoOomSpec] at hpost
    dsimp only [withRoData, keepsFs, aesEncBudgetSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
        satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hacp, hrest'⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hacp.1, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨aesEncEvents x, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hacp.2.1, aesEncEnv_events x⟩, hrest'⟩
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

theorem subroutine_ok_roData_budget_of_keepsFs {E : AesKey → Block → Block}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry rconAddr : BitVec 64}
    (h : subroutine_ok P entry (withRoData rconAddr aesRconBytes (keepsFs (aesEncBudgetSpec E M A lim)))) :
    subroutine_ok P entry (withRoData rconAddr aesRconBytes (aesEncBudgetSpec E M A lim)) := by
  rw [← keepsFs_withRoData] at h
  exact subroutine_ok_drop_keepsFs h

/-! ## 2. Pure CBC-PKCS#7 Decomposition Lemmas -/

/-- List-based CBC block encryption matching `CBC.cbcEncrypt`. -/
@[expose] def cbcEncBlocks (f : Block → Block) (prev : Block) : List Block → List Block
  | [] => []
  | b :: bs =>
    let c := f (b ^^^ prev)
    c :: cbcEncBlocks f c bs

/-- Final CBC chaining value after encrypting `bs` starting from `prev`. -/
@[expose] def cbcChain (f : Block → Block) (prev : Block) : List Block → Block
  | [] => prev
  | b :: bs => cbcChain f (f (b ^^^ prev)) bs

theorem cbcEncBlocks_append (f : Block → Block) (prev : Block) (xs ys : List Block) :
    cbcEncBlocks f prev (xs ++ ys) =
      cbcEncBlocks f prev xs ++ cbcEncBlocks f (cbcChain f prev xs) ys := by
  induction xs generalizing prev with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.cons_append, cbcEncBlocks, cbcChain]
    exact congrArg (f (b ^^^ prev) :: ·) (ih (f (b ^^^ prev)))

theorem cbcChain_append (f : Block → Block) (prev : Block) (xs ys : List Block) :
    cbcChain f prev (xs ++ ys) = cbcChain f (cbcChain f prev xs) ys := by
  induction xs generalizing prev with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.cons_append, cbcChain]
    exact ih (f (b ^^^ prev))

private theorem toList_cbcEncrypt (f : Block → Block) :
    ∀ {n : Nat} (prev : Block) (v : List.Vector Block n),
      (cbcEncrypt f prev v).toList = cbcEncBlocks f prev v.toList
  | 0, _, v => by
    cases v with | mk l hl =>
    have : l = [] := List.length_eq_zero_iff.mp hl
    subst this; rfl
  | n + 1, prev, v => by
    cases v with | mk l hl =>
    rcases l with _ | ⟨b, bs⟩
    · simp at hl
    · have hbs : bs.length = n := by simp at hl; omega
      have hhead : List.Vector.head ⟨b :: bs, hl⟩ = b := rfl
      have htail : List.Vector.tail ⟨b :: bs, hl⟩ = ⟨bs, hbs⟩ := rfl
      simp only [cbcEncrypt, hhead, htail, List.Vector.toList_cons]
      exact congrArg (f (b ^^^ prev) :: ·) (toList_cbcEncrypt f (f (b ^^^ prev)) ⟨bs, hbs⟩)

theorem length_blockToBytesLE (b : Block) : (blockToBytesLE b).length = 16 := by
  simp [blockToBytesLE]

theorem length_cbcEncBlocks_flatMap (f : Block → Block) (prev : Block) (bs : List Block) :
    ((cbcEncBlocks f prev bs).flatMap blockToBytesLE).length = 16 * bs.length := by
  induction bs generalizing prev with
  | nil => rfl
  | cons b rest ih =>
    simp only [cbcEncBlocks, List.flatMap_cons, List.length_append, List.length_cons,
      length_blockToBytesLE, ih]
    omega

/-- Full 16-byte plaintext blocks `0 .. pt.length / 16 - 1`. -/
@[expose] def ptFullBlocks (pt : List (BitVec 8)) : List Block :=
  List.ofFn fun i : Fin (pt.length / 16) => bytesToBlock ((pt.drop (16 * i.val)).take 16)

@[simp] theorem length_ptFullBlocks (pt : List (BitVec 8)) :
    (ptFullBlocks pt).length = pt.length / 16 := by
  simp [ptFullBlocks]

theorem ptFullBlocks_take_zero (pt : List (BitVec 8)) :
    (ptFullBlocks pt).take 0 = [] := rfl

theorem ptFullBlocks_take_all (pt : List (BitVec 8)) :
    (ptFullBlocks pt).take (pt.length / 16) = ptFullBlocks pt :=
  List.take_of_length_le (by simp)

theorem ptFullBlocks_take_succ (pt : List (BitVec 8)) {i : Nat} (hi : i < pt.length / 16) :
    (ptFullBlocks pt).take (i + 1) =
      (ptFullBlocks pt).take i ++ [bytesToBlock ((pt.drop (16 * i)).take 16)] := by
  have hi' : i < (ptFullBlocks pt).length := by simp [hi]
  rw [List.take_add_one, List.getElem?_eq_getElem hi', Option.toList_some]
  simp [ptFullBlocks]

theorem cbcEncBlocks_take_succ_flatMap (f : Block → Block) (iv : Block)
    (pt : List (BitVec 8)) {i : Nat} (hi : i < pt.length / 16) :
    (cbcEncBlocks f iv ((ptFullBlocks pt).take (i + 1))).flatMap blockToBytesLE =
      (cbcEncBlocks f iv ((ptFullBlocks pt).take i)).flatMap blockToBytesLE ++
        blockToBytesLE (f (bytesToBlock ((pt.drop (16 * i)).take 16) ^^^
          cbcChain f iv ((ptFullBlocks pt).take i))) := by
  rw [ptFullBlocks_take_succ pt hi, cbcEncBlocks_append, List.flatMap_append]
  simp [cbcEncBlocks]

theorem cbcChain_take_succ (f : Block → Block) (iv : Block)
    (pt : List (BitVec 8)) {i : Nat} (hi : i < pt.length / 16) :
    cbcChain f iv ((ptFullBlocks pt).take (i + 1)) =
      f (bytesToBlock ((pt.drop (16 * i)).take 16) ^^^
        cbcChain f iv ((ptFullBlocks pt).take i)) := by
  rw [ptFullBlocks_take_succ pt hi, cbcChain_append]
  rfl

/-- PKCS#7 padded final 16-byte tail block of `pt`. -/
@[expose] def pkcs7TailBytes (pt : List (BitVec 8)) : List (BitVec 8) :=
  pt.drop (16 * (pt.length / 16)) ++
    List.replicate (padLen pt.length) (BitVec.ofNat 8 (padLen pt.length))

theorem pkcs7TailBytes_length (pt : List (BitVec 8)) :
    (pkcs7TailBytes pt).length = 16 := by
  unfold pkcs7TailBytes padLen
  rw [List.length_append, List.length_drop, List.length_replicate]
  omega

private theorem toList_pkcs7Blocks_eq (pt : List (BitVec 8)) :
    (pkcs7Blocks (⟨pt, rfl⟩ : Plain pt.length)).toList =
      ptFullBlocks pt ++ [bytesToBlock (pkcs7TailBytes pt)] := by
  apply List.ext_getElem
  · simp [pkcs7Blocks, ptFullBlocks, nBlocks]
  · intro i hi1 hi2
    simp only [pkcs7Blocks, List.Vector.toList_ofFn, List.getElem_ofFn]
    have hq : i ≤ pt.length / 16 := by
      simp [pkcs7Blocks, nBlocks] at hi1; omega
    by_cases hlt : i < pt.length / 16
    · rw [List.getElem_append_left (by simp [ptFullBlocks]; exact hlt)]
      simp only [ptFullBlocks, List.getElem_ofFn, pkcs7Bytes, List.Vector.toList_mk]
      have hdrop : (pt ++ List.replicate (padLen pt.length) (BitVec.ofNat 8 (padLen pt.length))).drop
            (16 * i) =
          pt.drop (16 * i) ++
            List.replicate (padLen pt.length) (BitVec.ofNat 8 (padLen pt.length)) :=
        List.drop_append_of_le_length (by omega)
      have htake : ((pt.drop (16 * i) ++
            List.replicate (padLen pt.length) (BitVec.ofNat 8 (padLen pt.length))).take 16) =
          (pt.drop (16 * i)).take 16 :=
        List.take_append_of_le_length (by rw [List.length_drop]; omega)
      rw [hdrop, htake]
    · have hi_eq : i = pt.length / 16 := by omega
      subst hi_eq
      rw [List.getElem_append_right (by simp [ptFullBlocks])]
      simp only [ptFullBlocks, List.length_ofFn, Nat.sub_self, List.getElem_singleton,
        pkcs7Bytes, List.Vector.toList_mk]
      have hdrop : (pt ++ List.replicate (padLen pt.length)
            (BitVec.ofNat 8 (padLen pt.length))).drop (16 * (pt.length / 16)) =
          pkcs7TailBytes pt :=
        List.drop_append_of_le_length (by omega)
      rw [hdrop, List.take_of_length_le (by rw [pkcs7TailBytes_length])]

/-- Split `aesCbcEncrypt` into the `pt.length / 16` full-block CBC prefix plus the single
    encrypted PKCS#7 tail block. -/
theorem aesCbcEncrypt_split_tail (E : AesKey → Block → Block) (k : AesKey)
    (iv : Block) (pt : List (BitVec 8)) :
    aesCbcEncrypt E k iv pt =
      (cbcEncBlocks (E k) iv (ptFullBlocks pt)).flatMap blockToBytesLE ++
        blockToBytesLE (E k (bytesToBlock (pkcs7TailBytes pt) ^^^
          cbcChain (E k) iv (ptFullBlocks pt))) := by
  unfold aesCbcEncrypt
  change ((cbcEncrypt (E k) iv (pkcs7Blocks (⟨pt, rfl⟩ : Plain pt.length))).toList).flatMap
      blockToBytesLE = _
  rw [toList_cbcEncrypt, toList_pkcs7Blocks_eq, cbcEncBlocks_append, List.flatMap_append]
  simp [cbcEncBlocks]

theorem aesCbcEncrypt_length (E : AesKey → Block → Block) (k : AesKey)
    (iv : Block) (pt : List (BitVec 8)) :
    (aesCbcEncrypt E k iv pt).length = (pt.length / 16 + 1) * 16 := by
  rw [aesCbcEncrypt_split_tail, List.length_append, length_cbcEncBlocks_flatMap, length_blockToBytesLE]
  simp only [ptFullBlocks, List.length_ofFn]
  omega

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.CbcEnc.Specs
