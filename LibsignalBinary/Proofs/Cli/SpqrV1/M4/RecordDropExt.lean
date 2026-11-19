/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordCallees.Defs
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Getters.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Common
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local2
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

/-!
# Dealloc-Only `SessionStructure` Drop (`local#4`, 4192 B)

Proves `DropSessionStructureLocal2OkExt b A ext` directly from `rustDeallocSpec A`,
`dropProtoChainSpec A`, and `dropChainSpec A` without requiring `AllocContracts`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalSpqrV1.M4

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.HMAC
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.DropsCommon
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private abbrev ssFirst3HeadersAt := ssFirst3HeadersAt_shared_lb
private abbrev ssTail3HeadersAt := ssTail3HeadersAt_shared_lb
private abbrev sender_none_entails_memRegion_104 := sender_none_entails_memRegion_104_shared_lb
private abbrev optSenderChainAt_some_expose := optSenderChainAt_some_expose_shared_lb
private abbrev chainAt_of_exposed_sender := @chainAt_of_exposed_sender_shared_lb
private abbrev session_memRegions_entails_344 := session_memRegions_entails_344_shared_lb
private abbrev pq_header24_weaken := pq_header24_weaken_shared_lb
private abbrev drop6_strengthen_post := @drop6_strengthen_post_shared_lb
private abbrev post_loop_weaken_at_72 := post_loop_weaken_at_72_shared_lb
private abbrev chains_header24_weaken := chains_header24_weaken_shared_lb

@[reducible]
private def Saved48Preserved (s0 s : State) (fsp : BitVec 64) : Prop :=
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  s.sp = fsp ∧
  s.trace = s0.trace ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

private theorem stackAt_ss_local2_split (sp : BitVec 64) :
    stackAt sp dropSessionStructureLocal2Stack =
      stackAt (sp - 48#64) dropChainStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp dropChainStack 6 (by decide)

private theorem stackAt_dropChain_split_alloc (fsp : BitVec 64) :
    stackAt fsp dropChainStack =
      memRegion (fsp - 4144#64) 48 ∗ stackAt fsp allocHookStack := by
  rw [show dropChainStack = allocHookStack + 48 from rfl,
      stackAt_split_bottom' fsp allocHookStack 48 (by decide)]

private theorem tail_stack_ss_local2_96_from_bottom (sp : BitVec 64) :
    memRegion (sp - 4192#64) 96 ∗ stackAt sp allocHookStack =
      stackAt (sp - 48#64) dropChainStack ∗ cells (sp - 48#64) 6 := by
  rw [← stackAt_split_bottom' sp allocHookStack 96 (by decide),
      show allocHookStack + 96 = dropSessionStructureLocal2Stack from rfl,
      ← stackAt_ss_local2_split sp]

private theorem tail_dealloc_ss_local2_pre_weaken (ss cap ptr : BitVec 64)
    (live rest pool : SepProp) (sp : BitVec 64) (fp lr x22 x21 x20 x19 : BitVec 64) :
    ((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8 ∗
      live ∗ rest ∗ pool ∗
      stackAt (sp - 48#64) dropChainStack ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    memRegion (ss + 120#64) 24 ∗ rest ∗ pool ∗
      memRegion (sp - 4192#64) 96 ∗ stackAt sp allocHookStack ∗ live := by
  have h1 : ((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8 ⊢
      memRegion (ss + 120#64) 24 := by
    have ha1 : (ss + 120#64) + 8#64 = ss + 128#64 := by bv_omega
    have ha2 : (ss + 120#64) + 16#64 = ss + 136#64 := by bv_omega
    rw [← ha1, ← ha2]
    exact header_cells_entails_memRegion_24 (ss + 120#64) cap ptr
  have h2 :
      stackAt (sp - 48#64) dropChainStack ∗
        ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
        ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
      memRegion (sp - 4192#64) 96 ∗ stackAt sp allocHookStack := by
    rw [tail_stack_ss_local2_96_from_bottom sp]
    cells_unfold
    refine Entails.sepExists_right fp (Entails.sepExists_right lr
      (Entails.sepExists_right x22 (Entails.sepExists_right x21
        (Entails.sepExists_right x20 (Entails.sepExists_right x19 (Entails.refl _))))))
  have hreord :
      (((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8 ∗
        live ∗ rest ∗ pool ∗
        stackAt (sp - 48#64) dropChainStack ∗
        ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
        ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) =
      (((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8) ∗
        (live ∗ rest ∗ pool ∗
         (stackAt (sp - 48#64) dropChainStack ∗
          ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
          ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))) := by ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono h1 (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h2)))) ?_
  exact Entails.of_eq (by ac_rfl)

private theorem ofNat_succ_eq_add_one (n : Nat) :
    BitVec.ofNat 64 (n + 1) = BitVec.ofNat 64 n + 1#64 :=
  BitVec.ofNat_add n 1

private theorem ofNat_ne_zero_of_pos {n : Nat} (hpos : 0 < n) (hlt : n * 104 < 2 ^ 63) :
    BitVec.ofNat 64 n ≠ 0#64 := by
  intro heq
  have h := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat] at h
  have hlt2 : n < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hlt2] at h
  omega

private theorem ofNat_beq_zero_false {n : Nat} (hpos : 0 < n) (hlt : n * 104 < 2 ^ 63) :
    ¬((BitVec.ofNat 64 n == 0#64) = true) := by
  rw [beq_iff_eq]
  exact ofNat_ne_zero_of_pos hpos hlt

private theorem ofNat_add_one_beq_one_false {n : Nat} (hpos : 0 < n) (hlt : n * 104 < 2 ^ 63) :
    ¬((BitVec.ofNat 64 n + 1#64 == 1#64) = true) := by
  rw [beq_iff_eq]
  intro heq
  have h0 : BitVec.ofNat 64 n = 0#64 := by bv_omega
  exact ofNat_ne_zero_of_pos hpos hlt h0

private theorem tail_len_mul_lt {α : Type} {x : α} {xs : List α} {k m : Nat}
    (h : (x :: xs).length * k < m) : xs.length * k < m := by
  simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at h
  omega

private theorem cons_len_mul {α : Type} (x : α) (xs : List α) (k : Nat) :
    (x :: xs).length * k = k + xs.length * k := by
  simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
  omega

private theorem sep_pull_body (M Arr Pool Stk Frame : SepProp) :
    (M ∗ Arr) ∗ Pool ∗ Stk ∗ Frame = M ∗ Pool ∗ Stk ∗ (Arr ∗ Frame) := by ac_rfl

private theorem sep_push_body (M Arr Pool Stk Frame : SepProp) :
    M ∗ Pool ∗ Stk ∗ (Arr ∗ Frame) = Arr ∗ Pool ∗ Stk ∗ (M ∗ Frame) := by ac_rfl

private theorem sep_rejoin_loop (M1 M2 Pool Stk Frame : SepProp) :
    M2 ∗ Pool ∗ Stk ∗ (M1 ∗ Frame) = (M1 ∗ M2) ∗ Pool ∗ Stk ∗ Frame := by ac_rfl

private theorem vecAt_expose_loop_at_72 {α : Type} (A : RustAlloc) (sz align : Nat)
    (elem : α → BitVec 64 → SepProp) (ss cap ptr : BitVec 64) (xs : List α) :
    vecAt A sz align elem (ss + 72#64) cap ptr xs ⊢
      ⌜xs.length ≤ cap.toNat ∧ cap.toNat * sz < 2 ^ 63 ∧ xs.length * sz < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (((ss + 72#64) ↦₆₄ cap) ∗ ((ss + 80#64) ↦₆₄ ptr) ∗
        ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
        arrayAt elem sz ptr xs ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * sz) align ∗
           memRegion (ptr + BitVec.ofNat 64 (xs.length * sz)) ((cap.toNat - xs.length) * sz))) := by
  unfold vecAt vecHeader
  refine Entails.trans (sepConj_mono_right (vecBuf_expose_arrayAt A sz align elem cap ptr xs)) ?_
  have h1 : (ss + 72#64) + 8#64 = ss + 80#64 := by bv_omega
  have h2 : (ss + 72#64) + 16#64 = ss + 88#64 := by bv_omega
  rw [h1, h2]
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.Cli.LibsignalSpqrV1.M4
