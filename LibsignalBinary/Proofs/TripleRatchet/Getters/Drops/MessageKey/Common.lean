/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.Placed.Bridge
import LibsignalBinary.Proofs.Placed.PlacedCallSym
import ProofLib.Sep

/-!
# Shared Separation-Logic Helpers for Drop Glue

Stack-splitting, memory-region, and `SepWP` composition lemmas shared across the
triple-ratchet `drop_glue` proofs.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.Getters

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?

namespace DropGlueFacts

theorem dealloc_hookSat_tripleRatchetExterns {A : RustAlloc} (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    HookSat (Rust.withPanics (tripleRatchetExterns C ctl abs)) "__rustc::__rust_dealloc"
      (rustDeallocSpec A) := by
  simpa [HookSat, Rust.withPanics, Rust.isPanicSymbol, tripleRatchetExterns,
    CryptoVerification.LibsignalSession.sessionExterns, dhName, pubFromSecretName,
    staticDropName, sharedDropName, rngFillName, uuidTryParseName,
    varintSlowName, noHookNames] using hA.dealloc

theorem stackAt_dropVecMessageKey_split (sp : BitVec 64) :
    stackAt sp dropVecMessageKeyStack =
      stackAt (sp - 48#64) allocHookStack ∗ cells (sp - 48#64) 6 := by
  exact stackAt_split_cells sp allocHookStack 6 (by decide)

theorem stackAt_dropChain_split (sp : BitVec 64) :
    stackAt sp dropChainStack =
      stackAt (sp - 48#64) allocHookStack ∗ cells (sp - 48#64) 6 := by
  exact stackAt_split_cells sp allocHookStack 6 (by decide)

theorem stackAt_dropSpe_split (sp : BitVec 64) :
    stackAt sp dropSpeStack =
      stackAt (sp - 32#64) allocHookStack ∗ cells (sp - 32#64) 4 := by
  exact stackAt_split_cells sp allocHookStack 4 (by decide)

theorem stackAt_dropVecChain_split (sp : BitVec 64) :
    stackAt sp dropVecChainStack =
      stackAt (sp - 48#64) dropVecMessageKeyStack ∗ cells (sp - 48#64) 6 := by
  exact stackAt_split_cells sp dropVecMessageKeyStack 6 (by decide)

@[expose] def vecPinDealloc (A : RustAlloc) (pin : VecPin) : SepProp :=
  if (pin.cap == 0#64) = true then emp
  else A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat

theorem slt_one_iff_eq_zero {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap.slt 1#64 = true) ↔ cap = 0 := by
  have h1 : (cap = 0) ↔ cap.toNat = 0 := ⟨by rintro rfl; rfl, fun h0 => BitVec.eq_of_toNat_eq h0⟩
  have h2 : (1#64 : BitVec 64).toNat = 1 := rfl
  have h3 : 2 * cap.toNat < 2 ^ 64 := by omega
  rw [h1]
  unfold BitVec.slt BitVec.toInt
  simp only [decide_eq_true_iff, h2, h3, ↓reduceIte]
  omega

theorem vecU8At_entails_pin_dealloc (A : RustAlloc) (a : BitVec 64) (pin : VecPin)
    (bs : List (BitVec 8)) :
    vecU8At A a pin.cap pin.ptr bs ⊢
      (a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗ memRegion (a + 16#64) 8 ∗
      vecPinDealloc A pin := by
  refine Entails.trans (vecU8At_entails_dealloc A a pin.cap pin.ptr bs) ?_
  unfold vecHeader vecPinDealloc
  have hrhs : memRegion (a + 16#64) 8 = ∃∗ w : BitVec 64, (a + 16#64) ↦₆₄ w := by sep_interval_eq
  rw [hrhs]
  simp only [show (0 : BitVec 64) = 0#64 from rfl, beq_iff_eq]
  by_cases h0 : pin.cap = 0#64 <;> simp only [h0, ↓reduceIte] <;> bi_entail

theorem vecGhostAt_entails_pin_dealloc (A : RustAlloc) (g : VecGhost) (a : BitVec 64) :
    vecGhostAt A g a ⊢
      (a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗ memRegion (a + 16#64) 8 ∗
      vecPinDealloc A ⟨g.cap, g.ptr⟩ :=
  vecU8At_entails_pin_dealloc A a ⟨g.cap, g.ptr⟩ g.bytes

theorem header_cells_entails_memRegion_24 (a cap ptr : BitVec 64) :
    ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 8) ⊢ memRegion a 24 := by
  sep_interval

theorem header_cells_entails_memRegion_32 (a cap ptr : BitVec 64) :
    ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 16) ⊢ memRegion a 32 := by
  sep_interval

theorem optChainKeyAt_entails_dealloc (A : RustAlloc) (pin : VecPin)
    (ck : Option ChainKey) (a : BitVec 64) :
    optChainKeyAt A pin ck a ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 16 ∗
        (if cap.slt 1#64 = true then emp
         else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  cases ck with
  | none =>
    unfold optChainKeyAt
    have hsplit : memRegion (a + 8#64) 24 =
        (∃∗ ptr : BitVec 64, (a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 16 := by sep_interval_eq
    have hslt : optChainKeyNone.slt 1#64 = true := by decide
    rw [hsplit]
    refine Entails.sepExists_right optChainKeyNone ?_
    simp only [hslt, ↓reduceIte]; bi_entail
  | some c =>
    unfold optChainKeyAt
    refine Entails.trans (sepConj_mono_left (vecU8At_entails_dealloc A a pin.cap pin.ptr (keyToBytes32 c.key))) ?_
    simp only [sepConj_assoc]
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; rintro ⟨_, hcap_lt, _⟩
    unfold vecHeader
    refine Entails.sepExists_right pin.cap (Entails.sepExists_right pin.ptr ?_)
    have hrhs : memRegion (a + 16#64) 16 =
        (∃∗ w : BitVec 64, (a + 16#64) ↦₆₄ w) ∗
        (∃∗ idx : BitVec 32, (a + 24#64) ↦₃₂ idx) ∗
        memRegion (a + 28#64) 4 := by sep_interval_eq
    rw [hrhs]; simp only [slt_one_iff_eq_zero hcap_lt]; bi_entail

theorem seq_clean {prog : Program} {mid target : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  SepWP.seq h1 fun sm _ hpc hrun ⟨hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hQ)

theorem vecAt_expose_loop {α : Type} (A : RustAlloc) (sz align : Nat)
    (elem : α → BitVec 64 → SepProp) (base cap ptr : BitVec 64) (xs : List α) :
    vecAt A sz align elem base cap ptr xs ⊢
      ⌜xs.length ≤ cap.toNat ∧ cap.toNat * sz < 2 ^ 63 ∧ xs.length * sz < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (base ↦₆₄ cap) ∗ ((base + 8#64) ↦₆₄ ptr) ∗
      ((base + 16#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
      arrayAt elem sz ptr xs ∗
      (if cap = 0 then emp
       else A.live ptr (cap.toNat * sz) align ∗
         memRegion (ptr + BitVec.ofNat 64 (xs.length * sz)) ((cap.toNat - xs.length) * sz)) := by
  unfold vecAt vecHeader
  refine Entails.trans (sepConj_mono_right (vecBuf_expose_arrayAt A sz align elem cap ptr xs)) ?_
  bi_entail

theorem memRegion_rejoin_vecBuf (A : RustAlloc) (sz align : Nat) (cap ptr : BitVec 64)
    (n : Nat) (hle : n ≤ cap.toNat) (hcap_lt : cap.toNat * sz < 2 ^ 63) :
    memRegion ptr (n * sz) ∗
      (if cap = 0 then emp
       else A.live ptr (cap.toNat * sz) align ∗
         memRegion (ptr + BitVec.ofNat 64 (n * sz)) ((cap.toNat - n) * sz)) ⊢
    (if (cap == 0#64) = true then emp else A.live ptr (cap.toNat * sz) align ∗ memRegion ptr (cap.toNat * sz)) := by
  simp only [beq_iff_eq]
  by_cases hcap : cap = 0
  · subst hcap
    simp only [Nat.eq_zero_of_le_zero hle, Nat.zero_mul, memRegion_zero, ↓reduceIte, emp_sepConj]
    exact Entails.refl _
  · simp only [hcap, ↓reduceIte]
    have hsplit : cap.toNat * sz = n * sz + (cap.toNat - n) * sz := by
      rw [← Nat.add_mul, Nat.add_sub_of_le hle]
    rw [hsplit, ProofLib.memRegion_split ptr (n * sz) ((cap.toNat - n) * sz) (by omega)]
    bi_entail

@[expose, reducible]
def mkHeadersAt (cur : BitVec 64) (pin : MessageKeyGhost) : SepProp :=
  (cur ↦₆₄ pin.cipher.cap) ∗ ((cur + 8#64) ↦₆₄ pin.cipher.ptr) ∗ memRegion (cur + 16#64) 8 ∗
  ((cur + 24#64) ↦₆₄ pin.mac.cap) ∗ ((cur + 32#64) ↦₆₄ pin.mac.ptr) ∗ memRegion (cur + 40#64) 8 ∗
  ((cur + 48#64) ↦₆₄ pin.iv.cap) ∗ ((cur + 56#64) ↦₆₄ pin.iv.ptr) ∗ memRegion (cur + 64#64) 8 ∗
  ((cur + 72#64) ↦₆₄ pin.seed.cap) ∗ ((cur + 80#64) ↦₆₄ pin.seed.ptr) ∗ memRegion (cur + 88#64) 8 ∗
  memRegion (cur + 96#64) 8

theorem mkHeadersAt_entails_memRegion_104 (cur : BitVec 64) (pin : MessageKeyGhost) :
    mkHeadersAt cur pin ⊢ memRegion cur 104 := by
  unfold mkHeadersAt; sep_interval

theorem messageKeyAt_entails_dealloc (A : RustAlloc) (cur : BitVec 64)
    (pin : MessageKeyGhost) (mk : MessageKeyGenerator) :
    messageKeyAt A (pin, mk) cur ⊢
      mkHeadersAt cur pin ∗
      vecPinDealloc A pin.cipher ∗ vecPinDealloc A pin.mac ∗
      vecPinDealloc A pin.iv ∗ vecPinDealloc A pin.seed := by
  unfold messageKeyAt mkHeadersAt
  apply Entails.pure_left; intro _
  refine Entails.trans (sepConj_mono (vecU8At_entails_pin_dealloc A cur pin.cipher [])
    (sepConj_mono (vecU8At_entails_pin_dealloc A (cur + 24#64) pin.mac [])
      (sepConj_mono (vecU8At_entails_pin_dealloc A (cur + 48#64) pin.iv [])
        (sepConj_mono_left (vecU8At_entails_pin_dealloc A (cur + 72#64) pin.seed mk.seed))))) ?_
  have hrhs : memRegion (cur + 96#64) 8 =
      (∃∗ cnt : BitVec 32, (cur + 96#64) ↦₃₂ cnt) ∗ memRegion (cur + 100#64) 4 := by sep_interval_eq
  rw [hrhs]; bi_entail

theorem ofNat_succ_eq_add_one (n : Nat) :
    BitVec.ofNat 64 (n + 1) = BitVec.ofNat 64 n + 1#64 :=
  BitVec.ofNat_add n 1

theorem ofNat_ne_zero_of_pos {n : Nat} (hpos : 0 < n) (hlt : n * 104 < 2 ^ 63) :
    BitVec.ofNat 64 n ≠ 0#64 := by
  intro heq
  have h := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat] at h
  have hlt2 : n < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hlt2] at h
  omega

theorem ofNat_beq_zero_false {n : Nat} (hpos : 0 < n) (hlt : n * 104 < 2 ^ 63) :
    ¬((BitVec.ofNat 64 n == 0#64) = true) := by
  rw [beq_iff_eq]
  exact ofNat_ne_zero_of_pos hpos hlt

theorem ofNat_add_one_beq_one_false {n : Nat} (hpos : 0 < n) (hlt : n * 104 < 2 ^ 63) :
    ¬((BitVec.ofNat 64 n + 1#64 == 1#64) = true) := by
  rw [beq_iff_eq]
  intro heq
  have h0 : BitVec.ofNat 64 n = 0#64 := by bv_omega
  exact ofNat_ne_zero_of_pos hpos hlt h0

theorem tail_len_mul_lt {α : Type} {x : α} {xs : List α} {k m : Nat}
    (h : (x :: xs).length * k < m) : xs.length * k < m := by
  simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at h
  omega

theorem cons_len_mul {α : Type} (x : α) (xs : List α) (k : Nat) :
    (x :: xs).length * k = k + xs.length * k := by
  simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
  omega

theorem add_104_add_48 (cur : BitVec 64) : cur + 104#64 + 48#64 = cur + 152#64 := by
  bv_omega

theorem sep_pull_body (M Arr Pool Stk Frame : SepProp) :
    (M ∗ Arr) ∗ Pool ∗ Stk ∗ Frame = M ∗ Pool ∗ Stk ∗ (Arr ∗ Frame) := by sep_ac_rfl

theorem sep_push_body (M Arr Pool Stk Frame : SepProp) :
    M ∗ Pool ∗ Stk ∗ (Arr ∗ Frame) = Arr ∗ Pool ∗ Stk ∗ (M ∗ Frame) := by sep_ac_rfl

theorem sep_rejoin_loop (M1 M2 Pool Stk Frame : SepProp) :
    M2 ∗ Pool ∗ Stk ∗ (M1 ∗ Frame) = (M1 ∗ M2) ∗ Pool ∗ Stk ∗ Frame := by sep_ac_rfl

theorem post_loop_weaken (A : RustAlloc) (v cap ptr : BitVec 64) (n : Nat)
    (hle : n ≤ cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63) (Rest : SepProp) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
      memRegion ptr (n * 104) ∗
      (if cap = 0 then emp
       else A.live ptr (cap.toNat * 104) 8 ∗
         memRegion (ptr + BitVec.ofNat 64 (n * 104)) ((cap.toNat - n) * 104)) ∗
      Rest ⊢
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8 ∗
      (if (cap == 0#64) = true then emp
       else A.live ptr (cap.toNat * 104) 8 ∗ memRegion ptr (cap.toNat * 104)) ∗
      Rest := by
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _) ?_))
  rw [← sepConj_assoc]
  exact sepConj_mono_left (memRegion_rejoin_vecBuf A 104 8 cap ptr n hle hcap_lt)

theorem header24_weaken (v cap ptr : BitVec 64) (Rest : SepProp) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8 ∗ Rest ⊢
      memRegion v 24 ∗ Rest := by
  have h : (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8 ∗ Rest =
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8) ∗ Rest := by sep_ac_rfl
  rw [h]; exact sepConj_mono_left (header_cells_entails_memRegion_24 v cap ptr)

theorem tail_stack_48_from_bottom (sp : BitVec 64) :
    memRegion (sp - 4144#64) 48 ∗ stackAt sp allocHookStack =
      stackAt (sp - 48#64) allocHookStack ∗ cells (sp - 48#64) 6 := by
  dsimp only [allocHookStack]; sep_interval_eq

theorem cells6_sub48_entails (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    cells (sp - 48#64) 6 := by
  sep_interval

private theorem cells6_sub48_eq (sp : BitVec 64) :
    cells (sp - 48#64) 6 =
      (∃∗ w0 : BitVec 64, (sp - 48#64) ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (sp - 40#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (sp - 32#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (sp - 24#64) ↦₆₄ w3) ∗
      (∃∗ w4 : BitVec 64, (sp - 16#64) ↦₆₄ w4) ∗
      (∃∗ w5 : BitVec 64, (sp - 8#64) ↦₆₄ w5) := by
  sep_interval_eq

theorem stack_restore_48_allocHook (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    stackAt (sp - 48#64) allocHookStack ∗
      (((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
       ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
       ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ⊢
    stackAt sp dropVecMessageKeyStack := by
  dsimp only [allocHookStack, dropVecMessageKeyStack]; sep_interval

theorem stack_restore_48_vecChain (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    stackAt (sp - 48#64) dropVecMessageKeyStack ∗
      (((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
       ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
       ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ⊢
    stackAt sp dropVecChainStack := by
  dsimp only [dropVecMessageKeyStack, dropVecChainStack]; sep_interval

theorem cap0_weaken_48_allocHook (v cap ptr : BitVec 64) (Pool : SepProp)
    (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8 ∗
      Pool ∗ stackAt (sp - 48#64) allocHookStack ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    memRegion v 24 ∗ Pool ∗ stackAt sp dropVecMessageKeyStack := by
  refine Entails.trans (header24_weaken v cap ptr _) ?_
  rw [stackAt_dropVecMessageKey_split sp, cells6_sub48_eq sp]; bi_entail

theorem cap0_weaken_48_vecChain (v cap ptr : BitVec 64) (Pool : SepProp)
    (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8 ∗
      Pool ∗ stackAt (sp - 48#64) dropVecMessageKeyStack ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    memRegion v 24 ∗ Pool ∗ stackAt sp dropVecChainStack := by
  refine Entails.trans (header24_weaken v cap ptr _) ?_
  rw [stackAt_dropVecChain_split sp, cells6_sub48_eq sp]; bi_entail

theorem tail_dealloc_post_48_allocHook (v : BitVec 64) (Pool : SepProp) (sp : BitVec 64) :
    Pool ∗ stackAt sp allocHookStack ∗ memRegion v 24 ∗ memRegion (sp - 4144#64) 48 ⊢
      memRegion v 24 ∗ Pool ∗ stackAt sp dropVecMessageKeyStack := by
  rw [stackAt_dropVecMessageKey_split sp, ← tail_stack_48_from_bottom sp]; bi_entail

theorem tail_dealloc_pre_weaken (v cap ptr : BitVec 64) (Live Pool : SepProp)
    (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8 ∗
      Live ∗ Pool ∗
      stackAt (sp - 48#64) allocHookStack ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    memRegion v 24 ∗ Live ∗ Pool ∗
      memRegion (sp - 4144#64) 48 ∗ stackAt sp allocHookStack := by
  refine Entails.trans (header24_weaken v cap ptr _) ?_
  rw [tail_stack_48_from_bottom sp, cells6_sub48_eq sp]; bi_entail

@[expose, reducible]
def Saved48Preserved (s0 s : State) (fsp : BitVec 64) : Prop :=
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  s.sp = fsp ∧
  s.trace = s0.trace ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

theorem align_pre {prog : Program} {target : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop}
    (heq : P = P_mid)
    (h : SepWP prog target s P_mid (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm) :=
  heq ▸ h

@[expose, reducible]
def ckDealloc (A : RustAlloc) (cap ptr : BitVec 64) : SepProp :=
  if cap.slt 1#64 = true then emp
  else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat

@[expose, reducible]
def chainOuterHeadersAt (a : BitVec 64) (g : ChainGhost) (ckCap ckPtr : BitVec 64) : SepProp :=
  (a ↦₆₄ g.srk.cap) ∗ ((a + 8#64) ↦₆₄ g.srk.ptr) ∗ memRegion (a + 16#64) 8 ∗
  ((a + 24#64) ↦₆₄ g.priv.cap) ∗ ((a + 32#64) ↦₆₄ g.priv.ptr) ∗ memRegion (a + 40#64) 8 ∗
  ((a + 72#64) ↦₆₄ ckCap) ∗ ((a + 80#64) ↦₆₄ ckPtr) ∗ memRegion (a + 88#64) 16

theorem chainOuterHeadersAt_entails_memRegion_104 (a : BitVec 64) (g : ChainGhost)
    (ckCap ckPtr : BitVec 64) :
    chainOuterHeadersAt a g ckCap ckPtr ∗ memRegion (a + 48#64) 24 ⊢ memRegion a 104 := by
  unfold chainOuterHeadersAt; sep_interval

theorem chainAt_entails_dealloc (A : RustAlloc) (a : BitVec 64)
    (g : ChainGhost) (c : ReceiverChain) :
    chainAt A (g, c) a ⊢
      ∃∗ ckCap : BitVec 64, ∃∗ ckPtr : BitVec 64,
        chainOuterHeadersAt a g ckCap ckPtr ∗
        vecPinDealloc A ⟨g.srk.cap, g.srk.ptr⟩ ∗
        vecPinDealloc A ⟨g.priv.cap, g.priv.ptr⟩ ∗
        ckDealloc A ckCap ckPtr ∗
        vecAt A 104 8 (messageKeyAt A) (a + 48#64) g.mkCap g.mkPtr
          (g.keys.zip c.messageKeys) := by
  unfold chainAt chainOuterHeadersAt ckDealloc
  apply Entails.pure_left; intro _
  refine Entails.trans (sepConj_mono (vecGhostAt_entails_pin_dealloc A g.srk a)
    (sepConj_mono (vecGhostAt_entails_pin_dealloc A g.priv (a + 24#64))
      (sepConj_mono_right (optChainKeyAt_entails_dealloc A g.ck c.chainKey (a + 72#64))))) ?_
  bi_entail

theorem protoChainAt_entails_dealloc (A : RustAlloc) (a : BitVec 64)
    (g : ChainGhost) (c : ReceiverChain) :
    protoChainAt A (g, c) a ⊢
      ∃∗ ckCap : BitVec 64, ∃∗ ckPtr : BitVec 64,
        chainOuterHeadersAt a g ckCap ckPtr ∗
        vecPinDealloc A ⟨g.srk.cap, g.srk.ptr⟩ ∗
        vecPinDealloc A ⟨g.priv.cap, g.priv.ptr⟩ ∗
        ckDealloc A ckCap ckPtr ∗
        vecAt A 104 8 (messageKeyAt A) (a + 48#64) g.mkCap g.mkPtr
          (g.keys.zip c.messageKeys) := by
  unfold protoChainAt chainOuterHeadersAt ckDealloc
  apply Entails.pure_left; intro _
  refine Entails.trans (sepConj_mono (vecGhostAt_entails_pin_dealloc A g.srk a)
    (sepConj_mono (vecGhostAt_entails_pin_dealloc A g.priv (a + 24#64))
      (sepConj_mono_right (optChainKeyAt_entails_dealloc A g.ck c.chainKey (a + 72#64))))) ?_
  bi_entail

end DropGlueFacts

end CryptoVerification.LibsignalTripleRatchet.Getters
