/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Layout -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalPublicApiRepr
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs

/-!
# Layout and Loop Helpers for CLI Store Drop Glue

Provides `Dir` heap layout decompositions, 48-byte saved-register frame invariants, and reusable
symbolic-execution lemmas for the inline `Dir` map/tree deallocation loops in `IdentityFiles` and
`Stores` drop glue.
-/

public section

set_option autoImplicit false
set_option linter.unusedVariables false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession.Cli CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Arithmetic and bit-vector helpers -/

@[local wp_norm] theorem exists_two_pow_one : (∃ k : Nat, 1 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨0, rfl⟩

@[local wp_norm] theorem exists_two_pow_eight : (∃ k : Nat, 8 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨3, rfl⟩

theorem mul_48_bv (n : BitVec 64) :
    ((n + (n <<< 1)) <<< 4) = 48#64 * n := by
  bv_bits

theorem mul_48_ofNat {cap : BitVec 64} (h : cap.toNat * 48 < 2 ^ 63) :
    48#64 * cap = BitVec.ofNat 64 (cap.toNat * 48) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem mul_48_reg {cap : BitVec 64} (h : cap.toNat * 48 < 2 ^ 63) :
    ((cap + (cap <<< 1)) <<< 4) = BitVec.ofNat 64 (cap.toNat * 48) := by
  rw [mul_48_bv, mul_48_ofNat h]

theorem pos_of_beq_zero_false {cap : BitVec 64} (h : ¬(cap == 0#64) = true) :
    0 < cap.toNat := by
  have hne : cap ≠ 0#64 := fun heq => h (beq_iff_eq.mpr heq)
  exact Nat.pos_of_ne_zero (fun h0 => hne (BitVec.eq_of_toNat_eq h0))

theorem ofNat_beq_zero_false {n : Nat} (h0 : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 0 at ht
  omega

theorem ofNat_succ_eq_add_one (n : Nat) :
    BitVec.ofNat 64 (n + 1) = BitVec.ofNat 64 n + 1#64 :=
  BitVec.ofNat_add n 1

theorem ofNat_add_one_beq_one_false {n : Nat} (hpos : 0 < n) (hlt : n * 48 < 2 ^ 63) :
    (BitVec.ofNat 64 n + 1#64 == 1#64) = false := by
  rw [← ofNat_succ_eq_add_one n]
  apply beq_false_of_ne
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  change n + 1 = 1 at ht
  omega

theorem add_32_add_48 (cur : BitVec 64) : cur + 80#64 = (cur + 48#64) + 32#64 := by
  bv_omega

@[local wp_norm, local arm64_norm] theorem sub_32_of_add_32 (cur : BitVec 64) :
    (cur + 32#64) - 32#64 = cur := by bv_omega

@[local wp_norm, local arm64_norm] theorem sub_24_of_add_32 (cur : BitVec 64) :
    (cur + 32#64) - 24#64 = cur + 8#64 := by bv_omega

@[local wp_norm, local arm64_norm] theorem sub_8_of_add_32 (cur : BitVec 64) :
    (cur + 32#64) - 8#64 = cur + 24#64 := by bv_omega

@[local wp_norm, local arm64_norm] theorem add_32_sub_32 (cur : BitVec 64) :
    cur + 32#64 + bv% (2 ^ 64 - 32) = cur := by bv_omega

@[local wp_norm, local arm64_norm] theorem add_32_sub_32_assoc (cur : BitVec 64) :
    cur + (32#64 + bv% (2 ^ 64 - 32)) = cur := by bv_omega

@[local wp_norm, local arm64_norm] theorem add_32_sub_24 (cur : BitVec 64) :
    cur + 32#64 + bv% (2 ^ 64 - 24) = cur + 8#64 := by bv_omega

@[local wp_norm, local arm64_norm] theorem add_32_sub_24_assoc (cur : BitVec 64) :
    cur + (32#64 + bv% (2 ^ 64 - 24)) = cur + 8#64 := by bv_omega

@[local wp_norm, local arm64_norm] theorem add_32_sub_8 (cur : BitVec 64) :
    cur + 32#64 + bv% (2 ^ 64 - 8) = cur + 24#64 := by bv_omega

@[local wp_norm, local arm64_norm] theorem add_32_sub_8_assoc (cur : BitVec 64) :
    cur + (32#64 + bv% (2 ^ 64 - 8)) = cur + 24#64 := by bv_omega

@[local wp_norm, local arm64_norm] theorem add_32_neg_32 (cur : BitVec 64) :
    (cur + 32#64) + (-32#64) = cur := by bv_omega

@[local wp_norm, local arm64_norm] theorem add_32_neg_32_assoc (cur : BitVec 64) :
    cur + (32#64 + (-32#64)) = cur := by bv_omega

@[local wp_norm, local arm64_norm] theorem add_32_neg_24 (cur : BitVec 64) :
    (cur + 32#64) + (-24#64) = cur + 8#64 := by bv_omega

@[local wp_norm, local arm64_norm] theorem add_32_neg_24_assoc (cur : BitVec 64) :
    cur + (32#64 + (-24#64)) = cur + 8#64 := by bv_omega

@[local wp_norm, local arm64_norm] theorem add_32_neg_8 (cur : BitVec 64) :
    (cur + 32#64) + (-8#64) = cur + 24#64 := by bv_omega

@[local wp_norm, local arm64_norm] theorem add_32_neg_8_assoc (cur : BitVec 64) :
    cur + (32#64 + (-8#64)) = cur + 24#64 := by bv_omega

@[local wp_norm, local arm64_norm] theorem add_one_sub_one (x : BitVec 64) :
    (x + 1#64) - 1#64 = x := by bv_omega

@[local simp, local wp_norm, local arm64_norm] theorem reg_x0_eq : Reg.x0 = Reg.gpr 0#5 := rfl
@[local simp, local wp_norm, local arm64_norm] theorem reg_x1_eq : Reg.x1 = Reg.gpr 1#5 := rfl
@[local simp, local wp_norm, local arm64_norm] theorem reg_x2_eq : Reg.x2 = Reg.gpr 2#5 := rfl
@[local simp, local wp_norm, local arm64_norm] theorem reg_x19_eq : Reg.x19 = Reg.gpr 19#5 := rfl
@[local simp, local wp_norm, local arm64_norm] theorem reg_x20_eq : Reg.x20 = Reg.gpr 20#5 := rfl
@[local simp, local wp_norm, local arm64_norm] theorem reg_x21_eq : Reg.x21 = Reg.gpr 21#5 := rfl
@[local simp, local wp_norm, local arm64_norm] theorem reg_x22_eq : Reg.x22 = Reg.gpr 22#5 := rfl
@[local simp, local wp_norm, local arm64_norm] theorem reg_x23_eq : Reg.x23 = Reg.gpr 23#5 := rfl
@[local simp, local wp_norm, local arm64_norm] theorem reg_x24_eq : Reg.x24 = Reg.gpr 24#5 := rfl
@[local simp, local wp_norm, local arm64_norm] theorem reg_x25_eq : Reg.x25 = Reg.gpr 25#5 := rfl
@[local simp, local wp_norm, local arm64_norm] theorem reg_x26_eq : Reg.x26 = Reg.gpr 26#5 := rfl
@[local simp, local wp_norm, local arm64_norm] theorem reg_x27_eq : Reg.x27 = Reg.gpr 27#5 := rfl
@[local simp, local wp_norm, local arm64_norm] theorem reg_x28_eq : Reg.x28 = Reg.gpr 28#5 := rfl
@[local simp, local wp_norm, local arm64_norm] theorem reg_fp_eq : Reg.fp = Reg.gpr 29#5 := rfl
@[local simp, local wp_norm, local arm64_norm] theorem reg_lr_eq : Reg.lr = Reg.gpr 30#5 := rfl

/-! ## Saved-register frame invariant and `SepWP` sequencing -/

@[expose, reducible]
def Saved48Preserved (s0 s : State) (fsp : BitVec 64) : Prop :=
  s.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5) ∧
  s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) ∧
  s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) ∧
  s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) ∧
  s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) ∧
  s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
  s.sp = fsp ∧
  s.trace = s0.trace ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

/-! ## Stack and heap separation-logic helpers -/

abbrev idExactStk : Nat := 48 + extHookStack
abbrev storesExactStk : Nat := 96 + extHookStack

theorem stackAt_id_split (sp : BitVec 64) :
    stackAt sp idExactStk = stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp extHookStack 6 (by decide)

theorem stackAt_stores_split (sp : BitVec 64) :
    stackAt sp storesExactStk = stackAt (sp - 48#64) idExactStk ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp idExactStk 6 (by decide)

theorem stackAt_id_split_bottom (fsp : BitVec 64) :
    stackAt fsp idExactStk = memRegion (fsp - 16432#64) 48 ∗ stackAt fsp extHookStack :=
  stackAt_split_bottom fsp extHookStack 48 (by decide)

theorem cells6_sub48_entails (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    (((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
     ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
     ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ⊢
    cells (sp - 48#64) 6 := by
  have hc : cells (sp - 48#64) 6 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
       ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 48#64) ↦₆₄ v0) ∗ ((sp - 40#64) ↦₆₄ v1) ∗
        ((sp - 32#64) ↦₆₄ v2) ∗ ((sp - 24#64) ↦₆₄ v3) ∗
        ((sp - 16#64) ↦₆₄ v4) ∗ ((sp - 8#64) ↦₆₄ v5)) := by
    cells_unfold
  rw [hc]
  exact Entails.sepExists_right fp (Entails.sepExists_right lr
    (Entails.sepExists_right x22 (Entails.sepExists_right x21
      (Entails.sepExists_right x20 (Entails.sepExists_right x19 (Entails.refl _))))))

theorem stack_restore_id (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    stackAt (sp - 48#64) extHookStack ∗
      (((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
       ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
       ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ⊢
    stackAt sp idExactStk := by
  rw [stackAt_id_split sp]
  exact sepConj_mono_right (cells6_sub48_entails sp fp lr x22 x21 x20 x19)

theorem stack_restore_stores (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    stackAt (sp - 48#64) idExactStk ∗
      (((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
       ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
       ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ⊢
    stackAt sp storesExactStk := by
  rw [stackAt_stores_split sp]
  exact sepConj_mono_right (cells6_sub48_entails sp fp lr x22 x21 x20 x19)

theorem tail_stack_id_eq (sp : BitVec 64) :
    memRegion (sp - 16432#64) 48 ∗ stackAt sp extHookStack =
      stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 := by
  rw [← stackAt_id_split sp]
  exact (stackAt_split_bottom sp extHookStack 48 (by decide)).symm

theorem tail_stack_stores_eq (sp : BitVec 64) :
    memRegion (sp - 16480#64) 96 ∗ stackAt sp extHookStack =
      stackAt (sp - 48#64) idExactStk ∗ cells (sp - 48#64) 6 := by
  rw [← stackAt_stores_split sp]
  exact (stackAt_split_bottom sp extHookStack 96 (by decide)).symm

theorem tail_stack_id_entails (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    stackAt (sp - 48#64) extHookStack ∗
      (((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
       ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
       ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ⊢
    memRegion (sp - 16432#64) 48 ∗ stackAt sp extHookStack := by
  rw [tail_stack_id_eq sp]
  exact sepConj_mono_right (cells6_sub48_entails sp fp lr x22 x21 x20 x19)

theorem tail_stack_stores_entails (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    stackAt (sp - 48#64) idExactStk ∗
      (((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
       ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
       ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ⊢
    memRegion (sp - 16480#64) 96 ∗ stackAt sp extHookStack := by
  rw [tail_stack_stores_eq sp]
  exact sepConj_mono_right (cells6_sub48_entails sp fp lr x22 x21 x20 x19)

@[expose] def roPathAt (lit : List (BitVec 8)) : SepProp :=
  ∃∗ p : BitVec 64, p ↦ᵣ lit

theorem strRefAt_entails_memRegion16_ro (a : BitVec 64) (lit : List (BitVec 8)) :
    strRefAt a lit ⊢ memRegion a 16 ∗ roPathAt lit := by
  unfold strRefAt roPathAt
  apply Entails.sepExists_elim
  intro p
  have hm : (a ↦₆₄ p) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 lit.length) ⊢ memRegion a 16 := by
    rw [show (16 : Nat) = 8 + 8 from rfl, ProofLib.memRegion_split a 8 8 (by decide)]
    exact sepConj_mono (pointsTo64_entails_memRegion a p)
      (pointsTo64_entails_memRegion (a + 8#64) _)
  refine Entails.trans (Entails.of_eq (show _ =
      ((a ↦₆₄ p) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 lit.length)) ∗ (p ↦ᵣ lit) by ac_rfl)) ?_
  exact sepConj_mono hm (Entails.sepExists_right p (Entails.refl _))

@[expose] def dirRawAt (A : RustAlloc) (d : BitVec 64) (xs : List (List (BitVec 8) × List (BitVec 8))) :
    SepProp :=
  RustHeap.vecOf A 48 8 (dirEntryAt A) d xs ∗ memRegion (d + 0x18#64) 16

theorem dirAt_entails_raw_ro (A : RustAlloc) (d : BitVec 64) (g : DirGhost) :
    dirAt A d g ⊢ dirRawAt A d g.changed ∗ roPathAt g.path := by
  unfold dirAt dirRawAt
  refine Entails.trans
    (sepConj_mono_right (strRefAt_entails_memRegion16_ro (d + 0x18#64) g.path)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem id_entry_raw_ro (A : RustAlloc) (a : BitVec 64) (d0 d1 : DirGhost) :
    dirAt A a d0 ∗ dirAt A (a + 0x28#64) d1 ⊢
      (dirRawAt A a d0.changed ∗ dirRawAt A (a + 0x28#64) d1.changed) ∗
      (roPathAt d0.path ∗ roPathAt d1.path) := by
  refine Entails.trans
    (sepConj_mono (dirAt_entails_raw_ro A a d0) (dirAt_entails_raw_ro A (a + 0x28#64) d1)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem stores_entry_raw_ro (A : RustAlloc) (a : BitVec 64) (g : StoresGhost) :
    storesAt A a g ⊢
      (dirAt A a g.identity.own ∗ dirAt A (a + 0x28#64) g.identity.peers ∗
        dirRawAt A (a + 0x50#64) g.signed.changed ∗
        dirAt A (a + 0x78#64) g.kyber.oneTime ∗ dirAt A (a + 0xa0#64) g.kyber.lastResort ∗
        dirRawAt A (a + 0xc8#64) g.oneTime.changed ∗
        dirRawAt A (a + 0xf0#64) g.sessions.changed ∗
        dirRawAt A (a + 0x118#64) g.pub.changed) ∗
      (roPathAt g.signed.path ∗ roPathAt g.oneTime.path ∗
        roPathAt g.sessions.path ∗ roPathAt g.pub.path) := by
  unfold storesAt
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (dirAt_entails_raw_ro A (a + 0x50#64) g.signed)
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono (dirAt_entails_raw_ro A (a + 0xc8#64) g.oneTime)
            (sepConj_mono (dirAt_entails_raw_ro A (a + 0xf0#64) g.sessions)
              (dirAt_entails_raw_ro A (a + 0x118#64) g.pub)))))))) ?_
  exact Entails.of_eq (by ac_rfl)

@[expose, reducible]
def vecPinDeallocX (A : RustAlloc) (cap ptr : BitVec 64) : SepProp :=
  if (cap == 0#64) = true then emp
  else ⌜0 < cap.toNat ∧ cap.toNat < 2 ^ 63⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat

@[expose] def entryHeadersAt (cur nc np bc bp : BitVec 64) : SepProp :=
  (cur ↦₆₄ nc) ∗ ((cur + 8#64) ↦₆₄ np) ∗ memRegion (cur + 16#64) 8 ∗
  ((cur + 24#64) ↦₆₄ bc) ∗ ((cur + 32#64) ↦₆₄ bp) ∗ memRegion (cur + 40#64) 8

theorem vecU8At_entails_pin_deallocX (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs ⊢
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 8 ∗
      vecPinDeallocX A cap ptr := by
  unfold vecU8At vecHeader vecPinDeallocX
  refine Entails.trans (Entails.of_eq (show _ =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
            memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) by ac_rfl)) ?_
  apply Entails.pure_left
  rintro ⟨hbs_le, hcap_lt, _⟩
  have hbeq : ((cap == 0#64) = true) ↔ cap = 0 := beq_iff_eq
  simp only [hbeq]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _) ?_))
  by_cases h0 : cap = 0
  · simp only [h0, ↓reduceIte]
    exact Entails.refl _
  · simp only [h0, ↓reduceIte]
    have hpos : 0 < cap.toNat := Nat.pos_of_ne_zero (fun h => h0 (BitVec.eq_of_toNat_eq h))
    have hsplit := ProofLib.memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega)
    rw [show bs.length + (cap.toNat - bs.length) = cap.toNat by omega] at hsplit
    refine Entails.pure_right ⟨hpos, hcap_lt⟩ ?_
    rw [hsplit]
    exact sepConj_mono_right (sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs))

theorem dirEntryAt_expose (A : RustAlloc) (e : List (BitVec 8) × List (BitVec 8)) (cur : BitVec 64) :
    dirEntryAt A e cur ⊢
      ∃∗ nc : BitVec 64, ∃∗ np : BitVec 64, ∃∗ bc : BitVec 64, ∃∗ bp : BitVec 64,
        entryHeadersAt cur nc np bc bp ∗ vecPinDeallocX A nc np ∗ vecPinDeallocX A bc bp := by
  unfold dirEntryAt vecU8
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro nc
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro np
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro bc
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro bp
  refine Entails.sepExists_right nc (Entails.sepExists_right np
    (Entails.sepExists_right bc (Entails.sepExists_right bp ?_)))
  have h1 := vecU8At_entails_pin_deallocX A cur nc np e.1
  have h2 := vecU8At_entails_pin_deallocX A (cur + 24#64) bc bp e.2
  have ha1 : (cur + 24#64) + 8#64 = cur + 32#64 := by bv_omega
  have ha2 : (cur + 24#64) + 16#64 = cur + 40#64 := by bv_omega
  rw [ha1, ha2] at h2
  unfold entryHeadersAt
  refine Entails.trans (sepConj_mono h1 h2) ?_
  exact Entails.of_eq (by ac_rfl)

theorem entryHeadersAt_entails_memRegion_48 (cur nc np bc bp : BitVec 64) :
    entryHeadersAt cur nc np bc bp ⊢ memRegion cur 48 := by
  unfold entryHeadersAt
  have hs1 := ProofLib.memRegion_split cur 8 40 (by decide)
  have hs2 := ProofLib.memRegion_split (cur + 8#64) 8 32 (by decide)
  have hs3 := ProofLib.memRegion_split (cur + 16#64) 8 24 (by decide)
  have hs4 := ProofLib.memRegion_split (cur + 24#64) 8 16 (by decide)
  have hs5 := ProofLib.memRegion_split (cur + 32#64) 8 8 (by decide)
  rw [show cur + BitVec.ofNat 64 8 = cur + 8#64 by rfl] at hs1
  rw [show cur + 8#64 + BitVec.ofNat 64 8 = cur + 16#64 by bv_omega] at hs2
  rw [show cur + 16#64 + BitVec.ofNat 64 8 = cur + 24#64 by bv_omega] at hs3
  rw [show cur + 24#64 + BitVec.ofNat 64 8 = cur + 32#64 by bv_omega] at hs4
  rw [show cur + 32#64 + BitVec.ofNat 64 8 = cur + 40#64 by bv_omega] at hs5
  rw [hs1, hs2, hs3, hs4, hs5]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (Entails.refl _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)))))

theorem dirRawAt_expose (A : RustAlloc) (d : BitVec 64)
    (xs : List (List (BitVec 8) × List (BitVec 8))) :
    dirRawAt A d xs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜xs.length ≤ cap.toNat ∧ cap.toNat * 48 < 2 ^ 63 ∧ xs.length * 48 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (d ↦₆₄ cap) ∗ ((d + 8#64) ↦₆₄ ptr) ∗ ((d + 16#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
        arrayAt (dirEntryAt A) 48 ptr xs ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * 48) 8 ∗
           memRegion (ptr + BitVec.ofNat 64 (xs.length * 48)) ((cap.toNat - xs.length) * 48)) ∗
        memRegion (d + 24#64) 16 := by
  unfold dirRawAt RustHeap.vecOf RustHeap.vecAt vecHeader vecBuf
  simp only [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  refine Entails.trans (Entails.of_eq (show _ =
      (⌜xs.length ≤ cap.toNat ∧ cap.toNat * 48 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ((d ↦₆₄ cap) ∗ ((d + 8#64) ↦₆₄ ptr) ∗ ((d + 16#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
          (if cap = 0 then emp
           else A.live ptr (cap.toNat * 48) 8 ∗ arrayAt (dirEntryAt A) 48 ptr xs ∗
             memRegion (ptr + BitVec.ofNat 64 (xs.length * 48)) ((cap.toNat - xs.length) * 48)) ∗
          memRegion (d + 24#64) 16)) by ac_rfl)) ?_
  apply Entails.pure_left
  rintro ⟨hlen_le, hcap_lt, hptr_ne⟩
  have hlen_lt : xs.length * 48 < 2 ^ 63 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 48 hlen_le) hcap_lt
  refine Entails.pure_right ⟨hlen_le, hcap_lt, hlen_lt, hptr_ne⟩ ?_
  by_cases h0 : cap = 0
  · subst h0
    have hnil : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen_le)
    subst hnil
    simp only [↓reduceIte, arrayAt, emp_sepConj]
    exact Entails.of_eq (by ac_rfl)
  · simp only [h0, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)

theorem dirRawAt_expose_off (A : RustAlloc) (base off off8 off16 off24 : BitVec 64)
    (h8 : (base + off) + 8#64 = base + off8)
    (h16 : (base + off) + 16#64 = base + off16)
    (h24 : (base + off) + 24#64 = base + off24)
    (xs : List (List (BitVec 8) × List (BitVec 8))) :
    dirRawAt A (base + off) xs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜xs.length ≤ cap.toNat ∧ cap.toNat * 48 < 2 ^ 63 ∧ xs.length * 48 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ((base + off) ↦₆₄ cap) ∗ ((base + off8) ↦₆₄ ptr) ∗
        ((base + off16) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
        arrayAt (dirEntryAt A) 48 ptr xs ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * 48) 8 ∗
           memRegion (ptr + BitVec.ofNat 64 (xs.length * 48)) ((cap.toNat - xs.length) * 48)) ∗
        memRegion (base + off24) 16 := by
  have h := dirRawAt_expose A (base + off) xs
  rw [h8, h16, h24] at h
  exact h

theorem post_dir_loop_weaken (A : RustAlloc) (d cap ptr : BitVec 64) (len : Nat)
    (hlen_le : len ≤ cap.toNat) (hcap_lt : cap.toNat * 48 < 2 ^ 63) (Rest : SepProp) :
    (d ↦₆₄ cap) ∗ ((d + 8#64) ↦₆₄ ptr) ∗ ((d + 16#64) ↦₆₄ BitVec.ofNat 64 len) ∗
      memRegion ptr (len * 48) ∗
      (if cap = 0 then emp
       else A.live ptr (cap.toNat * 48) 8 ∗
         memRegion (ptr + BitVec.ofNat 64 (len * 48)) ((cap.toNat - len) * 48)) ∗
      memRegion (d + 24#64) 16 ∗ Rest ⊢
    (d ↦₆₄ cap) ∗ memRegion (d + 8#64) 32 ∗
      (if (cap == 0#64) = true then emp
       else A.live ptr (cap.toNat * 48) 8 ∗ memRegion ptr (cap.toNat * 48)) ∗ Rest := by
  have hcore :
      ((d ↦₆₄ cap) ∗ ((d + 8#64) ↦₆₄ ptr) ∗ ((d + 16#64) ↦₆₄ BitVec.ofNat 64 len) ∗
        memRegion ptr (len * 48) ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * 48) 8 ∗
           memRegion (ptr + BitVec.ofNat 64 (len * 48)) ((cap.toNat - len) * 48)) ∗
        memRegion (d + 24#64) 16) ⊢
      ((d ↦₆₄ cap) ∗ memRegion (d + 8#64) 32 ∗
        (if (cap == 0#64) = true then emp
         else A.live ptr (cap.toNat * 48) 8 ∗ memRegion ptr (cap.toNat * 48))) := by
    have h32 : ((d + 8#64) ↦₆₄ ptr) ∗ ((d + 16#64) ↦₆₄ BitVec.ofNat 64 len) ∗
        memRegion (d + 24#64) 16 ⊢ memRegion (d + 8#64) 32 := by
      have hs1 := ProofLib.memRegion_split (d + 8#64) 8 24 (by decide)
      have hs2 := ProofLib.memRegion_split (d + 16#64) 8 16 (by decide)
      rw [show d + 8#64 + BitVec.ofNat 64 8 = d + 16#64 by bv_omega] at hs1
      rw [show d + 16#64 + BitVec.ofNat 64 8 = d + 24#64 by bv_omega] at hs2
      rw [hs1, hs2]
      exact sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _))
    have hbeq : ((cap == 0#64) = true) ↔ cap = 0 := beq_iff_eq
    simp only [hbeq]
    by_cases h0 : cap = 0
    · subst h0
      have hlen0 : len = 0 := by simpa using hlen_le
      subst hlen0
      simp only [Nat.zero_mul, memRegion_zero, ↓reduceIte, emp_sepConj, sepConj_emp]
      refine Entails.trans (Entails.of_eq (show
          ((d ↦₆₄ 0#64) ∗ ((d + 8#64) ↦₆₄ ptr) ∗ ((d + 16#64) ↦₆₄ BitVec.ofNat 64 0) ∗
            memRegion (d + 24#64) 16) =
          ((d ↦₆₄ 0#64) ∗ (((d + 8#64) ↦₆₄ ptr) ∗ ((d + 16#64) ↦₆₄ BitVec.ofNat 64 0) ∗
            memRegion (d + 24#64) 16)) by ac_rfl))
        (sepConj_mono_right h32)
    · simp only [h0, ↓reduceIte]
      have hbuf : memRegion ptr (len * 48) ∗
          memRegion (ptr + BitVec.ofNat 64 (len * 48)) ((cap.toNat - len) * 48) =
          memRegion ptr (cap.toNat * 48) := by
        have hs := ProofLib.memRegion_split ptr (len * 48) ((cap.toNat - len) * 48) (by omega)
        rw [show len * 48 + (cap.toNat - len) * 48 = cap.toNat * 48 by
          rw [← Nat.add_mul]; congr 1; omega] at hs
        exact hs.symm
      refine Entails.trans (Entails.of_eq (show _ =
          (d ↦₆₄ cap) ∗
          (((d + 8#64) ↦₆₄ ptr) ∗ ((d + 16#64) ↦₆₄ BitVec.ofNat 64 len) ∗ memRegion (d + 24#64) 16) ∗
          A.live ptr (cap.toNat * 48) 8 ∗
          (memRegion ptr (len * 48) ∗
            memRegion (ptr + BitVec.ofNat 64 (len * 48)) ((cap.toNat - len) * 48)) by ac_rfl)) ?_
      rw [hbuf]
      exact sepConj_mono_right (sepConj_mono_left h32)
  refine Entails.trans (Entails.of_eq (show _ =
    ((d ↦₆₄ cap) ∗ ((d + 8#64) ↦₆₄ ptr) ∗ ((d + 16#64) ↦₆₄ BitVec.ofNat 64 len) ∗
      memRegion ptr (len * 48) ∗
      (if cap = 0 then emp
       else A.live ptr (cap.toNat * 48) 8 ∗
         memRegion (ptr + BitVec.ofNat 64 (len * 48)) ((cap.toNat - len) * 48)) ∗
      memRegion (d + 24#64) 16) ∗ Rest by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hcore) ?_
  exact Entails.of_eq (by ac_rfl)

theorem post_dir_loop_weaken_off (A : RustAlloc) (base off off8 off16 off24 cap ptr : BitVec 64)
    (h8 : (base + off) + 8#64 = base + off8)
    (h16 : (base + off) + 16#64 = base + off16)
    (h24 : (base + off) + 24#64 = base + off24)
    (len : Nat) (hlen_le : len ≤ cap.toNat) (hcap_lt : cap.toNat * 48 < 2 ^ 63) (Rest : SepProp) :
    ((base + off) ↦₆₄ cap) ∗ ((base + off8) ↦₆₄ ptr) ∗
      ((base + off16) ↦₆₄ BitVec.ofNat 64 len) ∗
      memRegion ptr (len * 48) ∗
      (if cap = 0 then emp
       else A.live ptr (cap.toNat * 48) 8 ∗
         memRegion (ptr + BitVec.ofNat 64 (len * 48)) ((cap.toNat - len) * 48)) ∗
      memRegion (base + off24) 16 ∗ Rest ⊢
    ((base + off) ↦₆₄ cap) ∗ memRegion (base + off8) 32 ∗
      (if (cap == 0#64) = true then emp
       else A.live ptr (cap.toNat * 48) 8 ∗ memRegion ptr (cap.toNat * 48)) ∗ Rest := by
  rw [← h8, ← h16, ← h24]
  exact post_dir_loop_weaken A (base + off) cap ptr len hlen_le hcap_lt Rest

theorem word_and_32_entails_40 (d cap : BitVec 64) :
    (d ↦₆₄ cap) ∗ memRegion (d + 8#64) 32 ⊢ memRegion d 40 := by
  rw [show (40 : Nat) = 8 + 32 from rfl, ProofLib.memRegion_split d 8 32 (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion d cap)

theorem word_and_32_rest_entails_40 (d cap : BitVec 64) (Rest : SepProp) :
    (d ↦₆₄ cap) ∗ memRegion (d + 8#64) 32 ∗ Rest ⊢ memRegion d 40 ∗ Rest := by
  refine Entails.trans (Entails.of_eq (show _ =
    ((d ↦₆₄ cap) ∗ memRegion (d + 8#64) 32) ∗ Rest by ac_rfl)) ?_
  exact sepConj_mono_left (word_and_32_entails_40 d cap)

theorem word_and_32_rest_entails_40_off (base off off8 cap : BitVec 64)
    (h8 : (base + off) + 8#64 = base + off8) (Rest : SepProp) :
    ((base + off) ↦₆₄ cap) ∗ memRegion (base + off8) 32 ∗ Rest ⊢
      memRegion (base + off) 40 ∗ Rest := by
  rw [← h8]
  exact word_and_32_rest_entails_40 (base + off) cap Rest

theorem memRegion_40_40 (a : BitVec 64) :
    memRegion a 40 ∗ memRegion (a + 0x28#64) 40 = memRegion a 80 :=
  (ProofLib.memRegion_split a 40 40 (by decide)).symm

theorem stores_regions_merge (a : BitVec 64) :
    memRegion a 80 ∗ memRegion (a + 0x50#64) 40 ∗ memRegion (a + 0x78#64) 80 ∗
      memRegion (a + 0xc8#64) 40 ∗ memRegion (a + 0xf0#64) 40 ∗
      memRegion (a + 0x118#64) 40 = memRegion a 320 := by
  have h1 := ProofLib.memRegion_split a 80 240 (by decide)
  have h2 := ProofLib.memRegion_split (a + 80#64) 40 200 (by decide)
  have h3 := ProofLib.memRegion_split (a + 120#64) 80 120 (by decide)
  have h4 := ProofLib.memRegion_split (a + 200#64) 40 80 (by decide)
  have h5 := ProofLib.memRegion_split (a + 240#64) 40 40 (by decide)
  rw [show a + BitVec.ofNat 64 80 = a + 80#64 by rfl] at h1
  rw [show a + 80#64 + BitVec.ofNat 64 40 = a + 120#64 by bv_omega] at h2
  rw [show a + 120#64 + BitVec.ofNat 64 80 = a + 200#64 by bv_omega] at h3
  rw [show a + 200#64 + BitVec.ofNat 64 40 = a + 240#64 by bv_omega] at h4
  rw [show a + 240#64 + BitVec.ofNat 64 40 = a + 280#64 by bv_omega] at h5
  rw [h1, h2, h3, h4, h5]

theorem id_cap0_ret_weaken (a cap : BitVec 64) (Pool : SepProp)
    (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    memRegion a 40 ∗ ((a + 0x28#64) ↦₆₄ cap) ∗ memRegion (a + 48#64) 32 ∗
      Pool ∗ stackAt (sp - 48#64) extHookStack ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    memRegion a 80 ∗ Pool ∗ stackAt sp idExactStk := by
  have hd1 := word_and_32_entails_40 (a + 0x28#64) cap
  rw [show (a + 0x28#64) + 8#64 = a + 48#64 by bv_omega] at hd1
  have hstk := stack_restore_id sp fp lr x22 x21 x20 x19
  refine Entails.trans (Entails.of_eq (show _ =
      memRegion a 40 ∗ (((a + 0x28#64) ↦₆₄ cap) ∗ memRegion (a + 48#64) 32) ∗
      Pool ∗
      (stackAt (sp - 48#64) extHookStack ∗
        (((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
         ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
         ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono hd1 (sepConj_mono_right hstk))) ?_
  rw [← sepConj_assoc, memRegion_40_40 a]
  exact Entails.of_eq (by ac_rfl)

theorem id_tail_dealloc_pre_weaken (a cap : BitVec 64) (Live Pool : SepProp)
    (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    memRegion a 40 ∗ ((a + 0x28#64) ↦₆₄ cap) ∗ memRegion (a + 48#64) 32 ∗
      Live ∗ Pool ∗ stackAt (sp - 48#64) extHookStack ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    Pool ∗ Live ∗ stackAt sp extHookStack ∗
      (memRegion a 80 ∗ memRegion (sp - 16432#64) 48) := by
  have hd1 := word_and_32_entails_40 (a + 0x28#64) cap
  rw [show (a + 0x28#64) + 8#64 = a + 48#64 by bv_omega] at hd1
  have hstk := tail_stack_id_entails sp fp lr x22 x21 x20 x19
  refine Entails.trans (Entails.of_eq (show _ =
      (memRegion a 40 ∗ (((a + 0x28#64) ↦₆₄ cap) ∗ memRegion (a + 48#64) 32)) ∗
      Live ∗ Pool ∗
      (stackAt (sp - 48#64) extHookStack ∗
        (((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
         ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
         ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono (sepConj_mono_right hd1)
    (sepConj_mono_right (sepConj_mono_right hstk))) ?_
  rw [memRegion_40_40 a]
  exact Entails.of_eq (by ac_rfl)

theorem id_tail_dealloc_post (a : BitVec 64) (Pool : SepProp) (sp : BitVec 64) :
    Pool ∗ stackAt sp extHookStack ∗ (memRegion a 80 ∗ memRegion (sp - 16432#64) 48) ⊢
      memRegion a 80 ∗ Pool ∗ stackAt sp idExactStk := by
  rw [stackAt_id_split sp, ← tail_stack_id_eq sp]
  exact Entails.of_eq (by ac_rfl)

theorem stores_cap0_ret_weaken (a cap : BitVec 64) (Pool : SepProp)
    (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    memRegion a 80 ∗ memRegion (a + 0x50#64) 40 ∗ memRegion (a + 0x78#64) 80 ∗
      memRegion (a + 0xc8#64) 40 ∗ memRegion (a + 0xf0#64) 40 ∗
      ((a + 0x118#64) ↦₆₄ cap) ∗ memRegion (a + 288#64) 32 ∗
      Pool ∗ memRegion ((sp - 48#64) - 16432#64) 48 ∗ stackAt (sp - 48#64) extHookStack ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    memRegion a 320 ∗ Pool ∗ stackAt sp storesExactStk := by
  have hd7 := word_and_32_entails_40 (a + 0x118#64) cap
  rw [show (a + 0x118#64) + 8#64 = a + 288#64 by bv_omega] at hd7
  have hstk := stack_restore_stores sp fp lr x22 x21 x20 x19
  rw [stackAt_id_split_bottom (sp - 48#64)] at hstk
  refine Entails.trans (Entails.of_eq (show _ =
      (memRegion a 80 ∗ memRegion (a + 0x50#64) 40 ∗ memRegion (a + 0x78#64) 80 ∗
        memRegion (a + 0xc8#64) 40 ∗ memRegion (a + 0xf0#64) 40 ∗
        (((a + 0x118#64) ↦₆₄ cap) ∗ memRegion (a + 288#64) 32)) ∗
      Pool ∗
      ((memRegion ((sp - 48#64) - 16432#64) 48 ∗ stackAt (sp - 48#64) extHookStack) ∗
        (((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
         ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
         ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right hd7)))))
    (sepConj_mono_right hstk)) ?_
  rw [show memRegion a 80 ∗
        (memRegion (a + 0x50#64) 40 ∗
          (memRegion (a + 0x78#64) 80 ∗
            (memRegion (a + 0xc8#64) 40 ∗
              (memRegion (a + 0xf0#64) 40 ∗ memRegion (a + 0x118#64) 40)))) =
        memRegion a 320 by
      rw [← stores_regions_merge a]]
  exact Entails.of_eq (by ac_rfl)

theorem stores_tail_dealloc_pre_weaken (a cap : BitVec 64) (Live Pool : SepProp)
    (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    memRegion a 80 ∗ memRegion (a + 0x50#64) 40 ∗ memRegion (a + 0x78#64) 80 ∗
      memRegion (a + 0xc8#64) 40 ∗ memRegion (a + 0xf0#64) 40 ∗
      ((a + 0x118#64) ↦₆₄ cap) ∗ memRegion (a + 288#64) 32 ∗
      Live ∗ Pool ∗ memRegion ((sp - 48#64) - 16432#64) 48 ∗ stackAt (sp - 48#64) extHookStack ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    Pool ∗ Live ∗ stackAt sp extHookStack ∗
      (memRegion a 320 ∗ memRegion (sp - 16480#64) 96) := by
  have hd7 := word_and_32_entails_40 (a + 0x118#64) cap
  rw [show (a + 0x118#64) + 8#64 = a + 288#64 by bv_omega] at hd7
  have hstk := tail_stack_stores_entails sp fp lr x22 x21 x20 x19
  rw [stackAt_id_split_bottom (sp - 48#64)] at hstk
  refine Entails.trans (Entails.of_eq (show _ =
      (memRegion a 80 ∗ memRegion (a + 0x50#64) 40 ∗ memRegion (a + 0x78#64) 80 ∗
        memRegion (a + 0xc8#64) 40 ∗ memRegion (a + 0xf0#64) 40 ∗
        (((a + 0x118#64) ↦₆₄ cap) ∗ memRegion (a + 288#64) 32)) ∗
      Live ∗ Pool ∗
      ((memRegion ((sp - 48#64) - 16432#64) 48 ∗ stackAt (sp - 48#64) extHookStack) ∗
        (((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
         ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
         ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right hd7)))))
    (sepConj_mono_right (sepConj_mono_right hstk))) ?_
  rw [show memRegion a 80 ∗
        (memRegion (a + 0x50#64) 40 ∗
          (memRegion (a + 0x78#64) 80 ∗
            (memRegion (a + 0xc8#64) 40 ∗
              (memRegion (a + 0xf0#64) 40 ∗ memRegion (a + 0x118#64) 40)))) =
        memRegion a 320 by
      rw [← stores_regions_merge a]]
  exact Entails.of_eq (by ac_rfl)

theorem stores_tail_dealloc_post (a : BitVec 64) (Pool : SepProp) (sp : BitVec 64) :
    Pool ∗ stackAt sp extHookStack ∗ (memRegion a 320 ∗ memRegion (sp - 16480#64) 96) ⊢
      memRegion a 320 ∗ Pool ∗ stackAt sp storesExactStk := by
  rw [stackAt_stores_split sp, ← tail_stack_stores_eq sp]
  exact Entails.of_eq (by ac_rfl)

/-! ## Loop and inline `Dir` drop block helpers -/

theorem sep_pull_entry (M Arr Pool Stk Frame : SepProp) :
    (M ∗ Arr) ∗ Pool ∗ Stk ∗ Frame = M ∗ Pool ∗ Stk ∗ (Arr ∗ Frame) := by ac_rfl

theorem sep_push_entry (M Arr Pool Stk Frame : SepProp) :
    M ∗ Pool ∗ Stk ∗ (Arr ∗ Frame) = Arr ∗ Pool ∗ Stk ∗ (M ∗ Frame) := by ac_rfl

theorem sep_rejoin_entries (M1 M2 Pool Stk Frame : SepProp) :
    M2 ∗ Pool ∗ Stk ∗ (M1 ∗ Frame) = (M1 ∗ M2) ∗ Pool ∗ Stk ∗ Frame := by ac_rfl

theorem tail_len_mul_48_lt {α : Type} {hd : α} {tl : List α}
    (h : (hd :: tl).length * 48 < 2 ^ 63) :
    tl.length * 48 < 2 ^ 63 := by
  simp only [List.length_cons] at h
  omega

theorem cons_len_mul_48 {α : Type} (hd : α) (tl : List α) :
    48 + tl.length * 48 = (hd :: tl).length * 48 := by
  simp only [List.length_cons, Nat.succ_mul]
  omega

theorem weaken_perm {P P' Q : SepProp} (h : P' ⊢ Q) (heq : P = P') : P ⊢ Q :=
  heq ▸ h

end CryptoVerification.SignalSession.Cli.RunProofs.Helpers
