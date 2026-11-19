/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Bytes.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Bytes.BytesCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Common.InImageLift -- proof-setup: allow-public-import
public import ProofLib.SepLogic.WP
import LibsignalBinary.Proofs.CodeLayout -- shake: keep
public import ProofLib.SepLogic.WP.Apply -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContracts
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.InImageLift

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Decoded Instructions for Drop Functions -/

/-! ### `bytes::bytes::static_drop` (`0x40950`, 4 bytes) -/
private theorem stackAt_add_48_opt {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (hookStack + 48) =
      stackAt (sp - 48#64) hookStack ∗ cells (sp - 48#64) 6 :=
  stackAt_split_cells sp hookStack 6 hstack

private theorem stackAt_add_48_comm_opt {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (hookStack + 48) =
      stackAt (sp - BitVec.ofNat 64 hookStack) 48 ∗ stackAt sp hookStack := by
  unfold stackAt
  have h0 : hookStack + 48 = 48 + hookStack := Nat.add_comm hookStack 48
  have hsplit := memRegion_split (sp - BitVec.ofNat 64 (48 + hookStack)) 48 hookStack (by omega)
  have h1 : sp - BitVec.ofNat 64 (48 + hookStack) =
      sp - BitVec.ofNat 64 hookStack - 48#64 := by
    rw [BitVec.ofNat_add]
    bv_lin
  have h2 : sp - BitVec.ofNat 64 (48 + hookStack) + 48#64 =
      sp - BitVec.ofNat 64 hookStack := by
    rw [BitVec.ofNat_add]
    bv_lin
  rw [h0, hsplit, h2, h1]

private theorem pointsTo64_entails_exists (a v : BitVec 64) {R Q : SepProp}
    (h : R ⊢ Q) : ((a ↦₆₄ v) ∗ R) ⊢ ∃∗ x, (a ↦₆₄ x) ∗ Q :=
  Entails.trans (sepConj_mono_right h) (Entails.sepExists_intro (P := fun x => (a ↦₆₄ x) ∗ Q) v)

private theorem pointsTo64_entails_exists_single (a v : BitVec 64) :
    (a ↦₆₄ v) ⊢ ∃∗ x, (a ↦₆₄ x) :=
  Entails.sepExists_intro (P := fun x => a ↦₆₄ x) v

private theorem pointsTo64_6_entails_cells (base : BitVec 64)
    (v0 v1 v2 v3 v4 v5 : BitVec 64) :
    ((base ↦₆₄ v0) ∗ ((base + 8#64) ↦₆₄ v1) ∗
      ((base + 16#64) ↦₆₄ v2) ∗ ((base + 24#64) ↦₆₄ v3) ∗
      ((base + 32#64) ↦₆₄ v4) ∗ ((base + 40#64) ↦₆₄ v5)) ⊢ cells base 6 := by
  simp only [cells_succ, cells_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  exact pointsTo64_entails_exists _ v0
    (pointsTo64_entails_exists _ v1
      (pointsTo64_entails_exists _ v2
        (pointsTo64_entails_exists _ v3
          (pointsTo64_entails_exists _ v4
            (pointsTo64_entails_exists_single _ v5)))))

private abbrev DeallocTailGhost :=
  BitVec 64 × List (BitVec 8) × Nat ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

private def rustDeallocTailSpecWithStack (A : RustAlloc) (hookStack : Nat) : Spec DeallocTailGhost where
  pre := fun (p, bs, align, v0, v1, v2, v3, v4, v5) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ (s.readReg64 .x2).toNat = align ∧
      LayoutOk bs.length align⌝ ∗
      A.pool ∗ A.live p bs.length align ∗ (p ↦ₛ bs) ∗
      stackAt (s.sp - 48#64) hookStack ∗
      ((s.sp - 48#64) ↦₆₄ v0) ∗ ((s.sp - 40#64) ↦₆₄ v1) ∗
      ((s.sp - 32#64) ↦₆₄ v2) ∗ ((s.sp - 24#64) ↦₆₄ v3) ∗
      ((s.sp - 16#64) ↦₆₄ v4) ∗ ((s.sp - 8#64) ↦₆₄ v5)
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt s0.sp (hookStack + 48)

private theorem dealloc_tail_ok_of_dealloc {A : RustAlloc}
    {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64)
    (hdealloc : subroutine_ok P addr (rustDeallocExternSpecWithStack A hookStack)) :
    subroutine_ok P addr (rustDeallocTailSpecWithStack A hookStack) := by
  refine subroutine_ok_outcome_intro ?_
  intro ⟨p, bs, align, v0, v1, v2, v3, v4, v5⟩ R s0 hpc hrun hpre hsp
  have hcells :
      (((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗
        ((s0.sp - 32#64) ↦₆₄ v2) ∗ ((s0.sp - 24#64) ↦₆₄ v3) ∗
        ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5)) ⊢ cells (s0.sp - 48#64) 6 := by
    have h := pointsTo64_6_entails_cells (s0.sp - 48#64) v0 v1 v2 v3 v4 v5
    have ha1 : s0.sp - 48#64 + 8#64 = s0.sp - 40#64 := by bv_lin
    have ha2 : s0.sp - 48#64 + 16#64 = s0.sp - 32#64 := by bv_lin
    have ha3 : s0.sp - 48#64 + 24#64 = s0.sp - 24#64 := by bv_lin
    have ha4 : s0.sp - 48#64 + 32#64 = s0.sp - 16#64 := by bv_lin
    have ha5 : s0.sp - 48#64 + 40#64 = s0.sp - 8#64 := by bv_lin
    rwa [ha1, ha2, ha3, ha4, ha5] at h
  have hbs_mem := pointsToBytes_entails_memRegion p bs
  have hpre' : s0.mem ⊨
      (rustDeallocExternSpecWithStack A hookStack).pre (p, bs.length, align) s0 ∗
      (stackAt (s0.sp - BitVec.ofNat 64 hookStack) 48 ∗ R) := by
    unfold rustDeallocTailSpecWithStack at hpre
    unfold rustDeallocExternSpecWithStack
    dsimp only at hpre ⊢
    have h1 : s0.mem ⊨
        (⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
          (s0.readReg64 .x2).toNat = align ∧ LayoutOk bs.length align⌝ ∗
          A.pool ∗ A.live p bs.length align ∗ memRegion p bs.length ∗
          (stackAt (s0.sp - 48#64) hookStack ∗ cells (s0.sp - 48#64) 6)) ∗ R := by
      refine Satisfies.mono (sepConj_mono_left ?_) hpre
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hbs_mem (sepConj_mono_right hcells))))
    rw [← stackAt_add_48_opt hstack, stackAt_add_48_comm_opt hstack] at h1
    exact (by ac_rfl :
      ((⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
          (s0.readReg64 .x2).toNat = align ∧ LayoutOk bs.length align⌝ ∗
        A.pool ∗ A.live p bs.length align ∗ memRegion p bs.length ∗
        (stackAt (s0.sp - BitVec.ofNat 64 hookStack) 48 ∗ stackAt s0.sp hookStack)) ∗ R) =
      ((⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧
          (s0.readReg64 .x2).toNat = align ∧ LayoutOk bs.length align⌝ ∗
        A.pool ∗ A.live p bs.length align ∗ memRegion p bs.length ∗ stackAt s0.sp hookStack) ∗
        (stackAt (s0.sp - BitVec.ofNat 64 hookStack) 48 ∗ R))) ▸ h1
  refine hdealloc.mono_outcome (p, bs.length, align)
    (stackAt (s0.sp - BitVec.ofNat 64 hookStack) 48 ∗ R) s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨_, hpost⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    unfold rustDeallocTailSpecWithStack
    unfold rustDeallocExternSpecWithStack at hpost
    dsimp only at hpost ⊢
    rw [stackAt_add_48_comm_opt hstack]
    exact (by ac_rfl :
      ((⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt s0.sp hookStack) ∗
        (stackAt (s0.sp - BitVec.ofNat 64 hookStack) 48 ∗ R)) =
      ((⌜sf.trace = s0.trace⌝ ∗ A.pool ∗
        (stackAt (s0.sp - BitVec.ofNat 64 hookStack) 48 ∗ stackAt s0.sp hookStack)) ∗ R)) ▸ hpost
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

@[simp, arm64_norm]
private theorem getLsbD_or_one (ptr : BitVec 64) : (ptr ||| 1#64).getLsbD 0 = true := by
  bv_bits

private theorem or_one_and_not_one {ptr : BitVec 64} (h : (ptr &&& 1#64) = 0#64) :
    (ptr ||| 1#64) &&& (-2#64) = ptr := by
  bv_bits

private theorem odd_drop_add {off len : Nat} (hoff : off ≤ len) :
    BitVec.ofNat 64 off + BitVec.ofNat 64 (len - off) = BitVec.ofNat 64 len := by
  rw [← BitVec.ofNat_add, Nat.add_sub_of_le hoff]

private theorem ult_ofNat_false {off len : Nat} (hoff : off ≤ len) (hlen : len < 2 ^ 63) :
    (BitVec.ofNat 64 len).ult (BitVec.ofNat 64 off) = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : len < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : off < 2 ^ 64)]
  omega

private theorem getLsbD_63_ofNat_eq_false {n : Nat} (hn : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).getLsbD 63 = false := by
  rw [BitVec.getLsbD_ofNat]
  simp only [Nat.testBit_lt_two_pow hn, Bool.and_false]

/-! ## 4. Relocated `.rodata` Vtable Slot Helper (`hasReloc8At`) -/

private theorem read64_of_read8_extractLsb' (m : Memory) (a v : BitVec 64)
    (h0 : m.read8 (a + 0#64) = v.extractLsb' 0 8)
    (h1 : m.read8 (a + 1#64) = v.extractLsb' 8 8)
    (h2 : m.read8 (a + 2#64) = v.extractLsb' 16 8)
    (h3 : m.read8 (a + 3#64) = v.extractLsb' 24 8)
    (h4 : m.read8 (a + 4#64) = v.extractLsb' 32 8)
    (h5 : m.read8 (a + 5#64) = v.extractLsb' 40 8)
    (h6 : m.read8 (a + 6#64) = v.extractLsb' 48 8)
    (h7 : m.read8 (a + 7#64) = v.extractLsb' 56 8) :
    m.read64 a = v := by
  simp only [Memory.read64, h0, h1, h2, h3, h4, h5, h6, h7]
  bv_bits

namespace ImageDataOffFacts

end ImageDataOffFacts

@[expose] def promotableEvenDropSpecWithStack (A : RustAlloc) (hookStack : Nat) : Spec BytesDropGhost where
  pre := fun (ptr, bs, off) s =>
    ⌜0 < bs.length ∧
      off ≤ bs.length ∧
      (ptr &&& 1#64) = 0#64 ∧
      s.readReg64 .x0 = (ptr ||| 1#64) ∧
      s.readReg64 .x1 = ptr + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off)⌝ ∗
    bytesBoxU8Buf A ptr bs ∗
    A.pool ∗
    stackAt s.sp (hookStack + 48)
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    A.pool ∗
    stackAt s0.sp (hookStack + 48)

@[expose] def promotableOddDropSpecWithStack (A : RustAlloc) (hookStack : Nat) : Spec BytesDropGhost where
  pre := fun (ptr, bs, off) s =>
    ⌜0 < bs.length ∧
      off ≤ bs.length ∧
      (ptr &&& 1#64) ≠ 0#64 ∧
      s.readReg64 .x0 = ptr ∧
      s.readReg64 .x1 = ptr + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off)⌝ ∗
    bytesBoxU8Buf A ptr bs ∗
    A.pool ∗
    stackAt s.sp (hookStack + 48)
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    A.pool ∗
    stackAt s0.sp (hookStack + 48)

@[expose] def bytesVtableDropSpecWithStack (A : RustAlloc) (hookStack : Nat)
    (ptr : BitVec 64) (bs : List (BitVec 8)) (off : Nat) : Spec Unit where
  pre := fun _ s =>
    ⌜off ≤ bs.length ∧
      s.readReg64 .x0 = bytesData ptr bs.length ∧
      s.readReg64 .x1 = bytesPtr ptr bs.length + BitVec.ofNat 64 off ∧
      s.readReg64 .x2 = BitVec.ofNat 64 (bs.length - off)⌝ ∗
    bytesBoxU8Buf A ptr bs ∗
    A.pool ∗
    stackAt s.sp (hookStack + 48)
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    A.pool ∗
    stackAt s0.sp (hookStack + 48)

abbrev lsBytesRustDeallocSym : String := "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"

theorem ls_externAt?_rustDealloc [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    prog.externAt? (lsρ lsBytesRustDeallocSym) = H lsBytesRustDeallocSym := by
  have hmem : lsBytesRustDeallocSym ∈ libsignalSessionExterns := by decide
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hmem
  exact ls_externAt?_of_blockProg (k := k) (by simp [hk, hget]) hi hunmut

theorem ls_hook_ok_rustDealloc [LibsignalPlacement] {α : Type} {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {spec : Spec α} (hsat : HookSat H lsBytesRustDeallocSym spec)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsBytesRustDeallocSym) spec := by
  obtain ⟨f, hf, hok⟩ := hsat
  exact subroutine_ok_of_hookOk ((ls_externAt?_rustDealloc hi hunmut).trans hf) hok

/-- Block `224`: `bytes::bytes::static_drop` meets `bytesStaticDropSpec` under `[LibsignalPlacement]`. -/
theorem bytesStaticDrop_placed_ok [LibsignalPlacement]
    (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_224).rebase (blkPl_224).base H) (blkPl_224).base
      bytesStaticDropSpec := by
  unfold bytesStaticDropSpec
  wp_init x s0
  wp_steps
  wp_done

theorem promotableEvenDrop_placed_ok_of_dealloc [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hdealloc_ext : subroutine_ok ((blkPC_237).rebase (blkPl_237).base H)
      (lsρ lsBytesRustDeallocSym)
      (rustDeallocExternSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_237).rebase (blkPl_237).base H) (blkPl_237).base
      (promotableEvenDropSpecWithStack A hookStack) := by
  unfold promotableEvenDropSpecWithStack bytesBoxU8Buf
  have hdealloc := dealloc_tail_ok_of_dealloc hstack hdealloc_ext
  clear hdealloc_ext
  conv =>
    arg 3; arg 1; ext x s
    dsimp only
    rw [stackAt_add_48_opt hstack]
  cells_unfold
  wp_init x s0
  obtain ⟨ptr, bs, off⟩ := x
  dsimp only at *
  have hpos : 0 < bs.length := by assumption
  have hoff : off ≤ bs.length := by assumption
  have heven : (ptr &&& 1#64) = 0#64 := by assumption
  have hlen63 : bs.length < 2 ^ 63 := by assumption
  have hbs_ne : bs ≠ [] := List.ne_nil_of_length_pos hpos
  have hlay : LayoutOk bs.length 1 := ⟨hpos, ⟨0, rfl⟩, by omega⟩
  simp only [hbs_ne, ↓reduceIte]
  have hand : (ptr ||| 1#64) &&& (-2#64) = ptr := or_one_and_not_one heven
  apply SepWP.cut (mid := lsρ lsBytesRustDeallocSym)
  wp_steps
  wp_if hcs
  · rw [bitvec_add_sub_self_left, odd_drop_add hoff,
      ult_ofNat_false hoff hlen63] at hcs
    cases hcs
  · wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    have hadd_even' : ptr + BitVec.ofNat 64 off - ptr + BitVec.ofNat 64 (bs.length - off) =
        BitVec.ofNat 64 bs.length := by
      rw [bitvec_add_sub_self_left, odd_drop_add hoff]
    have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    wp_call hdealloc (ptr, bs, 1, v_stk, v_stk_1,
      s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
      s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5))
    wp_done

/-- Block `237`: `bytes::bytes::promotable_even_drop` meets `promotableEvenDropSpec`
    under `[LibsignalPlacement]`. -/
theorem promotableEvenDrop_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H lsBytesRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_237).rebase (blkPl_237).base H) (blkPl_237).base
      (promotableEvenDropSpec A) :=
  promotableEvenDrop_placed_ok_of_dealloc (by decide)
    (rustDeallocExternWithStack_of_rustDealloc
      (ls_hook_ok_rustDealloc hdealloc) (by decide) (by decide))

theorem promotableOddDrop_placed_ok_of_dealloc [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hdealloc_ext : subroutine_ok ((blkPC_236).rebase (blkPl_236).base H)
      (lsρ lsBytesRustDeallocSym)
      (rustDeallocExternSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_236).rebase (blkPl_236).base H) (blkPl_236).base
      (promotableOddDropSpecWithStack A hookStack) := by
  unfold promotableOddDropSpecWithStack bytesBoxU8Buf
  have hdealloc := dealloc_tail_ok_of_dealloc hstack hdealloc_ext
  clear hdealloc_ext
  conv =>
    arg 3; arg 1; ext x s
    dsimp only
    rw [stackAt_add_48_opt hstack]
  cells_unfold
  wp_init x s0
  obtain ⟨ptr, bs, off⟩ := x
  dsimp only at *
  have hpos : 0 < bs.length := by assumption
  have hoff : off ≤ bs.length := by assumption
  have hodd : (ptr &&& 1#64) ≠ 0#64 := by assumption
  have hlen63 : bs.length < 2 ^ 63 := by assumption
  have hbs_ne : bs ≠ [] := List.ne_nil_of_length_pos hpos
  have hlay : LayoutOk bs.length 1 := ⟨hpos, ⟨0, rfl⟩, by omega⟩
  simp only [hbs_ne, ↓reduceIte]
  have hlsb0 : ptr.getLsbD 0 = true := getLsbD_zero_iff.mpr hodd
  apply SepWP.cut (mid := lsρ lsBytesRustDeallocSym)
  wp_steps
  wp_if hcs
  · rw [bitvec_add_sub_self_left, odd_drop_add hoff,
      ult_ofNat_false hoff hlen63] at hcs
    cases hcs
  · wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    have hadd_odd : ptr + BitVec.ofNat 64 off - ptr + BitVec.ofNat 64 (bs.length - off) =
        BitVec.ofNat 64 bs.length := by
      rw [bitvec_add_sub_self_left, odd_drop_add hoff]
    have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    wp_call hdealloc (ptr, bs, 1, v_stk, v_stk_1,
      s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
      s0.readReg64 (Reg.gpr 20#5), s0.readReg64 (Reg.gpr 19#5))
    wp_done

/-- Block `236`: `bytes::bytes::promotable_odd_drop` meets `promotableOddDropSpec`
    under `[LibsignalPlacement]`. -/
theorem promotableOddDrop_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H lsBytesRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_236).rebase (blkPl_236).base H) (blkPl_236).base
      (promotableOddDropSpec A) :=
  promotableOddDrop_placed_ok_of_dealloc (by decide)
    (rustDeallocExternWithStack_of_rustDealloc
      (ls_hook_ok_rustDealloc hdealloc) (by decide) (by decide))

/-- Relocatable `.rodata` vtable `+0x20` slot lookup under `[LibsignalPlacement]`:
    for any `m` satisfying `LibsignalRoLoaded lsmpl m`, the 8-byte word at
    `bytesPlacedVtable ptr len + 0x20#64` holds `bytesPlacedDropFnAddr ptr len` read-only. -/
theorem bytesVtableSlotLoaded_placed_intro [LibsignalPlacement] {m : Memory}
    (hro : LibsignalRoLoaded lsmpl m) (ptr : BitVec 64) (len : Nat)
    {P : SepProp} (hP : m ⊨ P) :
    m ⊨ ((bytesPlacedVtable ptr len + 0x20#64) ↦₆₄ᵣ bytesPlacedDropFnAddr ptr len) ∗ P := by
  unfold bytesPlacedVtable bytesPlacedDropFnAddr staticVtablePlacedAddr
    promotableEvenVtablePlacedAddr promotableOddVtablePlacedAddr
  by_cases hlen : len = 0
  · simp only [hlen, ↓reduceIte]
    exact lsro_reloc64_intro hro (sym := staticVtableSym) (off := 32)
      (tgt := bytesStaticDropName) rfl (by simp) (by decide +kernel) hP
  · by_cases heven : (ptr &&& 1#64) = 0#64
    · simp only [hlen, heven, ↓reduceIte]
      exact lsro_reloc64_intro hro (sym := promotableEvenVtableName) (off := 32)
        (tgt := promotableEvenDropName) rfl (by simp) (by decide +kernel) hP
    · simp only [hlen, heven, ↓reduceIte]
      exact lsro_reloc64_intro hro (sym := promotableOddVtableName) (off := 32)
        (tgt := promotableOddDropName) rfl (by simp) (by decide +kernel) hP

theorem bytesVtableDrop_placed_ok_of_drops [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    {hookStack : Nat}
    (heven_ok : subroutine_ok ((blkPC_237).rebase (blkPl_237).base H) (blkPl_237).base
      (promotableEvenDropSpecWithStack A hookStack))
    (hodd_ok : subroutine_ok ((blkPC_236).rebase (blkPl_236).base H) (blkPl_236).base
      (promotableOddDropSpecWithStack A hookStack))
    (hi : i < 619 := by decide)
    (ptr : BitVec 64) (bs : List (BitVec 8)) (off : Nat) :
    subroutine_ok callerProg (bytesPlacedDropFnAddr ptr bs.length)
      (withLsCodeLoaded lsmpl (bytesVtableDropSpecWithStack A hookStack ptr bs off)) := by
  refine subroutine_ok_outcome_intro ?_
  intro _ R s0 hpc hrun hpre hsp
  by_cases hbs : bs = []
  · subst hbs
    have haddr : bytesPlacedDropFnAddr ptr ([] : List (BitVec 8)).length = (blkPl_224).base := rfl
    rw [haddr] at hpc
    have hstatic := ls_subroutine_ok_of_block (callerProg := callerProg)
      (subroutine_ok_withLsCodeLoaded_of_plain (bytesStaticDrop_placed_ok H)) hi
    have ⟨hcl, hpre0⟩ := extract_withLsCodeLoaded hpre
    unfold bytesVtableDropSpecWithStack bytesBoxU8Buf at hpre0
    simp only [↓reduceIte, sepConj_emp, sepConj_assoc, satisfies_pure_sepConj] at hpre0
    rcases hpre0 with ⟨_, _, hmem⟩
    have hpre_static : s0.mem ⊨ (withLsCodeLoaded lsmpl bytesStaticDropSpec).pre () s0 ∗
        (A.pool ∗ (stackAt s0.sp (hookStack + 48) ∗ R)) := by
      dsimp only [withLsCodeLoaded, bytesStaticDropSpec]
      rw [emp_sepConj, satisfies_pure_sepConj]
      exact ⟨hcl, hmem⟩
    refine hstatic.mono_outcome () (A.pool ∗ (stackAt s0.sp (hookStack + 48) ∗ R)) s0 hpc hrun hpre_static hsp ?_
    rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨_, hpost⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withLsCodeLoaded, bytesVtableDropSpecWithStack]
      dsimp only [withLsCodeLoaded, bytesStaticDropSpec] at hpost
      simpa only [sepConj_assoc] using hpost
    · exact (not_satisfies_false_sepConj hpost).elim
    · exact (not_satisfies_false_sepConj hpost).elim
    · exact (not_satisfies_false_sepConj hpost).elim
  · have hpos : 0 < bs.length := List.length_pos_iff.mpr hbs
    have hlen_ne : bs.length ≠ 0 := by omega
    by_cases heven : (ptr &&& 1#64) = 0#64
    · have haddr : bytesPlacedDropFnAddr ptr bs.length = (blkPl_237).base := by
        unfold bytesPlacedDropFnAddr
        simp only [hlen_ne, heven, ↓reduceIte]
        rfl
      rw [haddr] at hpc
      have heven_cl := ls_subroutine_ok_of_block (callerProg := callerProg)
        (subroutine_ok_withLsCodeLoaded_of_plain heven_ok) hi
      have ⟨hcl, hpre0⟩ := extract_withLsCodeLoaded hpre
      have hpre_even :
          s0.mem ⊨ (withLsCodeLoaded lsmpl (promotableEvenDropSpecWithStack A hookStack)).pre
            (ptr, bs, off) s0 ∗ R := by
        dsimp only [withLsCodeLoaded, bytesVtableDropSpecWithStack, bytesData, bytesPtr] at hpre0
        dsimp only [withLsCodeLoaded, promotableEvenDropSpecWithStack]
        rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
        refine ⟨hcl, ?_⟩
        simp only [hlen_ne, heven, ↓reduceIte, sepConj_assoc, satisfies_pure_sepConj] at hpre0
        simp only [sepConj_assoc, satisfies_pure_sepConj]
        rcases hpre0 with ⟨⟨hoff, hx0, hx1, hx2⟩, hrest⟩
        exact ⟨⟨hpos, hoff, heven, hx0, hx1, hx2⟩, hrest⟩
      exact heven_cl.mono_outcome (ptr, bs, off) R s0 hpc hrun hpre_even hsp fun _ hout => hout
    · have haddr : bytesPlacedDropFnAddr ptr bs.length = (blkPl_236).base := by
        unfold bytesPlacedDropFnAddr
        simp only [hlen_ne, heven, ↓reduceIte]
        rfl
      rw [haddr] at hpc
      have hodd_cl := ls_subroutine_ok_of_block (callerProg := callerProg)
        (subroutine_ok_withLsCodeLoaded_of_plain hodd_ok) hi
      have ⟨hcl, hpre0⟩ := extract_withLsCodeLoaded hpre
      have hpre_odd :
          s0.mem ⊨ (withLsCodeLoaded lsmpl (promotableOddDropSpecWithStack A hookStack)).pre
            (ptr, bs, off) s0 ∗ R := by
        dsimp only [withLsCodeLoaded, bytesVtableDropSpecWithStack, bytesData, bytesPtr] at hpre0
        dsimp only [withLsCodeLoaded, promotableOddDropSpecWithStack]
        rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
        refine ⟨hcl, ?_⟩
        simp only [hlen_ne, heven, ↓reduceIte, sepConj_assoc, satisfies_pure_sepConj] at hpre0
        simp only [sepConj_assoc, satisfies_pure_sepConj]
        rcases hpre0 with ⟨⟨hoff, hx0, hx1, hx2⟩, hrest⟩
        exact ⟨⟨hpos, hoff, heven, hx0, hx1, hx2⟩, hrest⟩
      exact hodd_cl.mono_outcome (ptr, bs, off) R s0 hpc hrun hpre_odd hsp fun _ hout => hout

/-- Unified relocatable vtable `drop` dispatch (`entry_pc = bytesPlacedDropFnAddr ptr bs.length`)
    meets `bytesVtableDropSpec` for any caller block `i` under `[LibsignalPlacement]`. -/
theorem bytesVtableDrop_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H lsBytesRustDeallocSym (rustDeallocSpec A))
    (hi : i < 619 := by decide)
    (ptr : BitVec 64) (bs : List (BitVec 8)) (off : Nat) :
    subroutine_ok callerProg (bytesPlacedDropFnAddr ptr bs.length)
      (withLsCodeLoaded lsmpl (bytesVtableDropSpec A ptr bs off)) :=
  bytesVtableDrop_placed_ok_of_drops
    (promotableEvenDrop_placed_ok hdealloc)
    (promotableOddDrop_placed_ok hdealloc)
    hi ptr bs off

end CryptoVerification.LibsignalTripleRatchet
