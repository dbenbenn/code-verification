/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContracts -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<libsignal_core::curve::PublicKey>::serialize` (`0x3e1e0`)

Verifies `<libsignal_core::curve::PublicKey>::serialize` (`0x3e1e0`, 21 instructions)
against `publicKeySerializeSpec A` on `tripleRatchetProgAt`.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoVerification.RustHeap
  CryptoGames.LibsignalSession CryptoVerification.LibsignalSessionRepr
  CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSession
  CryptoVerification.InImageLift

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
private theorem stackAt_publicKeySerialize_opt {hookStack : Nat}
    (hstack : hookStack + 32 ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (hookStack + 32) =
      stackAt (sp - 32#64) hookStack ∗ cells (sp - 32#64) 4 :=
  stackAt_split_cells sp hookStack 4 hstack

private theorem memRegion_33_cells (a : BitVec 64) :
    memRegion a 33 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64, ∃∗ b0 : BitVec 8,
        (a ↦₈ b0) ∗ ((a + 1#64) ↦₆₄ u3) ∗ ((a + 9#64) ↦₆₄ u2) ∗
        ((a + 17#64) ↦₆₄ u1) ∗ ((a + 25#64) ↦₆₄ u0)) := by
  rw [memRegion_split a 1 32 (by decide),
    memRegion_split (a + 1#64) 8 24 (by decide),
    memRegion_split (a + 1#64 + 8#64) 8 16 (by decide),
    memRegion_split (a + 1#64 + 8#64 + 8#64) 8 8 (by decide),
    memRegion_one, memRegion_eight, memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

private theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

private theorem shimWithStack_of_noAllocShim {prog : Program} {addr : BitVec 64} (hookStack : Nat)
    (h : subroutine_ok prog addr noAllocShimSpec) :
    subroutine_ok prog addr (shimSpecWithStack hookStack) := by
  refine subroutine_ok_mono (subroutine_ok_withStack_of_subroutine_ok h hookStack)
    (fun x R s0 hpre => ?_) (fun _ _ _ _ hpost => hpost)
  dsimp only [withStack, noAllocShimSpec, shimSpecWithStack] at hpre ⊢
  simpa only [emp_sepConj, sepConj_assoc] using hpre

theorem public_key_serialize_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_205).rebase (blkPl_205).base H)
      (lsρ lsRustNoAllocShimSym) (shimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_205).rebase (blkPl_205).base H)
      (lsρ lsRustAllocSym) (rustAllocSpecWithStack A hookStack))
    (hpanic : ((blkPC_205).rebase (blkPl_205).base H).externAt? (lsρ lsHandleErrorSym) =
      some Rust.panicked) :
    subroutine_ok ((blkPC_205).rebase (blkPl_205).base H) (blkPl_205).base
      (publicKeySerializeSpecWithStack A hookStack) := by
  simp only [publicKeySerializeSpecWithStack, PublicKey.serialize, boxU8Buf,
    stackAt_publicKeySerialize_opt hstack]
  cells_unfold
  wpp_init x s0
  obtain ⟨self, pk⟩ := x
  dsimp only at *
  obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length pk.bytes)
  rw [hpk_cells self]
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 33 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := (blkPl_205).base + bv% (32))
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (33, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm, wp_norm] using hpanic) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace, ‹sf.trace = s0.trace›])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_33_cells, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 =>
      SepWPp.exists_elim fun b0 => ?_
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    simp only [List.length_cons, List.Vector.toList_length,
      List.cons_ne_nil, ite_false, djbType,
      pointsToBytes_cons, hpk_cells,
      BitVec.add_assoc, BitVec.reduceAdd]
    wp_done

/-- Relocatable `<libsignal_core::curve::PublicKey>::serialize` (Block `205`) meets
`publicKeySerializeSpec A`. -/
theorem public_key_serialize_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_205).rebase (blkPl_205).base H) (blkPl_205).base
      (publicKeySerializeSpec A) :=
  public_key_serialize_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
    (shimWithStack_of_noAllocShim allocHookStack (ls_hook_ok_of_mem hshim))
    (ls_hook_ok_of_mem halloc)
    ((ls_externAt?_of_mem).trans hpanic)

theorem public_key_serialize_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_205).rebase (blkPl_205).base H) (blkPl_205).base
      (publicKeySerializeSpecX A) :=
  public_key_serialize_placed_ok_of_hooks (hookStack := extHookStack) (by decide)
    (shimWithStack_of_noAllocShim extHookStack (ls_hook_ok_of_mem hshim))
    (rustAllocWithStack_of_rustAlloc (ls_hook_ok_of_mem halloc) (by decide) (by decide))
    ((ls_externAt?_of_mem).trans hpanic)

end CryptoVerification.LibsignalTripleRatchet
