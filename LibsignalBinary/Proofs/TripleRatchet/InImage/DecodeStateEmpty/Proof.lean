/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.TrapRng -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalTripleRatchetProofDefs
public section

namespace CryptoVerification.LibsignalTripleRatchet.InImage.DecodeStateEmpty

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet

theorem mr_cut' (sp : BitVec 64) (c c' n k N : Nat) (hN : n + k = N) (hc' : c - n = c')
    (hn : n ≤ c) (hc : c < 2 ^ 64) (h : N ≤ 2 ^ 64) :
    memRegion (sp - BitVec.ofNat 64 c) N =
      memRegion (sp - BitVec.ofNat 64 c) n ∗ memRegion (sp - BitVec.ofNat 64 c') k := by
  subst hN hc'
  refine memRegion_split' rfl ?_ h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have h1 : c % 2 ^ 64 = c := Nat.mod_eq_of_lt hc
  have h2 : (c - n) % 2 ^ 64 = c - n := Nat.mod_eq_of_lt (by omega)
  have h3 : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2, h3]
  omega

/-- The stack of `spqr::decode_state` (`extHookStack = 16384` bytes), split at the slots touched
by the prologue (`sp - 1392` probe and `sp - 96 .. sp - 8` callee-saved registers). -/
theorem stackAt_decodeState_split (sp : BitVec 64) :
    stackAt sp extHookStack =
      memRegion (sp - 16384#64) 14992 ∗
      (∃∗ v0 : BitVec 64, (sp - 1392#64) ↦₆₄ v0) ∗
      memRegion (sp - 1384#64) 1288 ∗
      (∃∗ s29 : BitVec 64, (sp - 96#64) ↦₆₄ s29) ∗
      (∃∗ s30 : BitVec 64, (sp - 88#64) ↦₆₄ s30) ∗
      (∃∗ s28 : BitVec 64, (sp - 80#64) ↦₆₄ s28) ∗
      (∃∗ s27 : BitVec 64, (sp - 72#64) ↦₆₄ s27) ∗
      (∃∗ s26 : BitVec 64, (sp - 64#64) ↦₆₄ s26) ∗
      (∃∗ s25 : BitVec 64, (sp - 56#64) ↦₆₄ s25) ∗
      (∃∗ s24 : BitVec 64, (sp - 48#64) ↦₆₄ s24) ∗
      (∃∗ s23 : BitVec 64, (sp - 40#64) ↦₆₄ s23) ∗
      (∃∗ s22 : BitVec 64, (sp - 32#64) ↦₆₄ s22) ∗
      (∃∗ s21 : BitVec 64, (sp - 24#64) ↦₆₄ s21) ∗
      (∃∗ s20 : BitVec 64, (sp - 16#64) ↦₆₄ s20) ∗
      (∃∗ s19 : BitVec 64, (sp - 8#64) ↦₆₄ s19) := by
  show memRegion (sp - BitVec.ofNat 64 16384) 16384 = _
  rw [mr_cut' sp 16384 1392 14992 1392 16384 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 1392 1384 8 1384 1392 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 1384 96 1288 96 1384 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 96 88 8 88 96 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 88 80 8 80 88 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 80 72 8 72 80 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 72 64 8 64 72 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 64 56 8 56 64 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 56 48 8 48 56 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 48 40 8 40 48 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 40 32 8 32 40 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 32 24 8 24 32 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 24 16 8 16 24 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 16 8 8 8 16 rfl rfl (by decide) (by decide) (by decide)]
  simp only [memRegion_eight]

/-- The 352-byte result buffer `ret`, split at the three words written on the empty-state path
(`+0`, `+48`, `+128`). -/
theorem ret_352_split (r : BitVec 64) :
    memRegion r 352 =
      (∃∗ w0 : BitVec 64, r ↦₆₄ w0) ∗
      memRegion (r + 8#64) 40 ∗
      (∃∗ w48 : BitVec 64, (r + 48#64) ↦₆₄ w48) ∗
      memRegion (r + 56#64) 72 ∗
      (∃∗ w128 : BitVec 64, (r + 128#64) ↦₆₄ w128) ∗
      memRegion (r + 136#64) 216 := by
  rw [ProofLib.memRegion_split' (b := r) (n := 8) (k := 344)
        (b' := r + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := r + 8#64) (n := 40) (k := 304)
        (b' := r + 48#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := r + 48#64) (n := 8) (k := 296)
        (b' := r + 56#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := r + 56#64) (n := 72) (k := 224)
        (b' := r + 128#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := r + 128#64) (n := 8) (k := 216)
        (b' := r + 136#64) rfl (by bv_arith) (by decide),
      memRegion_eight r, memRegion_eight (r + 48#64), memRegion_eight (r + 128#64)]

/-- The buffer tail of `vecU8At`, kept intact during symbolic execution of `decode_state`. -/
@[expose] def vecU8Tail (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecArg_at_nil (A : RustAlloc) (v cap ptr : BitVec 64) :
    VecArg.at A ⟨v, cap, ptr, []⟩ =
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ 0#64) ∗
        vecU8Tail A cap ptr [] := by
  simp only [VecArg.at, vecU8At, vecHeader, vecU8Tail, List.length_nil, BitVec.ofNat_eq_ofNat,
    sepConj_assoc]

end CryptoVerification.LibsignalTripleRatchet.InImage.DecodeStateEmpty
