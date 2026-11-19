/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Bytes.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Bytes.BytesCodeSym -- proof-setup: allow-public-import
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.CodeLayout -- shake: keep -- proof-setup: allow-public-import
public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Decoded Instructions of `Bytes::from(Vec<u8>)` (`0x423cc..0x424c4`) -/

theorem stackAt_48_eq_cells (sp : BitVec 64) : stackAt sp 48 = cells (sp - 48#64) 6 := by
  simpa using ProofLib.memRegion_cells (sp - 48#64) 6 (by decide)

theorem memRegion_32_eq_pointsTo64 (out : BitVec 64) :
    memRegion out 32 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        (out ↦₆₄ v0) ∗ ((out + 8#64) ↦₆₄ v1) ∗
          ((out + 16#64) ↦₆₄ v2) ∗ ((out + 24#64) ↦₆₄ v3) := by
  rw [show (32 : Nat) = 8 * 4 from rfl, ProofLib.memRegion_cells out 4 (by decide)]
  simp only [cells_succ, cells_zero, sepConj_emp, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem getLsbD_zero_iff {ptr : BitVec 64} :
    ptr.getLsbD 0 = true ↔ (ptr &&& 1#64) ≠ 0#64 := by
  constructor <;> intro h <;> revert h <;> bv_kernel

theorem not_getLsbD_zero_iff {ptr : BitVec 64} :
    ¬ ptr.getLsbD 0 = true ↔ (ptr &&& 1#64) = 0#64 := by
  constructor <;> intro h <;> revert h <;> bv_kernel

theorem bytesFromVec_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_250).rebase (blkPl_250).base H) (blkPl_250).base
      (bytesFromVecPlacedSpec A) := by
  unfold bytesFromVecPlacedSpec vecU8At vecHeader bytesPlacedAt bytesHeader bytesBoxU8Buf bytesFromVecStack
  simp only [memRegion_32_eq_pointsTo64, stackAt_48_eq_cells]
  cells_unfold
  wp_init x s0
  obtain ⟨v, out, cap, ptr, bs⟩ := x
  dsimp only at *
  have hcap_eq : BitVec.ofNat 64 bs.length = cap := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), ‹cap.toNat = bs.length›]
  have hif : (if cap = 0 then emp
      else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
      (if bs = [] then emp else A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs)) := by
    rw [‹cap.toNat = bs.length›]
    by_cases hbs : bs = []
    · subst hbs
      have hc0 : cap = 0 := by rw [← hcap_eq]; rfl
      simp [hc0]
    · have hc0 : cap ≠ 0 := by
        intro hc
        have hpos : 0 < bs.length := List.length_pos_iff.mpr hbs
        have h0 : cap.toNat = 0 := by simp [hc]
        omega
      simp only [hbs, hc0, ↓reduceIte, Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp]
  rw [hif, hcap_eq]
  wp_steps
  wp_if hlen0
  · have hbs_len0 : bs.length = 0 := by
      rw [← ‹cap.toNat = bs.length›, hlen0]; rfl
    wp_steps
    simp only [bytesPlacedVtable, staticVtablePlacedAddr, staticVtableSym,
      hbs_len0, bytesPtr, bytesData, ite_true]
    wp_done
  · have hbs_len_ne : bs.length ≠ 0 := by
      intro h0
      apply hlen0
      rw [← hcap_eq, h0]
    wp_steps
    wp_if hodd
    · have hodd64 : (ptr &&& 1#64) ≠ 0#64 := getLsbD_zero_iff.mp hodd
      wp_steps
      simp only [bytesPlacedVtable, promotableOddVtablePlacedAddr, promotableOddVtableName,
        hbs_len_ne, hodd64, bytesPtr, bytesData, ite_false]
      wp_done
    · have heven : (ptr &&& 1#64) = 0#64 := not_getLsbD_zero_iff.mp hodd
      wp_steps
      simp only [bytesPlacedVtable, promotableEvenVtablePlacedAddr, promotableEvenVtableName,
        hbs_len_ne, heven, bytesPtr, bytesData, ite_false, ite_true]
      wp_done

theorem bytesStaticClone_placed_ok [LibsignalPlacement]
    (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_226).rebase (blkPl_226).base H) (blkPl_226).base
      bytesStaticClonePlacedSpec := by
  unfold bytesStaticClonePlacedSpec bytesHeader
  simp only [memRegion_32_eq_pointsTo64]
  wp_init x s0
  obtain ⟨out, ptr, len⟩ := x
  dsimp only at *
  apply blkPC_226_pairStep_0x0 _ _ rfl (by simp [*]) (by assumption)
  wp_steps
  wp_done

end CryptoVerification.LibsignalTripleRatchet
