/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Ref -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Cells -- proof-setup: allow-public-import

/-!
# Linear Round Recurrence, Bitwise Bridges, and Step-Folding Lemmas for SHA-256

Pure 32-bit instruction-AST identities, linear ($O(n)$) message-schedule (`sha256W`) and
working-state (`sha256A`, `sha256E`) recurrences, and instruction-AST step-folding lemmas for
`sha2::sha256::compress256` and `libcrux_sha2::hacl::sha256_update`.

Kept independent of `VCVio` / `LibsignalHmac` so all 64-round stepping modules compile with a
minimal `Arm64` + `ProofLib` import cone.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256RoundDefs

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Ref
  (sha256K beU32OfBytes
   sha256SmallSigma0 sha256SmallSigma1 sha256BigSigma0 sha256BigSigma1
   sha256Ch sha256Maj sha256Schedule sha256Round sha256CompressBlock)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Cells
  (readLE32 rev32_readLE32_eq_beU32OfBytes)

/-! ## 1. Bitwise 32-Bit Identity Bridges (`Ch`, `Maj`, $\Sigma_0$, $\Sigma_1$, $\sigma_0$, $\sigma_1$) -/

private theorem bv32_add_left_comm (a b c : BitVec 32) : a + (b + c) = b + (a + c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

private theorem bv32_xor_left_comm (a b c : BitVec 32) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc]

local macro "bv32_add_ac" : tactic =>
  `(tactic| simp only [BitVec.add_assoc, BitVec.add_comm, bv32_add_left_comm])

local macro "bv32_xor_ac" : tactic =>
  `(tactic| simp only [BitVec.xor_assoc, BitVec.xor_comm, bv32_xor_left_comm])

theorem sha256Ch_eq_orr_bic (e f g : BitVec 32) :
    (e &&& f) ||| (g &&& ~~~e) = sha256Ch e f g := by
  unfold sha256Ch; bv_slice

theorem sha256Ch_eq_add_bic (e f g : BitVec 32) :
    (e &&& f) + (g &&& ~~~e) = sha256Ch e f g := by
  unfold sha256Ch; bv_robdd

theorem sha256Ch_add_1 (e f g x : BitVec 32) :
    ((e &&& f) + x) + (g &&& ~~~e) = x + sha256Ch e f g := by
  rw [← sha256Ch_eq_add_bic]; bv32_add_ac

theorem sha256Ch_add_2 (e f g x : BitVec 32) :
    (x + (g &&& ~~~e)) + (e &&& f) = x + sha256Ch e f g := by
  rw [← sha256Ch_eq_add_bic]; bv32_add_ac

theorem sha256Maj_eq_and_xor (a b c : BitVec 32) :
    (a &&& (b ^^^ c)) ^^^ (b &&& c) = sha256Maj a b c := by
  unfold sha256Maj; bv_slice

theorem sha256Maj_eq_and_xor_comm (a b c : BitVec 32) :
    ((a ^^^ b) &&& c) ^^^ (a &&& b) = sha256Maj a b c := by
  unfold sha256Maj; bv_slice

private theorem rotateRight32_eq_rotateLeft32 (x : BitVec 32) (r l : Nat)
    (hr : r < 32 := by decide) (hl : l < 32 := by decide)
    (h1 : 32 - r = l := by rfl) (h2 : 32 - l = r := by rfl) :
    x.rotateRight r = x.rotateLeft l := by
  rw [BitVec.rotateRight_eq_rotateRightAux_of_lt hr,
      BitVec.rotateLeft_eq_rotateLeftAux_of_lt hl]
  unfold BitVec.rotateRightAux BitVec.rotateLeftAux
  rw [h1, h2, BitVec.or_comm]

private theorem setWidth32_append_ushiftRight_eq_rotateLeft (x : BitVec 32) (r l : Nat)
    (hl : l < 32 := by decide) (hrl : r + l = 32 := by rfl) :
    BitVec.setWidth 32 ((x ++ x) >>> r) = x.rotateLeft l := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append,
      BitVec.getLsbD_rotateLeft_of_le hl]
  simp only [hi, decide_true, Bool.true_and]
  by_cases hlt : i < l
  · have hlt2 : r + i < 32 := by omega
    simp only [hlt, hlt2, ↓reduceIte]
    congr 1
    omega
  · have hlt2 : ¬(r + i < 32) := by omega
    simp only [hlt, hlt2, ↓reduceIte]
    congr 1
    omega

theorem extr32_2 (x : BitVec 32) :
    BitVec.setWidth 32 ((x ++ x) >>> 2) = x.rotateRight 2 := by
  rw [setWidth32_append_ushiftRight_eq_rotateLeft x 2 30, ← rotateRight32_eq_rotateLeft32 x 2 30]

theorem extr32_6 (x : BitVec 32) :
    BitVec.setWidth 32 ((x ++ x) >>> 6) = x.rotateRight 6 := by
  rw [setWidth32_append_ushiftRight_eq_rotateLeft x 6 26, ← rotateRight32_eq_rotateLeft32 x 6 26]

theorem extr32_7 (x : BitVec 32) :
    BitVec.setWidth 32 ((x ++ x) >>> 7) = x.rotateRight 7 := by
  rw [setWidth32_append_ushiftRight_eq_rotateLeft x 7 25, ← rotateRight32_eq_rotateLeft32 x 7 25]

theorem extr32_11 (x : BitVec 32) :
    BitVec.setWidth 32 ((x ++ x) >>> 11) = x.rotateRight 11 := by
  rw [setWidth32_append_ushiftRight_eq_rotateLeft x 11 21, ← rotateRight32_eq_rotateLeft32 x 11 21]

theorem extr32_13 (x : BitVec 32) :
    BitVec.setWidth 32 ((x ++ x) >>> 13) = x.rotateRight 13 := by
  rw [setWidth32_append_ushiftRight_eq_rotateLeft x 13 19, ← rotateRight32_eq_rotateLeft32 x 13 19]

theorem extr32_17 (x : BitVec 32) :
    BitVec.setWidth 32 ((x ++ x) >>> 17) = x.rotateRight 17 := by
  rw [setWidth32_append_ushiftRight_eq_rotateLeft x 17 15, ← rotateRight32_eq_rotateLeft32 x 17 15]

theorem sha256SmallSigma0_eq (x : BitVec 32) :
    ((BitVec.setWidth 32 ((x ++ x) >>> 7) ^^^ x.rotateRight 18) ^^^ (x >>> 3)) =
      sha256SmallSigma0 x := by unfold sha256SmallSigma0; rw [extr32_7]

theorem sha256SmallSigma0_eq_lsr_first (x : BitVec 32) :
    (((x >>> 3) ^^^ x.rotateRight 7) ^^^ x.rotateRight 18) =
      sha256SmallSigma0 x := by unfold sha256SmallSigma0; bv32_xor_ac

theorem sha256SmallSigma1_eq (x : BitVec 32) :
    ((BitVec.setWidth 32 ((x ++ x) >>> 17) ^^^ x.rotateRight 19) ^^^ (x >>> 10)) =
      sha256SmallSigma1 x := by unfold sha256SmallSigma1; rw [extr32_17]

theorem sha256SmallSigma1_eq_lsr_first (x : BitVec 32) :
    (((x >>> 10) ^^^ x.rotateRight 17) ^^^ x.rotateRight 19) =
      sha256SmallSigma1 x := by unfold sha256SmallSigma1; bv32_xor_ac

theorem sha256BigSigma0_eq (x : BitVec 32) :
    ((BitVec.setWidth 32 ((x ++ x) >>> 2) ^^^ x.rotateRight 13) ^^^ x.rotateRight 22) =
      sha256BigSigma0 x := by unfold sha256BigSigma0; rw [extr32_2]

theorem sha256BigSigma0_eq_13_22_2 (x : BitVec 32) :
    ((BitVec.setWidth 32 ((x ++ x) >>> 13) ^^^ x.rotateRight 22) ^^^ x.rotateRight 2) =
      sha256BigSigma0 x := by unfold sha256BigSigma0; rw [extr32_13]; bv32_xor_ac

theorem sha256BigSigma1_eq (x : BitVec 32) :
    ((BitVec.setWidth 32 ((x ++ x) >>> 6) ^^^ x.rotateRight 11) ^^^ x.rotateRight 25) =
      sha256BigSigma1 x := by unfold sha256BigSigma1; rw [extr32_6]

theorem sha256BigSigma1_eq_11_25_6 (x : BitVec 32) :
    ((BitVec.setWidth 32 ((x ++ x) >>> 11) ^^^ x.rotateRight 25) ^^^ x.rotateRight 6) =
      sha256BigSigma1 x := by unfold sha256BigSigma1; rw [extr32_11]; bv32_xor_ac

/-! ## 2. Linear Schedule (`sha256W`) & Linear Working-State Window (`sha256A`, `sha256E`) -/

private def sha256ScheduleStep (ws : List (BitVec 32)) (i : Nat) : List (BitVec 32) :=
  let w16_back := ws.getD i 0#32
  let w15_back := ws.getD (i + 1) 0#32
  let w7_back  := ws.getD (i + 9) 0#32
  let w2_back  := ws.getD (i + 14) 0#32
  let next := w16_back + sha256SmallSigma0 w15_back + w7_back + sha256SmallSigma1 w2_back
  ws ++ [next]

private def sha256ScheduleN (n : Nat) (w16 : List (BitVec 32)) : List (BitVec 32) :=
  (List.range n).foldl sha256ScheduleStep (w16.take 16)

private theorem sha256Schedule_eq_sha256ScheduleN (w16 : List (BitVec 32)) :
    sha256Schedule w16 = sha256ScheduleN 48 w16 := by
  unfold sha256Schedule sha256ScheduleN sha256ScheduleStep
  rfl

/-- Linear ($O(1)$ lookup over the 64-word `foldl` schedule) `i`-th schedule word `W_i`. -/
def sha256W (block : List (BitVec 8)) (i : Nat) : BitVec 32 :=
  (sha256ScheduleN 48 ((List.range 16).map fun j => beU32OfBytes ((block.drop (4 * j)).take 4))).getD i 0#32

theorem sha256Schedule_getD_eq_sha256W (block : List (BitVec 8)) (i : Nat) :
    (sha256Schedule ((List.range 16).map fun j => beU32OfBytes ((block.drop (4 * j)).take 4))).getD i 0#32 =
      sha256W block i := by
  unfold sha256W
  rw [sha256Schedule_eq_sha256ScheduleN]

private theorem getD_append_singleton {α : Type} (xs : List α) (x d : α) (k : Nat) :
    (xs ++ [x]).getD k d = if k < xs.length then xs.getD k d else if k = xs.length then x else d := by
  induction xs generalizing k with
  | nil =>
    rcases k with _ | _ | k <;> simp
  | cons y ys ih =>
    rcases k with _ | k
    · simp
    · simp only [List.cons_append, List.getD_cons_succ, List.length_cons, ih k]
      by_cases h1 : k < ys.length
      · have h2 : k + 1 < ys.length + 1 := by omega
        simp [h1, h2]
      · by_cases h2 : k = ys.length
        · subst h2; simp
        · have h3 : ¬(k + 1 < ys.length + 1) := by omega
          simp [h1, h2, h3]

private theorem sha256ScheduleN_zero (w16 : List (BitVec 32)) :
    sha256ScheduleN 0 w16 = w16.take 16 := by
  unfold sha256ScheduleN
  rfl

private theorem sha256ScheduleN_succ (n : Nat) (w16 : List (BitVec 32)) :
    sha256ScheduleN (n + 1) w16 = sha256ScheduleStep (sha256ScheduleN n w16) n := by
  unfold sha256ScheduleN
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

attribute [local irreducible] sha256ScheduleN

private theorem sha256ScheduleN_spec (block : List (BitVec 8)) (n : Nat) :
    let w16 := (List.range 16).map fun j => beU32OfBytes ((block.drop (4 * j)).take 4)
    (sha256ScheduleN n w16).length = 16 + n ∧
      (∀ k < 16, (sha256ScheduleN n w16).getD k 0#32 = beU32OfBytes ((block.drop (4 * k)).take 4)) ∧
      (∀ k, 16 ≤ k → k < 16 + n →
        (sha256ScheduleN n w16).getD k 0#32 =
          (sha256ScheduleN n w16).getD (k - 16) 0#32 +
            sha256SmallSigma0 ((sha256ScheduleN n w16).getD (k - 15) 0#32) +
            (sha256ScheduleN n w16).getD (k - 7) 0#32 +
            sha256SmallSigma1 ((sha256ScheduleN n w16).getD (k - 2) 0#32)) := by
  intro w16
  induction n with
  | zero =>
    rw [sha256ScheduleN_zero]
    have htake : w16.take 16 = w16 := List.take_of_length_le (by simp [w16])
    rw [htake]
    refine ⟨by simp [w16], fun k hk => ?_, fun k h16 hk => by omega⟩
    dsimp only [w16]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
        Option.map_some, Option.getD_some]
  | succ n ih =>
    rcases ih with ⟨hlen, hlt16, hge16⟩
    rw [sha256ScheduleN_succ]
    unfold sha256ScheduleStep
    refine ⟨by rw [List.length_append, List.length_singleton, hlen]; omega,
      fun k hk => ?_, fun k h16 hk => ?_⟩
    · rw [getD_append_singleton, hlen, ite_eq_left_iff.mpr (by omega)]
      exact hlt16 k hk
    · by_cases hlt : k < 16 + n
      · rw [getD_append_singleton, hlen, ite_eq_left_iff.mpr (by omega),
            getD_append_singleton, hlen, ite_eq_left_iff.mpr (by omega),
            getD_append_singleton, hlen, ite_eq_left_iff.mpr (by omega),
            getD_append_singleton, hlen, ite_eq_left_iff.mpr (by omega),
            getD_append_singleton, hlen, ite_eq_left_iff.mpr (by omega)]
        exact hge16 k h16 hlt
      · have heq : k = 16 + n := by omega
        subst heq
        rw [getD_append_singleton, hlen, ite_eq_right_iff.mpr (by omega),
            ite_eq_left_iff.mpr (by omega),
            getD_append_singleton, hlen, ite_eq_left_iff.mpr (by omega),
            getD_append_singleton, hlen, ite_eq_left_iff.mpr (by omega),
            getD_append_singleton, hlen, ite_eq_left_iff.mpr (by omega),
            getD_append_singleton, hlen, ite_eq_left_iff.mpr (by omega)]
        congr 1; congr 1; congr 1
        · congr 1; omega
        · congr 2; omega
        · congr 1; omega
        · congr 2; omega

theorem sha256W_lt_16 (block : List (BitVec 8)) (i : Nat) (hi : i < 16 := by decide) :
    sha256W block i = beU32OfBytes ((block.drop (4 * i)).take 4) := by
  unfold sha256W
  exact (sha256ScheduleN_spec block 48).2.1 i hi

theorem sha256W_ge_16 (block : List (BitVec 8)) (i : Nat)
    (h16 : 16 ≤ i := by decide) (hi64 : i < 64 := by decide) :
    sha256W block i =
      sha256W block (i - 16) + sha256SmallSigma0 (sha256W block (i - 15)) +
        sha256W block (i - 7) + sha256SmallSigma1 (sha256W block (i - 2)) := by
  unfold sha256W
  exact (sha256ScheduleN_spec block 48).2.2 i h16 (by omega)

theorem sha256W_init (block : List (BitVec 8)) (i : Nat)
    (hblock : block.length = 64) (hi : i < 16 := by decide) :
    (rev32_64 ((readLE32 block (4 * i)).zeroExtend 64)).truncate 32 = sha256W block i := by
  rw [rev32_readLE32_eq_beU32OfBytes block (4 * i) (by omega), sha256W_lt_16 block i hi]

theorem sha256W_init_off (block : List (BitVec 8)) (off i : Nat)
    (hblock : block.length = 64) (hi : i < 16 := by decide) (hoff : 4 * i = off := by decide) :
    (rev32_64 ((readLE32 block off).zeroExtend 64)).truncate 32 = sha256W block i := by
  subst hoff
  exact sha256W_init block i hblock hi

@[expose] def sha256T1 (e f g h k w : BitVec 32) : BitVec 32 :=
  h + sha256BigSigma1 e + sha256Ch e f g + k + w

@[expose] def sha256T2 (a b c : BitVec 32) : BitVec 32 :=
  sha256BigSigma0 a + sha256Maj a b c

/-- Linear ($O(i)$ single-recursion) 4-step sliding window of `(a, e)` pairs. -/
@[expose] def sha256Window (st : List (BitVec 32)) (block : List (BitVec 8)) :
    Nat → (BitVec 32 × BitVec 32) × (BitVec 32 × BitVec 32) ×
          (BitVec 32 × BitVec 32) × (BitVec 32 × BitVec 32)
  | 0 => ((st.getD 0 0#32, st.getD 4 0#32),
          (st.getD 1 0#32, st.getD 5 0#32),
          (st.getD 2 0#32, st.getD 6 0#32),
          (st.getD 3 0#32, st.getD 7 0#32))
  | i + 1 =>
    let ((a3, e3), (a2, e2), (a1, e1), (a0, e0)) := sha256Window st block i
    let t1 := sha256T1 e3 e2 e1 e0 (sha256K.getD i 0#32) (sha256W block i)
    let t2 := sha256T2 a3 a2 a1
    ((t1 + t2, a0 + t1), (a3, e3), (a2, e2), (a1, e1))

def sha256AE (st : List (BitVec 32)) (block : List (BitVec 8)) : Nat → BitVec 32 × BitVec 32
  | 0 => (st.getD 3 0#32, st.getD 7 0#32)
  | 1 => (st.getD 2 0#32, st.getD 6 0#32)
  | 2 => (st.getD 1 0#32, st.getD 5 0#32)
  | k + 3 => (sha256Window st block k).1

def sha256A (st : List (BitVec 32)) (block : List (BitVec 8)) (k : Nat) : BitVec 32 :=
  (sha256AE st block k).1

def sha256E (st : List (BitVec 32)) (block : List (BitVec 8)) (k : Nat) : BitVec 32 :=
  (sha256AE st block k).2

private theorem sha256Window_eq (st : List (BitVec 32)) (block : List (BitVec 8)) (i : Nat) :
    sha256Window st block i =
      (sha256AE st block (i + 3), sha256AE st block (i + 2),
       sha256AE st block (i + 1), sha256AE st block i) := by
  induction i with
  | zero =>
    simp only [sha256Window, sha256AE]
  | succ i ih =>
    have hstep : sha256AE st block (i + 1 + 3) = (sha256Window st block (i + 1)).1 := by
      simp only [sha256AE]
    rw [hstep]
    simp only [sha256Window, ih]

theorem sha256A_0 (st : List (BitVec 32)) (block : List (BitVec 8)) :
    st.getD 3 0#32 = sha256A st block 0 := by
  simp only [sha256A, sha256AE]
theorem sha256A_1 (st : List (BitVec 32)) (block : List (BitVec 8)) :
    st.getD 2 0#32 = sha256A st block 1 := by
  simp only [sha256A, sha256AE]
theorem sha256A_2 (st : List (BitVec 32)) (block : List (BitVec 8)) :
    st.getD 1 0#32 = sha256A st block 2 := by
  simp only [sha256A, sha256AE]
theorem sha256A_3 (st : List (BitVec 32)) (block : List (BitVec 8)) :
    st.getD 0 0#32 = sha256A st block 3 := by
  simp only [sha256A, sha256AE, sha256Window]
theorem sha256E_0 (st : List (BitVec 32)) (block : List (BitVec 8)) :
    st.getD 7 0#32 = sha256E st block 0 := by
  simp only [sha256E, sha256AE]
theorem sha256E_1 (st : List (BitVec 32)) (block : List (BitVec 8)) :
    st.getD 6 0#32 = sha256E st block 1 := by
  simp only [sha256E, sha256AE]
theorem sha256E_2 (st : List (BitVec 32)) (block : List (BitVec 8)) :
    st.getD 5 0#32 = sha256E st block 2 := by
  simp only [sha256E, sha256AE]
theorem sha256E_3 (st : List (BitVec 32)) (block : List (BitVec 8)) :
    st.getD 4 0#32 = sha256E st block 3 := by
  simp only [sha256E, sha256AE, sha256Window]

theorem sha256A_step (st : List (BitVec 32)) (block : List (BitVec 8)) (i : Nat) :
    sha256A st block (i + 4) =
      sha256T1 (sha256E st block (i + 3)) (sha256E st block (i + 2))
        (sha256E st block (i + 1)) (sha256E st block i) (sha256K.getD i 0#32) (sha256W block i) +
      sha256T2 (sha256A st block (i + 3)) (sha256A st block (i + 2)) (sha256A st block (i + 1)) := by
  have h : sha256A st block (i + 4) = (sha256Window st block (i + 1)).1.1 := by
    simp only [sha256A, sha256AE]
  rw [h]
  simp only [sha256Window, sha256Window_eq, sha256A, sha256E]

theorem sha256E_step (st : List (BitVec 32)) (block : List (BitVec 8)) (i : Nat) :
    sha256E st block (i + 4) =
      sha256A st block i +
      sha256T1 (sha256E st block (i + 3)) (sha256E st block (i + 2))
        (sha256E st block (i + 1)) (sha256E st block i) (sha256K.getD i 0#32) (sha256W block i) := by
  have h : sha256E st block (i + 4) = (sha256Window st block (i + 1)).1.2 := by
    simp only [sha256E, sha256AE]
  rw [h]
  simp only [sha256Window, sha256Window_eq, sha256A, sha256E]

attribute [local irreducible] sha256W sha256Window sha256AE sha256A sha256E

private def sha256CompressRounds (n : Nat) (st : List (BitVec 32)) (ws : List (BitVec 32)) :
    List (BitVec 32) :=
  (List.range n).foldl (fun cur i => sha256Round cur (sha256K.getD i 0#32) (ws.getD i 0#32)) st

private theorem sha256CompressRounds_zero (st ws : List (BitVec 32)) :
    sha256CompressRounds 0 st ws = st := by
  unfold sha256CompressRounds
  rfl

private theorem sha256CompressRounds_succ (n : Nat) (st ws : List (BitVec 32)) :
    sha256CompressRounds (n + 1) st ws =
      sha256Round (sha256CompressRounds n st ws) (sha256K.getD n 0#32) (ws.getD n 0#32) := by
  unfold sha256CompressRounds
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem sha256CompressBlock_eq_rounds (st : List (BitVec 32)) (block : List (BitVec 8)) :
    sha256CompressBlock st block =
      let w16 := (List.range 16).map fun i => beU32OfBytes ((block.drop (4 * i)).take 4)
      let ws := sha256Schedule w16
      let st' := sha256CompressRounds 64 st ws
      (List.range 8).map fun i => st.getD i 0#32 + st'.getD i 0#32 := by
  unfold sha256CompressBlock sha256CompressRounds
  rfl

attribute [local irreducible] sha256CompressRounds

private theorem sha256CompressRounds_eq_sha256AE (st : List (BitVec 32)) (block : List (BitVec 8))
    (hst : st.length = 8) (n : Nat) :
    sha256CompressRounds n st
      (sha256Schedule ((List.range 16).map fun i => beU32OfBytes ((block.drop (4 * i)).take 4))) =
      [sha256A st block (n + 3), sha256A st block (n + 2),
       sha256A st block (n + 1), sha256A st block n,
       sha256E st block (n + 3), sha256E st block (n + 2),
       sha256E st block (n + 1), sha256E st block n] := by
  induction n with
  | zero =>
    rw [sha256CompressRounds_zero]
    rcases st with _ | ⟨s0, _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, _ | ⟨s4, _ | ⟨s5, _ | ⟨s6, _ | ⟨s7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      try (simp at hst)
    simp only [Nat.zero_add, List.getD_cons_zero, List.getD_cons_succ,
      ← sha256A_0, ← sha256A_1, ← sha256A_2, ← sha256A_3,
      ← sha256E_0, ← sha256E_1, ← sha256E_2, ← sha256E_3]
  | succ n ih =>
    rw [sha256CompressRounds_succ, ih, sha256Schedule_getD_eq_sha256W block n]
    unfold sha256Round
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    have ha : n + 1 + 3 = n + 4 := by omega
    have he : n + 1 + 2 = n + 3 := by omega
    have hf : n + 1 + 1 = n + 2 := by omega
    rw [ha, he, hf, sha256A_step, sha256E_step]
    unfold sha256T1 sha256T2
    rfl

private theorem map_range8_add (st st' : List (BitVec 32)) :
    ((List.range 8).map fun i => st.getD i 0#32 + st'.getD i 0#32) =
      [st.getD 0 0#32 + st'.getD 0 0#32,
       st.getD 1 0#32 + st'.getD 1 0#32,
       st.getD 2 0#32 + st'.getD 2 0#32,
       st.getD 3 0#32 + st'.getD 3 0#32,
       st.getD 4 0#32 + st'.getD 4 0#32,
       st.getD 5 0#32 + st'.getD 5 0#32,
       st.getD 6 0#32 + st'.getD 6 0#32,
       st.getD 7 0#32 + st'.getD 7 0#32] :=
  rfl

theorem sha256CompressBlock_eq_sha256AE (st : List (BitVec 32)) (block : List (BitVec 8))
    (hst : st.length = 8) :
    sha256CompressBlock st block =
      [st.getD 0 0#32 + sha256A st block 67,
       st.getD 1 0#32 + sha256A st block 66,
       st.getD 2 0#32 + sha256A st block 65,
       st.getD 3 0#32 + sha256A st block 64,
       st.getD 4 0#32 + sha256E st block 67,
       st.getD 5 0#32 + sha256E st block 66,
       st.getD 6 0#32 + sha256E st block 65,
       st.getD 7 0#32 + sha256E st block 64] := by
  rw [sha256CompressBlock_eq_rounds, map_range8_add, sha256CompressRounds_eq_sha256AE st block hst 64]
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.reduceAdd]

/-! ## 3. Instruction-AST Step-Folding Lemmas (`ac_rfl`) -/

theorem sha256W_step1 (block : List (BitVec 8)) (i15 i16 i7 i2 i : Nat)
    (h16 : 16 ≤ i := by decide) (hi64 : i < 64 := by decide)
    (hi16 : i - 16 = i16 := by decide) (hi15 : i - 15 = i15 := by decide)
    (hi7 : i - 7 = i7 := by decide) (hi2 : i - 2 = i2 := by decide) :
    ((((BitVec.setWidth 32 ((sha256W block i15 ++ sha256W block i15) >>> 7) ^^^
        (sha256W block i15).rotateRight 18) ^^^ (sha256W block i15 >>> 3)) +
      sha256W block i16 + sha256W block i7) +
     (((BitVec.setWidth 32 ((sha256W block i2 ++ sha256W block i2) >>> 17) ^^^
        (sha256W block i2).rotateRight 19) ^^^ (sha256W block i2 >>> 10)))) =
      sha256W block i := by
  subst hi16 hi15 hi7 hi2
  rw [sha256SmallSigma0_eq, sha256SmallSigma1_eq, sha256W_ge_16 block i h16 hi64]
  bv32_add_ac

theorem sha256W_step2 (block : List (BitVec 8)) (i15 i16 i7 i2 i : Nat)
    (h16 : 16 ≤ i := by decide) (hi64 : i < 64 := by decide)
    (hi16 : i - 16 = i16 := by decide) (hi15 : i - 15 = i15 := by decide)
    (hi7 : i - 7 = i7 := by decide) (hi2 : i - 2 = i2 := by decide) :
    ((((BitVec.setWidth 32 ((sha256W block i15 ++ sha256W block i15) >>> 7) ^^^
        (sha256W block i15).rotateRight 18) ^^^ (sha256W block i15 >>> 3)) +
      (sha256W block i16 + sha256W block i7)) +
     (((BitVec.setWidth 32 ((sha256W block i2 ++ sha256W block i2) >>> 17) ^^^
        (sha256W block i2).rotateRight 19) ^^^ (sha256W block i2 >>> 10)))) =
      sha256W block i := by
  subst hi16 hi15 hi7 hi2
  rw [sha256SmallSigma0_eq, sha256SmallSigma1_eq, sha256W_ge_16 block i h16 hi64]
  bv32_add_ac

theorem sha256W_add_k (block : List (BitVec 8)) (k : BitVec 32) (i16 i15 i7 i2 i : Nat)
    (h16 : 16 ≤ i := by decide) (hi64 : i < 64 := by decide)
    (hi16 : i - 16 = i16 := by decide) (hi15 : i - 15 = i15 := by decide)
    (hi7 : i - 7 = i7 := by decide) (hi2 : i - 2 = i2 := by decide) :
    ((((sha256W block i16 + k) +
       ((BitVec.setWidth 32 ((sha256W block i15 ++ sha256W block i15) >>> 7) ^^^
         (sha256W block i15).rotateRight 18) ^^^ (sha256W block i15 >>> 3))) +
      sha256W block i7) +
     ((BitVec.setWidth 32 ((sha256W block i2 ++ sha256W block i2) >>> 17) ^^^
       (sha256W block i2).rotateRight 19) ^^^ (sha256W block i2 >>> 10))) =
      sha256W block i + k := by
  subst hi16 hi15 hi7 hi2
  rw [sha256SmallSigma0_eq, sha256SmallSigma1_eq, sha256W_ge_16 block i h16 hi64]
  bv32_add_ac

theorem sha256T2_eq (a b c : BitVec 32) :
    ((BitVec.setWidth 32 ((a ++ a) >>> 2) ^^^ a.rotateRight 13) ^^^ a.rotateRight 22) +
      ((a &&& (b ^^^ c)) ^^^ (b &&& c)) =
      sha256T2 a b c := by
  unfold sha256T2; rw [sha256BigSigma0_eq, sha256Maj_eq_and_xor]

theorem sha256T1_eq1 (e f g h k w : BitVec 32) :
    (((((e &&& f) + h) + (g &&& ~~~e)) + w) + k) +
      ((BitVec.setWidth 32 ((e ++ e) >>> 6) ^^^ e.rotateRight 11) ^^^ e.rotateRight 25) =
      sha256T1 e f g h k w := by
  unfold sha256T1; rw [sha256Ch_add_1, sha256BigSigma1_eq]; bv32_add_ac

theorem sha256T1_eq2 (e f g h k w : BitVec 32) :
    ((((k + w) + h) + (g &&& ~~~e)) + (e &&& f)) +
      ((BitVec.setWidth 32 ((e ++ e) >>> 6) ^^^ e.rotateRight 11) ^^^ e.rotateRight 25) =
      sha256T1 e f g h k w := by
  unfold sha256T1; rw [sha256Ch_add_2, sha256BigSigma1_eq]; bv32_add_ac

theorem sha256T1_eq3 (e f g h k w : BitVec 32) :
    (((h + (w + k)) + (g &&& ~~~e)) + (e &&& f)) +
      ((BitVec.setWidth 32 ((e ++ e) >>> 6) ^^^ e.rotateRight 11) ^^^ e.rotateRight 25) =
      sha256T1 e f g h k w := by
  unfold sha256T1; rw [sha256Ch_add_2, sha256BigSigma1_eq]; bv32_add_ac

theorem sha256T1_eq4 (e f g h k w : BitVec 32) :
    (((k + w) + h) + ((e &&& f) ||| (g &&& ~~~e))) +
      ((BitVec.setWidth 32 ((e ++ e) >>> 6) ^^^ e.rotateRight 11) ^^^ e.rotateRight 25) =
      sha256T1 e f g h k w := by
  unfold sha256T1; rw [sha256Ch_eq_orr_bic, sha256BigSigma1_eq]; bv32_add_ac

theorem sha256T1_eq5 (e f g h k w : BitVec 32) :
    (((w + (h + k)) + (g &&& ~~~e)) + (e &&& f)) +
      ((BitVec.setWidth 32 ((e ++ e) >>> 6) ^^^ e.rotateRight 11) ^^^ e.rotateRight 25) =
      sha256T1 e f g h k w := by
  unfold sha256T1; rw [sha256Ch_add_2, sha256BigSigma1_eq]; bv32_add_ac

theorem sha256T1_eq6 (e f g h k w : BitVec 32) :
    (((w + k) + h) + ((e &&& f) ||| (g &&& ~~~e))) +
      ((BitVec.setWidth 32 ((e ++ e) >>> 6) ^^^ e.rotateRight 11) ^^^ e.rotateRight 25) =
      sha256T1 e f g h k w := by
  unfold sha256T1; rw [sha256Ch_eq_orr_bic, sha256BigSigma1_eq]; bv32_add_ac

theorem sha256E_from_t1 (st : List (BitVec 32)) (block : List (BitVec 8))
    (i3 i2 i1 i i4 : Nat)
    (hi1 : i + 1 = i1 := by decide) (hi2 : i + 2 = i2 := by decide)
    (hi3 : i + 3 = i3 := by decide) (hi4 : i + 4 = i4 := by decide) :
    sha256T1 (sha256E st block i3) (sha256E st block i2) (sha256E st block i1)
      (sha256E st block i) (sha256K.getD i 0#32) (sha256W block i) +
      sha256A st block i =
      sha256E st block i4 := by
  subst hi1 hi2 hi3 hi4
  rw [sha256E_step]
  exact BitVec.add_comm _ _

theorem sha256A_from_t1_t2 (st : List (BitVec 32)) (block : List (BitVec 8))
    (i3 i2 i1 i i4 : Nat)
    (hi1 : i + 1 = i1 := by decide) (hi2 : i + 2 = i2 := by decide)
    (hi3 : i + 3 = i3 := by decide) (hi4 : i + 4 = i4 := by decide) :
    sha256T2 (sha256A st block i3) (sha256A st block i2) (sha256A st block i1) +
      sha256T1 (sha256E st block i3) (sha256E st block i2) (sha256E st block i1)
        (sha256E st block i) (sha256K.getD i 0#32) (sha256W block i) =
      sha256A st block i4 := by
  subst hi1 hi2 hi3 hi4
  rw [sha256A_step]
  exact BitVec.add_comm _ _

private theorem sha256Final0_gen (st : List (BitVec 32)) (block : List (BitVec 8))
    (i3 i2 i1 i i4 : Nat)
    (hi1 : i + 1 = i1 := by decide) (hi2 : i + 2 = i2 := by decide)
    (hi3 : i + 3 = i3 := by decide) (hi4 : i + 4 = i4 := by decide) :
    ((((sha256A st block i3 &&& (sha256A st block i2 ^^^ sha256A st block i1)) ^^^
        (sha256A st block i2 &&& sha256A st block i1)) + st.getD 0 0#32) +
      ((BitVec.setWidth 32 ((sha256A st block i3 ++ sha256A st block i3) >>> 2) ^^^
        (sha256A st block i3).rotateRight 13) ^^^ (sha256A st block i3).rotateRight 22)) +
      sha256T1 (sha256E st block i3) (sha256E st block i2) (sha256E st block i1)
        (sha256E st block i) (sha256K.getD i 0#32) (sha256W block i) =
      st.getD 0 0#32 + sha256A st block i4 := by
  subst hi1 hi2 hi3 hi4
  rw [sha256Maj_eq_and_xor, sha256BigSigma0_eq, sha256A_step]
  unfold sha256T2; bv32_add_ac

theorem sha256Final0 (st : List (BitVec 32)) (block : List (BitVec 8)) :
    ((((sha256A st block 66 &&& (sha256A st block 65 ^^^ sha256A st block 64)) ^^^
        (sha256A st block 65 &&& sha256A st block 64)) + st.getD 0 0#32) +
      ((BitVec.setWidth 32 ((sha256A st block 66 ++ sha256A st block 66) >>> 2) ^^^
        (sha256A st block 66).rotateRight 13) ^^^ (sha256A st block 66).rotateRight 22)) +
      sha256T1 (sha256E st block 66) (sha256E st block 65) (sha256E st block 64)
        (sha256E st block 63) (sha256K.getD 63 0#32) (sha256W block 63) =
      st.getD 0 0#32 + sha256A st block 67 :=
  sha256Final0_gen st block 66 65 64 63 67

private theorem sha256Final4_gen (st : List (BitVec 32)) (block : List (BitVec 8))
    (i3 i2 i1 i i4 : Nat)
    (hi1 : i + 1 = i1 := by decide) (hi2 : i + 2 = i2 := by decide)
    (hi3 : i + 3 = i3 := by decide) (hi4 : i + 4 = i4 := by decide) :
    (sha256A st block i + st.getD 4 0#32) +
      sha256T1 (sha256E st block i3) (sha256E st block i2) (sha256E st block i1)
        (sha256E st block i) (sha256K.getD i 0#32) (sha256W block i) =
      st.getD 4 0#32 + sha256E st block i4 := by
  subst hi1 hi2 hi3 hi4
  rw [sha256E_step]; bv32_add_ac

theorem sha256Final4 (st : List (BitVec 32)) (block : List (BitVec 8)) :
    (sha256A st block 63 + st.getD 4 0#32) +
      sha256T1 (sha256E st block 66) (sha256E st block 65) (sha256E st block 64)
        (sha256E st block 63) (sha256K.getD 63 0#32) (sha256W block 63) =
      st.getD 4 0#32 + sha256E st block 67 :=
  sha256Final4_gen st block 66 65 64 63 67

attribute [local irreducible] sha256T1 sha256T2

end LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256RoundDefs
