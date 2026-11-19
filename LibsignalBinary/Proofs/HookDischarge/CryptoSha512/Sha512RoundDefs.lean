/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Ref -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Cells -- proof-setup: allow-public-import

/-!
# Linear Round Recurrence, Bitwise Bridges, and Step-Folding Lemmas for SHA-512

Pure 64-bit instruction-AST identities, linear ($O(n)$) message-schedule (`sha512W`) and
working-state (`sha512A`, `sha512E`) recurrences, and instruction-AST step-folding lemmas for
`sha2::sha512::compress512`.

Kept independent of `VCVio` / `SignalPqxdh` so the 80-round stepping module compiles with a
minimal `Arm64` + `ProofLib` import cone.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512RoundDefs

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Ref
  (sha512K beU64OfBytes
   sha512SmallSigma0 sha512SmallSigma1 sha512BigSigma0 sha512BigSigma1
   sha512Ch sha512Maj sha512Schedule sha512Round sha512CompressBlock)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Cells
  (readLE64 rev64_readLE64_eq_beU64OfBytes)

/-! ## 1. Bitwise 64-Bit Identity Bridges (`Ch`, `Maj`, $\Sigma_0$, $\Sigma_1$, $\sigma_0$, $\sigma_1$) -/

private theorem bv64_add_left_comm (a b c : BitVec 64) : a + (b + c) = b + (a + c) := by
  rw [← BitVec.add_assoc, BitVec.add_comm a b, BitVec.add_assoc]

private theorem bv64_xor_left_comm (a b c : BitVec 64) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc]

local macro "bv64_add_ac" : tactic =>
  `(tactic| simp only [BitVec.add_assoc, BitVec.add_comm, bv64_add_left_comm])

local macro "bv64_xor_ac" : tactic =>
  `(tactic| simp only [BitVec.xor_assoc, BitVec.xor_comm, bv64_xor_left_comm])

theorem sha512Ch_eq_orr_bic (e f g : BitVec 64) :
    (e &&& f) ||| (g &&& ~~~e) = sha512Ch e f g := by
  unfold sha512Ch; bv_slice

theorem sha512Ch_eq_add_bic (e f g : BitVec 64) :
    (e &&& f) + (g &&& ~~~e) = sha512Ch e f g := by
  unfold sha512Ch; bv_robdd

theorem sha512Ch_add_1 (e f g x : BitVec 64) :
    ((e &&& f) + x) + (g &&& ~~~e) = x + sha512Ch e f g := by
  rw [← sha512Ch_eq_add_bic]; bv64_add_ac

theorem sha512Ch_add_2 (e f g x : BitVec 64) :
    (x + (g &&& ~~~e)) + (e &&& f) = x + sha512Ch e f g := by
  rw [← sha512Ch_eq_add_bic]; bv64_add_ac

theorem sha512Maj_eq_and_xor (a b c : BitVec 64) :
    (a &&& (b ^^^ c)) ^^^ (b &&& c) = sha512Maj a b c := by
  unfold sha512Maj; bv_slice

theorem sha512Maj_eq_and_xor_comm (a b c : BitVec 64) :
    ((a ^^^ b) &&& c) ^^^ (a &&& b) = sha512Maj a b c := by
  unfold sha512Maj; bv_slice

private theorem rotateRight64_eq_rotateLeft64 (x : BitVec 64) (r l : Nat)
    (hr : r < 64 := by decide) (hl : l < 64 := by decide)
    (h1 : 64 - r = l := by rfl) (h2 : 64 - l = r := by rfl) :
    x.rotateRight r = x.rotateLeft l := by
  rw [BitVec.rotateRight_eq_rotateRightAux_of_lt hr,
      BitVec.rotateLeft_eq_rotateLeftAux_of_lt hl]
  unfold BitVec.rotateRightAux BitVec.rotateLeftAux
  rw [h1, h2, BitVec.or_comm]

private theorem setWidth64_append_ushiftRight_eq_rotateLeft (x : BitVec 64) (r l : Nat)
    (hl : l < 64 := by decide) (hrl : r + l = 64 := by rfl) :
    BitVec.setWidth 64 ((x ++ x) >>> r) = x.rotateLeft l := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append,
      BitVec.getLsbD_rotateLeft_of_le hl]
  simp only [hi, decide_true, Bool.true_and]
  by_cases hlt : i < l
  · have hlt2 : r + i < 64 := by omega
    simp only [hlt, hlt2, ↓reduceIte]
    congr 1
    omega
  · have hlt2 : ¬(r + i < 64) := by omega
    simp only [hlt, hlt2, ↓reduceIte]
    congr 1
    omega

theorem extr64_1 (x : BitVec 64) :
    BitVec.setWidth 64 ((x ++ x) >>> 1) = x.rotateRight 1 := by
  rw [setWidth64_append_ushiftRight_eq_rotateLeft x 1 63, ← rotateRight64_eq_rotateLeft64 x 1 63]

theorem extr64_14 (x : BitVec 64) :
    BitVec.setWidth 64 ((x ++ x) >>> 14) = x.rotateRight 14 := by
  rw [setWidth64_append_ushiftRight_eq_rotateLeft x 14 50, ← rotateRight64_eq_rotateLeft64 x 14 50]

theorem extr64_19 (x : BitVec 64) :
    BitVec.setWidth 64 ((x ++ x) >>> 19) = x.rotateRight 19 := by
  rw [setWidth64_append_ushiftRight_eq_rotateLeft x 19 45, ← rotateRight64_eq_rotateLeft64 x 19 45]

theorem extr64_28 (x : BitVec 64) :
    BitVec.setWidth 64 ((x ++ x) >>> 28) = x.rotateRight 28 := by
  rw [setWidth64_append_ushiftRight_eq_rotateLeft x 28 36, ← rotateRight64_eq_rotateLeft64 x 28 36]

theorem sha512SmallSigma0_eq (x : BitVec 64) :
    ((BitVec.setWidth 64 ((x ++ x) >>> 1) ^^^ x.rotateRight 8) ^^^ (x >>> 7)) =
      sha512SmallSigma0 x := by unfold sha512SmallSigma0; rw [extr64_1]

theorem sha512SmallSigma1_eq (x : BitVec 64) :
    ((BitVec.setWidth 64 ((x ++ x) >>> 19) ^^^ x.rotateRight 61) ^^^ (x >>> 6)) =
      sha512SmallSigma1 x := by unfold sha512SmallSigma1; rw [extr64_19]

theorem sha512BigSigma0_eq (x : BitVec 64) :
    ((BitVec.setWidth 64 ((x ++ x) >>> 28) ^^^ x.rotateRight 34) ^^^ x.rotateRight 39) =
      sha512BigSigma0 x := by unfold sha512BigSigma0; rw [extr64_28]

theorem sha512BigSigma1_eq (x : BitVec 64) :
    ((BitVec.setWidth 64 ((x ++ x) >>> 14) ^^^ x.rotateRight 18) ^^^ x.rotateRight 41) =
      sha512BigSigma1 x := by unfold sha512BigSigma1; rw [extr64_14]

/-! ## 2. Linear Schedule (`sha512W`) & Linear Working-State Window (`sha512A`, `sha512E`) -/

private def sha512ScheduleStep (ws : List (BitVec 64)) (i : Nat) : List (BitVec 64) :=
  let w16_back := ws.getD i 0#64
  let w15_back := ws.getD (i + 1) 0#64
  let w7_back  := ws.getD (i + 9) 0#64
  let w2_back  := ws.getD (i + 14) 0#64
  let next := w16_back + sha512SmallSigma0 w15_back + w7_back + sha512SmallSigma1 w2_back
  ws ++ [next]

private def sha512ScheduleN (n : Nat) (w16 : List (BitVec 64)) : List (BitVec 64) :=
  (List.range n).foldl sha512ScheduleStep (w16.take 16)

private theorem sha512Schedule_eq_sha512ScheduleN (w16 : List (BitVec 64)) :
    sha512Schedule w16 = sha512ScheduleN 64 w16 := by
  unfold sha512Schedule sha512ScheduleN sha512ScheduleStep
  rfl

/-- Linear ($O(1)$ lookup over the 80-word `foldl` schedule) `i`-th schedule word `W_i`. -/
def sha512W (block : List (BitVec 8)) (i : Nat) : BitVec 64 :=
  (sha512ScheduleN 64 ((List.range 16).map fun j => beU64OfBytes ((block.drop (8 * j)).take 8))).getD i 0#64

theorem sha512Schedule_getD_eq_sha512W (block : List (BitVec 8)) (i : Nat) :
    (sha512Schedule ((List.range 16).map fun j => beU64OfBytes ((block.drop (8 * j)).take 8))).getD i 0#64 =
      sha512W block i := by
  unfold sha512W
  rw [sha512Schedule_eq_sha512ScheduleN]

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

private theorem sha512ScheduleN_zero (w16 : List (BitVec 64)) :
    sha512ScheduleN 0 w16 = w16.take 16 := by
  unfold sha512ScheduleN
  rfl

private theorem sha512ScheduleN_succ (n : Nat) (w16 : List (BitVec 64)) :
    sha512ScheduleN (n + 1) w16 = sha512ScheduleStep (sha512ScheduleN n w16) n := by
  unfold sha512ScheduleN
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

attribute [local irreducible] sha512ScheduleN

private theorem sha512ScheduleN_spec (block : List (BitVec 8)) (n : Nat) :
    let w16 := (List.range 16).map fun j => beU64OfBytes ((block.drop (8 * j)).take 8)
    (sha512ScheduleN n w16).length = 16 + n ∧
      (∀ k < 16, (sha512ScheduleN n w16).getD k 0#64 = beU64OfBytes ((block.drop (8 * k)).take 8)) ∧
      (∀ k, 16 ≤ k → k < 16 + n →
        (sha512ScheduleN n w16).getD k 0#64 =
          (sha512ScheduleN n w16).getD (k - 16) 0#64 +
            sha512SmallSigma0 ((sha512ScheduleN n w16).getD (k - 15) 0#64) +
            (sha512ScheduleN n w16).getD (k - 7) 0#64 +
            sha512SmallSigma1 ((sha512ScheduleN n w16).getD (k - 2) 0#64)) := by
  intro w16
  induction n with
  | zero =>
    rw [sha512ScheduleN_zero]
    have htake : w16.take 16 = w16 := List.take_of_length_le (by simp [w16])
    rw [htake]
    refine ⟨by simp [w16], fun k hk => ?_, fun k h16 hk => by omega⟩
    dsimp only [w16]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
        Option.map_some, Option.getD_some]
  | succ n ih =>
    rcases ih with ⟨hlen, hlt16, hge16⟩
    rw [sha512ScheduleN_succ]
    unfold sha512ScheduleStep
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

theorem sha512W_lt_16 (block : List (BitVec 8)) (i : Nat) (hi : i < 16 := by decide) :
    sha512W block i = beU64OfBytes ((block.drop (8 * i)).take 8) := by
  unfold sha512W
  exact (sha512ScheduleN_spec block 64).2.1 i hi

theorem sha512W_ge_16 (block : List (BitVec 8)) (i : Nat)
    (h16 : 16 ≤ i := by decide) (hi80 : i < 80 := by decide) :
    sha512W block i =
      sha512W block (i - 16) + sha512SmallSigma0 (sha512W block (i - 15)) +
        sha512W block (i - 7) + sha512SmallSigma1 (sha512W block (i - 2)) := by
  unfold sha512W
  exact (sha512ScheduleN_spec block 64).2.2 i h16 (by omega)

theorem sha512W_init (block : List (BitVec 8)) (i : Nat)
    (hblock : block.length = 128) (hi : i < 16 := by decide) :
    rev64 (readLE64 block (8 * i)) = sha512W block i := by
  rw [rev64_readLE64_eq_beU64OfBytes block (8 * i) (by omega), sha512W_lt_16 block i hi]

theorem sha512W_init_off (block : List (BitVec 8)) (off i : Nat)
    (hblock : block.length = 128) (hi : i < 16 := by decide) (hoff : 8 * i = off := by decide) :
    rev64 (readLE64 block off) = sha512W block i := by
  subst hoff
  exact sha512W_init block i hblock hi

def sha512T1 (e f g h k w : BitVec 64) : BitVec 64 :=
  h + sha512BigSigma1 e + sha512Ch e f g + k + w

def sha512T2 (a b c : BitVec 64) : BitVec 64 :=
  sha512BigSigma0 a + sha512Maj a b c

/-- Linear ($O(i)$ single-recursion) 4-step sliding window of `(a, e)` pairs. -/
def sha512Window (st : List (BitVec 64)) (block : List (BitVec 8)) :
    Nat → (BitVec 64 × BitVec 64) × (BitVec 64 × BitVec 64) ×
          (BitVec 64 × BitVec 64) × (BitVec 64 × BitVec 64)
  | 0 => ((st.getD 0 0#64, st.getD 4 0#64),
          (st.getD 1 0#64, st.getD 5 0#64),
          (st.getD 2 0#64, st.getD 6 0#64),
          (st.getD 3 0#64, st.getD 7 0#64))
  | i + 1 =>
    let ((a3, e3), (a2, e2), (a1, e1), (a0, e0)) := sha512Window st block i
    let t1 := sha512T1 e3 e2 e1 e0 (sha512K.getD i 0#64) (sha512W block i)
    let t2 := sha512T2 a3 a2 a1
    ((t1 + t2, a0 + t1), (a3, e3), (a2, e2), (a1, e1))

def sha512AE (st : List (BitVec 64)) (block : List (BitVec 8)) : Nat → BitVec 64 × BitVec 64
  | 0 => (st.getD 3 0#64, st.getD 7 0#64)
  | 1 => (st.getD 2 0#64, st.getD 6 0#64)
  | 2 => (st.getD 1 0#64, st.getD 5 0#64)
  | k + 3 => (sha512Window st block k).1

def sha512A (st : List (BitVec 64)) (block : List (BitVec 8)) (k : Nat) : BitVec 64 :=
  (sha512AE st block k).1

def sha512E (st : List (BitVec 64)) (block : List (BitVec 8)) (k : Nat) : BitVec 64 :=
  (sha512AE st block k).2

private theorem sha512Window_eq (st : List (BitVec 64)) (block : List (BitVec 8)) (i : Nat) :
    sha512Window st block i =
      (sha512AE st block (i + 3), sha512AE st block (i + 2),
       sha512AE st block (i + 1), sha512AE st block i) := by
  induction i with
  | zero =>
    simp only [sha512Window, sha512AE]
  | succ i ih =>
    have hstep : sha512AE st block (i + 1 + 3) = (sha512Window st block (i + 1)).1 := by
      simp only [sha512AE]
    rw [hstep]
    simp only [sha512Window, ih]

theorem sha512A_0 (st : List (BitVec 64)) (block : List (BitVec 8)) :
    st.getD 3 0#64 = sha512A st block 0 := by
  simp only [sha512A, sha512AE]
theorem sha512A_1 (st : List (BitVec 64)) (block : List (BitVec 8)) :
    st.getD 2 0#64 = sha512A st block 1 := by
  simp only [sha512A, sha512AE]
theorem sha512A_2 (st : List (BitVec 64)) (block : List (BitVec 8)) :
    st.getD 1 0#64 = sha512A st block 2 := by
  simp only [sha512A, sha512AE]
theorem sha512A_3 (st : List (BitVec 64)) (block : List (BitVec 8)) :
    st.getD 0 0#64 = sha512A st block 3 := by
  simp only [sha512A, sha512AE, sha512Window]
theorem sha512E_0 (st : List (BitVec 64)) (block : List (BitVec 8)) :
    st.getD 7 0#64 = sha512E st block 0 := by
  simp only [sha512E, sha512AE]
theorem sha512E_1 (st : List (BitVec 64)) (block : List (BitVec 8)) :
    st.getD 6 0#64 = sha512E st block 1 := by
  simp only [sha512E, sha512AE]
theorem sha512E_2 (st : List (BitVec 64)) (block : List (BitVec 8)) :
    st.getD 5 0#64 = sha512E st block 2 := by
  simp only [sha512E, sha512AE]
theorem sha512E_3 (st : List (BitVec 64)) (block : List (BitVec 8)) :
    st.getD 4 0#64 = sha512E st block 3 := by
  simp only [sha512E, sha512AE, sha512Window]

theorem sha512A_step (st : List (BitVec 64)) (block : List (BitVec 8)) (i : Nat) :
    sha512A st block (i + 4) =
      sha512T1 (sha512E st block (i + 3)) (sha512E st block (i + 2))
        (sha512E st block (i + 1)) (sha512E st block i) (sha512K.getD i 0#64) (sha512W block i) +
      sha512T2 (sha512A st block (i + 3)) (sha512A st block (i + 2)) (sha512A st block (i + 1)) := by
  have h : sha512A st block (i + 4) = (sha512Window st block (i + 1)).1.1 := by
    simp only [sha512A, sha512AE]
  rw [h]
  simp only [sha512Window, sha512Window_eq, sha512A, sha512E]

theorem sha512E_step (st : List (BitVec 64)) (block : List (BitVec 8)) (i : Nat) :
    sha512E st block (i + 4) =
      sha512A st block i +
      sha512T1 (sha512E st block (i + 3)) (sha512E st block (i + 2))
        (sha512E st block (i + 1)) (sha512E st block i) (sha512K.getD i 0#64) (sha512W block i) := by
  have h : sha512E st block (i + 4) = (sha512Window st block (i + 1)).1.2 := by
    simp only [sha512E, sha512AE]
  rw [h]
  simp only [sha512Window, sha512Window_eq, sha512A, sha512E]

attribute [local irreducible] sha512W sha512Window sha512AE sha512A sha512E

private def sha512CompressRounds (n : Nat) (st : List (BitVec 64)) (ws : List (BitVec 64)) :
    List (BitVec 64) :=
  (List.range n).foldl (fun cur i => sha512Round cur (sha512K.getD i 0#64) (ws.getD i 0#64)) st

private theorem sha512CompressRounds_zero (st ws : List (BitVec 64)) :
    sha512CompressRounds 0 st ws = st := by
  unfold sha512CompressRounds
  rfl

private theorem sha512CompressRounds_succ (n : Nat) (st ws : List (BitVec 64)) :
    sha512CompressRounds (n + 1) st ws =
      sha512Round (sha512CompressRounds n st ws) (sha512K.getD n 0#64) (ws.getD n 0#64) := by
  unfold sha512CompressRounds
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem sha512CompressBlock_eq_rounds (st : List (BitVec 64)) (block : List (BitVec 8)) :
    sha512CompressBlock st block =
      let w16 := (List.range 16).map fun i => beU64OfBytes ((block.drop (8 * i)).take 8)
      let ws := sha512Schedule w16
      let st' := sha512CompressRounds 80 st ws
      (List.range 8).map fun i => st.getD i 0#64 + st'.getD i 0#64 := by
  unfold sha512CompressBlock sha512CompressRounds
  rfl

attribute [local irreducible] sha512CompressRounds

private theorem sha512CompressRounds_eq_sha512AE (st : List (BitVec 64)) (block : List (BitVec 8))
    (hst : st.length = 8) (n : Nat) :
    sha512CompressRounds n st
      (sha512Schedule ((List.range 16).map fun i => beU64OfBytes ((block.drop (8 * i)).take 8))) =
      [sha512A st block (n + 3), sha512A st block (n + 2),
       sha512A st block (n + 1), sha512A st block n,
       sha512E st block (n + 3), sha512E st block (n + 2),
       sha512E st block (n + 1), sha512E st block n] := by
  induction n with
  | zero =>
    rw [sha512CompressRounds_zero]
    rcases st with _ | ⟨s0, _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, _ | ⟨s4, _ | ⟨s5, _ | ⟨s6, _ | ⟨s7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      try (simp at hst)
    simp only [Nat.zero_add, List.getD_cons_zero, List.getD_cons_succ,
      ← sha512A_0, ← sha512A_1, ← sha512A_2, ← sha512A_3,
      ← sha512E_0, ← sha512E_1, ← sha512E_2, ← sha512E_3]
  | succ n ih =>
    rw [sha512CompressRounds_succ, ih, sha512Schedule_getD_eq_sha512W block n]
    unfold sha512Round
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    have ha : n + 1 + 3 = n + 4 := by omega
    have he : n + 1 + 2 = n + 3 := by omega
    have hf : n + 1 + 1 = n + 2 := by omega
    rw [ha, he, hf, sha512A_step, sha512E_step]
    unfold sha512T1 sha512T2
    rfl

private theorem map_range8_add64 (st st' : List (BitVec 64)) :
    ((List.range 8).map fun i => st.getD i 0#64 + st'.getD i 0#64) =
      [st.getD 0 0#64 + st'.getD 0 0#64,
       st.getD 1 0#64 + st'.getD 1 0#64,
       st.getD 2 0#64 + st'.getD 2 0#64,
       st.getD 3 0#64 + st'.getD 3 0#64,
       st.getD 4 0#64 + st'.getD 4 0#64,
       st.getD 5 0#64 + st'.getD 5 0#64,
       st.getD 6 0#64 + st'.getD 6 0#64,
       st.getD 7 0#64 + st'.getD 7 0#64] :=
  rfl

theorem sha512CompressBlock_eq_sha512AE (st : List (BitVec 64)) (block : List (BitVec 8))
    (hst : st.length = 8) :
    sha512CompressBlock st block =
      [st.getD 0 0#64 + sha512A st block 83,
       st.getD 1 0#64 + sha512A st block 82,
       st.getD 2 0#64 + sha512A st block 81,
       st.getD 3 0#64 + sha512A st block 80,
       st.getD 4 0#64 + sha512E st block 83,
       st.getD 5 0#64 + sha512E st block 82,
       st.getD 6 0#64 + sha512E st block 81,
       st.getD 7 0#64 + sha512E st block 80] := by
  rw [sha512CompressBlock_eq_rounds, map_range8_add64, sha512CompressRounds_eq_sha512AE st block hst 80]
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.reduceAdd]

/-! ## 3. Instruction-AST Step-Folding Lemmas (`ac_rfl`) -/

theorem sha512W_step1 (block : List (BitVec 8)) (i15 i16 i7 i2 i : Nat)
    (h16 : 16 ≤ i := by decide) (hi80 : i < 80 := by decide)
    (hi16 : i - 16 = i16 := by decide) (hi15 : i - 15 = i15 := by decide)
    (hi7 : i - 7 = i7 := by decide) (hi2 : i - 2 = i2 := by decide) :
    ((((BitVec.setWidth 64 ((sha512W block i15 ++ sha512W block i15) >>> 1) ^^^
        (sha512W block i15).rotateRight 8) ^^^ (sha512W block i15 >>> 7)) +
      sha512W block i16 + sha512W block i7) +
     (((BitVec.setWidth 64 ((sha512W block i2 ++ sha512W block i2) >>> 19) ^^^
        (sha512W block i2).rotateRight 61) ^^^ (sha512W block i2 >>> 6)))) =
      sha512W block i := by
  subst hi16 hi15 hi7 hi2
  rw [sha512SmallSigma0_eq, sha512SmallSigma1_eq, sha512W_ge_16 block i h16 hi80]
  bv64_add_ac

theorem sha512W_step2 (block : List (BitVec 8)) (i15 i16 i7 i2 i : Nat)
    (h16 : 16 ≤ i := by decide) (hi80 : i < 80 := by decide)
    (hi16 : i - 16 = i16 := by decide) (hi15 : i - 15 = i15 := by decide)
    (hi7 : i - 7 = i7 := by decide) (hi2 : i - 2 = i2 := by decide) :
    ((((BitVec.setWidth 64 ((sha512W block i15 ++ sha512W block i15) >>> 1) ^^^
        (sha512W block i15).rotateRight 8) ^^^ (sha512W block i15 >>> 7)) +
      (sha512W block i16 + sha512W block i7)) +
     (((BitVec.setWidth 64 ((sha512W block i2 ++ sha512W block i2) >>> 19) ^^^
        (sha512W block i2).rotateRight 61) ^^^ (sha512W block i2 >>> 6)))) =
      sha512W block i := by
  subst hi16 hi15 hi7 hi2
  rw [sha512SmallSigma0_eq, sha512SmallSigma1_eq, sha512W_ge_16 block i h16 hi80]
  bv64_add_ac

theorem sha512W_add_k (block : List (BitVec 8)) (k : BitVec 64) (i16 i15 i7 i2 i : Nat)
    (h16 : 16 ≤ i := by decide) (hi80 : i < 80 := by decide)
    (hi16 : i - 16 = i16 := by decide) (hi15 : i - 15 = i15 := by decide)
    (hi7 : i - 7 = i7 := by decide) (hi2 : i - 2 = i2 := by decide) :
    ((((sha512W block i16 + k) +
       ((BitVec.setWidth 64 ((sha512W block i15 ++ sha512W block i15) >>> 1) ^^^
         (sha512W block i15).rotateRight 8) ^^^ (sha512W block i15 >>> 7))) +
      sha512W block i7) +
     ((BitVec.setWidth 64 ((sha512W block i2 ++ sha512W block i2) >>> 19) ^^^
       (sha512W block i2).rotateRight 61) ^^^ (sha512W block i2 >>> 6))) =
      sha512W block i + k := by
  subst hi16 hi15 hi7 hi2
  rw [sha512SmallSigma0_eq, sha512SmallSigma1_eq, sha512W_ge_16 block i h16 hi80]
  bv64_add_ac

theorem sha512T2_eq (a b c : BitVec 64) :
    ((BitVec.setWidth 64 ((a ++ a) >>> 28) ^^^ a.rotateRight 34) ^^^ a.rotateRight 39) +
      ((a &&& (b ^^^ c)) ^^^ (b &&& c)) =
      sha512T2 a b c := by
  unfold sha512T2; rw [sha512BigSigma0_eq, sha512Maj_eq_and_xor]

theorem sha512T1_eq1 (e f g h k w : BitVec 64) :
    (((((e &&& f) + h) + (g &&& ~~~e)) + w) + k) +
      ((BitVec.setWidth 64 ((e ++ e) >>> 14) ^^^ e.rotateRight 18) ^^^ e.rotateRight 41) =
      sha512T1 e f g h k w := by
  unfold sha512T1; rw [sha512Ch_add_1, sha512BigSigma1_eq]; bv64_add_ac

theorem sha512T1_eq2 (e f g h k w : BitVec 64) :
    ((((k + w) + h) + (g &&& ~~~e)) + (e &&& f)) +
      ((BitVec.setWidth 64 ((e ++ e) >>> 14) ^^^ e.rotateRight 18) ^^^ e.rotateRight 41) =
      sha512T1 e f g h k w := by
  unfold sha512T1; rw [sha512Ch_add_2, sha512BigSigma1_eq]; bv64_add_ac

theorem sha512T1_eq3 (e f g h k w : BitVec 64) :
    (((h + (w + k)) + (g &&& ~~~e)) + (e &&& f)) +
      ((BitVec.setWidth 64 ((e ++ e) >>> 14) ^^^ e.rotateRight 18) ^^^ e.rotateRight 41) =
      sha512T1 e f g h k w := by
  unfold sha512T1; rw [sha512Ch_add_2, sha512BigSigma1_eq]; bv64_add_ac

theorem sha512T1_eq4 (e f g h k w : BitVec 64) :
    (((k + w) + h) + ((e &&& f) ||| (g &&& ~~~e))) +
      ((BitVec.setWidth 64 ((e ++ e) >>> 14) ^^^ e.rotateRight 18) ^^^ e.rotateRight 41) =
      sha512T1 e f g h k w := by
  unfold sha512T1; rw [sha512Ch_eq_orr_bic, sha512BigSigma1_eq]; bv64_add_ac

theorem sha512T1_eq5 (e f g h k w : BitVec 64) :
    (((w + (h + k)) + (g &&& ~~~e)) + (e &&& f)) +
      ((BitVec.setWidth 64 ((e ++ e) >>> 14) ^^^ e.rotateRight 18) ^^^ e.rotateRight 41) =
      sha512T1 e f g h k w := by
  unfold sha512T1; rw [sha512Ch_add_2, sha512BigSigma1_eq]; bv64_add_ac

theorem sha512T1_eq6 (e f g h k w : BitVec 64) :
    (((w + k) + h) + ((e &&& f) ||| (g &&& ~~~e))) +
      ((BitVec.setWidth 64 ((e ++ e) >>> 14) ^^^ e.rotateRight 18) ^^^ e.rotateRight 41) =
      sha512T1 e f g h k w := by
  unfold sha512T1; rw [sha512Ch_eq_orr_bic, sha512BigSigma1_eq]; bv64_add_ac

theorem sha512E_from_t1 (st : List (BitVec 64)) (block : List (BitVec 8))
    (i3 i2 i1 i i4 : Nat)
    (hi1 : i + 1 = i1 := by decide) (hi2 : i + 2 = i2 := by decide)
    (hi3 : i + 3 = i3 := by decide) (hi4 : i + 4 = i4 := by decide) :
    sha512T1 (sha512E st block i3) (sha512E st block i2) (sha512E st block i1)
      (sha512E st block i) (sha512K.getD i 0#64) (sha512W block i) +
      sha512A st block i =
      sha512E st block i4 := by
  subst hi1 hi2 hi3 hi4
  rw [sha512E_step]
  exact BitVec.add_comm _ _

theorem sha512A_from_t1_t2 (st : List (BitVec 64)) (block : List (BitVec 8))
    (i3 i2 i1 i i4 : Nat)
    (hi1 : i + 1 = i1 := by decide) (hi2 : i + 2 = i2 := by decide)
    (hi3 : i + 3 = i3 := by decide) (hi4 : i + 4 = i4 := by decide) :
    sha512T2 (sha512A st block i3) (sha512A st block i2) (sha512A st block i1) +
      sha512T1 (sha512E st block i3) (sha512E st block i2) (sha512E st block i1)
        (sha512E st block i) (sha512K.getD i 0#64) (sha512W block i) =
      sha512A st block i4 := by
  subst hi1 hi2 hi3 hi4
  rw [sha512A_step]
  exact BitVec.add_comm _ _

private theorem sha512Final0_gen (st : List (BitVec 64)) (block : List (BitVec 8))
    (i3 i2 i1 i i4 : Nat)
    (hi1 : i + 1 = i1 := by decide) (hi2 : i + 2 = i2 := by decide)
    (hi3 : i + 3 = i3 := by decide) (hi4 : i + 4 = i4 := by decide) :
    ((((sha512A st block i3 &&& (sha512A st block i2 ^^^ sha512A st block i1)) ^^^
        (sha512A st block i2 &&& sha512A st block i1)) + st.getD 0 0#64) +
      ((BitVec.setWidth 64 ((sha512A st block i3 ++ sha512A st block i3) >>> 28) ^^^
        (sha512A st block i3).rotateRight 34) ^^^ (sha512A st block i3).rotateRight 39)) +
      sha512T1 (sha512E st block i3) (sha512E st block i2) (sha512E st block i1)
        (sha512E st block i) (sha512K.getD i 0#64) (sha512W block i) =
      st.getD 0 0#64 + sha512A st block i4 := by
  subst hi1 hi2 hi3 hi4
  rw [sha512Maj_eq_and_xor, sha512BigSigma0_eq, sha512A_step]
  unfold sha512T2; bv64_add_ac

theorem sha512Final0 (st : List (BitVec 64)) (block : List (BitVec 8)) :
    ((((sha512A st block 82 &&& (sha512A st block 81 ^^^ sha512A st block 80)) ^^^
        (sha512A st block 81 &&& sha512A st block 80)) + st.getD 0 0#64) +
      ((BitVec.setWidth 64 ((sha512A st block 82 ++ sha512A st block 82) >>> 28) ^^^
        (sha512A st block 82).rotateRight 34) ^^^ (sha512A st block 82).rotateRight 39)) +
      sha512T1 (sha512E st block 82) (sha512E st block 81) (sha512E st block 80)
        (sha512E st block 79) (sha512K.getD 79 0#64) (sha512W block 79) =
      st.getD 0 0#64 + sha512A st block 83 :=
  sha512Final0_gen st block 82 81 80 79 83

private theorem sha512Final4_gen (st : List (BitVec 64)) (block : List (BitVec 8))
    (i3 i2 i1 i i4 : Nat)
    (hi1 : i + 1 = i1 := by decide) (hi2 : i + 2 = i2 := by decide)
    (hi3 : i + 3 = i3 := by decide) (hi4 : i + 4 = i4 := by decide) :
    (sha512A st block i + st.getD 4 0#64) +
      sha512T1 (sha512E st block i3) (sha512E st block i2) (sha512E st block i1)
        (sha512E st block i) (sha512K.getD i 0#64) (sha512W block i) =
      st.getD 4 0#64 + sha512E st block i4 := by
  subst hi1 hi2 hi3 hi4
  rw [sha512E_step]; bv64_add_ac

theorem sha512Final4 (st : List (BitVec 64)) (block : List (BitVec 8)) :
    (sha512A st block 79 + st.getD 4 0#64) +
      sha512T1 (sha512E st block 82) (sha512E st block 81) (sha512E st block 80)
        (sha512E st block 79) (sha512K.getD 79 0#64) (sha512W block 79) =
      st.getD 4 0#64 + sha512E st block 83 :=
  sha512Final4_gen st block 82 81 80 79 83

attribute [local irreducible] sha512T1 sha512T2

end LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512RoundDefs
