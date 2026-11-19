/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp -- proof-setup: allow-public-import

/-!
# Keccak-f[1600] round characterization and 24-round countdown

Round-level definitions and lemmas shared across the inlined NEON Keccak proofs:
- Per-step 64-bit lane projections `keccakC`, `keccakD`, `keccakTheta`, `keccakRhoPi`, and
  `keccakRoundLane`, proved equal to `(keccakF1600Round s rc).getD idx 0#64` (`idx < 25`).
- Bitwise XOR, rotation, and `chi` normalization helpers (`rotateLeft_xor`, `keccakChi_eq`,
  `keccakChi0_eq`) matching LLVM's NEON `EOR` + `BIC` + `LD1R` instruction order.
- Tail-recursive 24-round countdown `keccakRunFrom r s` connecting round `r → r + 1` with
  `RoTables.keccakRcAt r` (`r < 24`) to `Spec.keccakF1600 s`.
- `SepWP` step macros (`wp_simd_ld1_d`, `wp_simd_ld2_2d`, `wp_simd_ld1r_2d`) for the three
  `SimdSteps` instructions used across `Keccak/`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (keccakRcAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps (
  step_simdLd1Single64
  step_simdLd2_2d
  step_simdLd1r_2d
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  KeccakState
  keccakF1600
  keccakF1600Round
  keccakRhoOffset
  keccakRoundConstants
  laneGet
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs (
  keccak2Lane
  keccakRcAt_eq
)

/-! ## `SimdSteps` step macros -/

/-- Step `LD1 {Vt.D}[1], [Xn]` via `SimdSteps.step_simdLd1Single64`. -/
macro "wp_simd_ld1_d" : tactic => `(tactic| (
  apply step_simdLd1Single64
  · wp_norm_lhs
  · wp_norm_lhs
  · wp_norm_lhs
  · first | wp_norm_lhs | wp_norm_goal
  · wp_norm_lhs
  · wp_sep_access
  · wp_norm_lhs))

/-- Step `LD2 {Vt.2D, Vt+1.2D}, [Xn]` via `SimdSteps.step_simdLd2_2d`. -/
macro "wp_simd_ld2_2d" : tactic => `(tactic| (
  apply step_simdLd2_2d
  · wp_norm_lhs
  · wp_norm_lhs
  · wp_norm_lhs
  · first | wp_norm_lhs | wp_norm_goal
  · wp_norm_lhs
  · wp_norm_lhs
  · wp_norm_lhs
  · wp_norm_lhs
  · wp_sep_access
  · wp_sep_access
  · wp_sep_access
  · wp_sep_access
  · wp_norm_lhs))

/-- Step `LD1R {Vt.2D}, [Xn]` via `SimdSteps.step_simdLd1r_2d`. -/
macro "wp_simd_ld1r_2d" : tactic => `(tactic| (
  apply step_simdLd1r_2d
  · wp_norm_lhs
  · wp_norm_lhs
  · wp_norm_lhs
  · first | wp_norm_lhs | wp_norm_goal
  · wp_norm_lhs
  · wp_sep_access
  · wp_norm_lhs))

/-! ## Per-step `keccakF1600Round` lane projections -/

/-- Column parity `C[x] = A[x,0] ^ A[x,1] ^ A[x,2] ^ A[x,3] ^ A[x,4]` (`x < 5`). -/
@[expose] def keccakC (s : KeccakState) (x : Nat) : BitVec 64 :=
  s.getD x 0#64 ^^^ s.getD (5 + x) 0#64 ^^^ s.getD (10 + x) 0#64 ^^^
    s.getD (15 + x) 0#64 ^^^ s.getD (20 + x) 0#64

/-- Theta column effect `D[x] = C[(x + 4) % 5] ^ rotl(C[(x + 1) % 5], 1)` (`x < 5`). -/
@[expose] def keccakD (s : KeccakState) (x : Nat) : BitVec 64 :=
  keccakC s ((x + 4) % 5) ^^^ (keccakC s ((x + 1) % 5)).rotateLeft 1

/-- Post-theta lane `A'[idx] = A[idx] ^ D[idx % 5]` (`idx < 25`). -/
@[expose] def keccakTheta (s : KeccakState) (idx : Nat) : BitVec 64 :=
  s.getD idx 0#64 ^^^ keccakD s (idx % 5)

/-- Source lane index `5 * y + x` in `A'` feeding `B[idx]` under `ρ` and `π`. -/
@[expose] def keccakRhoPiSrc (idx : Nat) : Nat :=
  let x' := idx % 5
  let y' := idx / 5
  5 * x' + (x' + 3 * y') % 5

/-- Post-`ρ`/`π` lane `B[idx]` (`idx < 25`). -/
@[expose] def keccakRhoPi (s : KeccakState) (idx : Nat) : BitVec 64 :=
  let src := keccakRhoPiSrc idx
  (keccakTheta s src).rotateLeft (keccakRhoOffset src)

/-- Post-`χ`/`ι` output lane `(keccakF1600Round s rc)[idx]` (`idx < 25`). -/
@[expose] def keccakRoundLane (s : KeccakState) (rc : BitVec 64) (idx : Nat) : BitVec 64 :=
  let x := idx % 5
  let y := idx / 5
  let chi := keccakRhoPi s (5 * y + x) ^^^
    ((~~~(keccakRhoPi s (5 * y + (x + 1) % 5))) &&& keccakRhoPi s (5 * y + (x + 2) % 5))
  if idx == 0 then chi ^^^ rc else chi

theorem keccakF1600Round_size (s : KeccakState) (rc : BitVec 64) :
    (keccakF1600Round s rc).size = 25 := by
  simp [keccakF1600Round]

theorem keccakF1600_size (s : KeccakState) :
    (keccakF1600 s).size = 25 := by
  unfold keccakF1600 keccakRoundConstants
  simp only [List.foldl_cons, List.foldl_nil, keccakF1600Round_size]

private theorem getD_ofFn {n : Nat} (f : Fin n → BitVec 64) {i : Nat} (hi : i < n) :
    (Array.ofFn f).getD i 0#64 = f ⟨i, hi⟩ := by
  simp [Array.getD_eq_getD_getElem?, hi]

theorem keccakF1600Round_getD (s : KeccakState) (rc : BitVec 64) {idx : Nat} (h : idx < 25) :
    (keccakF1600Round s rc).getD idx 0#64 = keccakRoundLane s rc idx := by
  let c : Array (BitVec 64) := Array.ofFn (n := 5) fun ⟨x, _⟩ =>
    laneGet s x 0 ^^^ laneGet s x 1 ^^^ laneGet s x 2 ^^^ laneGet s x 3 ^^^ laneGet s x 4
  let d : Array (BitVec 64) := Array.ofFn (n := 5) fun ⟨x, _⟩ =>
    c.getD ((x + 4) % 5) 0#64 ^^^ (c.getD ((x + 1) % 5) 0#64).rotateLeft 1
  let aTheta : KeccakState := Array.ofFn (n := 25) fun ⟨k, _⟩ =>
    laneGet s (k % 5) (k / 5) ^^^ d.getD (k % 5) 0#64
  let bRhoPi : KeccakState := Array.ofFn (n := 25) fun ⟨k, _⟩ =>
    let x' := k % 5
    let y' := k / 5
    let x := (x' + 3 * y') % 5
    let y := x'
    (laneGet aTheta x y).rotateLeft (keccakRhoOffset (5 * y + x))
  have hc (x : Nat) (hx : x < 5) : c.getD x 0#64 = keccakC s x := by
    dsimp only [c]
    rw [getD_ofFn _ hx]
    simp only [keccakC, laneGet, Nat.mul_zero, Nat.zero_add, Nat.mul_one]
  have hd (x : Nat) (hx : x < 5) : d.getD x 0#64 = keccakD s x := by
    dsimp only [d]
    rw [getD_ofFn _ hx,
        hc ((x + 4) % 5) (Nat.mod_lt _ (by decide)),
        hc ((x + 1) % 5) (Nat.mod_lt _ (by decide))]
    rfl
  have ha (k : Nat) (hk : k < 25) : aTheta.getD k 0#64 = keccakTheta s k := by
    dsimp only [aTheta]
    rw [getD_ofFn _ hk]
    simp only [keccakTheta, laneGet, Nat.div_add_mod k 5, hd (k % 5) (Nat.mod_lt _ (by decide))]
  have hb (k : Nat) (hk : k < 25) : bRhoPi.getD k 0#64 = keccakRhoPi s k := by
    have hsrc : keccakRhoPiSrc k < 25 := by dsimp only [keccakRhoPiSrc]; omega
    dsimp only [bRhoPi]
    rw [getD_ofFn _ hk]
    simp only [keccakRhoPi, keccakRhoPiSrc, laneGet]
    rw [ha (5 * (k % 5) + (k % 5 + 3 * (k / 5)) % 5) hsrc]
  change (Array.ofFn (n := 25) fun ⟨k, _⟩ =>
    let x := k % 5
    let y := k / 5
    let chi := laneGet bRhoPi x y ^^^
      ((~~~(laneGet bRhoPi ((x + 1) % 5) y)) &&& laneGet bRhoPi ((x + 2) % 5) y)
    if k == 0 then chi ^^^ rc else chi).getD idx 0#64 = keccakRoundLane s rc idx
  rw [getD_ofFn _ h]
  simp only [keccakRoundLane, laneGet,
    hb (5 * (idx / 5) + idx % 5) (by omega),
    hb (5 * (idx / 5) + (idx % 5 + 1) % 5) (by omega),
    hb (5 * (idx / 5) + (idx % 5 + 2) % 5) (by omega)]

/-! ## Bitwise XOR, rotation, and `chi` normalization helpers -/

theorem rotateLeft_xor (a b : BitVec 64) (n : Nat) :
    (a ^^^ b).rotateLeft n = a.rotateLeft n ^^^ b.rotateLeft n := by
  ext i hi
  by_cases hlt : i < n % 64 <;> simp [BitVec.getElem_rotateLeft, BitVec.getElem_xor, hlt]

theorem rotateLeft_zero_64 (a : BitVec 64) :
    a.rotateLeft 0 = a := by
  ext i hi
  simp [BitVec.getElem_rotateLeft]

/-- Match LLVM's `BIC vTmp, b2, b1; EOR vOut, vTmp, b0` (`(b2 &&& ~~~b1) ^^^ b0`) with FIPS 202 `chi`. -/
theorem keccakChi_eq (b0 b1 b2 : BitVec 64) :
    (b2 &&& ~~~b1) ^^^ b0 = b0 ^^^ (~~~b1 &&& b2) := by
  rw [BitVec.and_comm, BitVec.xor_comm]

/-- Match LLVM's lane-0 `EOR v0, vRc, b0; BIC v1, b2, b1; EOR vOut, v1, v0` with FIPS 202 `chi ^ rc`. -/
theorem keccakChi0_eq (b0 b1 b2 rc : BitVec 64) :
    (b2 &&& ~~~b1) ^^^ (rc ^^^ b0) = (b0 ^^^ (~~~b1 &&& b2)) ^^^ rc := by
  ext i hi
  simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not]
  cases b0[i] <;> cases b1[i] <;> cases b2[i] <;> cases rc[i] <;> rfl

/-- Two `KeccakState`s of size `25` are equal iff all 25 lanes (`0..24`) agree via `getD · 0#64`. -/
theorem keccakState_eq_of_getD {s t : KeccakState} (hs : s.size = 25) (ht : t.size = 25)
    (h : ∀ idx, idx < 25 → s.getD idx 0#64 = t.getD idx 0#64) : s = t := by
  apply Array.ext (hs.trans ht.symm)
  intro i hi1 hi2
  have hi : i < 25 := hs ▸ hi1
  have := h i hi
  simpa [Array.getD, hi1, hi2] using this

/-! ## Tail-recursive 24-round countdown `keccakRunFrom` -/

/-- Run rounds `r .. 23` of `Keccak-f[1600]` starting from state `s`. -/
@[expose] def keccakRunFrom (r : Nat) (s : KeccakState) : KeccakState :=
  (keccakRoundConstants.drop r).foldl keccakF1600Round s

theorem keccakRunFrom_zero (s : KeccakState) :
    keccakRunFrom 0 s = keccakF1600 s := rfl

theorem keccakRunFrom_24 (s : KeccakState) :
    keccakRunFrom 24 s = s := by
  unfold keccakRunFrom
  have hlen : keccakRoundConstants.length = 24 := rfl
  rw [← hlen, List.drop_length, List.foldl_nil]

theorem keccakRunFrom_step (r : Nat) (hr : r < 24) (s : KeccakState) :
    keccakRunFrom r s = keccakRunFrom (r + 1) (keccakF1600Round s (keccakRcAt r)) := by
  unfold keccakRunFrom
  have hlen : r < keccakRoundConstants.length := hr
  have hdrop : keccakRoundConstants.drop r =
      keccakRoundConstants.getD r 0#64 :: keccakRoundConstants.drop (r + 1) :=
    List.drop_eq_getD_cons keccakRoundConstants r 0#64 hlen
  rw [hdrop, List.foldl_cons, keccakRcAt_eq r hr]

theorem keccakRunFrom_size (r : Nat) (s : KeccakState) (hs : s.size = 25) :
    (keccakRunFrom r s).size = 25 := by
  unfold keccakRunFrom
  suffices ∀ (rcs : List (BitVec 64)) (s : KeccakState),
      s.size = 25 → (rcs.foldl keccakF1600Round s).size = 25 from this _ s hs
  intro rcs
  induction rcs with
  | nil => intro s hs; exact hs
  | cons rc rest ih =>
    intro s _
    rw [List.foldl_cons]
    exact ih (keccakF1600Round s rc) (keccakF1600Round_size s rc)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round
