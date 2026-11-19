/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec -- proof-setup: allow-public-import

/-!
# SHAKE-128 XOF Stream Prefix, Uniqueness, and Multi-Lane Fuel Lemmas (`SampleNttLoop.XofDeterminism`)

SHAKE-128 XOF stream, sponge absorb/squeeze (`rateLanes = 21`, `168 = 24 × 7` bytes),
first-256 candidate uniqueness (`shake128FirstBlocks_take256_unique`), and multi-lane finite-fuel
termination witnesses (`multiLaneMaxExtra`) for `B03`–`B07`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.XofDeterminism

open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  KeccakState
  Poly
  keccakAbsorb
  keccakAbsorbBlock
  keccakExtractRate
  keccakF1600
  keccakPadBlocks
  keccakPermuteN
  keccakSqueezeBlocks
  keccakZeroState
  packLane64
  parseRej12Candidates
  sampleNttBounded
  shake128BlockAt
  shake128FirstBlocks
  Shake128SeedTerminates
  unpackLane64
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (
  keccakLastBlock
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.PureSpec (
  extra_lt_of_lt256
  parseRej12Candidates_shake128_mono
  parseRej12Candidates_shake128_prefix
  sampleNttAt
  sampleNttAt_unique
  sampleNttBounded_eq_some_of_ge256
  sampleNttClassical
  sampleNttClassical_eq_sampleNttAt
  shake128BlockAt_length
  shake128FirstBlocks_length
  shake128FirstBlocks_succ
)

/-! ## 1. SHAKE-128 Block Prefix & Byte-Length Divisibility (`168 = 24 × 7`) -/

theorem shake128BlockAt_length_eq_24_mul_7 (seed34 : List (BitVec 8)) (blkIdx : Nat) :
    (shake128BlockAt seed34 blkIdx).length = 24 * 7 := by
  rw [shake128BlockAt_length]

theorem shake128FirstBlocks_length_eq_24_mul (seed34 : List (BitVec 8)) (m : Nat) :
    (shake128FirstBlocks seed34 m).length = 24 * (7 * m) := by
  rw [shake128FirstBlocks_length]
  omega

theorem shake128FirstBlocks_length_mod3 (seed34 : List (BitVec 8)) (m : Nat) :
    (shake128FirstBlocks seed34 m).length % 3 = 0 := by
  rw [shake128FirstBlocks_length]
  omega

theorem shake128FirstBlocks_length_mod24 (seed34 : List (BitVec 8)) (m : Nat) :
    (shake128FirstBlocks seed34 m).length % 24 = 0 := by
  rw [shake128FirstBlocks_length]
  omega

/-- Decompose `shake128FirstBlocks seed34 (m + k)` into `shake128FirstBlocks seed34 m` followed by
    blocks `m .. m + k - 1`. -/
theorem shake128FirstBlocks_append_range (seed34 : List (BitVec 8)) (m : Nat) :
    ∀ k : Nat,
      shake128FirstBlocks seed34 (m + k) =
        shake128FirstBlocks seed34 m ++
          ((List.range k).map fun i => shake128BlockAt seed34 (m + i)).flatten
  | 0 => by simp
  | k + 1 => by
    rw [← Nat.add_assoc, shake128FirstBlocks_succ, shake128FirstBlocks_append_range seed34 m k,
        List.range_succ, List.map_append, List.map_singleton, List.flatten_append]
    simp [List.append_assoc]

/-- `shake128FirstBlocks seed34 m` is a prefix of `shake128FirstBlocks seed34 M` whenever `m ≤ M`. -/
theorem shake128FirstBlocks_isPrefix {seed34 : List (BitVec 8)} {m M : Nat} (h : m ≤ M) :
    shake128FirstBlocks seed34 m <+: shake128FirstBlocks seed34 M := by
  refine ⟨((List.range (M - m)).map fun i => shake128BlockAt seed34 (m + i)).flatten, ?_⟩
  have h1 := shake128FirstBlocks_append_range seed34 m (M - m)
  rw [Nat.add_sub_of_le h] at h1
  exact h1.symm

/-- Taking the first `168 * m` bytes of `shake128FirstBlocks seed34 M` (`m ≤ M`) recovers
    `shake128FirstBlocks seed34 m`. -/
theorem shake128FirstBlocks_take {seed34 : List (BitVec 8)} {m M : Nat} (h : m ≤ M) :
    (shake128FirstBlocks seed34 M).take (168 * m) = shake128FirstBlocks seed34 m := by
  rcases shake128FirstBlocks_isPrefix (seed34 := seed34) h with ⟨rest, hrest⟩
  rw [← hrest, ← shake128FirstBlocks_length seed34 m, List.take_left]

/-! ## 2. First-256 Accepted Candidate Uniqueness (`shake128FirstBlocks_take256_unique`) -/

/-- For any two block counts `m1, m2` that each yield `≥ 256` accepted candidates `< 3329`,
    their first `256` accepted candidates are identical. -/
theorem shake128FirstBlocks_take256_unique_blocks {seed34 : List (BitVec 8)} {m1 m2 : Nat}
    (h1 : 256 ≤ (parseRej12Candidates (shake128FirstBlocks seed34 m1)).length)
    (h2 : 256 ≤ (parseRej12Candidates (shake128FirstBlocks seed34 m2)).length) :
    (parseRej12Candidates (shake128FirstBlocks seed34 m1)).take 256 =
      (parseRej12Candidates (shake128FirstBlocks seed34 m2)).take 256 := by
  by_cases hle : m1 ≤ m2
  · rcases parseRej12Candidates_shake128_prefix (seed34 := seed34) hle with ⟨rest, hrest⟩
    rw [hrest, List.take_append_of_le_length h1]
  · have hle' : m2 ≤ m1 := by omega
    rcases parseRej12Candidates_shake128_prefix (seed34 := seed34) hle' with ⟨rest, hrest⟩
    rw [hrest, List.take_append_of_le_length h2]

/-- Any two extra-block witnesses `e1, e2` reaching `≥ 256` accepted candidates after `e + 3`
    SHAKE-128 blocks produce the exact same 256-element candidate list. -/
theorem shake128FirstBlocks_take256_unique {seed34 : List (BitVec 8)} {e1 e2 : Nat}
    (h1 : 256 ≤ (parseRej12Candidates (shake128FirstBlocks seed34 (e1 + 3))).length)
    (h2 : 256 ≤ (parseRej12Candidates (shake128FirstBlocks seed34 (e2 + 3))).length) :
    (parseRej12Candidates (shake128FirstBlocks seed34 (e1 + 3))).take 256 =
      (parseRej12Candidates (shake128FirstBlocks seed34 (e2 + 3))).take 256 := by
  have heq := congrArg Array.toList (sampleNttAt_unique h1 h2)
  simpa [sampleNttAt] using heq

/-- Array form of `shake128FirstBlocks_take256_unique` bridging directly to `sampleNttClassical`. -/
theorem shake128FirstBlocks_take256_toArray_eq_classical {seed34 : List (BitVec 8)} {extra : Nat}
    (hge : 256 ≤ (parseRej12Candidates (shake128FirstBlocks seed34 (extra + 3))).length) :
    ((parseRej12Candidates (shake128FirstBlocks seed34 (extra + 3))).take 256).toArray =
      sampleNttClassical seed34 :=
  (sampleNttClassical_eq_sampleNttAt hge).symm

/-! ## 3. Rate-21 (`168`-Byte) SHAKE-128 Sponge Absorb & Squeeze Characterizations -/

/-- XOR a 168-byte (`21`-lane) block into lanes `0..20` of `s` without permuting (`B03`–`B07`). -/
@[expose] def keccakXorRate21 (s : KeccakState) (blk : List (BitVec 8)) : KeccakState :=
  Array.ofFn (n := 25) fun ⟨idx, _⟩ =>
    if idx < 21 then s.getD idx 0#64 ^^^ packLane64 blk (8 * idx)
    else s.getD idx 0#64

@[simp] theorem keccakXorRate21_size (s : KeccakState) (blk : List (BitVec 8)) :
    (keccakXorRate21 s blk).size = 25 := by
  simp [keccakXorRate21]

theorem keccakXorRate21_getD_lt (s : KeccakState) (blk : List (BitVec 8)) {idx : Nat}
    (h : idx < 21) :
    (keccakXorRate21 s blk).getD idx 0#64 = s.getD idx 0#64 ^^^ packLane64 blk (8 * idx) := by
  have h25 : idx < 25 := by omega
  simp [keccakXorRate21, Array.getD, h25, h]

theorem keccakXorRate21_getD_ge (s : KeccakState) (blk : List (BitVec 8)) {idx : Nat}
    (h21 : 21 ≤ idx) (hs : s.size ≤ 25) :
    (keccakXorRate21 s blk).getD idx 0#64 = s.getD idx 0#64 := by
  by_cases h25 : idx < 25
  · have hnot : ¬(idx < 21) := by omega
    simp [keccakXorRate21, Array.getD, h25, hnot]
  · have hnot_s : ¬(idx < s.size) := by omega
    simp [keccakXorRate21, Array.getD, h25, hnot_s]

theorem keccakAbsorbBlock_21 (s : KeccakState) (blk : List (BitVec 8)) :
    keccakAbsorbBlock 21 s blk = keccakF1600 (keccakXorRate21 s blk) := rfl

/-- Single-block SHAKE-128 absorb characterization for messages `< 168` bytes (including 34-byte
    matrix XOF seeds `ρ ‖ [i, j]`). -/
theorem keccakAbsorb_21_lt168 (dsByte : BitVec 8) (msg : List (BitVec 8)) (h : msg.length < 168) :
    keccakAbsorb 21 dsByte msg =
      keccakF1600 (keccakXorRate21 keccakZeroState (keccakLastBlock 168 dsByte msg)) := by
  unfold keccakAbsorb keccakPadBlocks
  have hdiv : msg.length / (8 * 21) = 0 := Nat.div_eq_of_lt h
  change (((List.range (msg.length / 168)).map fun i => (msg.drop (i * 168)).take 168) ++
      [keccakLastBlock 168 dsByte msg]).foldl (keccakAbsorbBlock 21) keccakZeroState = _
  rw [show msg.length / 168 = 0 from hdiv, List.range_zero, List.map_nil, List.nil_append,
      List.foldl_cons, List.foldl_nil, keccakAbsorbBlock_21]

/-- Explicit 21-lane (`168`-byte) expansion of `keccakExtractRate 21 s`. -/
theorem keccakExtractRate_21_eq_lanes (s : KeccakState) :
    keccakExtractRate 21 s =
      unpackLane64 (s.getD 0 0#64) ++ unpackLane64 (s.getD 1 0#64) ++
        unpackLane64 (s.getD 2 0#64) ++ unpackLane64 (s.getD 3 0#64) ++
        unpackLane64 (s.getD 4 0#64) ++ unpackLane64 (s.getD 5 0#64) ++
        unpackLane64 (s.getD 6 0#64) ++ unpackLane64 (s.getD 7 0#64) ++
        unpackLane64 (s.getD 8 0#64) ++ unpackLane64 (s.getD 9 0#64) ++
        unpackLane64 (s.getD 10 0#64) ++ unpackLane64 (s.getD 11 0#64) ++
        unpackLane64 (s.getD 12 0#64) ++ unpackLane64 (s.getD 13 0#64) ++
        unpackLane64 (s.getD 14 0#64) ++ unpackLane64 (s.getD 15 0#64) ++
        unpackLane64 (s.getD 16 0#64) ++ unpackLane64 (s.getD 17 0#64) ++
        unpackLane64 (s.getD 18 0#64) ++ unpackLane64 (s.getD 19 0#64) ++
        unpackLane64 (s.getD 20 0#64) := by
  unfold keccakExtractRate
  have hr21 : List.range 21 =
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] := by decide
  rw [hr21]
  simp [List.append_assoc]

/-- `shake128FirstBlocks seed34 n` unfolds directly to `keccakSqueezeBlocks 21 n`. -/
theorem shake128FirstBlocks_eq_squeeze (seed34 : List (BitVec 8)) (n : Nat) :
    shake128FirstBlocks seed34 n =
      keccakSqueezeBlocks 21 n (keccakAbsorb 21 0x1f#8 seed34) := rfl

/-! ## 4. Multi-Lane Finite-Fuel Witness (`maxOverLanes`, `multiLaneMaxExtra`) & `sampleNttBounded` -/

/-- Constructive maximum of `f lane hlt` across `lane ∈ {0, ..., N - 1}` (`0` when `N = 0`). -/
@[expose] def maxOverLanes : (N : Nat) → (∀ lane, lane < N → Nat) → Nat
  | 0, _ => 0
  | n + 1, f =>
    Nat.max (maxOverLanes n (fun lane hlt => f lane (Nat.lt_succ_of_lt hlt)))
      (f n (Nat.lt_succ_self n))

theorem le_maxOverLanes :
    ∀ {N : Nat} (f : ∀ lane, lane < N → Nat) {lane : Nat} (hlt : lane < N),
      f lane hlt ≤ maxOverLanes N f
  | 0, _, _, hlt => absurd hlt (Nat.not_lt_zero _)
  | n + 1, f, lane, hlt => by
    simp only [maxOverLanes]
    by_cases heq : lane = n
    · subst heq
      exact Nat.le_max_right _ _
    · have hlt' : lane < n := by omega
      exact Nat.le_trans (le_maxOverLanes (fun i hi => f i (Nat.lt_succ_of_lt hi)) hlt')
        (Nat.le_max_left _ _)

/-- Finite upper bound on the extra SHAKE-128 blocks needed for all `N` lanes simultaneously
    to reach `≥ 256` accepted candidates under `∀ lane < N, Shake128SeedTerminates (seeds lane)`. -/
@[expose] noncomputable def multiLaneMaxExtra (N : Nat) (seeds : Nat → List (BitVec 8))
    (hTerm : ∀ lane, lane < N → Shake128SeedTerminates (seeds lane)) : Nat :=
  maxOverLanes N (fun lane hlt => Classical.choose (hTerm lane hlt))

theorem choose_le_multiLaneMaxExtra {N : Nat} {seeds : Nat → List (BitVec 8)}
    (hTerm : ∀ lane, lane < N → Shake128SeedTerminates (seeds lane))
    {lane : Nat} (hlt : lane < N) :
    Classical.choose (hTerm lane hlt) ≤ multiLaneMaxExtra N seeds hTerm :=
  le_maxOverLanes (fun i hi => Classical.choose (hTerm i hi)) hlt

/-- At `extra = multiLaneMaxExtra N seeds hTerm` (or any `fuel ≥ multiLaneMaxExtra`), every lane
    `lane < N` has accumulated `≥ 256` accepted 12-bit candidates `< 3329`. -/
theorem multiLaneMaxExtra_ge256 {N : Nat} {seeds : Nat → List (BitVec 8)}
    (hTerm : ∀ lane, lane < N → Shake128SeedTerminates (seeds lane))
    {fuel : Nat} (hfuel : multiLaneMaxExtra N seeds hTerm ≤ fuel)
    {lane : Nat} (hlt : lane < N) :
    256 ≤ (parseRej12Candidates (shake128FirstBlocks (seeds lane) (fuel + 3))).length := by
  have hwit := Classical.choose_spec (hTerm lane hlt)
  have hle : Classical.choose (hTerm lane hlt) + 3 ≤ fuel + 3 := by
    have h1 := choose_le_multiLaneMaxExtra hTerm hlt
    omega
  exact Nat.le_trans hwit (parseRej12Candidates_shake128_mono hle)

/-- Whenever some lane `lane < N` still has `< 256` accepted candidates after `extra + 3` blocks,
    `extra` is strictly below `multiLaneMaxExtra N seeds hTerm` (guaranteeing positive remaining
    fuel `multiLaneMaxExtra - extra > 0` for the loop back-edge). -/
theorem multiLane_extra_lt_maxExtra {N : Nat} {seeds : Nat → List (BitVec 8)}
    (hTerm : ∀ lane, lane < N → Shake128SeedTerminates (seeds lane))
    {extra lane : Nat} (hlt : lane < N)
    (hcands : (parseRej12Candidates (shake128FirstBlocks (seeds lane) (extra + 3))).length < 256) :
    extra < multiLaneMaxExtra N seeds hTerm := by
  have hwit := Classical.choose_spec (hTerm lane hlt)
  have hlt_wit := extra_lt_of_lt256 hcands hwit
  have hle_max := choose_le_multiLaneMaxExtra hTerm hlt
  omega

/-- With fuel `fuel ≥ multiLaneMaxExtra N seeds hTerm`, `sampleNttBounded fuel (seeds lane)`
    evaluates to `some (sampleNttClassical (seeds lane))` simultaneously for every `lane < N`. -/
theorem multiLaneMaxExtra_sampleNttBounded {N : Nat} {seeds : Nat → List (BitVec 8)}
    (hTerm : ∀ lane, lane < N → Shake128SeedTerminates (seeds lane))
    {fuel : Nat} (hfuel : multiLaneMaxExtra N seeds hTerm ≤ fuel)
    {lane : Nat} (hlt : lane < N) :
    sampleNttBounded fuel (seeds lane) = some (sampleNttClassical (seeds lane)) := by
  have hge := multiLaneMaxExtra_ge256 hTerm (Nat.le_refl _) hlt
  rw [sampleNttBounded_eq_some_of_ge256 hfuel hge, sampleNttClassical_eq_sampleNttAt hge]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.XofDeterminism
