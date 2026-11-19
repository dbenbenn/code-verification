/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.KEM.MlKem
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKeccak -- proof-setup: allow-public-import

/-!
# Linear-Time Forced-`Poly` Kyber / ML-KEM Definitions and Soundness Lemmas

Provides linear-time (`O(N)`) forced-`Poly` polynomial arithmetic (`polyNttFast`, `polyInvNttFast`,
`polyNttMulFast`, `byteEncodeFast`, `byteDecodeRawFast`, `samplePolyCbd2Fast`, `sampleNttFast`,
`sampleMatrixCheckedFast`, `checkMatrixRowFast`) using exposed `List`/`Array.mk` primitives for
low-memory Lean kernel (`rfl_kernel`) evaluation without compiler trust.
-/

namespace Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberDefs

open CryptoGames.MLKEM (
  Poly Shake128SeedTerminates bitRev7 bitsToBytes byteDecodeMod byteDecodeRaw byteEncode
  bytesToBits compressAndEncode compressCoeff decodeAndDecompress decompressCoeff fipsZetas
  indCpaDecrypt indCpaEncryptWith invNttStage kyber1024Decaps kyber1024DecapsWith kyber1024Encaps
  kyber1024EncapsWith mlkemQ nttStage parseRej12Candidates polyAdd polyInvNtt polyNtt polyNttMul
  polySub sampleMatrixWith sampleNtt samplePolyCbd2 sampleVecCbd2 shake128FirstBlocks toByteVec
  vecDotNtt zeroPoly
)
open CryptoGames.SHA3 (
  KeccakState keccakAbsorb keccakExtractRate keccakF1600 keccakSqueezeBlocks sha3_256List
  sha3_512List
)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKeccak (
  arrayGetDFast arrayGetDFast_eq arrayMapFast arrayMapFast_eq arrayOfFnFast arrayOfFnFast_eq
  arraySetFast arraySetFast_eq forceArrayBV64 forceArrayBV64_eq forceListBV8 forceListBV8_eq
  forceListNat forceListNat_eq keccakAbsorbFast keccakAbsorbFast_eq keccakExtractRateFast
  keccakF1600Fast keccakSqueezeBlocksFast keccakSqueezeBlocksFast_eq sha3_256Fast
  sha3_256Fast_eq sha3_512Fast sha3_512Fast_eq shake256Fast shake256Fast_eq withForcedNat
  withForcedNat_eq
)

public section
set_option autoImplicit false
set_option maxRecDepth 200000

private theorem list_getD_drop {α : Type} (xs : List α) (d i : Nat) (v : α) :
    (xs.drop d).getD i v = xs.getD (d + i) v := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-! ## 1. Continuation-Forcing Combinators for `Poly`, `Array Poly`, and `Array (Array Poly)` -/

@[expose] def forcePoly {α : Type} (p : Poly) (k : Poly → α) : α :=
  forceListNat p.toList fun xs => k (Array.mk xs)

theorem forcePoly_eq {α : Type} (p : Poly) (k : Poly → α) : forcePoly p k = k p := by
  rcases p with ⟨xs⟩
  exact forceListNat_eq xs (fun xs => k (Array.mk xs))

@[expose] def forcePolyListAux {α : Type} : List Poly → List Poly → (List Poly → α) → α
  | [], acc, k => k acc.reverse
  | p :: ps, acc, k => forcePoly p fun p' => forcePolyListAux ps (p' :: acc) k

@[expose] def forcePolyList {α : Type} (ps : List Poly) (k : List Poly → α) : α :=
  forcePolyListAux ps [] k

private theorem forcePolyListAux_eq {α : Type} :
    ∀ (ps acc : List Poly) (k : List Poly → α), forcePolyListAux ps acc k = k (acc.reverse ++ ps)
  | [], acc, k => by simp [forcePolyListAux]
  | p :: ps, acc, k => by
    simp only [forcePolyListAux, forcePoly_eq, forcePolyListAux_eq ps (p :: acc) k,
      List.reverse_cons, List.append_assoc, List.singleton_append]

theorem forcePolyList_eq {α : Type} (ps : List Poly) (k : List Poly → α) :
    forcePolyList ps k = k ps :=
  forcePolyListAux_eq ps [] k

@[expose] def forcePolyVec {α : Type} (v : Array Poly) (k : Array Poly → α) : α :=
  forcePolyList v.toList fun ps => k (Array.mk ps)

theorem forcePolyVec_eq {α : Type} (v : Array Poly) (k : Array Poly → α) :
    forcePolyVec v k = k v := by
  rcases v with ⟨ps⟩
  exact forcePolyList_eq ps (fun ps => k (Array.mk ps))

@[expose] def forcePolyMatListAux {α : Type} :
    List (Array Poly) → List (Array Poly) → (List (Array Poly) → α) → α
  | [], acc, k => k acc.reverse
  | row :: rows, acc, k =>
    forcePolyVec row fun row' => forcePolyMatListAux rows (row' :: acc) k

@[expose] def forcePolyMatList {α : Type} (rows : List (Array Poly))
    (k : List (Array Poly) → α) : α :=
  forcePolyMatListAux rows [] k

private theorem forcePolyMatListAux_eq {α : Type} :
    ∀ (rows acc : List (Array Poly)) (k : List (Array Poly) → α),
      forcePolyMatListAux rows acc k = k (acc.reverse ++ rows)
  | [], acc, k => by simp [forcePolyMatListAux]
  | row :: rows, acc, k => by
    simp only [forcePolyMatListAux, forcePolyVec_eq, forcePolyMatListAux_eq rows (row :: acc) k,
      List.reverse_cons, List.append_assoc, List.singleton_append]

theorem forcePolyMatList_eq {α : Type} (rows : List (Array Poly)) (k : List (Array Poly) → α) :
    forcePolyMatList rows k = k rows :=
  forcePolyMatListAux_eq rows [] k

@[expose] def forceMatrix {α : Type} (m : Array (Array Poly)) (k : Array (Array Poly) → α) : α :=
  forcePolyMatList m.toList fun rows => k (Array.mk rows)

theorem forceMatrix_eq {α : Type} (m : Array (Array Poly)) (k : Array (Array Poly) → α) :
    forceMatrix m k = k m := by
  rcases m with ⟨rows⟩
  exact forcePolyMatList_eq rows (fun rows => k (Array.mk rows))

@[expose] def forcePolyNat {α : Type} (p : Poly × Nat) (k : Poly → Nat → α) : α :=
  match p with
  | (f, n) => forcePoly f fun f' => withForcedNat n fun n' => k f' n'

theorem forcePolyNat_eq {α : Type} (p : Poly × Nat) (k : Poly → Nat → α) :
    forcePolyNat p k = k p.1 p.2 := by
  rcases p with ⟨f, n⟩
  simp only [forcePolyNat, forcePoly_eq, withForcedNat_eq]

@[expose] def withDrop {α β : Type} : Nat → List α → (List α → β) → β
  | 0, xs, k => k xs
  | d + 1, _ :: xs, k => withDrop d xs k
  | _ + 1, [], k => k []

private theorem withDrop_eq {α β : Type} :
    ∀ (d : Nat) (xs : List α) (k : List α → β), withDrop d xs k = k (xs.drop d)
  | 0, _, _ => rfl
  | _ + 1, [], _ => rfl
  | d + 1, _ :: xs, k => withDrop_eq d xs k

/-! ## 2. Linear-Time `Poly` Arithmetic, NTT, Encoding, and Sampling Wrappers -/

@[expose] def pad256 (xs : List Nat) : List Nat :=
  let t := xs.take 256
  t ++ List.replicate (256 - t.length) 0

private theorem pad256_length (xs : List Nat) : (pad256 xs).length = 256 := by
  simp [pad256]; omega

private theorem pad256_getElem (xs : List Nat) {i : Nat} (hi : i < 256) :
    (pad256 xs)[i]'(by rw [pad256_length]; exact hi) = xs.getD i 0 := by
  unfold pad256
  by_cases h : i < xs.length
  · have ht : i < (xs.take 256).length := by simp; omega
    rw [List.getElem_append_left ht, List.getElem_take]
    simp [List.getD_eq_getElem?_getD, h]
  · have ht : (xs.take 256).length ≤ i := by simp; omega
    rw [List.getElem_append_right ht, List.getElem_replicate]
    simp [List.getD_eq_getElem?_getD, h]

@[expose] def bitRev7Fast (k : Nat) : Nat :=
  let k1 := k / 2; let k2 := k1 / 2; let k3 := k2 / 2
  let k4 := k3 / 2; let k5 := k4 / 2; let k6 := k5 / 2
  (k % 2) * 64 + (k1 % 2) * 32 + (k2 % 2) * 16 + (k3 % 2) * 8 +
    (k4 % 2) * 4 + (k5 % 2) * 2 + (k6 % 2)

private theorem bitRev7Fast_table :
    ((List.range 128).all fun k => decide (bitRev7Fast k = bitRev7 k)) = true := by
  decide +kernel

private theorem bitRev7Fast_eq {k : Nat} (hk : k < 128) : bitRev7Fast k = bitRev7 k :=
  of_decide_eq_true (List.all_eq_true.mp bitRev7Fast_table k (List.mem_range.mpr hk))

@[expose] def fipsZetasFast : Poly :=
  forcePoly (arrayOfFnFast 128 fun k => (17 ^ bitRev7Fast k) % mlkemQ) id

private theorem fipsZetasFast_eq : fipsZetasFast = fipsZetas := by
  unfold fipsZetasFast fipsZetas
  rw [forcePoly_eq, id_eq, arrayOfFnFast_eq]
  congr 1
  funext ⟨k, hk⟩
  rw [bitRev7Fast_eq hk]

@[expose] def polyAddFast (a b : Poly) : Poly :=
  forcePoly a fun a =>
  forcePoly b fun b =>
  forceListNat
    (List.zipWith (fun x y => (x + y) % mlkemQ) (pad256 a.toList) (pad256 b.toList))
    Array.mk

theorem polyAddFast_eq (a b : Poly) : polyAddFast a b = polyAdd a b := by
  unfold polyAddFast polyAdd
  rw [forcePoly_eq, forcePoly_eq, forceListNat_eq]
  apply Array.ext
  · simp [pad256_length]
  · intro i h1 h2
    have hi : i < 256 := by simpa using h2
    simp only [Array.getElem_ofFn, List.getElem_toArray, List.getElem_zipWith,
      pad256_getElem _ hi, ← arrayGetDFast_eq]
    rfl

@[expose] def polySubFast (a b : Poly) : Poly :=
  forcePoly a fun a =>
  forcePoly b fun b =>
  forceListNat
    (List.zipWith (fun x y => (x + mlkemQ - (y % mlkemQ)) % mlkemQ)
      (pad256 a.toList) (pad256 b.toList))
    Array.mk

theorem polySubFast_eq (a b : Poly) : polySubFast a b = polySub a b := by
  unfold polySubFast polySub
  rw [forcePoly_eq, forcePoly_eq, forceListNat_eq]
  apply Array.ext
  · simp [pad256_length]
  · intro i h1 h2
    have hi : i < 256 := by simpa using h2
    simp only [Array.getElem_ofFn, List.getElem_toArray, List.getElem_zipWith,
      pad256_getElem _ hi, ← arrayGetDFast_eq]
    rfl

/-! ### Parametric Linear-Time Butterfly Stage (`nttStageFast` / `invNttStageFast`) -/

@[expose] def butterflyBlocks (bf : Nat → Nat → Nat → Nat × Nat) (stepK : Nat → Nat)
    (zetas : List Nat) (len : Nat) : Nat → Nat → List Nat → List Nat × Nat
  | 0, k, _ => ([], k)
  | nBlocks + 1, k, cur =>
    withForcedNat (zetas.getD k 0) fun zeta =>
    let lo := cur.take len
    let hi := (cur.drop len).take len
    let outLo := List.zipWith (fun fj fjl => (bf zeta fj fjl).1) lo hi
    let outHi := List.zipWith (fun fj fjl => (bf zeta fj fjl).2) lo hi
    withDrop (2 * len) cur fun rest =>
    let (tail, k') := butterflyBlocks bf stepK zetas len nBlocks (stepK k) rest
    (outLo ++ outHi ++ tail, k')

private def butterflyInnerList (bf1 : Nat → Nat → Nat × Nat) (start m len : Nat)
    (cur : List Nat) : List Nat :=
  (List.range m).foldl
    (fun xs off =>
      let j := start + off
      let p := bf1 (xs.getD j 0) (xs.getD (j + len) 0)
      (xs.set j p.1).set (j + len) p.2)
    cur

private theorem butterflyInnerList_length (bf1 : Nat → Nat → Nat × Nat)
    (start m len : Nat) (cur : List Nat) :
    (butterflyInnerList bf1 start m len cur).length = cur.length := by
  unfold butterflyInnerList
  induction (List.range m) generalizing cur with
  | nil => rfl
  | cons _ _ ih =>
    simp only [List.foldl_cons]
    exact (ih _).trans (by simp)

private theorem list_getElem_of_eq {α : Type} {l1 l2 : List α} (heq : l1 = l2)
    {i : Nat} {h1 : i < l1.length} {h2 : i < l2.length} :
    l1[i]'h1 = l2[i]'h2 := by
  subst heq
  rfl

private theorem list_getElem_idx_eq {α : Type} (l : List α) {a b : Nat}
    {ha : a < l.length} {hb : b < l.length} (h : a = b) :
    l[a]'ha = l[b]'hb := by
  subst h
  rfl

private theorem butterflyInnerList_spec (bf1 : Nat → Nat → Nat × Nat) (start len : Nat)
    (cur : List Nat) (hbound : start + 2 * len ≤ cur.length) :
    ∀ (m : Nat) (_hm : m ≤ len) (idx : Nat) (hidx : idx < cur.length),
      (butterflyInnerList bf1 start m len cur)[idx]'(by
          rw [butterflyInnerList_length]; exact hidx) =
        if c1 : start ≤ idx ∧ idx < start + m then
          (bf1 (cur[idx]'hidx) (cur[idx + len]'(by omega))).1
        else if c2 : start + len ≤ idx ∧ idx < start + len + m then
          (bf1 (cur[idx - len]'(by omega)) (cur[idx]'hidx)).2
        else
          cur[idx]'hidx := by
  intro m hm
  induction m with
  | zero =>
    intro idx hidx
    unfold butterflyInnerList
    split_ifs <;> try omega
    rfl
  | succ m ih =>
    have hget_m := ih (by omega)
    have hlen_m := butterflyInnerList_length bf1 start m len cur
    have hstep : butterflyInnerList bf1 start (m + 1) len cur =
        let xs := butterflyInnerList bf1 start m len cur
        let j := start + m
        let p := bf1 (xs.getD j 0) (xs.getD (j + len) 0)
        (xs.set j p.1).set (j + len) p.2 := by
      simp only [butterflyInnerList, List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
    intro idx hidx
    set xs := butterflyInnerList bf1 start m len cur
    have hj_lt : start + m < cur.length := by omega
    have hjl_lt : start + m + len < cur.length := by omega
    have hxs_j : xs.getD (start + m) 0 = cur[start + m]'hj_lt := by
      have h1 : start + m < xs.length := by rw [hlen_m]; exact hj_lt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some,
        hget_m (start + m) hj_lt]
      split_ifs <;> omega
    have hxs_jl : xs.getD (start + m + len) 0 = cur[start + m + len]'hjl_lt := by
      have h1 : start + m + len < xs.length := by rw [hlen_m]; exact hjl_lt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some,
        hget_m (start + m + len) hjl_lt]
      split_ifs <;> omega
    have hlhs :
        (butterflyInnerList bf1 start (m + 1) len cur)[idx]'(by
            rw [butterflyInnerList_length]; exact hidx) =
          ((xs.set (start + m)
              (bf1 (cur[start + m]'hj_lt) (cur[start + m + len]'hjl_lt)).1).set
            (start + m + len)
              (bf1 (cur[start + m]'hj_lt) (cur[start + m + len]'hjl_lt)).2)[idx]'(by
            simp [hlen_m, hidx]) :=
      list_getElem_of_eq (by rw [hstep]; dsimp only; rw [hxs_j, hxs_jl])
    rw [hlhs]
    simp only [List.getElem_set]
    by_cases hhi : start + m + len = idx
    · simp only [hhi, ↓reduceIte]
      split_ifs with c1 c2
      · omega
      · rw [list_getElem_idx_eq cur (a := start + m) (b := idx - len) (by omega)]
      · omega
    · simp only [hhi, ↓reduceIte]
      by_cases hlo : start + m = idx
      · simp only [hlo, ↓reduceIte]
        split_ifs with c1 c2
        · rfl
        · omega
        · omega
      · simp only [hlo, ↓reduceIte]
        have hxs_idx : xs[idx]'(by rw [hlen_m]; exact hidx) =
            (butterflyInnerList bf1 start m len cur)[idx]'(by
              rw [butterflyInnerList_length]; exact hidx) := rfl
        rw [hxs_idx, hget_m idx hidx]
        split_ifs <;> first | rfl | omega

private theorem butterflyInnerList_split (bf1 : Nat → Nat → Nat × Nat) (len : Nat)
    (pre mid post : List Nat) (hmid : mid.length = 2 * len) :
    butterflyInnerList bf1 pre.length len len (pre ++ mid ++ post) =
      pre ++
        (List.zipWith (fun fj fjl => (bf1 fj fjl).1) (mid.take len) ((mid.drop len).take len) ++
         List.zipWith (fun fj fjl => (bf1 fj fjl).2) (mid.take len) ((mid.drop len).take len)) ++
        post := by
  set cur := pre ++ mid ++ post
  have hcur_len : cur.length = pre.length + 2 * len + post.length := by
    simp [cur, hmid]; omega
  have hlen_res := butterflyInnerList_length bf1 pre.length len len cur
  have hget_res :=
    butterflyInnerList_spec bf1 pre.length len cur (by omega) len (Nat.le_refl len)
  set lo := mid.take len
  set hi := (mid.drop len).take len
  set outLo := List.zipWith (fun fj fjl => (bf1 fj fjl).1) lo hi
  set outHi := List.zipWith (fun fj fjl => (bf1 fj fjl).2) lo hi
  have hlo_len : lo.length = len := by simp [lo, hmid]; omega
  have hhi_len : hi.length = len := by simp [hi, hmid]; omega
  have houtLo_len : outLo.length = len := by simp [outLo, hlo_len, hhi_len]
  have houtHi_len : outHi.length = len := by simp [outHi, hlo_len, hhi_len]
  have hrhs_len : (pre ++ (outLo ++ outHi) ++ post).length = cur.length := by
    simp [hcur_len, houtLo_len, houtHi_len]; omega
  have hcur_mid : ∀ j (hj : j < 2 * len),
      cur[pre.length + j]'(by omega) = mid[j]'(by omega) := by
    intro j hj
    have h1 : pre.length + j < (pre ++ mid).length := by simp [hmid]; omega
    have h2 : pre.length ≤ pre.length + j := by omega
    rw [List.getElem_append_left h1, List.getElem_append_right h2]
    congr 1; omega
  apply List.ext_getElem (hlen_res.trans hrhs_len.symm)
  intro idx h1 h2
  have hidx : idx < cur.length := hlen_res ▸ h1
  rw [hget_res idx hidx]
  split_ifs with c1 c2
  · have hp2 : idx < (pre ++ (outLo ++ outHi)).length := by
      simp [houtLo_len, houtHi_len]; omega
    have hp3 : pre.length ≤ idx := by omega
    have hp4 : idx - pre.length < outLo.length := by rw [houtLo_len]; omega
    rw [List.getElem_append_left hp2, List.getElem_append_right hp3,
      List.getElem_append_left hp4]
    simp only [outLo, lo, hi, List.getElem_zipWith, List.getElem_take, List.getElem_drop]
    have heq1 : pre.length + (idx - pre.length) = idx := by omega
    have heq2 : pre.length + (len + (idx - pre.length)) = idx + len := by omega
    have hm1 : cur[idx]'hidx = mid[idx - pre.length]'(by omega) := by
      simpa [heq1] using hcur_mid (idx - pre.length) (by omega)
    have hm2 : cur[idx + len]'(by omega) = mid[len + (idx - pre.length)]'(by omega) := by
      simpa [heq2] using hcur_mid (len + (idx - pre.length)) (by omega)
    rw [hm1, hm2]
  · have hp2 : idx < (pre ++ (outLo ++ outHi)).length := by
      simp [houtLo_len, houtHi_len]; omega
    have hp3 : pre.length ≤ idx := by omega
    have hp4 : outLo.length ≤ idx - pre.length := by rw [houtLo_len]; omega
    rw [List.getElem_append_left hp2, List.getElem_append_right hp3,
      List.getElem_append_right hp4]
    simp only [outHi, lo, hi, houtLo_len, List.getElem_zipWith, List.getElem_take,
      List.getElem_drop]
    have heq1 : pre.length + (idx - pre.length - len) = idx - len := by omega
    have heq2 : pre.length + (len + (idx - pre.length - len)) = idx := by omega
    have hm1 : cur[idx - len]'(by omega) = mid[idx - pre.length - len]'(by omega) := by
      simpa [heq1] using hcur_mid (idx - pre.length - len) (by omega)
    have hm2 : cur[idx]'hidx = mid[len + (idx - pre.length - len)]'(by omega) := by
      simpa [heq2] using hcur_mid (len + (idx - pre.length - len)) (by omega)
    rw [hm1, hm2]
  · by_cases hp : idx < pre.length
    · have hp1 : idx < (pre ++ mid).length := by simp; omega
      have hp2 : idx < (pre ++ (outLo ++ outHi)).length := by simp; omega
      rw [List.getElem_append_left hp1, List.getElem_append_left hp,
        List.getElem_append_left hp2, List.getElem_append_left hp]
    · have hp1 : (pre ++ mid).length ≤ idx := by simp [hmid]; omega
      have hp2 : (pre ++ (outLo ++ outHi)).length ≤ idx := by
        simp [houtLo_len, houtHi_len]; omega
      rw [List.getElem_append_right hp1, List.getElem_append_right hp2]
      congr 1
      simp [hmid, houtLo_len, houtHi_len]; omega

private theorem butterflyOuterList_eq (bf : Nat → Nat → Nat → Nat × Nat) (stepK : Nat → Nat)
    (zetas : List Nat) (len : Nat) :
    ∀ (nBlocks preBlocks : Nat) (pre cur : List Nat) (k : Nat),
      pre.length = preBlocks * 2 * len →
      cur.length = 2 * len * nBlocks →
      ((List.range nBlocks).map (· + preBlocks)).foldl
        (fun (acc : List Nat × Nat) blk =>
          let start := blk * 2 * len
          let zeta := zetas.getD acc.2 0
          (butterflyInnerList (bf zeta) start len len acc.1, stepK acc.2))
        (pre ++ cur, k) =
        let r := butterflyBlocks bf stepK zetas len nBlocks k cur
        (pre ++ r.1, r.2)
  | 0, _, pre, cur, k, _, hcur => by
    have hnil : cur = [] := List.eq_nil_of_length_eq_zero (by simpa using hcur)
    subst hnil
    simp [butterflyBlocks]
  | nBlocks + 1, preBlocks, pre, cur, k, hpre, hcur => by
    rw [Nat.mul_succ] at hcur
    set M := 2 * len * nBlocks
    set mid := cur.take (2 * len)
    set rest := cur.drop (2 * len)
    have hsplit : pre ++ cur = pre ++ mid ++ rest := by
      rw [List.append_assoc, List.take_append_drop]
    have hmid_len : mid.length = 2 * len := by simp [mid]; omega
    have hrest_len : rest.length = M := by simp [rest]; omega
    have hlo_eq : mid.take len = cur.take len := by
      simp [mid, List.take_take]; omega
    have hhi_eq : (mid.drop len).take len = (cur.drop len).take len := by
      simp [mid, List.drop_take, List.take_take, show 2 * len - len = len by omega]
    rw [List.range_succ_eq_map, List.map_cons, List.foldl_cons, List.map_map]
    dsimp only
    have hmap : ((· + preBlocks) ∘ (· + 1)) = (· + (preBlocks + 1)) := by
      funext x; dsimp only [Function.comp]; omega
    have hstart : (0 + preBlocks) * 2 * len = pre.length := by
      rw [Nat.zero_add, hpre]
    rw [hmap, hstart, hsplit, butterflyInnerList_split (bf (zetas.getD k 0)) len pre mid rest hmid_len,
      hlo_eq, hhi_eq]
    set outStep :=
      List.zipWith (fun fj fjl => (bf (zetas.getD k 0) fj fjl).1) (cur.take len) ((cur.drop len).take len) ++
      List.zipWith (fun fj fjl => (bf (zetas.getD k 0) fj fjl).2) (cur.take len) ((cur.drop len).take len)
    have hpre' : (pre ++ outStep).length = (preBlocks + 1) * 2 * len := by
      have hl1 : (cur.take len).length = len := by simp; omega
      have hl2 : ((cur.drop len).take len).length = len := by simp; omega
      have hout_len : outStep.length = 2 * len := by simp [outStep, hl1, hl2]; omega
      have hrhs : (preBlocks + 1) * 2 * len = preBlocks * 2 * len + 2 * len := by
        rw [Nat.add_mul preBlocks 1 2, Nat.one_mul, Nat.add_mul]
      rw [List.length_append, hpre, hout_len, hrhs]
    have ih := butterflyOuterList_eq bf stepK zetas len nBlocks (preBlocks + 1)
      (pre ++ outStep) rest (stepK k) hpre' hrest_len
    rw [ih]
    simp only [butterflyBlocks, withForcedNat_eq, withDrop_eq]
    change (let r := butterflyBlocks bf stepK zetas len nBlocks (stepK k) rest; (pre ++ outStep ++ r.1, r.2)) =
      let r := (let (tail, k') := butterflyBlocks bf stepK zetas len nBlocks (stepK k) rest; (_ ++ tail, k'))
      (pre ++ r.1, r.2)
    rcases butterflyBlocks bf stepK zetas len nBlocks (stepK k) rest with ⟨tail, k'⟩
    simp only [outStep, List.append_assoc]

private theorem foldl_arrayMk {α : Type} (l : List α) (g : List Nat → α → List Nat) (xs : List Nat) :
    l.foldl (fun (a : Poly) x => Array.mk (g a.toList x)) (Array.mk xs) =
      Array.mk (l.foldl g xs) := by
  induction l generalizing xs with
  | nil => rfl
  | cons x xs' ih => exact ih (g xs x)

private theorem foldl_arrayMk_pair {α : Type} (l : List α)
    (g1 : List Nat → Nat → α → List Nat) (g2 : Nat → α → Nat)
    (xs : List Nat) (k : Nat) :
    l.foldl (fun (ak : Poly × Nat) x =>
      (Array.mk (g1 ak.1.toList ak.2 x), g2 ak.2 x)) (Array.mk xs, k) =
      let r := l.foldl (fun (acc : List Nat × Nat) x => (g1 acc.1 acc.2 x, g2 acc.2 x)) (xs, k)
      (Array.mk r.1, r.2) := by
  induction l generalizing xs k with
  | nil => rfl
  | cons x xs' ih => exact ih (g1 xs k x) (g2 k x)

@[expose] def nttBf (zeta fj fjl : Nat) : Nat × Nat :=
  let t := (zeta * fjl) % mlkemQ
  ((fj + t) % mlkemQ, (fj + mlkemQ - t) % mlkemQ)

@[expose] def invNttBf (zeta t fjl : Nat) : Nat × Nat :=
  ((t + fjl) % mlkemQ, (zeta * (fjl + mlkemQ - t)) % mlkemQ)

@[expose] def nttStageWith (zetas : Poly) (len kInit : Nat) (f : Poly) : Poly × Nat :=
  let nBlocks := 256 / (2 * len)
  (List.range nBlocks).foldl
    (fun (cur, k) blk =>
      let start := blk * 2 * len
      let zeta := arrayGetDFast zetas k 0
      let next := (List.range len).foldl
        (fun arr off =>
          let j := start + off
          let fj := arrayGetDFast arr j 0
          let fjl := arrayGetDFast arr (j + len) 0
          let t := (zeta * fjl) % mlkemQ
          let a' := (fj + t) % mlkemQ
          let b' := (fj + mlkemQ - t) % mlkemQ
          arraySetFast (arraySetFast arr j a') (j + len) b')
        cur
      (next, k + 1))
    (f, kInit)

private theorem nttStageWith_eq (len kInit : Nat) (f : Poly) :
    nttStageWith fipsZetas len kInit f = nttStage len kInit f := by
  unfold nttStageWith nttStage
  simp only [arrayGetDFast_eq, arraySetFast_eq]

@[expose] def nttStageFast (zetas : Poly) (len kInit : Nat) (f : Poly) : Poly × Nat :=
  if f.toList.length == 256 then
    let (out, k') := butterflyBlocks nttBf (· + 1) zetas.toList len (256 / (2 * len)) kInit f.toList
    (Array.mk out, k')
  else
    nttStageWith zetas len kInit f

private theorem nttStageFast_eq (len kInit : Nat) (f : Poly)
    (hdiv : 2 * len * (256 / (2 * len)) = 256) :
    nttStageFast fipsZetas len kInit f = nttStage len kInit f := by
  rw [← nttStageWith_eq]
  unfold nttStageFast
  by_cases hf : (f.toList.length == 256) = true
  · simp only [hf, ↓reduceIte]
    have hlen256 : f.toList.length = 256 := beq_iff_eq.mp hf
    rcases f with ⟨xs⟩
    have hxs : xs.length = 2 * len * (256 / (2 * len)) := hlen256.trans hdiv.symm
    have router := butterflyOuterList_eq nttBf (· + 1) fipsZetas.toList len
      (256 / (2 * len)) 0 [] xs kInit (by simp) hxs
    have hmap_id : List.map (· + 0) (List.range (256 / (2 * len))) =
        List.range (256 / (2 * len)) := by simp
    rw [hmap_id, List.nil_append] at router
    unfold nttStageWith
    have hstep :
        (List.range (256 / (2 * len))).foldl
          (fun (ak : Poly × Nat) blk =>
            (Array.mk
              (butterflyInnerList (nttBf (fipsZetas.toList.getD ak.2 0)) (blk * 2 * len) len len
                ak.1.toList),
             ak.2 + 1))
          (Array.mk xs, kInit) =
        let r := (List.range (256 / (2 * len))).foldl
          (fun (acc : List Nat × Nat) blk =>
            (butterflyInnerList (nttBf (fipsZetas.toList.getD acc.2 0)) (blk * 2 * len) len len
              acc.1,
             acc.2 + 1))
          (xs, kInit)
        (Array.mk r.1, r.2) :=
      foldl_arrayMk_pair (List.range (256 / (2 * len)))
        (fun ys k blk =>
          butterflyInnerList (nttBf (fipsZetas.toList.getD k 0)) (blk * 2 * len) len len ys)
        (fun k _ => k + 1) xs kInit
    have dinner :
        (fun ((cur, k) : Poly × Nat) (blk : Nat) =>
          let start := blk * 2 * len
          let zeta := arrayGetDFast fipsZetas k 0
          let next := (List.range len).foldl
            (fun arr off =>
              let j := start + off
              let fj := arrayGetDFast arr j 0
              let fjl := arrayGetDFast arr (j + len) 0
              let t := (zeta * fjl) % mlkemQ
              let a' := (fj + t) % mlkemQ
              let b' := (fj + mlkemQ - t) % mlkemQ
              arraySetFast (arraySetFast arr j a') (j + len) b')
            cur
          (next, k + 1)) =
        (fun (ak : Poly × Nat) (blk : Nat) =>
          (Array.mk
            (butterflyInnerList (nttBf (fipsZetas.toList.getD ak.2 0)) (blk * 2 * len) len len
              ak.1.toList),
           ak.2 + 1)) := by
      funext ⟨⟨ys⟩, k⟩ blk
      dsimp only [arrayGetDFast]
      congr 1
      simpa [butterflyInnerList, nttBf, arrayGetDFast, arraySetFast] using
        foldl_arrayMk (List.range len)
          (fun zs off =>
            let j := blk * 2 * len + off
            let p := nttBf (fipsZetas.toList.getD k 0) (zs.getD j 0) (zs.getD (j + len) 0)
            (zs.set j p.1).set (j + len) p.2)
          ys
    dsimp only
    rw [dinner, hstep]
    dsimp only
    rw [router]
    rcases butterflyBlocks nttBf (· + 1) fipsZetas.toList len (256 / (2 * len)) kInit xs with
      ⟨out, k'⟩
    rfl
  · simp only [Bool.not_eq_true] at hf
    simp only [hf, Bool.false_eq_true, ↓reduceIte]

@[expose] def polyNttFast (f : Poly) : Poly :=
  forcePoly fipsZetasFast fun zetas =>
  forcePoly f fun f =>
  forcePolyNat (nttStageFast zetas 128 1 f) fun f k =>
  forcePolyNat (nttStageFast zetas 64 k f) fun f k =>
  forcePolyNat (nttStageFast zetas 32 k f) fun f k =>
  forcePolyNat (nttStageFast zetas 16 k f) fun f k =>
  forcePolyNat (nttStageFast zetas 8 k f) fun f k =>
  forcePolyNat (nttStageFast zetas 4 k f) fun f k =>
  forcePoly (nttStageFast zetas 2 k f).1 id

theorem polyNttFast_eq (f : Poly) : polyNttFast f = polyNtt f := by
  unfold polyNttFast polyNtt
  simp only [forcePoly_eq, forcePolyNat_eq, id_eq, fipsZetasFast_eq,
    nttStageFast_eq 128 _ _ rfl,
    nttStageFast_eq 64 _ _ rfl,
    nttStageFast_eq 32 _ _ rfl,
    nttStageFast_eq 16 _ _ rfl,
    nttStageFast_eq 8 _ _ rfl,
    nttStageFast_eq 4 _ _ rfl,
    nttStageFast_eq 2 _ _ rfl]

@[expose] def invNttStageWith (zetas : Poly) (len kInit : Nat) (f : Poly) : Poly × Nat :=
  let nBlocks := 256 / (2 * len)
  (List.range nBlocks).foldl
    (fun (cur, k) blk =>
      let start := blk * 2 * len
      let zeta := arrayGetDFast zetas k 0
      let next := (List.range len).foldl
        (fun arr off =>
          let j := start + off
          let t := arrayGetDFast arr j 0
          let fjl := arrayGetDFast arr (j + len) 0
          let a' := (t + fjl) % mlkemQ
          let b' := (zeta * (fjl + mlkemQ - t)) % mlkemQ
          arraySetFast (arraySetFast arr j a') (j + len) b')
        cur
      (next, k - 1))
    (f, kInit)

private theorem invNttStageWith_eq (len kInit : Nat) (f : Poly) :
    invNttStageWith fipsZetas len kInit f = invNttStage len kInit f := by
  unfold invNttStageWith invNttStage
  simp only [arrayGetDFast_eq, arraySetFast_eq]

@[expose] def invNttStageFast (zetas : Poly) (len kInit : Nat) (f : Poly) : Poly × Nat :=
  if f.toList.length == 256 then
    let (out, k') :=
      butterflyBlocks invNttBf (· - 1) zetas.toList len (256 / (2 * len)) kInit f.toList
    (Array.mk out, k')
  else
    invNttStageWith zetas len kInit f

private theorem invNttStageFast_eq (len kInit : Nat) (f : Poly)
    (hdiv : 2 * len * (256 / (2 * len)) = 256) :
    invNttStageFast fipsZetas len kInit f = invNttStage len kInit f := by
  rw [← invNttStageWith_eq]
  unfold invNttStageFast
  by_cases hf : (f.toList.length == 256) = true
  · simp only [hf, ↓reduceIte]
    have hlen256 : f.toList.length = 256 := beq_iff_eq.mp hf
    rcases f with ⟨xs⟩
    have hxs : xs.length = 2 * len * (256 / (2 * len)) := hlen256.trans hdiv.symm
    have router := butterflyOuterList_eq invNttBf (· - 1) fipsZetas.toList len
      (256 / (2 * len)) 0 [] xs kInit (by simp) hxs
    have hmap_id : List.map (· + 0) (List.range (256 / (2 * len))) =
        List.range (256 / (2 * len)) := by simp
    rw [hmap_id, List.nil_append] at router
    unfold invNttStageWith
    have hstep :
        (List.range (256 / (2 * len))).foldl
          (fun (ak : Poly × Nat) blk =>
            (Array.mk
              (butterflyInnerList (invNttBf (fipsZetas.toList.getD ak.2 0)) (blk * 2 * len) len len
                ak.1.toList),
             ak.2 - 1))
          (Array.mk xs, kInit) =
        let r := (List.range (256 / (2 * len))).foldl
          (fun (acc : List Nat × Nat) blk =>
            (butterflyInnerList (invNttBf (fipsZetas.toList.getD acc.2 0)) (blk * 2 * len) len len
              acc.1,
             acc.2 - 1))
          (xs, kInit)
        (Array.mk r.1, r.2) :=
      foldl_arrayMk_pair (List.range (256 / (2 * len)))
        (fun ys k blk =>
          butterflyInnerList (invNttBf (fipsZetas.toList.getD k 0)) (blk * 2 * len) len len ys)
        (fun k _ => k - 1) xs kInit
    have dinner :
        (fun ((cur, k) : Poly × Nat) (blk : Nat) =>
          let start := blk * 2 * len
          let zeta := arrayGetDFast fipsZetas k 0
          let next := (List.range len).foldl
            (fun arr off =>
              let j := start + off
              let t := arrayGetDFast arr j 0
              let fjl := arrayGetDFast arr (j + len) 0
              let a' := (t + fjl) % mlkemQ
              let b' := (zeta * (fjl + mlkemQ - t)) % mlkemQ
              arraySetFast (arraySetFast arr j a') (j + len) b')
            cur
          (next, k - 1)) =
        (fun (ak : Poly × Nat) (blk : Nat) =>
          (Array.mk
            (butterflyInnerList (invNttBf (fipsZetas.toList.getD ak.2 0)) (blk * 2 * len) len len
              ak.1.toList),
           ak.2 - 1)) := by
      funext ⟨⟨ys⟩, k⟩ blk
      dsimp only [arrayGetDFast]
      congr 1
      simpa [butterflyInnerList, invNttBf, arrayGetDFast, arraySetFast] using
        foldl_arrayMk (List.range len)
          (fun zs off =>
            let j := blk * 2 * len + off
            let p := invNttBf (fipsZetas.toList.getD k 0) (zs.getD j 0) (zs.getD (j + len) 0)
            (zs.set j p.1).set (j + len) p.2)
          ys
    dsimp only
    rw [dinner, hstep]
    dsimp only
    rw [router]
    rcases butterflyBlocks invNttBf (· - 1) fipsZetas.toList len (256 / (2 * len)) kInit xs with
      ⟨out, k'⟩
    rfl
  · simp only [Bool.not_eq_true] at hf
    simp only [hf, Bool.false_eq_true, ↓reduceIte]

@[expose] def polyInvNttFast (f : Poly) : Poly :=
  forcePoly fipsZetasFast fun zetas =>
  forcePoly f fun f =>
  forcePolyNat (invNttStageFast zetas 2 127 f) fun f k =>
  forcePolyNat (invNttStageFast zetas 4 k f) fun f k =>
  forcePolyNat (invNttStageFast zetas 8 k f) fun f k =>
  forcePolyNat (invNttStageFast zetas 16 k f) fun f k =>
  forcePolyNat (invNttStageFast zetas 32 k f) fun f k =>
  forcePolyNat (invNttStageFast zetas 64 k f) fun f k =>
  forcePoly (invNttStageFast zetas 128 k f).1 fun f =>
  forcePoly (arrayMapFast (fun c => (c * 3303) % mlkemQ) f) id

theorem polyInvNttFast_eq (f : Poly) : polyInvNttFast f = polyInvNtt f := by
  unfold polyInvNttFast polyInvNtt
  simp only [forcePoly_eq, forcePolyNat_eq, id_eq, fipsZetasFast_eq, arrayMapFast_eq,
    invNttStageFast_eq 2 _ _ rfl,
    invNttStageFast_eq 4 _ _ rfl,
    invNttStageFast_eq 8 _ _ rfl,
    invNttStageFast_eq 16 _ _ rfl,
    invNttStageFast_eq 32 _ _ rfl,
    invNttStageFast_eq 64 _ _ rfl,
    invNttStageFast_eq 128 _ _ rfl]

/-! ### Linear-Time `MultiplyNTTs` (`polyNttMulFast`) -/

@[expose] def nttMulPairs (zetas : List Nat) : Nat → Nat → List Nat → List Nat → List Nat
  | 0, _, _, _ => []
  | rem + 1, p, xs, ys =>
    let a0 := xs.getD 0 0
    let a1 := xs.getD 1 0
    let b0 := ys.getD 0 0
    let b1 := ys.getD 1 0
    let baseZeta := zetas.getD (64 + p / 2) 0
    let gamma := if p % 2 == 0 then baseZeta else (mlkemQ - baseZeta) % mlkemQ
    let c0 := (a0 * b0 + ((a1 * b1) % mlkemQ) * gamma) % mlkemQ
    let c1 := (a0 * b1 + a1 * b0) % mlkemQ
    withDrop 2 xs fun xs' =>
    withDrop 2 ys fun ys' =>
    c0 :: c1 :: nttMulPairs zetas rem (p + 1) xs' ys'

private theorem nttMulPairs_length (zetas : List Nat) :
    ∀ (rem p : Nat) (xs ys : List Nat), (nttMulPairs zetas rem p xs ys).length = 2 * rem
  | 0, _, _, _ => rfl
  | rem + 1, p, xs, ys => by
    simp only [nttMulPairs, withDrop_eq, List.length_cons, nttMulPairs_length zetas rem]
    omega

private theorem nttMulPairs_getElem (zetas : List Nat) :
    ∀ (rem p : Nat) (xs ys : List Nat) {idx : Nat} (hidx : idx < 2 * rem),
      (nttMulPairs zetas rem p xs ys)[idx]'(by rw [nttMulPairs_length]; exact hidx) =
        let q := p + idx / 2
        let a0 := xs.getD (2 * (idx / 2)) 0
        let a1 := xs.getD (2 * (idx / 2) + 1) 0
        let b0 := ys.getD (2 * (idx / 2)) 0
        let b1 := ys.getD (2 * (idx / 2) + 1) 0
        let baseZeta := zetas.getD (64 + q / 2) 0
        let gamma := if q % 2 == 0 then baseZeta else (mlkemQ - baseZeta) % mlkemQ
        if idx % 2 == 0 then
          (a0 * b0 + ((a1 * b1) % mlkemQ) * gamma) % mlkemQ
        else
          (a0 * b1 + a1 * b0) % mlkemQ
  | 0, _, _, _, _, hidx => absurd hidx (by omega)
  | rem + 1, p, xs, ys, 0, _ => by simp [nttMulPairs, withDrop_eq]
  | rem + 1, p, xs, ys, 1, _ => by simp [nttMulPairs, withDrop_eq]
  | rem + 1, p, xs, ys, idx + 2, hidx => by
    simp only [nttMulPairs, withDrop_eq, List.getElem_cons_succ]
    rw [nttMulPairs_getElem zetas rem (p + 1) (xs.drop 2) (ys.drop 2) (by omega)]
    have hmod : (idx + 2) % 2 = idx % 2 := by omega
    have hq : p + 1 + idx / 2 = p + (idx + 2) / 2 := by omega
    have hi0 : 2 + 2 * (idx / 2) = 2 * ((idx + 2) / 2) := by omega
    have hi1 : 2 + (2 * (idx / 2) + 1) = 2 * ((idx + 2) / 2) + 1 := by omega
    simp only [list_getD_drop, hq, hi0, hi1, hmod]

@[expose] def polyNttMulFast (f g : Poly) : Poly :=
  forcePoly fipsZetasFast fun zetas =>
  forcePoly f fun f =>
  forcePoly g fun g =>
  forceListNat (nttMulPairs zetas.toList 128 0 f.toList g.toList) Array.mk

theorem polyNttMulFast_eq (f g : Poly) : polyNttMulFast f g = polyNttMul f g := by
  unfold polyNttMulFast polyNttMul
  rw [forcePoly_eq, fipsZetasFast_eq, forcePoly_eq, forcePoly_eq, forceListNat_eq]
  apply Array.ext
  · simp [nttMulPairs_length]
  · intro idx h1 h2
    have hidx : idx < 2 * 128 := by simpa using h2
    simp only [Array.getElem_ofFn, List.getElem_toArray]
    rw [nttMulPairs_getElem fipsZetas.toList 128 0 f.toList g.toList hidx]
    simp only [Nat.zero_add, ← arrayGetDFast_eq, arrayGetDFast]

@[expose] def vecDotNttFast (k : Nat) (a b : Array Poly) : Poly :=
  (List.range k).foldl
    (fun acc j =>
      polyAddFast acc (polyNttMulFast (arrayGetDFast a j zeroPoly) (arrayGetDFast b j zeroPoly)))
    zeroPoly

theorem vecDotNttFast_eq (k : Nat) (a b : Array Poly) : vecDotNttFast k a b = vecDotNtt k a b := by
  unfold vecDotNttFast vecDotNtt
  simp only [arrayGetDFast_eq,
    show polyAddFast = polyAdd from funext₂ polyAddFast_eq,
    show polyNttMulFast = polyNttMul from funext₂ polyNttMulFast_eq]

/-! ### Linear-Time Bit/Byte Conversion, `ByteEncode`, `ByteDecode`, and `SamplePolyCBD_2` -/

@[expose] def byteBits8 (b : BitVec 8) : List Nat :=
  withForcedNat b.toNat fun v =>
    let v1 := v / 2; let v2 := v1 / 2; let v3 := v2 / 2
    let v4 := v3 / 2; let v5 := v4 / 2; let v6 := v5 / 2; let v7 := v6 / 2
    [v % 2, v1 % 2, v2 % 2, v3 % 2, v4 % 2, v5 % 2, v6 % 2, v7 % 2]

private theorem byteBits8_length (b : BitVec 8) : (byteBits8 b).length = 8 := by
  unfold byteBits8
  rw [withForcedNat_eq]
  rfl

@[expose] def bytesToBitsList (bs : List (BitVec 8)) : List Nat :=
  bs.flatMap byteBits8

private theorem bytesToBitsList_length (bs : List (BitVec 8)) :
    (bytesToBitsList bs).length = 8 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [bytesToBitsList, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    have hb := byteBits8_length b
    omega

private theorem byteBits8_getElem (b : BitVec 8) {r : Nat} (hr : r < 8) :
    (byteBits8 b)[r]'(by rw [byteBits8_length]; exact hr) = (b.toNat >>> r) &&& 1 := by
  unfold byteBits8
  simp only [withForcedNat_eq, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  rcases r with _ | _ | _ | _ | _ | _ | _ | _ | r
  · simp
  · simp
  · simp [Nat.div_div_eq_div_mul]
  · simp [Nat.div_div_eq_div_mul]
  · simp [Nat.div_div_eq_div_mul]
  · simp [Nat.div_div_eq_div_mul]
  · simp [Nat.div_div_eq_div_mul]
  · simp [Nat.div_div_eq_div_mul]
  · omega

private theorem bytesToBitsList_getElem (bs : List (BitVec 8)) {idx : Nat}
    (hidx : idx < 8 * bs.length) :
    (bytesToBitsList bs)[idx]'(by rw [bytesToBitsList_length]; exact hidx) =
      ((bs.getD (idx / 8) 0#8).toNat >>> (idx % 8)) &&& 1 := by
  induction bs generalizing idx with
  | nil => simp at hidx
  | cons b bs ih =>
    have hcons : bytesToBitsList (b :: bs) = byteBits8 b ++ bytesToBitsList bs := rfl
    simp only [hcons]
    by_cases h8 : idx < 8
    · have hdiv : idx / 8 = 0 := by omega
      have hmod : idx % 8 = idx := by omega
      rw [List.getElem_append_left (by rw [byteBits8_length]; exact h8), byteBits8_getElem b h8,
        hdiv, hmod]
      rfl
    · have hge : (byteBits8 b).length ≤ idx := by rw [byteBits8_length]; omega
      have hsub : idx - 8 < 8 * bs.length := by simp at hidx; omega
      have hdiv : idx / 8 = (idx - 8) / 8 + 1 := by omega
      have hmod : idx % 8 = (idx - 8) % 8 := by omega
      have hb_len := byteBits8_length b
      rw [List.getElem_append_right hge]
      simp only [hb_len]
      rw [ih hsub, hdiv, hmod]
      rfl

private theorem bytesToBitsList_getD (bs : List (BitVec 8)) (idx : Nat) :
    (bytesToBitsList bs).getD idx 0 = (bytesToBits bs).getD idx 0 := by
  by_cases h : idx < 8 * bs.length
  · have h1 : idx < (bytesToBitsList bs).length := by rw [bytesToBitsList_length]; exact h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some,
      bytesToBitsList_getElem bs h]
    unfold bytesToBits
    rw [Array.getD]
    split_ifs with hlt
    · change _ = (Array.ofFn (n := 8 * bs.length) _)[idx]'hlt
      simp only [Array.getElem_ofFn, ← arrayGetDFast_eq bs.toArray, arrayGetDFast]
    · exfalso; simp at hlt; omega
  · have h1 : (bytesToBitsList bs).length ≤ idx := by rw [bytesToBitsList_length]; omega
    have h2 : ¬ idx < (bytesToBits bs).size := by simp [bytesToBits]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h1, Option.getD_none]
    simp [Array.getD, h2]

private theorem bytesToBitsList_getD_lt_two (bs : List (BitVec 8)) (idx : Nat) :
    (bytesToBitsList bs).getD idx 0 < 2 := by
  by_cases h : idx < 8 * bs.length
  · have h1 : idx < (bytesToBitsList bs).length := by rw [bytesToBitsList_length]; exact h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some,
      bytesToBitsList_getElem bs h, Nat.and_one_is_mod]
    omega
  · have h1 : (bytesToBitsList bs).length ≤ idx := by rw [bytesToBitsList_length]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h1]
    decide

private theorem or_shiftLeft_eq_add {acc b k : Nat} (hacc : acc < 2 ^ k) (hb : b < 2) :
    acc ||| (b <<< k) = acc + b * 2 ^ k := by
  rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
  · simp [Nat.shiftLeft_eq]
  · rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.add_comm acc (2 ^ k)]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_or]
    rcases Nat.lt_trichotomy i k with hlt | rfl | hgt
    · rw [Nat.testBit_two_pow_add_gt hlt, Nat.testBit_two_pow_of_ne (by omega), Bool.or_false]
    · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hacc, Nat.testBit_two_pow_self]
      rfl
    · have hlt2 : 2 ^ k + acc < 2 ^ i := by
        have hle : 2 ^ (k + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
        have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
        omega
      rw [Nat.testBit_lt_two_pow (Nat.lt_trans (by omega : acc < 2 ^ k + acc) hlt2),
        Nat.testBit_two_pow_of_ne (by omega), Nat.testBit_lt_two_pow hlt2]
      rfl

@[expose] def packBits8 : List Nat → List (BitVec 8)
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
    withForcedNat
      (b0 + 2 * (b1 + 2 * (b2 + 2 * (b3 + 2 * (b4 + 2 * (b5 + 2 * (b6 + 2 * b7)))))))
      fun v => BitVec.ofNat 8 v :: packBits8 rest
  | _ => []

private theorem pack8_or_eq_horner {b0 b1 b2 b3 b4 b5 b6 b7 : Nat}
    (h0 : b0 < 2) (h1 : b1 < 2) (h2 : b2 < 2) (h3 : b3 < 2)
    (h4 : b4 < 2) (h5 : b5 < 2) (h6 : b6 < 2) (h7 : b7 < 2) :
    b0 + 2 * (b1 + 2 * (b2 + 2 * (b3 + 2 * (b4 + 2 * (b5 + 2 * (b6 + 2 * b7)))))) =
      (b0 <<< 0) ||| (b1 <<< 1) ||| (b2 <<< 2) ||| (b3 <<< 3) |||
      (b4 <<< 4) ||| (b5 <<< 5) ||| (b6 <<< 6) ||| (b7 <<< 7) := by
  have e0 : b0 <<< 0 = b0 := by simp [Nat.shiftLeft_eq]
  have e1 := or_shiftLeft_eq_add (acc := b0) (b := b1) (k := 1) (by omega) h1
  have e2 := or_shiftLeft_eq_add (acc := b0 + b1 * 2 ^ 1) (b := b2) (k := 2) (by omega) h2
  have e3 :=
    or_shiftLeft_eq_add (acc := b0 + b1 * 2 ^ 1 + b2 * 2 ^ 2) (b := b3) (k := 3) (by omega) h3
  have e4 :=
    or_shiftLeft_eq_add (acc := b0 + b1 * 2 ^ 1 + b2 * 2 ^ 2 + b3 * 2 ^ 3) (b := b4) (k := 4)
      (by omega) h4
  have e5 :=
    or_shiftLeft_eq_add
      (acc := b0 + b1 * 2 ^ 1 + b2 * 2 ^ 2 + b3 * 2 ^ 3 + b4 * 2 ^ 4) (b := b5) (k := 5)
      (by omega) h5
  have e6 :=
    or_shiftLeft_eq_add
      (acc := b0 + b1 * 2 ^ 1 + b2 * 2 ^ 2 + b3 * 2 ^ 3 + b4 * 2 ^ 4 + b5 * 2 ^ 5) (b := b6)
      (k := 6) (by omega) h6
  have e7 :=
    or_shiftLeft_eq_add
      (acc :=
        b0 + b1 * 2 ^ 1 + b2 * 2 ^ 2 + b3 * 2 ^ 3 + b4 * 2 ^ 4 + b5 * 2 ^ 5 + b6 * 2 ^ 6)
      (b := b7) (k := 7) (by omega) h7
  rw [e0, e1, e2, e3, e4, e5, e6, e7]
  omega

private theorem packBits8_eq (bits : List Nat) (hbits : ∀ b ∈ bits, b < 2) :
    packBits8 bits = bitsToBytes (Array.mk bits) := by
  unfold bitsToBytes
  simp only [← arrayGetDFast_eq (Array.mk bits), arrayGetDFast]
  suffices ∀ n (xs : List Nat), xs.length = n → (∀ b ∈ xs, b < 2) →
      packBits8 xs =
        (List.range (xs.length / 8)).map fun byteIdx =>
          BitVec.ofNat 8
            ((xs.getD (8 * byteIdx + 0) 0 <<< 0) |||
             (xs.getD (8 * byteIdx + 1) 0 <<< 1) |||
             (xs.getD (8 * byteIdx + 2) 0 <<< 2) |||
             (xs.getD (8 * byteIdx + 3) 0 <<< 3) |||
             (xs.getD (8 * byteIdx + 4) 0 <<< 4) |||
             (xs.getD (8 * byteIdx + 5) 0 <<< 5) |||
             (xs.getD (8 * byteIdx + 6) 0 <<< 6) |||
             (xs.getD (8 * byteIdx + 7) 0 <<< 7)) from
    this bits.length bits rfl hbits
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro xs hlen hxs
    rcases xs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, rest⟩⟩⟩⟩⟩⟩⟩⟩
    · simp [packBits8]
    · simp [packBits8]
    · simp [packBits8]
    · simp [packBits8]
    · simp [packBits8]
    · simp [packBits8]
    · simp [packBits8]
    · simp [packBits8]
    · have hdiv : (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest).length / 8 =
          rest.length / 8 + 1 := by simp; omega
      simp only [packBits8, withForcedNat_eq, hdiv, List.range_succ_eq_map, List.map_cons,
        List.map_map, List.cons.injEq]
      have hb0 : b0 < 2 := hxs b0 (by simp)
      have hb1 : b1 < 2 := hxs b1 (by simp)
      have hb2 : b2 < 2 := hxs b2 (by simp)
      have hb3 : b3 < 2 := hxs b3 (by simp)
      have hb4 : b4 < 2 := hxs b4 (by simp)
      have hb5 : b5 < 2 := hxs b5 (by simp)
      have hb6 : b6 < 2 := hxs b6 (by simp)
      have hb7 : b7 < 2 := hxs b7 (by simp)
      have hrest : ∀ b ∈ rest, b < 2 := fun b hb => hxs b (by simp [hb])
      refine ⟨congrArg (BitVec.ofNat 8) (pack8_or_eq_horner hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7), ?_⟩
      rw [ih rest.length (by simp at hlen; omega) rest rfl hrest]
      apply List.map_congr_left
      intro byteIdx _
      dsimp only [Function.comp]
      have s0 : 8 * (byteIdx + 1) = 8 * byteIdx + 8 := by omega
      have s1 : 8 * (byteIdx + 1) + 1 = (8 * byteIdx + 1) + 8 := by omega
      have s2 : 8 * (byteIdx + 1) + 2 = (8 * byteIdx + 2) + 8 := by omega
      have s3 : 8 * (byteIdx + 1) + 3 = (8 * byteIdx + 3) + 8 := by omega
      have s4 : 8 * (byteIdx + 1) + 4 = (8 * byteIdx + 4) + 8 := by omega
      have s5 : 8 * (byteIdx + 1) + 5 = (8 * byteIdx + 5) + 8 := by omega
      have s6 : 8 * (byteIdx + 1) + 6 = (8 * byteIdx + 6) + 8 := by omega
      have s7 : 8 * (byteIdx + 1) + 7 = (8 * byteIdx + 7) + 8 := by omega
      have g8 : ∀ m,
          (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest).getD (m + 8) 0 =
            rest.getD m 0 := fun _ => rfl
      simp only [Nat.add_zero]
      rw [s7, s6, s5, s4, s3, s2, s1, s0]
      simp only [g8]

@[expose] def coeffBits : Nat → Nat → List Nat
  | 0, _ => []
  | d + 1, coeff => (coeff % 2) :: coeffBits d (coeff / 2)

private theorem coeffBits_length : ∀ (d coeff : Nat), (coeffBits d coeff).length = d
  | 0, _ => rfl
  | d + 1, coeff => by simp [coeffBits, coeffBits_length d]

private theorem coeffBits_getElem :
    ∀ (d coeff : Nat) {k : Nat} (hk : k < d),
      (coeffBits d coeff)[k]'(by rw [coeffBits_length]; exact hk) = (coeff >>> k) &&& 1
  | 0, _, _, hk => absurd hk (by omega)
  | d + 1, coeff, 0, _ => by simp [coeffBits, Nat.and_one_is_mod]
  | d + 1, coeff, k + 1, hk => by
    simp only [coeffBits, List.getElem_cons_succ]
    rw [coeffBits_getElem d (coeff / 2) (by omega)]
    simp [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, Nat.pow_succ']

private theorem coeffBits_mem_lt_two :
    ∀ (d coeff b : Nat), b ∈ coeffBits d coeff → b < 2
  | 0, _, _, hb => nomatch hb
  | d + 1, coeff, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hmem
    · omega
    · exact coeffBits_mem_lt_two d (coeff / 2) b hmem

private theorem flatMap_coeffBits_length (d : Nat) (xs : List Nat) :
    (xs.flatMap (coeffBits d)).length = xs.length * d := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, coeffBits_length, List.length_cons, ih,
      Nat.succ_mul, Nat.add_comm]

private theorem flatMap_coeffBits_getElem (d : Nat) (xs : List Nat) {idx : Nat}
    (hidx : idx < xs.length * d) :
    (xs.flatMap (coeffBits d))[idx]'(by rw [flatMap_coeffBits_length]; exact hidx) =
      ((xs[idx / d]'(by
          have hd : 0 < d := Nat.pos_of_ne_zero fun h0 => by subst h0; simp at hidx
          exact (Nat.div_lt_iff_lt_mul hd).mpr hidx)) >>> (idx % d)) &&& 1 := by
  have hd : 0 < d := Nat.pos_of_ne_zero fun h0 => by subst h0; simp at hidx
  induction xs generalizing idx with
  | nil => simp at hidx
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    by_cases hlt : idx < d
    · have hlen_c : idx < (coeffBits d x).length := by rw [coeffBits_length]; exact hlt
      have hdiv : idx / d = 0 := Nat.div_eq_of_lt hlt
      have hmod : idx % d = idx := Nat.mod_eq_of_lt hlt
      rw [List.getElem_append_left hlen_c, coeffBits_getElem d x hlt]
      simp [hdiv, hmod]
    · have hge : d ≤ idx := Nat.le_of_not_lt hlt
      have hlen_c : (coeffBits d x).length ≤ idx := by rw [coeffBits_length]; exact hge
      have hidx' : idx < xs.length * d + d := by simpa [Nat.succ_mul] using hidx
      have hsub : idx - d < xs.length * d := by omega
      have hdiv : idx / d = (idx - d) / d + 1 := Nat.div_eq_sub_div hd hge
      have hmod : idx % d = (idx - d) % d := Nat.mod_eq_sub_mod hge
      rw [List.getElem_append_right hlen_c]
      have hlen_eq := coeffBits_length d x
      simp only [hlen_eq]
      rw [ih hsub]
      simp [hdiv, hmod]

@[expose] def byteEncodeFast (d : Nat) (f : Poly) : List (BitVec 8) :=
  forcePoly f fun f =>
  forceListBV8 (packBits8 ((pad256 f.toList).flatMap (coeffBits d))) id

theorem byteEncodeFast_eq (d : Nat) (f : Poly) : byteEncodeFast d f = byteEncode d f := by
  unfold byteEncodeFast byteEncode
  rw [forcePoly_eq, forceListBV8_eq, id_eq,
    packBits8_eq _ (fun b hb => by
      rcases List.mem_flatMap.mp hb with ⟨x, _, hbx⟩
      exact coeffBits_mem_lt_two d x b hbx)]
  congr 1
  apply Array.ext
  · rw [Array.size_ofFn]
    change ((pad256 f.toList).flatMap (coeffBits d)).length = 256 * d
    rw [flatMap_coeffBits_length, pad256_length]
  · intro idx h1 h2
    have hidx : idx < (pad256 f.toList).length * d := by
      rw [pad256_length]; simpa using h2
    have hdiv256 : idx / d < 256 := by
      rw [pad256_length] at hidx
      have hd : 0 < d := Nat.pos_of_ne_zero fun h0 => by subst h0; simp at hidx
      exact (Nat.div_lt_iff_lt_mul hd).mpr hidx
    simp only [Array.getElem_ofFn]
    change ((pad256 f.toList).flatMap (coeffBits d))[idx]'h1 = _
    rw [flatMap_coeffBits_getElem d (pad256 f.toList) hidx,
      pad256_getElem f.toList hdiv256, ← arrayGetDFast_eq f, arrayGetDFast]

@[expose] def bitsValLE : Nat → List Nat → Nat
  | 0, _ => 0
  | d + 1, b :: bs => (b % 2) + 2 * bitsValLE d bs
  | _ + 1, [] => 0

private theorem bitsValLE_lt_two_pow : ∀ (d : Nat) (bits : List Nat), bitsValLE d bits < 2 ^ d
  | 0, _ => by simp [bitsValLE]
  | d + 1, [] => by simp [bitsValLE]; exact Nat.two_pow_pos _
  | d + 1, b :: bs => by
    have ih := bitsValLE_lt_two_pow d bs
    simp only [bitsValLE, Nat.pow_succ]
    omega

private theorem bitsValLE_succ :
    ∀ (d : Nat) (bits : List Nat),
      bitsValLE (d + 1) bits = bitsValLE d bits + (bits.getD d 0 % 2) * 2 ^ d
  | 0, [] => by simp [bitsValLE]
  | 0, b :: bs => by simp [bitsValLE]
  | d + 1, [] => by simp [bitsValLE]
  | d + 1, b :: bs => by
    simp only [bitsValLE, bitsValLE_succ d bs]
    have hget : (b :: bs).getD (d + 1) 0 = bs.getD d 0 := rfl
    rw [hget, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm _ 2]
    omega

private theorem bitsValLE_eq_foldl (bits : List Nat) (hbits : ∀ j, bits.getD j 0 < 2) :
    ∀ (d : Nat),
      bitsValLE d bits = (List.range d).foldl (fun acc k => acc ||| (bits.getD k 0 <<< k)) 0
  | 0 => rfl
  | d + 1 => by
    rw [bitsValLE_succ d bits, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil, ← bitsValLE_eq_foldl bits hbits d]
    have hb : bits.getD d 0 < 2 := hbits d
    rw [Nat.mod_eq_of_lt hb, or_shiftLeft_eq_add (bitsValLE_lt_two_pow d bits) hb]

@[expose] def decodeChunks (d : Nat) : Nat → List Nat → List Nat
  | 0, _ => []
  | n + 1, bits =>
    withForcedNat (bitsValLE d bits) fun v =>
    withDrop d bits fun rest =>
      v :: decodeChunks d n rest

private theorem decodeChunks_length (d : Nat) :
    ∀ (n : Nat) (bits : List Nat), (decodeChunks d n bits).length = n
  | 0, _ => rfl
  | n + 1, bits => by simp [decodeChunks, withForcedNat_eq, withDrop_eq, decodeChunks_length d n]

private theorem decodeChunks_getElem (d : Nat) :
    ∀ (n : Nat) (bits : List Nat) (_hbits : ∀ j, bits.getD j 0 < 2) {i : Nat} (hi : i < n),
      (decodeChunks d n bits)[i]'(by rw [decodeChunks_length]; exact hi) =
        (List.range d).foldl (fun acc k => acc ||| (bits.getD (i * d + k) 0 <<< k)) 0
  | 0, _, _, _, hi => absurd hi (by omega)
  | n + 1, bits, hbits, 0, _ => by
    simp [decodeChunks, withForcedNat_eq, withDrop_eq, bitsValLE_eq_foldl bits hbits d]
  | n + 1, bits, hbits, i + 1, hi => by
    simp only [decodeChunks, withForcedNat_eq, withDrop_eq, List.getElem_cons_succ]
    have hbits' : ∀ j, (bits.drop d).getD j 0 < 2 := by
      intro j; rw [list_getD_drop]; exact hbits (d + j)
    rw [decodeChunks_getElem d n (bits.drop d) hbits' (by omega)]
    congr 1
    funext acc k
    rw [list_getD_drop]
    have hidx : d + (i * d + k) = (i + 1) * d + k := by
      rw [Nat.succ_mul, Nat.add_comm (i * d) d, Nat.add_assoc]
    rw [hidx]

@[expose] def byteDecodeRawFast (d : Nat) (bs : List (BitVec 8)) : Poly :=
  forceListBV8 bs fun bs' =>
  forceListNat (bytesToBitsList bs') fun bits =>
  forceListNat (decodeChunks d 256 bits) Array.mk

theorem byteDecodeRawFast_eq (d : Nat) (bs : List (BitVec 8)) :
    byteDecodeRawFast d bs = byteDecodeRaw d bs := by
  unfold byteDecodeRawFast byteDecodeRaw
  rw [forceListBV8_eq, forceListNat_eq, forceListNat_eq]
  apply Array.ext
  · simp [decodeChunks_length]
  · intro i h1 h2
    have hi : i < 256 := by simpa using h2
    simp only [Array.getElem_ofFn]
    change (decodeChunks d 256 (bytesToBitsList bs))[i]'h1 = _
    rw [decodeChunks_getElem d 256 (bytesToBitsList bs) (bytesToBitsList_getD_lt_two bs) hi]
    congr 1
    funext acc k
    rw [bytesToBitsList_getD]

@[expose] def byteDecodeModFast (d : Nat) (bs : List (BitVec 8)) : Poly :=
  forcePoly (arrayMapFast (· % mlkemQ) (byteDecodeRawFast d bs)) id

theorem byteDecodeModFast_eq (d : Nat) (bs : List (BitVec 8)) :
    byteDecodeModFast d bs = byteDecodeMod d bs := by
  unfold byteDecodeModFast byteDecodeMod
  simp only [forcePoly_eq, id_eq, arrayMapFast_eq, byteDecodeRawFast_eq]

@[expose] def compressCoeffFast (d x : Nat) : Nat :=
  let p := 2 ^ d
  ((((x % mlkemQ) * p) + 1664) / mlkemQ) % p

private theorem compressCoeffFast_eq (d x : Nat) : compressCoeffFast d x = compressCoeff d x := by
  unfold compressCoeffFast compressCoeff
  simp [Nat.shiftLeft_eq]

@[expose] def decompressCoeffFast (d y : Nat) : Nat :=
  if d == 0 then 0 else ((y * mlkemQ) + 2 ^ (d - 1)) / (2 ^ d)

private theorem decompressCoeffFast_eq (d y : Nat) :
    decompressCoeffFast d y = decompressCoeff d y := by
  unfold decompressCoeffFast decompressCoeff
  simp [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]

@[expose] def compressAndEncodeFast (d : Nat) (f : Poly) : List (BitVec 8) :=
  forcePoly f fun f' => byteEncodeFast d (arrayMapFast (compressCoeffFast d) f')

theorem compressAndEncodeFast_eq (d : Nat) (f : Poly) :
    compressAndEncodeFast d f = compressAndEncode d f := by
  unfold compressAndEncodeFast compressAndEncode
  simp only [forcePoly_eq, arrayMapFast_eq, byteEncodeFast_eq,
    show compressCoeffFast d = compressCoeff d from funext (compressCoeffFast_eq d)]

@[expose] def decodeAndDecompressFast (d : Nat) (bs : List (BitVec 8)) : Poly :=
  forcePoly (arrayMapFast (decompressCoeffFast d) (byteDecodeRawFast d bs)) id

theorem decodeAndDecompressFast_eq (d : Nat) (bs : List (BitVec 8)) :
    decodeAndDecompressFast d bs = decodeAndDecompress d bs := by
  unfold decodeAndDecompressFast decodeAndDecompress
  simp only [forcePoly_eq, id_eq, arrayMapFast_eq, byteDecodeRawFast_eq,
    show decompressCoeffFast d = decompressCoeff d from funext (decompressCoeffFast_eq d)]

@[expose] def cbd2Chunks : Nat → List Nat → List Nat
  | 0, _ => []
  | n + 1, bits =>
    withDrop 4 bits fun rest =>
      let a := bits.getD 0 0 + bits.getD 1 0
      let b := bits.getD 2 0 + bits.getD 3 0
      ((a + mlkemQ - b) % mlkemQ) :: cbd2Chunks n rest

private theorem cbd2Chunks_length :
    ∀ (n : Nat) (bits : List Nat), (cbd2Chunks n bits).length = n
  | 0, _ => rfl
  | n + 1, bits => by simp [cbd2Chunks, withDrop_eq, cbd2Chunks_length n]

private theorem cbd2Chunks_getElem :
    ∀ (n : Nat) (bits : List Nat) {i : Nat} (hi : i < n),
      (cbd2Chunks n bits)[i]'(by rw [cbd2Chunks_length]; exact hi) =
        let a := bits.getD (4 * i) 0 + bits.getD (4 * i + 1) 0
        let b := bits.getD (4 * i + 2) 0 + bits.getD (4 * i + 3) 0
        (a + mlkemQ - b) % mlkemQ
  | 0, _, _, hi => absurd hi (by omega)
  | n + 1, bits, 0, _ => by simp [cbd2Chunks, withDrop_eq]
  | n + 1, bits, i + 1, hi => by
    simp only [cbd2Chunks, withDrop_eq, List.getElem_cons_succ]
    rw [cbd2Chunks_getElem n (bits.drop 4) (by omega)]
    simp only [list_getD_drop]
    have s0 : 4 + 4 * i = 4 * (i + 1) := by omega
    have s1 : 4 + (4 * i + 1) = 4 * (i + 1) + 1 := by omega
    have s2 : 4 + (4 * i + 2) = 4 * (i + 1) + 2 := by omega
    have s3 : 4 + (4 * i + 3) = 4 * (i + 1) + 3 := by omega
    rw [s0, s1, s2, s3]

@[expose] def samplePolyCbd2Fast (bs : List (BitVec 8)) : Poly :=
  forceListBV8 bs fun bs' =>
  forceListNat (bytesToBitsList bs') fun bits =>
  forceListNat (cbd2Chunks 256 bits) Array.mk

theorem samplePolyCbd2Fast_eq (bs : List (BitVec 8)) :
    samplePolyCbd2Fast bs = samplePolyCbd2 bs := by
  unfold samplePolyCbd2Fast samplePolyCbd2
  rw [forceListBV8_eq, forceListNat_eq, forceListNat_eq]
  apply Array.ext
  · simp [cbd2Chunks_length]
  · intro i h1 h2
    have hi : i < 256 := by simpa using h2
    simp only [Array.getElem_ofFn]
    change (cbd2Chunks 256 (bytesToBitsList bs))[i]'h1 = _
    rw [cbd2Chunks_getElem 256 (bytesToBitsList bs) hi]
    simp only [bytesToBitsList_getD]

@[expose] def sampleVecCbd2Fast (k : Nat) (sigma : List (BitVec 8)) (ds : Nat) : Array Poly :=
  forceListBV8 (sigma.take 32) fun sig32 =>
  forcePolyVec
    (arrayOfFnFast k fun i =>
      samplePolyCbd2Fast (shake256Fast 128 (sig32 ++ [BitVec.ofNat 8 (ds + i)])))
    id

theorem sampleVecCbd2Fast_eq (k : Nat) (sigma : List (BitVec 8)) (ds : Nat) :
    sampleVecCbd2Fast k sigma ds = sampleVecCbd2 k sigma ds := by
  unfold sampleVecCbd2Fast sampleVecCbd2
  simp only [forceListBV8_eq, forcePolyVec_eq, id_eq, arrayOfFnFast_eq,
    samplePolyCbd2Fast_eq, shake256Fast_eq]

theorem toByteVec_toList_of_length {n : Nat} {bs : List (BitVec 8)} (h : bs.length = n) :
    (toByteVec n bs).toList = bs := by
  subst h
  apply List.ext_getElem
  · simp [toByteVec]
  · intro i h1 h2
    simp [toByteVec, List.getD_eq_getElem?_getD, h2]

/-! ## 3. Computable Incremental `SampleNTT` (`3..6` Blocks) Bridged to Unbounded `sampleNtt` -/

@[expose] def parseRej12CandidatesFast : List (BitVec 8) → List Nat
  | b0 :: b1 :: b2 :: rest =>
    let d1 := b0.toNat + 256 * (b1.toNat % 16)
    let d2 := (b1.toNat / 16) + 16 * b2.toNat
    (if d1 < mlkemQ then [d1] else []) ++
      (if d2 < mlkemQ then [d2] else []) ++
      parseRej12CandidatesFast rest
  | _ => []

private theorem parseRej12CandidatesFast_eq (bs : List (BitVec 8)) :
    parseRej12CandidatesFast bs = parseRej12Candidates bs := by
  unfold parseRej12Candidates
  have hsz : bs.toArray.size = bs.length := rfl
  have hg (i : Nat) : bs.toArray.getD i 0#8 = bs.getD i 0#8 := (arrayGetDFast_eq bs.toArray i 0#8).symm
  simp only [hsz, hg]
  suffices ∀ n (xs : List (BitVec 8)), xs.length = n →
      parseRej12CandidatesFast xs =
        ((List.range (xs.length / 3)).map fun t =>
          let b0 := (xs.getD (3 * t) 0#8).toNat
          let b1 := (xs.getD (3 * t + 1) 0#8).toNat
          let b2 := (xs.getD (3 * t + 2) 0#8).toNat
          let d1 := b0 + 256 * (b1 % 16)
          let d2 := (b1 / 16) + 16 * b2
          (if d1 < mlkemQ then [d1] else []) ++
            (if d2 < mlkemQ then [d2] else [])).flatten from
    this bs.length bs rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro xs hlen
    rcases xs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, rest⟩⟩⟩
    · simp [parseRej12CandidatesFast]
    · simp [parseRej12CandidatesFast]
    · simp [parseRej12CandidatesFast]
    · have hdiv : (b0 :: b1 :: b2 :: rest).length / 3 = rest.length / 3 + 1 := by simp; omega
      simp only [parseRej12CandidatesFast, hdiv, List.range_succ_eq_map, List.map_cons,
        List.flatten_cons, List.map_map, List.append_assoc]
      congr 2
      rw [ih rest.length (by simp at hlen; omega) rest rfl]
      congr 1

private theorem keccakExtractRate_21_length (s : KeccakState) :
    (keccakExtractRate 21 s).length = 168 := by
  have hr : List.range 21 =
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] := rfl
  unfold keccakExtractRate
  rw [hr]
  rfl

private theorem keccakSqueezeBlocks_21_length :
    ∀ (m : Nat) (s : KeccakState), (keccakSqueezeBlocks 21 m s).length = 168 * m
  | 0, _ => rfl
  | 1, s => by simp [keccakSqueezeBlocks, keccakExtractRate_21_length]
  | m + 2, s => by
    simp only [keccakSqueezeBlocks, List.length_append, keccakExtractRate_21_length,
      keccakSqueezeBlocks_21_length (m + 1) (keccakF1600 s)]
    omega

private theorem keccakSqueezeBlocks_21_prefix :
    ∀ (m n : Nat) (s : KeccakState), m ≤ n →
      ∃ tail, keccakSqueezeBlocks 21 n s = keccakSqueezeBlocks 21 m s ++ tail
  | 0, n, s, _ => ⟨keccakSqueezeBlocks 21 n s, rfl⟩
  | 1, 0, _, h => absurd h (by omega)
  | 1, 1, s, _ => ⟨[], by simp [keccakSqueezeBlocks]⟩
  | 1, n + 2, s, _ => ⟨keccakSqueezeBlocks 21 (n + 1) (keccakF1600 s), rfl⟩
  | m + 2, 0, _, h => absurd h (by omega)
  | m + 2, 1, _, h => absurd h (by omega)
  | m + 2, n + 2, s, h => by
    obtain ⟨tail, htail⟩ :=
      keccakSqueezeBlocks_21_prefix (m + 1) (n + 1) (keccakF1600 s) (by omega)
    exact ⟨tail, by simp only [keccakSqueezeBlocks, htail, List.append_assoc]⟩

private theorem toArray_append_getD_left {a b : List (BitVec 8)} {idx : Nat}
    (h : idx < a.length) :
    (a ++ b).toArray.getD idx 0#8 = a.toArray.getD idx 0#8 := by
  have hab : idx < a.length + b.length := by omega
  simp [Array.getD, h, hab, List.getElem_append_left h]

private theorem parseRej12Candidates_prefix {a b : List (BitVec 8)} {k : Nat}
    (ha_len : a.length = 3 * k) :
    ∃ rest, parseRej12Candidates (a ++ b) = parseRej12Candidates a ++ rest := by
  have hsa : a.toArray.size / 3 = k := by simp [ha_len]
  have hsab : (a ++ b).toArray.size / 3 = k + b.length / 3 := by simp [ha_len]; omega
  unfold parseRej12Candidates
  dsimp only
  rw [hsa, hsab, List.range_add, List.map_append, List.flatten_append]
  refine ⟨_, congrArg (· ++ _) (congrArg List.flatten (List.map_congr_left fun t ht => ?_))⟩
  have htk : t < k := List.mem_range.mp ht
  have h0 : 3 * t < a.length := by omega
  have h1 : 3 * t + 1 < a.length := by omega
  have h2 : 3 * t + 2 < a.length := by omega
  simp only [toArray_append_getD_left h0, toArray_append_getD_left h1, toArray_append_getD_left h2]

private theorem shake128_take_of_le (cap : Nat) {seed34 : List (BitVec 8)} {m n : Nat}
    (hmn : m ≤ n)
    (hge : cap ≤ (parseRej12Candidates (shake128FirstBlocks seed34 m)).length) :
    (parseRej12Candidates (shake128FirstBlocks seed34 n)).take cap =
      (parseRej12Candidates (shake128FirstBlocks seed34 m)).take cap := by
  unfold shake128FirstBlocks at hge ⊢
  set s0 := keccakAbsorb 21 0x1f#8 seed34
  obtain ⟨tail, htail⟩ := keccakSqueezeBlocks_21_prefix m n s0 hmn
  have hlen : (keccakSqueezeBlocks 21 m s0).length = 3 * (56 * m) := by
    rw [keccakSqueezeBlocks_21_length]; omega
  obtain ⟨rest, hrest⟩ := parseRej12Candidates_prefix (b := tail) hlen
  rw [htail, hrest, List.take_append_of_le_length hge]

private theorem sampleNtt_eq_take256 {seed34 : List (BitVec 8)} {extra : Nat}
    (hge : 256 ≤ (parseRej12Candidates (shake128FirstBlocks seed34 (extra + 3))).length) :
    sampleNtt seed34 =
      ((parseRej12Candidates (shake128FirstBlocks seed34 (extra + 3))).take 256).toArray := by
  have hterm : Shake128SeedTerminates seed34 := ⟨extra, hge⟩
  have hdite : sampleNtt seed34 =
      ((parseRej12Candidates
        (shake128FirstBlocks seed34 (Classical.choose hterm + 3))).take 256).toArray := by
    classical exact dite_eq_left_of_eq_true (eq_true hterm)
  rw [hdite]
  apply congrArg List.toArray
  have hchoose := Classical.choose_spec hterm
  rcases Nat.le_total (Classical.choose hterm + 3) (extra + 3) with hle | hle
  · exact (shake128_take_of_le 256 hle hchoose).symm
  · exact shake128_take_of_le 256 hle hge

@[expose] def sampleNttFast (seed34 : List (BitVec 8)) : Poly × Bool :=
  forceArrayBV64 (keccakAbsorbFast 21 0x1f#8 seed34) fun s0 =>
  forceListBV8 (keccakExtractRateFast 21 s0) fun b0 =>
  forceArrayBV64 (keccakF1600Fast s0) fun s1 =>
  forceListBV8 (keccakExtractRateFast 21 s1) fun b1 =>
  forceArrayBV64 (keccakF1600Fast s1) fun s2 =>
  forceListBV8 (keccakExtractRateFast 21 s2) fun b2 =>
  forceListNat (parseRej12CandidatesFast (b0 ++ (b1 ++ b2))) fun c3 =>
  if 256 ≤ c3.length then
    (Array.mk (c3.take 256), true)
  else
    forceArrayBV64 (keccakF1600Fast s2) fun s3 =>
    forceListBV8 (keccakExtractRateFast 21 s3) fun b3 =>
    forceListNat (parseRej12CandidatesFast (b0 ++ (b1 ++ (b2 ++ b3)))) fun c4 =>
    if 256 ≤ c4.length then
      (Array.mk (c4.take 256), true)
    else
      forceArrayBV64 (keccakF1600Fast s3) fun s4 =>
      forceListBV8 (keccakExtractRateFast 21 s4) fun b4 =>
      forceListNat (parseRej12CandidatesFast (b0 ++ (b1 ++ (b2 ++ (b3 ++ b4))))) fun c5 =>
      if 256 ≤ c5.length then
        (Array.mk (c5.take 256), true)
      else
        forceArrayBV64 (keccakF1600Fast s4) fun s5 =>
        forceListBV8 (keccakExtractRateFast 21 s5) fun b5 =>
        forceListNat (parseRej12CandidatesFast (b0 ++ (b1 ++ (b2 ++ (b3 ++ (b4 ++ b5)))))) fun c6 =>
        if 256 ≤ c6.length then
          (Array.mk (c6.take 256), true)
        else
          (zeroPoly, false)

private theorem array_mk_eq_toArray {α : Type} (xs : List α) : Array.mk xs = xs.toArray := by
  apply Array.ext <;> simp

theorem sampleNttFast_eq_of_snd {seed34 : List (BitVec 8)}
    (hok : (sampleNttFast seed34).2 = true) :
    (sampleNttFast seed34).1 = sampleNtt seed34 := by
  unfold sampleNttFast at hok ⊢
  simp only [forceArrayBV64_eq, forceListBV8_eq, forceListNat_eq,
    parseRej12CandidatesFast_eq] at hok ⊢
  set s0 := keccakAbsorbFast 21 0x1f#8 seed34
  have hs3 : keccakExtractRateFast 21 s0 ++
      (keccakExtractRateFast 21 (keccakF1600Fast s0) ++
        keccakExtractRateFast 21 (keccakF1600Fast (keccakF1600Fast s0))) =
      shake128FirstBlocks seed34 3 := by
    unfold shake128FirstBlocks
    rw [← keccakAbsorbFast_eq, ← keccakSqueezeBlocksFast_eq 21 3 s0]
    simp only [keccakSqueezeBlocksFast, forceArrayBV64_eq]
  have hs4 : keccakExtractRateFast 21 s0 ++
      (keccakExtractRateFast 21 (keccakF1600Fast s0) ++
        (keccakExtractRateFast 21 (keccakF1600Fast (keccakF1600Fast s0)) ++
          keccakExtractRateFast 21 (keccakF1600Fast (keccakF1600Fast (keccakF1600Fast s0))))) =
      shake128FirstBlocks seed34 4 := by
    unfold shake128FirstBlocks
    rw [← keccakAbsorbFast_eq, ← keccakSqueezeBlocksFast_eq 21 4 s0]
    simp only [keccakSqueezeBlocksFast, forceArrayBV64_eq]
  have hs5 : keccakExtractRateFast 21 s0 ++
      (keccakExtractRateFast 21 (keccakF1600Fast s0) ++
        (keccakExtractRateFast 21 (keccakF1600Fast (keccakF1600Fast s0)) ++
          (keccakExtractRateFast 21 (keccakF1600Fast (keccakF1600Fast (keccakF1600Fast s0))) ++
            keccakExtractRateFast 21
              (keccakF1600Fast (keccakF1600Fast (keccakF1600Fast (keccakF1600Fast s0))))))) =
      shake128FirstBlocks seed34 5 := by
    unfold shake128FirstBlocks
    rw [← keccakAbsorbFast_eq, ← keccakSqueezeBlocksFast_eq 21 5 s0]
    simp only [keccakSqueezeBlocksFast, forceArrayBV64_eq]
  have hs6 : keccakExtractRateFast 21 s0 ++
      (keccakExtractRateFast 21 (keccakF1600Fast s0) ++
        (keccakExtractRateFast 21 (keccakF1600Fast (keccakF1600Fast s0)) ++
          (keccakExtractRateFast 21 (keccakF1600Fast (keccakF1600Fast (keccakF1600Fast s0))) ++
            (keccakExtractRateFast 21
              (keccakF1600Fast (keccakF1600Fast (keccakF1600Fast (keccakF1600Fast s0)))) ++
              keccakExtractRateFast 21
                (keccakF1600Fast
                  (keccakF1600Fast (keccakF1600Fast (keccakF1600Fast (keccakF1600Fast s0))))))))) =
      shake128FirstBlocks seed34 6 := by
    unfold shake128FirstBlocks
    rw [← keccakAbsorbFast_eq, ← keccakSqueezeBlocksFast_eq 21 6 s0]
    simp only [keccakSqueezeBlocksFast, forceArrayBV64_eq]
  rw [hs3, hs4, hs5, hs6] at hok ⊢
  by_cases h3 : 256 ≤ (parseRej12Candidates (shake128FirstBlocks seed34 3)).length
  · simp only [h3, ↓reduceIte]
    exact (array_mk_eq_toArray _).trans (sampleNtt_eq_take256 (extra := 0) h3).symm
  · simp only [h3, ↓reduceIte] at hok ⊢
    by_cases h4 : 256 ≤ (parseRej12Candidates (shake128FirstBlocks seed34 4)).length
    · simp only [h4, ↓reduceIte]
      exact (array_mk_eq_toArray _).trans (sampleNtt_eq_take256 (extra := 1) h4).symm
    · simp only [h4, ↓reduceIte] at hok ⊢
      by_cases h5 : 256 ≤ (parseRej12Candidates (shake128FirstBlocks seed34 5)).length
      · simp only [h5, ↓reduceIte]
        exact (array_mk_eq_toArray _).trans (sampleNtt_eq_take256 (extra := 2) h5).symm
      · simp only [h5, ↓reduceIte] at hok ⊢
        by_cases h6 : 256 ≤ (parseRej12Candidates (shake128FirstBlocks seed34 6)).length
        · simp only [h6, ↓reduceIte]
          exact (array_mk_eq_toArray _).trans (sampleNtt_eq_take256 (extra := 3) h6).symm
        · simp only [h6, ↓reduceIte] at hok
          cases hok

/-! ### Single-Pass Matrix Checkers and Samplers -/

@[expose] def checkSampleNttEntry (seed34 : List (BitVec 8)) (exp : Poly) : Bool :=
  match sampleNttFast seed34 with
  | (p, true) => p.toList == exp.toList
  | (_, false) => false

theorem checkSampleNttEntry_sound {seed34 : List (BitVec 8)} {exp : Poly}
    (h : checkSampleNttEntry seed34 exp = true) :
    sampleNtt seed34 = exp := by
  unfold checkSampleNttEntry at h
  rcases hsn : sampleNttFast seed34 with ⟨p, ok⟩
  rw [hsn] at h
  cases ok with
  | false => cases h
  | true =>
    have hp : p = exp := by
      rcases p with ⟨xs⟩
      rcases exp with ⟨ys⟩
      exact congrArg Array.mk (beq_iff_eq.mp h)
    have hfst : (sampleNttFast seed34).1 = p := by rw [hsn]
    have hsnd : (sampleNttFast seed34).2 = true := by rw [hsn]
    rw [← sampleNttFast_eq_of_snd hsnd, hfst, hp]

@[expose] def checkMatrixRowFast (k r : Nat) (rho : List (BitVec 8)) (transpose : Bool)
    (rowExp : Array Poly) : Bool :=
  (rowExp.toList.length == k) &&
  forceListBV8 (rho.take 32) fun rho32 =>
  (List.range k).all fun c =>
    let (i, j) := if transpose then (c, r) else (r, c)
    checkSampleNttEntry (rho32 ++ [BitVec.ofNat 8 i, BitVec.ofNat 8 j])
      (arrayGetDFast rowExp c zeroPoly)

theorem checkMatrixRowFast_sound {k r : Nat} {rho : List (BitVec 8)} {transpose : Bool}
    {rowExp : Array Poly} (h : checkMatrixRowFast k r rho transpose rowExp = true) :
    rowExp = Array.ofFn (n := k) fun ⟨c, _⟩ =>
      let (i, j) := if transpose then (c, r) else (r, c)
      sampleNtt (rho.take 32 ++ [BitVec.ofNat 8 i, BitVec.ofNat 8 j]) := by
  unfold checkMatrixRowFast at h
  rw [forceListBV8_eq] at h
  rcases (Bool.and_eq_true _ _).mp h with ⟨hlen', hall⟩
  have hlen : rowExp.size = k := beq_iff_eq.mp hlen'
  apply Array.ext
  · rw [hlen, Array.size_ofFn]
  · intro c hc1 hc2
    rw [Array.getElem_ofFn]
    have hc : c < k := by simpa using hc2
    have hmem := List.all_eq_true.mp hall c (List.mem_range.mpr hc)
    rcases rowExp with ⟨xs⟩
    have hc_xs : c < xs.length := hc1
    cases transpose <;>
      · dsimp only at hmem ⊢
        rw [checkSampleNttEntry_sound hmem]
        simp [arrayGetDFast, List.getD_eq_getElem?_getD, hc_xs]

@[expose] def sampleListCheckedFast {α : Type} : List α → (α → Poly × Bool) → List Poly × Bool
  | [], _ => ([], true)
  | x :: xs, f =>
    match f x, sampleListCheckedFast xs f with
    | (p, o1), (ps, o2) => forcePoly p fun p' => (p' :: ps, o1 && o2)

private theorem sampleListCheckedFast_sound {α : Type} :
    ∀ (xs : List α) (f : α → Poly × Bool),
      (sampleListCheckedFast xs f).2 = true →
        (sampleListCheckedFast xs f).1 = xs.map (fun x => (f x).1) ∧
        ∀ x ∈ xs, (f x).2 = true
  | [], _, _ => ⟨rfl, fun _ hm => nomatch hm⟩
  | x :: xs, f, h => by
    simp only [sampleListCheckedFast] at h ⊢
    rcases hfx : f x with ⟨p, o1⟩
    rcases hacc : sampleListCheckedFast xs f with ⟨ps, o2⟩
    simp only [hfx, hacc, forcePoly_eq, Bool.and_eq_true] at h ⊢
    rcases h with ⟨ho1, ho2⟩
    obtain ⟨hmap, hall⟩ := sampleListCheckedFast_sound xs f (by rw [hacc]; exact ho2)
    have hps : ps = xs.map (fun x => (f x).1) := by
      have h1 : (sampleListCheckedFast xs f).1 = ps := by rw [hacc]
      exact h1.symm.trans hmap
    have hcons : p :: ps = (x :: xs).map (fun x => (f x).1) := by
      simp [List.map_cons, hfx, hps]
    exact ⟨hcons, List.forall_mem_cons.mpr ⟨by simp [hfx, ho1], hall⟩⟩

@[expose] def sampleMatRowsCheckedFast (k : Nat) (rho32 : List (BitVec 8)) (transpose : Bool) :
    List Nat → List (Array Poly) × Bool
  | [] => ([], true)
  | r :: rs =>
    let row := sampleListCheckedFast (List.range k) fun c =>
      let (i, j) := if transpose then (c, r) else (r, c)
      sampleNttFast (rho32 ++ [BitVec.ofNat 8 i, BitVec.ofNat 8 j])
    match row, sampleMatRowsCheckedFast k rho32 transpose rs with
    | (ps, o1), (rows, o2) => forcePolyList ps fun ps' => (Array.mk ps' :: rows, o1 && o2)

private theorem sampleMatRowsCheckedFast_sound (k : Nat) (rho32 : List (BitVec 8))
    (transpose : Bool) :
    ∀ (rs : List Nat),
      (sampleMatRowsCheckedFast k rho32 transpose rs).2 = true →
        (sampleMatRowsCheckedFast k rho32 transpose rs).1 =
          rs.map fun r =>
            Array.ofFn (n := k) fun ⟨c, _⟩ =>
              let (i, j) := if transpose then (c, r) else (r, c)
              sampleNtt (rho32 ++ [BitVec.ofNat 8 i, BitVec.ofNat 8 j])
  | [], _ => rfl
  | r :: rs, h => by
    let g : Nat → Poly × Bool := fun c =>
      let (i, j) := if transpose then (c, r) else (r, c)
      sampleNttFast (rho32 ++ [BitVec.ofNat 8 i, BitVec.ofNat 8 j])
    have h_snd :
        (sampleListCheckedFast (List.range k) g).2 = true ∧
        (sampleMatRowsCheckedFast k rho32 transpose rs).2 = true := by
      simpa only [sampleMatRowsCheckedFast, forcePolyList_eq, Bool.and_eq_true] using h
    rcases h_snd with ⟨ho1, ho2⟩
    obtain ⟨hrow_map, hrow_ok⟩ := sampleListCheckedFast_sound (List.range k) g ho1
    have hrows_eq := sampleMatRowsCheckedFast_sound k rho32 transpose rs ho2
    simp only [sampleMatRowsCheckedFast]
    change (match sampleListCheckedFast (List.range k) g,
        sampleMatRowsCheckedFast k rho32 transpose rs with
      | (ps, o1), (rows, o2) =>
        forcePolyList ps fun ps' => (Array.mk ps' :: rows, o1 && o2)).1 = _
    rcases hrow : sampleListCheckedFast (List.range k) g with ⟨ps, o1⟩
    rcases hacc : sampleMatRowsCheckedFast k rho32 transpose rs with ⟨rows, o2⟩
    simp only [forcePolyList_eq, List.map_cons]
    refine congrArg₂ List.cons ?_ ?_
    · have hps : ps = (List.range k).map (fun c => (g c).1) := by
        rw [hrow] at hrow_map
        exact hrow_map
      apply Array.ext
      · simp [hps]
      · intro c hc1 hc2
        have hc : c < k := by simpa using hc2
        simp only [Array.getElem_ofFn, List.getElem_toArray, hps, List.getElem_map,
          List.getElem_range]
        have hok_c := hrow_ok c (List.mem_range.mpr hc)
        dsimp only [g] at hok_c ⊢
        cases transpose <;> exact sampleNttFast_eq_of_snd hok_c
    · rw [hacc] at hrows_eq
      exact hrows_eq

@[expose] def sampleMatrixCheckedFast (k : Nat) (rho : List (BitVec 8)) (transpose : Bool) :
    Array (Array Poly) × Bool :=
  forceListBV8 (rho.take 32) fun rho32 =>
  let r := sampleMatRowsCheckedFast k rho32 transpose (List.range k)
  (Array.mk r.1, r.2)

theorem sampleMatrixCheckedFast_eq {k : Nat} {rho : List (BitVec 8)} {transpose : Bool}
    (hok : (sampleMatrixCheckedFast k rho transpose).2 = true) :
    (sampleMatrixCheckedFast k rho transpose).1 =
      sampleMatrixWith sampleNtt k rho transpose := by
  unfold sampleMatrixCheckedFast at hok ⊢
  rw [forceListBV8_eq] at hok ⊢
  dsimp only at hok ⊢
  unfold sampleMatrixWith
  have hs := sampleMatRowsCheckedFast_sound k (rho.take 32) transpose (List.range k) hok
  apply Array.ext
  · simp [hs]
  · intro r hr1 hr2
    simp [hs, Array.getElem_ofFn, List.getElem_map, List.getElem_range]

/-! ## 4. Precomputed-Matrix `IND-CPA` Helpers and Row Soundness -/

@[expose] def indCpaEncryptPrecomp (k dU dV : Nat)
    (aTrans : Array (Array Poly)) (tHat : Array Poly)
    (m coins : List (BitVec 8)) : List (BitVec 8) × List (BitVec 8) :=
  forceMatrix aTrans fun aTrans =>
  forcePolyVec tHat fun tHat =>
  forcePolyVec (arrayMapFast polyNttFast (sampleVecCbd2Fast k coins 0)) fun rHat =>
  forcePolyVec (sampleVecCbd2Fast k coins k) fun e1 =>
  forcePoly (samplePolyCbd2Fast (shake256Fast 128 (coins.take 32 ++ [BitVec.ofNat 8 (2 * k)]))) fun e2 =>
  forcePolyVec (arrayOfFnFast k fun i =>
    polyAddFast
      (polyInvNttFast (vecDotNttFast k (arrayGetDFast aTrans i (Array.mk [])) rHat))
      (arrayGetDFast e1 i zeroPoly)) fun uVec =>
  let mPoly := decodeAndDecompressFast 1 (m.take 32)
  let vPoly := polyAddFast (polyAddFast (polyInvNttFast (vecDotNttFast k tHat rHat)) e2) mPoly
  let c1 := ((List.range k).map fun i => compressAndEncodeFast dU (arrayGetDFast uVec i zeroPoly)).flatten
  let c2 := compressAndEncodeFast dV vPoly
  (forceListBV8 c1 id, forceListBV8 c2 id)

theorem indCpaEncryptPrecomp_eq (k dU dV : Nat) (pk m coins : List (BitVec 8))
    (aTrans : Array (Array Poly)) (tHat : Array Poly)
    (ha : aTrans = sampleMatrixWith sampleNtt k ((pk.drop (384 * k)).take 32) false)
    (ht : tHat = Array.ofFn (n := k) fun ⟨i, _⟩ =>
      byteDecodeMod 12 ((pk.drop (384 * i)).take 384)) :
    indCpaEncryptPrecomp k dU dV aTrans tHat m coins =
      ((indCpaEncryptWith sampleNtt k dU dV pk m coins).1,
       (indCpaEncryptWith sampleNtt k dU dV pk m coins).2.1) := by
  subst ha; subst ht
  unfold indCpaEncryptPrecomp indCpaEncryptWith
  have hempty : Array.mk ([] : List Poly) = #[] := rfl
  simp only [forceMatrix_eq, forcePolyVec_eq, forcePoly_eq, forceListBV8_eq, id_eq, hempty,
    arrayMapFast_eq, arrayOfFnFast_eq, arrayGetDFast_eq, sampleVecCbd2Fast_eq,
    show polyNttFast = polyNtt from funext polyNttFast_eq,
    samplePolyCbd2Fast_eq, shake256Fast_eq, polyAddFast_eq, polyInvNttFast_eq,
    vecDotNttFast_eq, decodeAndDecompressFast_eq, compressAndEncodeFast_eq]

@[expose] def indCpaDecryptPrecomp (k dU dV : Nat) (sHat : Array Poly) (ct : List (BitVec 8)) :
    List (BitVec 8) :=
  let c1Block := 32 * dU
  let c1Len := k * c1Block
  forcePolyVec sHat fun sHat =>
  forceListBV8 ct fun ct =>
  forcePolyVec
    (arrayOfFnFast k fun i =>
      polyNttFast (decodeAndDecompressFast dU ((ct.drop (i * c1Block)).take c1Block)))
    fun uHat =>
  let vPoly := decodeAndDecompressFast dV ((ct.drop c1Len).take (32 * dV))
  let wPoly := polySubFast vPoly (polyInvNttFast (vecDotNttFast k sHat uHat))
  compressAndEncodeFast 1 wPoly

theorem indCpaDecryptPrecomp_eq (k dU dV : Nat) (skPke ct : List (BitVec 8))
    (sHat : Array Poly)
    (hs : sHat = Array.ofFn (n := k) fun ⟨i, _⟩ =>
      byteDecodeMod 12 ((skPke.drop (384 * i)).take 384)) :
    indCpaDecryptPrecomp k dU dV sHat ct = indCpaDecrypt k dU dV skPke ct := by
  subst hs
  unfold indCpaDecryptPrecomp indCpaDecrypt
  simp only [forcePolyVec_eq, forceListBV8_eq, arrayOfFnFast_eq, polyNttFast_eq,
    decodeAndDecompressFast_eq, polySubFast_eq, polyInvNttFast_eq, vecDotNttFast_eq,
    compressAndEncodeFast_eq]

@[expose] def kyberEncapsOnePrecomp (aTrans : Array (Array Poly)) (tHat : Array Poly)
    (hPk rand32 : List (BitVec 8)) : List (BitVec 8) × List (BitVec 8) :=
  forceListBV8 (sha3_256Fast (rand32.take 32)) fun m =>
  forceListBV8 (sha3_512Fast (m ++ hPk)) fun kr =>
  let kBar := kr.take 32
  let r := (kr.drop 32).take 32
  let (c1, c2) := indCpaEncryptPrecomp 4 11 5 aTrans tHat m r
  forceListBV8 (c1 ++ c2) fun ct =>
  let ss := shake256Fast 32 (kBar ++ sha3_256Fast ct)
  (ct, ss)

@[expose] def checkKyberRow (aTrans : Array (Array Poly)) (tHat sHat : Array Poly)
    (hPk e ctExp ssExp : List (BitVec 8)) : Bool :=
  forceListBV8 hPk fun hPk =>
  forceListBV8 e fun e =>
  forceListBV8 ctExp fun ctExp =>
  forceListBV8 ssExp fun ssExp =>
  let (ct, ss) := kyberEncapsOnePrecomp aTrans tHat hPk e
  (ct == ctExp) &&
  (ss == ssExp) &&
  (indCpaDecryptPrecomp 4 11 5 sHat ctExp == sha3_256Fast (e.take 32))

theorem kyberRow_sound {pk sk e ctExp ssExp : List (BitVec 8)}
    {aTrans : Array (Array Poly)} {tHat sHat : Array Poly} {hPk : List (BitVec 8)}
    (hpk_len : pk.length = 1568)
    (hct_len : ctExp.length = 1568)
    (hss_len : ssExp.length = 32)
    (haTrans : aTrans = sampleMatrixWith sampleNtt 4 ((pk.drop 1536).take 32) false)
    (htHat : tHat = Array.ofFn (n := 4) fun ⟨i, _⟩ =>
      byteDecodeMod 12 ((pk.drop (384 * i)).take 384))
    (hsHat : sHat = Array.ofFn (n := 4) fun ⟨i, _⟩ =>
      byteDecodeMod 12 (((sk.take 1536).drop (384 * i)).take 384))
    (hhPk : hPk = sha3_256List pk)
    (hsk_pk : (sk.drop 1536).take 1568 = pk)
    (hsk_hpk : (sk.drop 3104).take 32 = hPk)
    (hrow : checkKyberRow aTrans tHat sHat hPk e ctExp ssExp = true) :
    kyber1024Encaps pk e = (ctExp, ssExp) ∧
    kyber1024Decaps sk ctExp = ssExp := by
  unfold checkKyberRow kyberEncapsOnePrecomp at hrow
  simp only [forceListBV8_eq] at hrow
  rcases (Bool.and_eq_true _ _).mp hrow with ⟨hct_ss, hdec_m'⟩
  rcases (Bool.and_eq_true _ _).mp hct_ss with ⟨hct', hss'⟩
  have hct := beq_iff_eq.mp hct'
  have hss := beq_iff_eq.mp hss'
  have hdec_m := beq_iff_eq.mp hdec_m'
  have hpk_take : pk.take 1568 = pk :=
    List.take_of_length_le (by rw [hpk_len]; exact Nat.le_refl _)
  have hct_take : ctExp.take 1568 = ctExp :=
    List.take_of_length_le (by rw [hct_len]; exact Nat.le_refl _)
  have henc_pre := indCpaEncryptPrecomp_eq 4 11 5 pk
    (sha3_256List (e.take 32))
    ((sha3_512List (sha3_256List (e.take 32) ++ sha3_256List pk)).drop 32 |>.take 32)
    aTrans tHat haTrans htHat
  rw [hhPk, sha3_256Fast_eq, sha3_512Fast_eq] at hct
  rw [hhPk, sha3_256Fast_eq, sha3_512Fast_eq, shake256Fast_eq] at hss
  rw [sha3_256Fast_eq] at hdec_m
  rw [hhPk] at hsk_hpk
  rw [henc_pre] at hct hss
  dsimp only at hct hss
  rw [hct] at hss
  rw [indCpaDecryptPrecomp_eq 4 11 5 (sk.take 1536) ctExp sHat hsHat] at hdec_m
  have henc : kyber1024EncapsWith sampleNtt pk e = (ctExp, ssExp) := by
    unfold kyber1024EncapsWith
    dsimp only
    rw [hpk_take, hct, hss]
  have hdec : kyber1024DecapsWith sampleNtt sk ctExp = ssExp := by
    unfold kyber1024DecapsWith
    dsimp only
    rw [hsk_pk, hsk_hpk, hct_take, hdec_m, hct]
    simp only [beq_self_eq_true, ↓reduceIte]
    exact hss
  refine ⟨?_, ?_⟩
  · unfold kyber1024Encaps
    rw [henc]
    dsimp only
    rw [toByteVec_toList_of_length hct_len, toByteVec_toList_of_length hss_len]
  · unfold kyber1024Decaps
    rw [hdec, toByteVec_toList_of_length hss_len]

end

end Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKyberDefs
