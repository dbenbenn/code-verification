/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt -- proof-setup: allow-public-import

/-!
# Inverse NEON `NTT⁻¹` (`invert_ntt_montgomery`) soundness

1. `PolyCanonical` (`size = 256` and `< 3329` coefficients) and preservation across `Spec`
   polynomial constructors (`zeroPoly`, `polyAdd`, `polySub`, `polyNttMul`, `vecDotNtt`,
   `byteDecodeMod`, `samplePolyCbd2`, `nttStage`, `polyNtt`, `invNttStage`, `polyInvNtt`).
2. NEON 128-bit vector butterfly steps matching compiled `MlKemPlacedObj` (`B20`, `B03`, `B04`,
   `B06`, `B07`):
   - `simdBarrett8h` (`sqdmulh · 20159`, `+ 1024`, `sshr #11`, `mla · 0xf2ff`),
   - Layer 1 (`len = 2`, `barrettFirst = true`, `simdTrn1_4s`/`simdTrn2_4s`, `[k, k-2, k-1, k-3]`),
   - Layer 2 (`len = 4`, `barrettFirst = false`, `pack2x64` / `zip1.2d` + `zip2.2d`, `[k, k-1]`),
   - Whole-vector layers (`len ∈ {8, 16, 32, 64, 128}`, `barrettFirst = false` at `8` and `true`
     at `16..128`).
3. Full polynomial range trajectory (`8704 → 2496 → 4992 → 9984 → 2496 → ... → 1664`) and
   modular equivalence for `Spec.neonInvNttStage16`, `Spec.neonInvNttMontgomery16`, and final
   `neonMontgomeryMul16 · 1441#16` normalization against `Spec.polyInvNtt`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Poly16 mlkemQ zeroPoly fipsZetas zetasTimesMontgomeryR
  polyAdd polySub polyNttMul vecDotNtt byteDecodeRaw byteDecodeMod samplePolyCbd2
  nttStage polyNtt invNttStage polyInvNtt
  neonBarrettReduce16 neonMontgomeryMul16 neonInvNttStage16 neonInvNttMontgomery16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (zetaTableAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  lane16 lane64 pack8x16 pack2x64 dup8x16 ext_lane16
  lane16_pack8x16 lane16_dup8x16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdAdd8h simdSub8h simdMla8h simdSqdmulh8h simdSshr8h simdTrn1_4s simdTrn2_4s
  lane16_simdAdd8h lane16_simdSub8h lane16_simdMla8h lane16_simdSqdmulh8h lane16_simdSshr8h
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith (
  zetaTableAt_eq_zetasTimesMontgomeryR zetasTimesMontgomeryR_bounds
  zetasTimesMontgomeryR_ne_0x8000 zetasTimesMontgomeryR_mod_3329
  toInt_add_of_bounds toInt_sub_of_bounds
  barrett_mla_0xf2ff neonBarrettReduce16_spec neonMontgomeryMul16_spec neonMontgomeryMul16_1441
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (
  PolyBounded16 PolyRepresents PolyRepresentsMontInv
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt (
  foldl_range_stepK butterflyStage butterflyStage_size butterflyStage_getD
  lane16_pack2x64_sel lane16_simdTrn1_4s lane16_simdTrn2_4s
  simdMontMul8h lane16_simdMontMul8h
  neonMontgomeryMul16_zeta_spec neonBarrettReducePoly16_spec
)

/-! ## 1. Canonical `[0, 3328]` `Spec.Poly` Invariant -/

/-- `f : Poly` has size `256` and every coefficient is canonically reduced `< 3329`. -/
@[expose] def PolyCanonical (f : Poly) : Prop :=
  f.size = 256 ∧ ∀ i < 256, f.getD i 0 < mlkemQ

theorem zeroPoly_canonical : PolyCanonical zeroPoly := by
  refine ⟨by simp [zeroPoly], fun i hi => ?_⟩
  simp [zeroPoly, Array.getD, hi, mlkemQ]

theorem polyAdd_canonical (a b : Poly) : PolyCanonical (polyAdd a b) := by
  refine ⟨by simp [polyAdd], fun i hi => ?_⟩
  have hget : (polyAdd a b).getD i 0 = (a.getD i 0 + b.getD i 0) % mlkemQ := by
    simp [polyAdd, Array.getD, hi]
  rw [hget]
  exact Nat.mod_lt _ (by decide : 0 < mlkemQ)

theorem polySub_canonical (a b : Poly) : PolyCanonical (polySub a b) := by
  refine ⟨by simp [polySub], fun i hi => ?_⟩
  have hget : (polySub a b).getD i 0 = (a.getD i 0 + mlkemQ - (b.getD i 0 % mlkemQ)) % mlkemQ := by
    simp [polySub, Array.getD, hi]
  rw [hget]
  exact Nat.mod_lt _ (by decide : 0 < mlkemQ)

theorem polyNttMul_canonical (f g : Poly) : PolyCanonical (polyNttMul f g) := by
  refine ⟨by simp [polyNttMul], fun i hi => ?_⟩
  have hlt : (polyNttMul f g)[i]'(by simp [polyNttMul]; exact hi) < mlkemQ := by
    simp only [polyNttMul, Array.getElem_ofFn]
    by_cases he : (i % 2 == 0) = true
    · simp only [he, ↓reduceIte]; exact Nat.mod_lt _ (by decide : 0 < mlkemQ)
    · have hf : (i % 2 == 0) = false := Bool.eq_false_iff.mpr he
      simp only [hf, Bool.false_eq_true, ↓reduceIte]; exact Nat.mod_lt _ (by decide : 0 < mlkemQ)
  simpa [Array.getD, show i < (polyNttMul f g).size by simp [polyNttMul]; exact hi] using hlt

theorem vecDotNtt_canonical (k : Nat) (a b : Array Poly) : PolyCanonical (vecDotNtt k a b) := by
  unfold vecDotNtt
  induction k with
  | zero => simpa using zeroPoly_canonical
  | succ m _ =>
    rw [List.range_succ, List.foldl_append]
    simpa only [List.foldl_cons, List.foldl_nil] using polyAdd_canonical _ _

theorem byteDecodeMod_canonical (d : Nat) (bs : List (BitVec 8)) :
    PolyCanonical (byteDecodeMod d bs) := by
  have hraw : (byteDecodeRaw d bs).size = 256 := by simp [byteDecodeRaw]
  refine ⟨by simp [byteDecodeMod, hraw], fun i hi => ?_⟩
  have hget : (byteDecodeMod d bs).getD i 0 = (byteDecodeRaw d bs).getD i 0 % mlkemQ := by
    simp [byteDecodeMod, Array.getD, hraw, hi]
  rw [hget]
  exact Nat.mod_lt _ (by decide : 0 < mlkemQ)

theorem samplePolyCbd2_canonical (bs : List (BitVec 8)) : PolyCanonical (samplePolyCbd2 bs) := by
  refine ⟨by simp [samplePolyCbd2], fun i hi => ?_⟩
  have hlt : (samplePolyCbd2 bs)[i]'(by simp [samplePolyCbd2]; exact hi) < mlkemQ := by
    simp only [samplePolyCbd2, Array.getElem_ofFn]
    exact Nat.mod_lt _ (by decide : 0 < mlkemQ)
  simpa [Array.getD, show i < (samplePolyCbd2 bs).size by simp [samplePolyCbd2]; exact hi] using hlt

theorem nttStage_canonical {len kInit : Nat} {f : Poly}
    (hf : PolyCanonical f) (hlen : 0 < len) (hdiv : 2 * len ∣ 256) :
    PolyCanonical (nttStage len kInit f).1 := by
  have heq : (nttStage len kInit f).1 =
      butterflyStage len
        (fun blk fj fjl =>
          let t := (fipsZetas.getD (kInit + blk) 0 * fjl) % mlkemQ
          ((fj + t) % mlkemQ, (fj + mlkemQ - t) % mlkemQ))
        0 f := by
    unfold nttStage butterflyStage
    exact congrArg Prod.fst (foldl_range_stepK (256 / (2 * len))
      (fun cur k blk =>
        let start := blk * 2 * len
        (List.range len).foldl
          (fun arr off =>
            let j := start + off
            let fj := arr.getD j 0
            let fjl := arr.getD (j + len) 0
            let t := (fipsZetas.getD k 0 * fjl) % mlkemQ
            (arr.set! j ((fj + t) % mlkemQ)).set! (j + len) ((fj + mlkemQ - t) % mlkemQ))
          cur)
      (· + 1) (kInit + ·) kInit (Nat.add_zero kInit) (fun b => (Nat.add_assoc kInit b 1).symm) f)
  rw [heq]
  refine ⟨butterflyStage_size _ 0 hf.1 hlen hdiv, fun idx hidx => ?_⟩
  rw [butterflyStage_getD _ 0 hf.1 hlen hdiv hidx]
  dsimp only
  by_cases hhalf : idx % (2 * len) < len <;>
    simp only [hhalf, ↓reduceIte] <;> exact Nat.mod_lt _ (by decide)

theorem polyNtt_canonical {f : Poly} (hf : PolyCanonical f) : PolyCanonical (polyNtt f) := by
  unfold polyNtt
  have h1 := nttStage_canonical (len := 128) (kInit := 1) hf (by decide) (by decide)
  rcases hf1 : nttStage 128 1 f with ⟨f1, k1⟩; rw [hf1] at h1; dsimp only at h1 ⊢
  have h2 := nttStage_canonical (len := 64) (kInit := k1) h1 (by decide) (by decide)
  rcases hf2 : nttStage 64 k1 f1 with ⟨f2, k2⟩; rw [hf2] at h2; dsimp only at h2 ⊢
  have h3 := nttStage_canonical (len := 32) (kInit := k2) h2 (by decide) (by decide)
  rcases hf3 : nttStage 32 k2 f2 with ⟨f3, k3⟩; rw [hf3] at h3; dsimp only at h3 ⊢
  have h4 := nttStage_canonical (len := 16) (kInit := k3) h3 (by decide) (by decide)
  rcases hf4 : nttStage 16 k3 f3 with ⟨f4, k4⟩; rw [hf4] at h4; dsimp only at h4 ⊢
  have h5 := nttStage_canonical (len := 8) (kInit := k4) h4 (by decide) (by decide)
  rcases hf5 : nttStage 8 k4 f4 with ⟨f5, k5⟩; rw [hf5] at h5; dsimp only at h5 ⊢
  have h6 := nttStage_canonical (len := 4) (kInit := k5) h5 (by decide) (by decide)
  rcases hf6 : nttStage 4 k5 f5 with ⟨f6, k6⟩; rw [hf6] at h6; dsimp only at h6 ⊢
  have h7 := nttStage_canonical (len := 2) (kInit := k6) h6 (by decide) (by decide)
  rcases hf7 : nttStage 2 k6 f6 with ⟨f7, k7⟩; rw [hf7] at h7; exact h7

/-! ## 2. NEON 128-Bit `InvNtt` Vector Butterfly Steps (`B20 +0x0f80..+0x1600`) -/

/-- 8-lane NEON Barrett reduction (`pack8x16` of `neonBarrettReduce16`). -/
@[expose] def simdBarrett8h (v : BitVec 128) : BitVec 128 :=
  pack8x16 fun i => neonBarrettReduce16 (lane16 v i)

@[simp] theorem lane16_simdBarrett8h (v : BitVec 128) (i : Fin 8) :
    lane16 (simdBarrett8h v) i = neonBarrettReduce16 (lane16 v i) :=
  lane16_pack8x16 _ i

/-- Exact instruction-level equivalence of NEON `barrett_reduce` (`sqdmulh · 20159`, `+ 1024`,
    `sshr #11`, `mla · 0xf2ff`, matching `B20 +0x0fc0..+0x0fe4`). -/
theorem simdBarrett8h_eq_mla (v : BitVec 128) :
    simdMla8h v
      (simdSshr8h (simdAdd8h (simdSqdmulh8h v (dup8x16 20159#16)) (dup8x16 1024#16)) 11)
      (dup8x16 0xf2ff#16) =
    simdBarrett8h v := by
  apply ext_lane16
  intro i
  simp only [lane16_simdMla8h, lane16_simdSshr8h, lane16_simdAdd8h, lane16_simdSqdmulh8h,
    lane16_dup8x16, lane16_simdBarrett8h, barrett_mla_0xf2ff]
  rfl

/-- Whole-vector NEON `InvNtt` butterfly (`len ∈ {8, 16, 32, 64, 128}`):
    `barrettFirst = false` at `len = 8`, `barrettFirst = true` at `len ∈ {16, 32, 64, 128}`. -/
@[expose] def invNttLayer8hVecPair (barrettFirst : Bool) (va vb : BitVec 128) (k : Nat) :
    BitVec 128 × BitVec 128 :=
  let sum := simdAdd8h va vb
  let diff := simdSub8h vb va
  let a' := if barrettFirst then simdBarrett8h sum else sum
  let b' := simdMontMul8h diff (dup8x16 (zetaTableAt k))
  (a', b')

theorem lane16_invNttLayer8hVecPair {k : Nat} (hk : k < 128) (barrettFirst : Bool)
    (va vb : BitVec 128) (i : Fin 8) :
    let z := zetasTimesMontgomeryR.getD k 0#16
    let sum := lane16 va i + lane16 vb i
    lane16 (invNttLayer8hVecPair barrettFirst va vb k).1 i =
      (if barrettFirst then neonBarrettReduce16 sum else sum) ∧
    lane16 (invNttLayer8hVecPair barrettFirst va vb k).2 i =
      neonMontgomeryMul16 (lane16 vb i - lane16 va i) z := by
  dsimp [invNttLayer8hVecPair]
  cases barrettFirst <;> simp [zetaTableAt_eq_zetasTimesMontgomeryR hk]

/-- Layer 2 (`len = 4`, `barrettFirst = false`, `B20 +0x103c..+0x109c`) NEON 2-vector butterfly:
    `zip1.2d`/`zip2.2d` (`pack2x64`) with `[zetaTableAt k (×4), zetaTableAt (k - 1) (×4)]`. -/
@[expose] def invNttLayer4VecPair (vLo vHi : BitVec 128) (k : Nat) : BitVec 128 × BitVec 128 :=
  let a := pack2x64 fun c => if c.val = 0 then lane64 vLo 0 else lane64 vHi 0
  let b := pack2x64 fun c => if c.val = 0 then lane64 vLo 1 else lane64 vHi 1
  let zVec := pack8x16 fun i => if i.val < 4 then zetaTableAt k else zetaTableAt (k - 1)
  let a' := simdAdd8h a b
  let b' := simdMontMul8h (simdSub8h b a) zVec
  (pack2x64 (fun c => if c.val = 0 then lane64 a' 0 else lane64 b' 0),
   pack2x64 (fun c => if c.val = 0 then lane64 a' 1 else lane64 b' 1))

@[local simp] private theorem lane16_pack2x64_sel_zero (x y : BitVec 128) (cx cy : Fin 2) (i : Fin 8) :
    lane16 (pack2x64 fun c => if c = 0 then lane64 x cx else lane64 y cy) i =
      if h : i.val < 4 then lane16 x ⟨4 * cx.val + i.val, by omega⟩
      else lane16 y ⟨4 * cy.val + (i.val - 4), by omega⟩ := by
  have hfn : (fun c : Fin 2 => if c = 0 then lane64 x cx else lane64 y cy) =
      (fun c : Fin 2 => if c.val = 0 then lane64 x cx else lane64 y cy) := by
    funext ⟨v, hv⟩
    rcases v with _ | _ | v <;> try omega
    all_goals rfl
  rw [hfn, lane16_pack2x64_sel]

theorem lane16_invNttLayer4VecPair {k : Nat} (hk1 : 1 ≤ k) (hk : k < 128)
    (vLo vHi : BitVec 128) (i : Fin 8) :
    let z0 := zetasTimesMontgomeryR.getD k 0#16
    let z1 := zetasTimesMontgomeryR.getD (k - 1) 0#16
    lane16 (invNttLayer4VecPair vLo vHi k).1 i =
      (if h : i.val < 4 then
        lane16 vLo i + lane16 vLo ⟨i.val + 4, by omega⟩
       else
        neonMontgomeryMul16 (lane16 vLo i - lane16 vLo ⟨i.val - 4, by omega⟩) z0) ∧
    lane16 (invNttLayer4VecPair vLo vHi k).2 i =
      (if h : i.val < 4 then
        lane16 vHi i + lane16 vHi ⟨i.val + 4, by omega⟩
       else
        neonMontgomeryMul16 (lane16 vHi i - lane16 vHi ⟨i.val - 4, by omega⟩) z1) := by
  have hz0 := zetaTableAt_eq_zetasTimesMontgomeryR hk
  have hz1 := zetaTableAt_eq_zetasTimesMontgomeryR (by omega : k - 1 < 128)
  unfold invNttLayer4VecPair
  rcases i with ⟨_ | _ | _ | _ | _ | _ | _ | _ | n, hi⟩ <;> try omega
  all_goals
    dsimp only
    simp [lane16_simdAdd8h, lane16_simdSub8h,
      lane16_simdMontMul8h, lane16_pack8x16, hz0, hz1]

/-- Layer 1 (`len = 2`, `barrettFirst = true`, `B20 +0x0f80..+0x1018`) NEON 2-vector butterfly:
    `trn1.4s`/`trn2.4s` with Barrett on `a + b` and `[z_k, z_k, z_{k-2}, z_{k-2}, z_{k-1}, z_{k-1}, z_{k-3}, z_{k-3}]`. -/
@[expose] def invNttLayer2VecPair (vLo vHi : BitVec 128) (k : Nat) : BitVec 128 × BitVec 128 :=
  let a := simdTrn1_4s vLo vHi
  let b := simdTrn2_4s vLo vHi
  let zVec := pack8x16 fun i =>
    if i.val / 2 = 0 then zetaTableAt k
    else if i.val / 2 = 1 then zetaTableAt (k - 2)
    else if i.val / 2 = 2 then zetaTableAt (k - 1)
    else zetaTableAt (k - 3)
  let a' := simdBarrett8h (simdAdd8h a b)
  let b' := simdMontMul8h (simdSub8h b a) zVec
  (simdTrn1_4s a' b', simdTrn2_4s a' b')

theorem lane16_invNttLayer2VecPair {k : Nat} (_hk3 : 3 ≤ k) (hk : k < 128)
    (vLo vHi : BitVec 128) (i : Fin 8) :
    let zk (m : Nat) := zetasTimesMontgomeryR.getD (k - m) 0#16
    lane16 (invNttLayer2VecPair vLo vHi k).1 i =
      (let z := zk (i.val / 4)
       if h : i.val % 4 < 2 then
         neonBarrettReduce16 (lane16 vLo i + lane16 vLo ⟨i.val + 2, by have := i.isLt; omega⟩)
       else
         neonMontgomeryMul16 (lane16 vLo i - lane16 vLo ⟨i.val - 2, by have := i.isLt; omega⟩) z) ∧
    lane16 (invNttLayer2VecPair vLo vHi k).2 i =
      (let z := zk (2 + i.val / 4)
       if h : i.val % 4 < 2 then
         neonBarrettReduce16 (lane16 vHi i + lane16 vHi ⟨i.val + 2, by have := i.isLt; omega⟩)
       else
         neonMontgomeryMul16 (lane16 vHi i - lane16 vHi ⟨i.val - 2, by have := i.isLt; omega⟩) z) := by
  have hz0 := zetaTableAt_eq_zetasTimesMontgomeryR hk
  have hz1 := zetaTableAt_eq_zetasTimesMontgomeryR (by omega : k - 1 < 128)
  have hz2 := zetaTableAt_eq_zetasTimesMontgomeryR (by omega : k - 2 < 128)
  have hz3 := zetaTableAt_eq_zetasTimesMontgomeryR (by omega : k - 3 < 128)
  unfold invNttLayer2VecPair
  rcases i with ⟨_ | _ | _ | _ | _ | _ | _ | _ | n, hi⟩ <;> try omega
  all_goals
    dsimp only
    simp only [lane16_simdTrn1_4s, lane16_simdTrn2_4s, lane16_simdBarrett8h,
      lane16_simdAdd8h, lane16_simdSub8h, lane16_simdMontMul8h, lane16_pack8x16,
      Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceSub,
      Nat.reduceLT, Nat.reduceEqDiff, ↓reduceDIte, ↓reduceIte, Nat.sub_zero,
      hz0, hz1, hz2, hz3]
    exact ⟨trivial, trivial⟩

/-! ## 3. Stage & Full Polynomial Soundness (`neonInvNttMontgomery16` & `polyInvNtt`) -/

private theorem invNttStage_eq_butterfly (len kInit : Nat) (f : Poly) :
    invNttStage len kInit f =
      (butterflyStage len
        (fun blk t fjl =>
          let zeta := fipsZetas.getD (kInit - blk) 0
          ((t + fjl) % mlkemQ, (zeta * (fjl + mlkemQ - t)) % mlkemQ))
        0 f,
       kInit - 256 / (2 * len)) := by
  unfold invNttStage butterflyStage
  exact foldl_range_stepK (256 / (2 * len))
    (fun cur k blk =>
      let start := blk * 2 * len
      (List.range len).foldl
        (fun arr off =>
          let j := start + off
          let t := arr.getD j 0
          let fjl := arr.getD (j + len) 0
          (arr.set! j ((t + fjl) % mlkemQ)).set!
            (j + len) ((fipsZetas.getD k 0 * (fjl + mlkemQ - t)) % mlkemQ))
        cur)
    (· - 1) (kInit - ·) kInit (Nat.sub_zero kInit) (fun b => Nat.sub_sub kInit b 1) f

private theorem neonInvNttStage16_eq_butterfly (len kInit : Nat) (barrettFirst : Bool) (p : Poly16) :
    neonInvNttStage16 len kInit barrettFirst p =
      (butterflyStage len
        (fun blk a b =>
          let sum := a + b
          let a' := if barrettFirst then neonBarrettReduce16 sum else sum
          let b' := neonMontgomeryMul16 (b - a) (zetasTimesMontgomeryR.getD (kInit - blk) 0#16)
          (a', b'))
        0#16 p,
       kInit - 256 / (2 * len)) := by
  unfold neonInvNttStage16 butterflyStage
  exact foldl_range_stepK (256 / (2 * len))
    (fun cur k blk =>
      let start := blk * 2 * len
      (List.range len).foldl
        (fun arr off =>
          let j := start + off
          let a := arr.getD j 0#16
          let b := arr.getD (j + len) 0#16
          let sum := a + b
          let a' := if barrettFirst then neonBarrettReduce16 sum else sum
          let b' := neonMontgomeryMul16 (b - a) (zetasTimesMontgomeryR.getD k 0#16)
          (arr.set! j a').set! (j + len) b')
        cur)
    (· - 1) (kInit - ·) kInit (Nat.sub_zero kInit) (fun b => Nat.sub_sub kInit b 1) p

private theorem inv_butterfly_montInv_mod {k : Nat} (hk : k < 128) (barrettFirst : Bool)
    {a b : BitVec 16} {t fjl : Nat}
    (ht_lt : t < mlkemQ)
    (ha_mod : (a.toInt * 65536) % 3329 = (t : Int) % 3329)
    (hb_mod : (b.toInt * 65536) % 3329 = (fjl : Int) % 3329)
    (ha_b : -16000 ≤ a.toInt ∧ a.toInt ≤ 16000)
    (hb_b : -16000 ≤ b.toInt ∧ b.toInt ≤ 16000) :
    let sum := a + b
    let a' := if barrettFirst then neonBarrettReduce16 sum else sum
    let b' := neonMontgomeryMul16 (b - a) (zetasTimesMontgomeryR.getD k 0#16)
    let zeta := fipsZetas.getD k 0
    (a'.toInt * 65536) % 3329 = (((t + fjl) % mlkemQ : Nat) : Int) % 3329 ∧
    (b'.toInt * 65536) % 3329 = (((zeta * (fjl + mlkemQ - t)) % mlkemQ : Nat) : Int) % 3329 := by
  dsimp only
  have hsum_int : (a + b).toInt = a.toInt + b.toInt := toInt_add_of_bounds (by omega) (by omega)
  have hdiff_int : (b - a).toInt = b.toInt - a.toInt := toInt_sub_of_bounds (by omega) (by omega)
  have ha'_mod : ((if barrettFirst then neonBarrettReduce16 (a + b) else a + b).toInt * 65536) % 3329 =
      (((t + fjl) % mlkemQ : Nat) : Int) % 3329 := by
    have ha'_base : (if barrettFirst then neonBarrettReduce16 (a + b) else a + b).toInt % 3329 =
        (a + b).toInt % 3329 := by
      cases barrettFirst
      · rfl
      · exact (neonBarrettReduce16_spec (a + b)).2.2
    have hmul64 : ((if barrettFirst then neonBarrettReduce16 (a + b) else a + b).toInt * 65536) % 3329 =
        ((a + b).toInt * 65536) % 3329 := by
      rw [Int.mul_emod, ha'_base, ← Int.mul_emod]
    rw [hmul64, hsum_int, Int.add_mul]
    dsimp only [mlkemQ] at ht_lt ⊢
    omega
  refine ⟨ha'_mod, ?_⟩
  set zBv := zetasTimesMontgomeryR.getD k 0#16
  set zeta := fipsZetas.getD k 0
  have hbm := (neonMontgomeryMul16_spec (b - a) zBv (zetasTimesMontgomeryR_ne_0x8000 hk)).1
  have hzm := zetasTimesMontgomeryR_mod_3329 hk
  have hstep1 : ((b - a).toInt * zBv.toInt) % 3329 =
      ((zeta : Int) * ((b.toInt * 65536) - (a.toInt * 65536))) % 3329 := by
    rw [Int.mul_emod (b - a).toInt zBv.toInt, hzm, ← Int.mul_emod, hdiff_int]
    apply congrArg (· % 3329)
    ring
  have hdiff_mod : (b.toInt * 65536 - a.toInt * 65536) % 3329 =
      ((fjl + mlkemQ - t : Nat) : Int) % 3329 := by
    dsimp only [mlkemQ] at ht_lt ⊢
    omega
  set subNat : Nat := fjl + mlkemQ - t
  set prodNat : Nat := zeta * subNat
  have hprod_cast : (prodNat : Int) = (zeta : Int) * (subNat : Int) := Int.natCast_mul zeta subNat
  have hstep2 : ((zeta : Int) * (b.toInt * 65536 - a.toInt * 65536)) % 3329 =
      (prodNat : Int) % 3329 := by
    rw [Int.mul_emod, hdiff_mod, ← Int.mul_emod, hprod_cast]
  rw [hbm, hstep1, hstep2]
  dsimp only [mlkemQ]
  omega

private theorem inv_butterfly_std_mod {k : Nat} (hk : k < 128) (barrettFirst : Bool)
    {a b : BitVec 16} {t fjl : Nat}
    (ht_lt : t < mlkemQ)
    (ha_mod : a.toInt % 3329 = (t : Int) % 3329)
    (hb_mod : b.toInt % 3329 = (fjl : Int) % 3329)
    (ha_b : -16000 ≤ a.toInt ∧ a.toInt ≤ 16000)
    (hb_b : -16000 ≤ b.toInt ∧ b.toInt ≤ 16000) :
    let sum := a + b
    let a' := if barrettFirst then neonBarrettReduce16 sum else sum
    let b' := neonMontgomeryMul16 (b - a) (zetasTimesMontgomeryR.getD k 0#16)
    let zeta := fipsZetas.getD k 0
    a'.toInt % 3329 = (((t + fjl) % mlkemQ : Nat) : Int) % 3329 ∧
    b'.toInt % 3329 = (((zeta * (fjl + mlkemQ - t)) % mlkemQ : Nat) : Int) % 3329 := by
  dsimp only
  have hsum_int : (a + b).toInt = a.toInt + b.toInt := toInt_add_of_bounds (by omega) (by omega)
  have hdiff_int : (b - a).toInt = b.toInt - a.toInt := toInt_sub_of_bounds (by omega) (by omega)
  have ha'_mod : (if barrettFirst then neonBarrettReduce16 (a + b) else a + b).toInt % 3329 =
      (((t + fjl) % mlkemQ : Nat) : Int) % 3329 := by
    have ha'_base : (if barrettFirst then neonBarrettReduce16 (a + b) else a + b).toInt % 3329 =
        (a + b).toInt % 3329 := by
      cases barrettFirst
      · rfl
      · exact (neonBarrettReduce16_spec (a + b)).2.2
    rw [ha'_base, hsum_int]
    dsimp only [mlkemQ] at ht_lt ⊢
    omega
  refine ⟨ha'_mod, ?_⟩
  set zeta := fipsZetas.getD k 0
  have hbm := (neonMontgomeryMul16_zeta_spec hk (b - a)).1
  have hdiff_mod : (b - a).toInt % 3329 = ((fjl + mlkemQ - t : Nat) : Int) % 3329 := by
    rw [hdiff_int]
    dsimp only [mlkemQ] at ht_lt ⊢
    omega
  set subNat : Nat := fjl + mlkemQ - t
  set prodNat : Nat := zeta * subNat
  have hprod_cast : (prodNat : Int) = (zeta : Int) * (subNat : Int) := Int.natCast_mul zeta subNat
  have hstep : ((b - a).toInt * (zeta : Int)) % 3329 = (prodNat : Int) % 3329 := by
    rw [Int.mul_comm, Int.mul_emod, hdiff_mod, ← Int.mul_emod, hprod_cast]
  rw [hbm, hstep]
  dsimp only [mlkemQ]
  omega

/-- Output signed bound of a single `neonInvNttStage16` stage (`2496` if `barrettFirst`, else `max (2 * B) 2496`). -/
@[expose] def invStageOutBound (barrettFirst : Bool) (B : Int) : Int :=
  if barrettFirst then 2496 else max (2 * B) 2496

/-- Soundness & signed bound of one `neonInvNttStage16` stage in the `R⁻¹` (`PolyRepresentsMontInv`) domain. -/
theorem neonInvNttStage16_montInv_spec {B : Int} (len kInit : Nat) (barrettFirst : Bool)
    {p : Poly16} {f : Poly}
    (hbnd : PolyBounded16 B p) (hrep : PolyRepresentsMontInv p f) (hf : PolyCanonical f)
    (hB0 : 0 ≤ B) (hBmax : B ≤ 16000)
    (hlen : 0 < len) (hdiv : 2 * len ∣ 256) (hk : kInit < 128) :
    (neonInvNttStage16 len kInit barrettFirst p).2 = kInit - 256 / (2 * len) ∧
    (invNttStage len kInit f).2 = kInit - 256 / (2 * len) ∧
    PolyCanonical (invNttStage len kInit f).1 ∧
    PolyBounded16 (invStageOutBound barrettFirst B) (neonInvNttStage16 len kInit barrettFirst p).1 ∧
    PolyRepresentsMontInv (neonInvNttStage16 len kInit barrettFirst p).1 (invNttStage len kInit f).1 := by
  rw [neonInvNttStage16_eq_butterfly, invNttStage_eq_butterfly]
  dsimp only
  let pairP : Nat → BitVec 16 → BitVec 16 → BitVec 16 × BitVec 16 := fun blk a b =>
    let sum := a + b
    let a' := if barrettFirst then neonBarrettReduce16 sum else sum
    let b' := neonMontgomeryMul16 (b - a) (zetasTimesMontgomeryR.getD (kInit - blk) 0#16)
    (a', b')
  let pairF : Nat → Nat → Nat → Nat × Nat := fun blk t fjl =>
    let zeta := fipsZetas.getD (kInit - blk) 0
    ((t + fjl) % mlkemQ, (zeta * (fjl + mlkemQ - t)) % mlkemQ)
  have hsz_p := butterflyStage_size pairP 0#16 hbnd.1 hlen hdiv
  have hsz_f := butterflyStage_size pairF 0 hf.1 hlen hdiv
  have hjl_of_half : ∀ idx < 256, idx % (2 * len) < len → idx + len < 256 := by
    intro idx hidx hhalf
    have hq_lt : idx / (2 * len) < 256 / (2 * len) :=
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_div_cancel' hdiv]; exact hidx)
    have hq_le : (idx / (2 * len) + 1) * (2 * len) ≤ 256 := by
      calc (idx / (2 * len) + 1) * (2 * len)
          ≤ (256 / (2 * len)) * (2 * len) := Nat.mul_le_mul_right _ hq_lt
        _ = 256 := by rw [Nat.mul_comm]; exact Nat.mul_div_cancel' hdiv
    have hsucc : (idx / (2 * len) + 1) * (2 * len) = (2 * len) * (idx / (2 * len)) + 2 * len := by
      rw [Nat.succ_mul, Nat.mul_comm]
    have hd := Nat.div_add_mod idx (2 * len)
    omega
  refine ⟨rfl, rfl, ⟨hsz_f, fun idx hidx => ?_⟩,
    ⟨hsz_p, fun idx hidx => ?_⟩, ⟨hsz_p, fun idx hidx => ?_⟩⟩
  · rw [butterflyStage_getD pairF 0 hf.1 hlen hdiv hidx]
    dsimp only [pairF]
    by_cases hhalf : idx % (2 * len) < len <;>
      simp only [hhalf, ↓reduceIte] <;> exact Nat.mod_lt _ (by decide)
  · rw [butterflyStage_getD pairP 0#16 hbnd.1 hlen hdiv hidx]
    dsimp only [pairP, invStageOutBound]
    have hblk : kInit - idx / (2 * len) < 128 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hk
    by_cases hhalf : idx % (2 * len) < len
    · simp only [hhalf, ↓reduceIte]
      have hjl := hjl_of_half idx hidx hhalf
      have ha := hbnd.2 idx hidx
      have hb := hbnd.2 (idx + len) hjl
      cases barrettFirst
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hsum := toInt_add_of_bounds (a := p.getD idx 0#16) (b := p.getD (idx + len) 0#16)
          (by omega) (by omega)
        omega
      · simp only [↓reduceIte]
        have hbar := neonBarrettReduce16_spec (p.getD idx 0#16 + p.getD (idx + len) 0#16)
        omega
    · simp only [hhalf, ↓reduceIte]
      have hm := neonMontgomeryMul16_zeta_spec hblk (p.getD idx 0#16 - p.getD (idx - len) 0#16)
      cases barrettFirst <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  · rw [butterflyStage_getD pairP 0#16 hbnd.1 hlen hdiv hidx,
      butterflyStage_getD pairF 0 hf.1 hlen hdiv hidx]
    dsimp only [pairP, pairF]
    have hblk : kInit - idx / (2 * len) < 128 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hk
    by_cases hhalf : idx % (2 * len) < len
    · simp only [hhalf, ↓reduceIte]
      have hjl := hjl_of_half idx hidx hhalf
      have ha_b := hbnd.2 idx hidx
      have hb_b := hbnd.2 (idx + len) hjl
      exact (inv_butterfly_montInv_mod hblk barrettFirst (hf.2 idx hidx)
        (hrep.2 idx hidx) (hrep.2 (idx + len) hjl)
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).1
    · simp only [hhalf, ↓reduceIte]
      have hij : idx - len < 256 := by omega
      have ha_b := hbnd.2 (idx - len) hij
      have hb_b := hbnd.2 idx hidx
      exact (inv_butterfly_montInv_mod hblk barrettFirst (hf.2 (idx - len) hij)
        (hrep.2 (idx - len) hij) (hrep.2 idx hidx)
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).2

/-- Soundness & signed bound of one `neonInvNttStage16` stage in the standard (`PolyRepresents`) domain. -/
theorem neonInvNttStage16_std_spec {B : Int} (len kInit : Nat) (barrettFirst : Bool)
    {p : Poly16} {f : Poly}
    (hbnd : PolyBounded16 B p) (hrep : PolyRepresents p f) (hf : PolyCanonical f)
    (hB0 : 0 ≤ B) (hBmax : B ≤ 16000)
    (hlen : 0 < len) (hdiv : 2 * len ∣ 256) (hk : kInit < 128) :
    (neonInvNttStage16 len kInit barrettFirst p).2 = kInit - 256 / (2 * len) ∧
    (invNttStage len kInit f).2 = kInit - 256 / (2 * len) ∧
    PolyCanonical (invNttStage len kInit f).1 ∧
    PolyBounded16 (invStageOutBound barrettFirst B) (neonInvNttStage16 len kInit barrettFirst p).1 ∧
    PolyRepresents (neonInvNttStage16 len kInit barrettFirst p).1 (invNttStage len kInit f).1 := by
  rw [neonInvNttStage16_eq_butterfly, invNttStage_eq_butterfly]
  dsimp only
  let pairP : Nat → BitVec 16 → BitVec 16 → BitVec 16 × BitVec 16 := fun blk a b =>
    let sum := a + b
    let a' := if barrettFirst then neonBarrettReduce16 sum else sum
    let b' := neonMontgomeryMul16 (b - a) (zetasTimesMontgomeryR.getD (kInit - blk) 0#16)
    (a', b')
  let pairF : Nat → Nat → Nat → Nat × Nat := fun blk t fjl =>
    let zeta := fipsZetas.getD (kInit - blk) 0
    ((t + fjl) % mlkemQ, (zeta * (fjl + mlkemQ - t)) % mlkemQ)
  have hsz_p := butterflyStage_size pairP 0#16 hbnd.1 hlen hdiv
  have hsz_f := butterflyStage_size pairF 0 hf.1 hlen hdiv
  have hjl_of_half : ∀ idx < 256, idx % (2 * len) < len → idx + len < 256 := by
    intro idx hidx hhalf
    have hq_lt : idx / (2 * len) < 256 / (2 * len) :=
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_div_cancel' hdiv]; exact hidx)
    have hq_le : (idx / (2 * len) + 1) * (2 * len) ≤ 256 := by
      calc (idx / (2 * len) + 1) * (2 * len)
          ≤ (256 / (2 * len)) * (2 * len) := Nat.mul_le_mul_right _ hq_lt
        _ = 256 := by rw [Nat.mul_comm]; exact Nat.mul_div_cancel' hdiv
    have hsucc : (idx / (2 * len) + 1) * (2 * len) = (2 * len) * (idx / (2 * len)) + 2 * len := by
      rw [Nat.succ_mul, Nat.mul_comm]
    have hd := Nat.div_add_mod idx (2 * len)
    omega
  refine ⟨rfl, rfl, ⟨hsz_f, fun idx hidx => ?_⟩,
    ⟨hsz_p, fun idx hidx => ?_⟩, ⟨hsz_p, fun idx hidx => ?_⟩⟩
  · rw [butterflyStage_getD pairF 0 hf.1 hlen hdiv hidx]
    dsimp only [pairF]
    by_cases hhalf : idx % (2 * len) < len <;>
      simp only [hhalf, ↓reduceIte] <;> exact Nat.mod_lt _ (by decide)
  · rw [butterflyStage_getD pairP 0#16 hbnd.1 hlen hdiv hidx]
    dsimp only [pairP, invStageOutBound]
    have hblk : kInit - idx / (2 * len) < 128 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hk
    by_cases hhalf : idx % (2 * len) < len
    · simp only [hhalf, ↓reduceIte]
      have hjl := hjl_of_half idx hidx hhalf
      have ha := hbnd.2 idx hidx
      have hb := hbnd.2 (idx + len) hjl
      cases barrettFirst
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hsum := toInt_add_of_bounds (a := p.getD idx 0#16) (b := p.getD (idx + len) 0#16)
          (by omega) (by omega)
        omega
      · simp only [↓reduceIte]
        have hbar := neonBarrettReduce16_spec (p.getD idx 0#16 + p.getD (idx + len) 0#16)
        omega
    · simp only [hhalf, ↓reduceIte]
      have hm := neonMontgomeryMul16_zeta_spec hblk (p.getD idx 0#16 - p.getD (idx - len) 0#16)
      cases barrettFirst <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  · rw [butterflyStage_getD pairP 0#16 hbnd.1 hlen hdiv hidx,
      butterflyStage_getD pairF 0 hf.1 hlen hdiv hidx]
    dsimp only [pairP, pairF]
    have hblk : kInit - idx / (2 * len) < 128 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hk
    by_cases hhalf : idx % (2 * len) < len
    · simp only [hhalf, ↓reduceIte]
      have hjl := hjl_of_half idx hidx hhalf
      have ha_b := hbnd.2 idx hidx
      have hb_b := hbnd.2 (idx + len) hjl
      exact (inv_butterfly_std_mod hblk barrettFirst (hf.2 idx hidx)
        (hrep.2 idx hidx) (hrep.2 (idx + len) hjl)
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).1
    · simp only [hhalf, ↓reduceIte]
      have hij : idx - len < 256 := by omega
      have ha_b := hbnd.2 (idx - len) hij
      have hb_b := hbnd.2 idx hidx
      exact (inv_butterfly_std_mod hblk barrettFirst (hf.2 (idx - len) hij)
        (hrep.2 (idx - len) hij) (hrep.2 idx hidx)
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).2

/-- Pre-scaled 7-stage `invNtt` (`polyInvNtt` before final `* 3303 % 3329` normalization). -/
@[expose] def invNttStagesOnly (f : Poly) : Poly :=
  let (f, k) := invNttStage 2 127 f
  let (f, k) := invNttStage 4 k f
  let (f, k) := invNttStage 8 k f
  let (f, k) := invNttStage 16 k f
  let (f, k) := invNttStage 32 k f
  let (f, k) := invNttStage 64 k f
  let (f, _) := invNttStage 128 k f
  f

theorem polyInvNtt_eq_map_3303 (f : Poly) :
    polyInvNtt f = (invNttStagesOnly f).map (fun c => (c * 3303) % mlkemQ) :=
  rfl

/-- Full 7-stage `neonInvNttMontgomery16` soundness on `R⁻¹`-domain dot products (`B ≤ 8704`,
    covering both `K = 3` (`8320`) and `K = 4` (`8704`)). -/
theorem neonInvNttMontgomery16_montInv_spec {dot : Poly16} {f : Poly}
    (hbnd : PolyBounded16 8704 dot) (hrep : PolyRepresentsMontInv dot f) (hf : PolyCanonical f) :
    PolyCanonical (invNttStagesOnly f) ∧
    PolyBounded16 1664 (neonInvNttMontgomery16 dot) ∧
    PolyRepresentsMontInv (neonInvNttMontgomery16 dot) (invNttStagesOnly f) := by
  unfold neonInvNttMontgomery16 invNttStagesOnly
  obtain ⟨hk1, hfk1, hfc1, hb1, hr1⟩ :=
    neonInvNttStage16_montInv_spec 2 127 true hbnd hrep hf (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases hp1 : neonInvNttStage16 2 127 true dot with ⟨p1, kp1⟩
  rcases hf1 : invNttStage 2 127 f with ⟨f1, kf1⟩
  rw [hp1] at hk1 hb1 hr1; rw [hf1] at hfk1 hfc1 hr1; dsimp only at hk1 hfk1 hb1 hr1 hfc1 ⊢
  subst hk1; subst hfk1
  obtain ⟨hk2, hfk2, hfc2, hb2, hr2⟩ :=
    neonInvNttStage16_montInv_spec 4 63 false hb1 hr1 hfc1 (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases hp2 : neonInvNttStage16 4 63 false p1 with ⟨p2, kp2⟩
  rcases hf2 : invNttStage 4 63 f1 with ⟨f2, kf2⟩
  rw [hp2] at hk2 hb2 hr2; rw [hf2] at hfk2 hfc2 hr2; dsimp only at hk2 hfk2 hb2 hr2 hfc2 ⊢
  subst hk2; subst hfk2
  obtain ⟨hk3, hfk3, hfc3, hb3, hr3⟩ :=
    neonInvNttStage16_montInv_spec 8 31 false hb2 hr2 hfc2 (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases hp3 : neonInvNttStage16 8 31 false p2 with ⟨p3, kp3⟩
  rcases hf3 : invNttStage 8 31 f2 with ⟨f3, kf3⟩
  rw [hp3] at hk3 hb3 hr3; rw [hf3] at hfk3 hfc3 hr3; dsimp only at hk3 hfk3 hb3 hr3 hfc3 ⊢
  subst hk3; subst hfk3
  obtain ⟨hk4, hfk4, hfc4, hb4, hr4⟩ :=
    neonInvNttStage16_montInv_spec 16 15 true hb3 hr3 hfc3 (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases hp4 : neonInvNttStage16 16 15 true p3 with ⟨p4, kp4⟩
  rcases hf4 : invNttStage 16 15 f3 with ⟨f4, kf4⟩
  rw [hp4] at hk4 hb4 hr4; rw [hf4] at hfk4 hfc4 hr4; dsimp only at hk4 hfk4 hb4 hr4 hfc4 ⊢
  subst hk4; subst hfk4
  obtain ⟨hk5, hfk5, hfc5, hb5, hr5⟩ :=
    neonInvNttStage16_montInv_spec 32 7 true hb4 hr4 hfc4 (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases hp5 : neonInvNttStage16 32 7 true p4 with ⟨p5, kp5⟩
  rcases hf5 : invNttStage 32 7 f4 with ⟨f5, kf5⟩
  rw [hp5] at hk5 hb5 hr5; rw [hf5] at hfk5 hfc5 hr5; dsimp only at hk5 hfk5 hb5 hr5 hfc5 ⊢
  subst hk5; subst hfk5
  obtain ⟨hk6, hfk6, hfc6, hb6, hr6⟩ :=
    neonInvNttStage16_montInv_spec 64 3 true hb5 hr5 hfc5 (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases hp6 : neonInvNttStage16 64 3 true p5 with ⟨p6, kp6⟩
  rcases hf6 : invNttStage 64 3 f5 with ⟨f6, kf6⟩
  rw [hp6] at hk6 hb6 hr6; rw [hf6] at hfk6 hfc6 hr6; dsimp only at hk6 hfk6 hb6 hr6 hfc6 ⊢
  subst hk6; subst hfk6
  obtain ⟨_, _, hfc7, _, hr7⟩ :=
    neonInvNttStage16_montInv_spec 128 1 true hb6 hr6 hfc6 (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases hp7 : neonInvNttStage16 128 1 true p6 with ⟨p7, kp7⟩
  rcases hf7 : invNttStage 128 1 f6 with ⟨f7, kf7⟩
  rw [hp7] at hr7; rw [hf7] at hfc7 hr7; dsimp only at hfc7 hr7 ⊢
  have hsz_map : (p7.map neonBarrettReduce16).size = 256 := by simp [hr7.1]
  refine ⟨hfc7, ⟨hsz_map, fun i hi => ?_⟩, ⟨hsz_map, fun i hi => ?_⟩⟩
  · have hmap : (p7.map neonBarrettReduce16).getD i 0#16 = neonBarrettReduce16 (p7.getD i 0#16) := by
      simp [Array.getD, hr7.1, hi]
    rw [hmap]
    have hb := neonBarrettReduce16_spec (p7.getD i 0#16)
    exact ⟨hb.1, hb.2.1⟩
  · have hmap : (p7.map neonBarrettReduce16).getD i 0#16 = neonBarrettReduce16 (p7.getD i 0#16) := by
      simp [Array.getD, hr7.1, hi]
    rw [hmap, Int.mul_emod, (neonBarrettReduce16_spec (p7.getD i 0#16)).2.2, ← Int.mul_emod]
    exact hr7.2 i hi

/-- Full 7-stage `neonInvNttMontgomery16` soundness on standard-domain inputs (`B ≤ 8704`). -/
theorem neonInvNttMontgomery16_std_spec {p : Poly16} {f : Poly}
    (hbnd : PolyBounded16 8704 p) (hrep : PolyRepresents p f) (hf : PolyCanonical f) :
    PolyCanonical (invNttStagesOnly f) ∧
    PolyBounded16 1664 (neonInvNttMontgomery16 p) ∧
    PolyRepresents (neonInvNttMontgomery16 p) (invNttStagesOnly f) := by
  unfold neonInvNttMontgomery16 invNttStagesOnly
  obtain ⟨hk1, hfk1, hfc1, hb1, hr1⟩ :=
    neonInvNttStage16_std_spec 2 127 true hbnd hrep hf (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases hp1 : neonInvNttStage16 2 127 true p with ⟨p1, kp1⟩
  rcases hf1 : invNttStage 2 127 f with ⟨f1, kf1⟩
  rw [hp1] at hk1 hb1 hr1; rw [hf1] at hfk1 hfc1 hr1; dsimp only at hk1 hfk1 hb1 hr1 hfc1 ⊢
  subst hk1; subst hfk1
  obtain ⟨hk2, hfk2, hfc2, hb2, hr2⟩ :=
    neonInvNttStage16_std_spec 4 63 false hb1 hr1 hfc1 (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases hp2 : neonInvNttStage16 4 63 false p1 with ⟨p2, kp2⟩
  rcases hf2 : invNttStage 4 63 f1 with ⟨f2, kf2⟩
  rw [hp2] at hk2 hb2 hr2; rw [hf2] at hfk2 hfc2 hr2; dsimp only at hk2 hfk2 hb2 hr2 hfc2 ⊢
  subst hk2; subst hfk2
  obtain ⟨hk3, hfk3, hfc3, hb3, hr3⟩ :=
    neonInvNttStage16_std_spec 8 31 false hb2 hr2 hfc2 (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases hp3 : neonInvNttStage16 8 31 false p2 with ⟨p3, kp3⟩
  rcases hf3 : invNttStage 8 31 f2 with ⟨f3, kf3⟩
  rw [hp3] at hk3 hb3 hr3; rw [hf3] at hfk3 hfc3 hr3; dsimp only at hk3 hfk3 hb3 hr3 hfc3 ⊢
  subst hk3; subst hfk3
  obtain ⟨hk4, hfk4, hfc4, hb4, hr4⟩ :=
    neonInvNttStage16_std_spec 16 15 true hb3 hr3 hfc3 (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases hp4 : neonInvNttStage16 16 15 true p3 with ⟨p4, kp4⟩
  rcases hf4 : invNttStage 16 15 f3 with ⟨f4, kf4⟩
  rw [hp4] at hk4 hb4 hr4; rw [hf4] at hfk4 hfc4 hr4; dsimp only at hk4 hfk4 hb4 hr4 hfc4 ⊢
  subst hk4; subst hfk4
  obtain ⟨hk5, hfk5, hfc5, hb5, hr5⟩ :=
    neonInvNttStage16_std_spec 32 7 true hb4 hr4 hfc4 (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases hp5 : neonInvNttStage16 32 7 true p4 with ⟨p5, kp5⟩
  rcases hf5 : invNttStage 32 7 f4 with ⟨f5, kf5⟩
  rw [hp5] at hk5 hb5 hr5; rw [hf5] at hfk5 hfc5 hr5; dsimp only at hk5 hfk5 hb5 hr5 hfc5 ⊢
  subst hk5; subst hfk5
  obtain ⟨hk6, hfk6, hfc6, hb6, hr6⟩ :=
    neonInvNttStage16_std_spec 64 3 true hb5 hr5 hfc5 (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases hp6 : neonInvNttStage16 64 3 true p5 with ⟨p6, kp6⟩
  rcases hf6 : invNttStage 64 3 f5 with ⟨f6, kf6⟩
  rw [hp6] at hk6 hb6 hr6; rw [hf6] at hfk6 hfc6 hr6; dsimp only at hk6 hfk6 hb6 hr6 hfc6 ⊢
  subst hk6; subst hfk6
  obtain ⟨_, _, hfc7, _, hr7⟩ :=
    neonInvNttStage16_std_spec 128 1 true hb6 hr6 hfc6 (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases hp7 : neonInvNttStage16 128 1 true p6 with ⟨p7, kp7⟩
  rcases hf7 : invNttStage 128 1 f6 with ⟨f7, kf7⟩
  rw [hp7] at hr7; rw [hf7] at hfc7 hr7; dsimp only at hfc7 hr7 ⊢
  exact ⟨hfc7, neonBarrettReducePoly16_spec hr7⟩

/-- Complete NEON `ntt_multiply → invert_ntt_montgomery → montgomery_mul(1441)` pipeline (`B03`,
    `B04`, `B06`, `B07`, `B20`): maps an `R⁻¹`-domain polynomial `dot` (`PolyBounded16 8704`)
    to standard-domain `Spec.polyInvNtt f` (`PolyBounded16 2496`). -/
@[expose] def neonPolyInvNttFromMontInv16 (dot : Poly16) : Poly16 :=
  (neonInvNttMontgomery16 dot).map (fun c => neonMontgomeryMul16 c 1441#16)

private theorem invNttStage_size {len kInit : Nat} {f : Poly}
    (hf : f.size = 256) (hlen : 0 < len) (hdiv : 2 * len ∣ 256) :
    (invNttStage len kInit f).1.size = 256 := by
  rw [invNttStage_eq_butterfly]
  exact butterflyStage_size _ 0 hf hlen hdiv

theorem polyInvNtt_canonical {f : Poly} (hf : PolyCanonical f) : PolyCanonical (polyInvNtt f) := by
  rw [polyInvNtt_eq_map_3303]
  have hsz : (invNttStagesOnly f).size = 256 := by
    unfold invNttStagesOnly
    have s1 := invNttStage_size (len := 2) (kInit := 127) hf.1 (by decide) (by decide)
    rcases e1 : invNttStage 2 127 f with ⟨f1, k1⟩; rw [e1] at s1; dsimp only at s1 ⊢
    have s2 := invNttStage_size (len := 4) (kInit := k1) s1 (by decide) (by decide)
    rcases e2 : invNttStage 4 k1 f1 with ⟨f2, k2⟩; rw [e2] at s2; dsimp only at s2 ⊢
    have s3 := invNttStage_size (len := 8) (kInit := k2) s2 (by decide) (by decide)
    rcases e3 : invNttStage 8 k2 f2 with ⟨f3, k3⟩; rw [e3] at s3; dsimp only at s3 ⊢
    have s4 := invNttStage_size (len := 16) (kInit := k3) s3 (by decide) (by decide)
    rcases e4 : invNttStage 16 k3 f3 with ⟨f4, k4⟩; rw [e4] at s4; dsimp only at s4 ⊢
    have s5 := invNttStage_size (len := 32) (kInit := k4) s4 (by decide) (by decide)
    rcases e5 : invNttStage 32 k4 f4 with ⟨f5, k5⟩; rw [e5] at s5; dsimp only at s5 ⊢
    have s6 := invNttStage_size (len := 64) (kInit := k5) s5 (by decide) (by decide)
    rcases e6 : invNttStage 64 k5 f5 with ⟨f6, k6⟩; rw [e6] at s6; dsimp only at s6 ⊢
    have s7 := invNttStage_size (len := 128) (kInit := k6) s6 (by decide) (by decide)
    rcases e7 : invNttStage 128 k6 f6 with ⟨f7, k7⟩; rw [e7] at s7; exact s7
  refine ⟨by simp [hsz], fun i hi => ?_⟩
  have hget : ((invNttStagesOnly f).map (fun c => (c * 3303) % mlkemQ)).getD i 0 =
      ((invNttStagesOnly f).getD i 0 * 3303) % mlkemQ := by
    simp [Array.getD, hsz, hi]
  rw [hget]
  exact Nat.mod_lt _ (by decide : 0 < mlkemQ)

private theorem mul_1441_3303_mod {outInt : Int} {fsNat : Nat}
    (h128 : (128 * outInt) % 3329 = (fsNat : Int) % 3329) :
    outInt % 3329 = (((fsNat * 3303) % mlkemQ : Nat) : Int) % 3329 := by
  have h3303 : (3303 * (128 * outInt)) % 3329 = (3303 * (fsNat : Int)) % 3329 := by
    rw [Int.mul_emod, h128, ← Int.mul_emod]
  have hlhs : (3303 * (128 * outInt)) % 3329 = outInt % 3329 := by omega
  rw [← hlhs, h3303]
  dsimp only [mlkemQ]
  omega

theorem neonPolyInvNttFromMontInv16_spec {dot : Poly16} {f : Poly}
    (hbnd : PolyBounded16 8704 dot) (hrep : PolyRepresentsMontInv dot f) (hf : PolyCanonical f) :
    PolyCanonical (polyInvNtt f) ∧
    PolyBounded16 2496 (neonPolyInvNttFromMontInv16 dot) ∧
    PolyRepresents (neonPolyInvNttFromMontInv16 dot) (polyInvNtt f) := by
  obtain ⟨hfc, hinv_b, hinv_r⟩ := neonInvNttMontgomery16_montInv_spec hbnd hrep hf
  refine ⟨polyInvNtt_canonical hf, ?_⟩
  unfold neonPolyInvNttFromMontInv16
  rw [polyInvNtt_eq_map_3303]
  let inv := neonInvNttMontgomery16 dot
  let fs := invNttStagesOnly f
  have hinv_sz : inv.size = 256 := hinv_b.1
  have hfs_sz : fs.size = 256 := hfc.1
  have hsz_out : (inv.map (fun c => neonMontgomeryMul16 c 1441#16)).size = 256 := by simp [hinv_sz]
  refine ⟨⟨hsz_out, fun i hi => ?_⟩, ⟨hsz_out, fun i hi => ?_⟩⟩
  · have hmap : (inv.map (fun c => neonMontgomeryMul16 c 1441#16)).getD i 0#16 =
        neonMontgomeryMul16 (inv.getD i 0#16) 1441#16 := by
      simp [Array.getD, hinv_sz, hi]
    rw [hmap]
    have hm := neonMontgomeryMul16_1441 (inv.getD i 0#16)
    exact ⟨hm.2.1, hm.2.2⟩
  · have hmap_p : (inv.map (fun c => neonMontgomeryMul16 c 1441#16)).getD i 0#16 =
        neonMontgomeryMul16 (inv.getD i 0#16) 1441#16 := by
      simp [Array.getD, hinv_sz, hi]
    have hmap_f : (fs.map (fun c => (c * 3303) % mlkemQ)).getD i 0 =
        (fs.getD i 0 * 3303) % mlkemQ := by
      simp [Array.getD, hfs_sz, hi]
    rw [hmap_p, hmap_f]
    have hm1441 := (neonMontgomeryMul16_1441 (inv.getD i 0#16)).1
    exact mul_1441_3303_mod (hm1441.trans (hinv_r.2 i hi))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.InvNtt
