/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import

/-!
# `decapsulate_compressed_key` (`B04`) — Flat Spill Vector Structures (`Spill6`, `Spill21`)

Complements `Encaps2.VecMem.Spill13` (`[sp + 1616 .. 1824)`, `13` vectors) with:
- `Spill6` (`[sp + 1824 .. 1920)`, `6` vectors, `96` bytes),
- `Spill21` (`[sp + 1920 .. 2256)`, `21` vectors, `336` bytes),
partitioning the 40-vector (`640`-byte) `B04` NEON spill region `[sp + 1616 .. 2256)` into exact
per-segment ownership bands (`21` for `Fwd1`/`Inv1`/`Inv3`, `6 + 21 = 27` for `Inv2`, and
`13 + 6 + 21 = 40` for `Fwd2`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem

open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  VecRangeMem vecRangeMem_congr vecRangeMem_entails_memRegion
  SepLoad128 SepStore128
)

/-! ## 1. `Spill6` (`6 × 128`-bit vectors = `96` bytes) -/

structure Spill6 where
  (s0 s1 s2 s3 s4 s5 : BitVec 128)

@[expose] def Spill6.get (t : Spill6) : Nat → BitVec 128
  | 0 => t.s0 | 1 => t.s1 | 2 => t.s2 | 3 => t.s3 | 4 => t.s4 | 5 => t.s5
  | _ => 0#128

@[expose] def Spill6.set (t : Spill6) (k : Nat) (x : BitVec 128) : Spill6 :=
  match k with
  | 0 => { t with s0 := x } | 1 => { t with s1 := x } | 2 => { t with s2 := x }
  | 3 => { t with s3 := x } | 4 => { t with s4 := x } | 5 => { t with s5 := x }
  | _ => t

@[expose] def Spill6.ofFn (f : Nat → BitVec 128) : Spill6 :=
  ⟨f 0, f 1, f 2, f 3, f 4, f 5⟩

@[expose] def Spill6.zero : Spill6 := Spill6.ofFn (fun _ => 0#128)
@[expose] def Spill6Mem (ptr : BitVec 64) (t : Spill6) : SepProp := VecRangeMem 6 ptr t.get

theorem spill6_ofFn_get (f : Nat → BitVec 128) (i : Nat) (hi : i < 6) :
    (Spill6.ofFn f).get i = f i := by
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 => rfl
  | _ + 6 => omega

theorem spill6Mem_ofFn (ptr : BitVec 64) (f : Nat → BitVec 128) :
    Spill6Mem ptr (Spill6.ofFn f) = VecRangeMem 6 ptr f :=
  vecRangeMem_congr fun i hi => spill6_ofFn_get f i hi

theorem spill6Mem_entails_memRegion (ptr : BitVec 64) (t : Spill6) :
    Spill6Mem ptr t ⊢ memRegion ptr 96 :=
  vecRangeMem_entails_memRegion 6 ptr t.get

private theorem spill6_set_eq_ofFn (t : Spill6) (k : Nat) (x : BitVec 128) (hk : k < 6) :
    t.set k x = Spill6.ofFn (fun j => if j = k then x else t.get j) := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 => rfl
  | _ + 6 => omega

theorem spill6_set_get (t : Spill6) (k : Nat) (x : BitVec 128) (hk : k < 6)
    (i : Nat) (hi : i < 6) :
    Function.update t.get k x i = (t.set k x).get i := by
  rw [spill6_set_eq_ofFn t k x hk, spill6_ofFn_get _ i hi]
  by_cases h : i = k <;> simp [h]

theorem SepLoad128.spill6 {k : Nat} {ea ptr : BitVec 64} {t : Spill6} {v : BitVec 128}
    (hk : k < 6) (ha : ptr + BitVec.ofNat 64 (16 * k) = ea) (hv : t.get k = v) :
    SepLoad128 ea (Spill6Mem ptr t) v := by
  rw [← hv]; exact SepLoad128.vecRange hk ha

theorem SepStore128.spill6 {k : Nat} {ea ptr : BitVec 64} {t t' : Spill6} {val : BitVec 128}
    (hk : k < 6) (ha : ptr + BitVec.ofNat 64 (16 * k) = ea) (ht : t.set k val = t') :
    SepStore128 ea val (Spill6Mem ptr t) (Spill6Mem ptr t') := by
  rw [← ht]; unfold Spill6Mem
  rw [← vecRangeMem_congr (spill6_set_get t k val hk)]
  exact SepStore128.vecRange hk ha

/-! ## 2. `Spill21` (`21 × 128`-bit vectors = `336` bytes) -/

structure Spill21 where
  (s0 s1 s2 s3 s4 s5 s6 s7 : BitVec 128)
  (s8 s9 s10 s11 s12 s13 s14 s15 : BitVec 128)
  (s16 s17 s18 s19 s20 : BitVec 128)

@[expose] def Spill21.get (t : Spill21) : Nat → BitVec 128
  | 0 => t.s0 | 1 => t.s1 | 2 => t.s2 | 3 => t.s3 | 4 => t.s4 | 5 => t.s5 | 6 => t.s6 | 7 => t.s7
  | 8 => t.s8 | 9 => t.s9 | 10 => t.s10 | 11 => t.s11 | 12 => t.s12 | 13 => t.s13 | 14 => t.s14 | 15 => t.s15
  | 16 => t.s16 | 17 => t.s17 | 18 => t.s18 | 19 => t.s19 | 20 => t.s20
  | _ => 0#128

@[expose] def Spill21.set (t : Spill21) (k : Nat) (x : BitVec 128) : Spill21 :=
  match k with
  | 0 => { t with s0 := x } | 1 => { t with s1 := x } | 2 => { t with s2 := x } | 3 => { t with s3 := x }
  | 4 => { t with s4 := x } | 5 => { t with s5 := x } | 6 => { t with s6 := x } | 7 => { t with s7 := x }
  | 8 => { t with s8 := x } | 9 => { t with s9 := x } | 10 => { t with s10 := x } | 11 => { t with s11 := x }
  | 12 => { t with s12 := x } | 13 => { t with s13 := x } | 14 => { t with s14 := x } | 15 => { t with s15 := x }
  | 16 => { t with s16 := x } | 17 => { t with s17 := x } | 18 => { t with s18 := x } | 19 => { t with s19 := x }
  | 20 => { t with s20 := x }
  | _ => t

@[expose] def Spill21.ofFn (f : Nat → BitVec 128) : Spill21 :=
  ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7,
   f 8, f 9, f 10, f 11, f 12, f 13, f 14, f 15,
   f 16, f 17, f 18, f 19, f 20⟩

@[expose] def Spill21.zero : Spill21 := Spill21.ofFn (fun _ => 0#128)
@[expose] def Spill21Mem (ptr : BitVec 64) (t : Spill21) : SepProp := VecRangeMem 21 ptr t.get

theorem spill21_ofFn_get (f : Nat → BitVec 128) (i : Nat) (hi : i < 21) :
    (Spill21.ofFn f).get i = f i := by
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 => rfl
  | _ + 21 => omega

theorem spill21Mem_ofFn (ptr : BitVec 64) (f : Nat → BitVec 128) :
    Spill21Mem ptr (Spill21.ofFn f) = VecRangeMem 21 ptr f :=
  vecRangeMem_congr fun i hi => spill21_ofFn_get f i hi

theorem spill21Mem_entails_memRegion (ptr : BitVec 64) (t : Spill21) :
    Spill21Mem ptr t ⊢ memRegion ptr 336 :=
  vecRangeMem_entails_memRegion 21 ptr t.get

private theorem spill21_set_eq_ofFn (t : Spill21) (k : Nat) (x : BitVec 128) (hk : k < 21) :
    t.set k x = Spill21.ofFn (fun j => if j = k then x else t.get j) := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 => rfl
  | _ + 21 => omega

theorem spill21_set_get (t : Spill21) (k : Nat) (x : BitVec 128) (hk : k < 21)
    (i : Nat) (hi : i < 21) :
    Function.update t.get k x i = (t.set k x).get i := by
  rw [spill21_set_eq_ofFn t k x hk, spill21_ofFn_get _ i hi]
  by_cases h : i = k <;> simp [h]

theorem SepLoad128.spill21 {k : Nat} {ea ptr : BitVec 64} {t : Spill21} {v : BitVec 128}
    (hk : k < 21) (ha : ptr + BitVec.ofNat 64 (16 * k) = ea) (hv : t.get k = v) :
    SepLoad128 ea (Spill21Mem ptr t) v := by
  rw [← hv]; exact SepLoad128.vecRange hk ha

theorem SepStore128.spill21 {k : Nat} {ea ptr : BitVec 64} {t t' : Spill21} {val : BitVec 128}
    (hk : k < 21) (ha : ptr + BitVec.ofNat 64 (16 * k) = ea) (ht : t.set k val = t') :
    SepStore128 ea val (Spill21Mem ptr t) (Spill21Mem ptr t') := by
  rw [← ht]; unfold Spill21Mem
  rw [← vecRangeMem_congr (spill21_set_get t k val hk)]
  exact SepStore128.vecRange hk ha

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem
