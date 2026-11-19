/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model

/-!
# Bit-Index Characterization of `bitslice`, `invBitslice`, and `shiftRows1..3` (`Fixslice64.Packing`)

Proves `bv_decide`-free bit-routing characterizations of the 64-bit fixslicing packing/unpacking
routines and ShiftRows powers:
- `getLsbD_bitslice`: slice `p` (`< 8`), bit `16 * r + 4 * c + lane` (`r, c, lane < 4`) of
  `bitslice bs` equals bit `p` of byte `r + 4 * c` of `bs.getLane lane`;
- `invBitslice_bitslice`, `bitslice_invBitslice`, and `eq_bitslice_of_getLsbD`;
- `shiftRowsPow` / `invShiftRowsPow` algebraic laws and `shiftRows1..3` / `invShiftRows1..3`
  commutation with `bitslice`.
-/

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Packing

open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Spec.Aes256
  (State subBytes invSubBytes shiftRows invShiftRows addRoundKey)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model
  (FsState Blocks4 deltaSwap1 deltaSwap2 readReordered bitslice writeReorderedPair invBitslice
   shiftRows1 shiftRows2 shiftRows3 invShiftRows1 invShiftRows2 invShiftRows3)

/-! ## Well-Formed 4-Block Batches and 16-Byte State Extensionality -/

/-- All four lanes of `bs` are 16-byte AES states. -/
@[expose] def Blocks4.Wf (bs : Blocks4) : Prop :=
  bs.b0.length = 16 ∧ bs.b1.length = 16 ∧ bs.b2.length = 16 ∧ bs.b3.length = 16

theorem Blocks4.wf_map {f : State → State} (hf : ∀ s, s.length = 16 → (f s).length = 16)
    {bs : Blocks4} (h : Blocks4.Wf bs) : Blocks4.Wf (bs.map f) :=
  ⟨hf _ h.1, hf _ h.2.1, hf _ h.2.2.1, hf _ h.2.2.2⟩

theorem Blocks4.wf_replicate {s : State} (hs : s.length = 16) :
    Blocks4.Wf (Blocks4.replicate s) :=
  ⟨hs, hs, hs, hs⟩

theorem state_eq_of_getD {s t : State} (hs : s.length = 16) (ht : t.length = 16)
    (h : ∀ j : Nat, j < 16 → s.getD j 0#8 = t.getD j 0#8) : s = t := by
  apply List.ext_getElem (by omega)
  intro j hj1 hj2
  have hj : j < 16 := by omega
  have h1 : s.getD j 0#8 = s[j] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj1]; rfl
  have h2 : t.getD j 0#8 = t[j] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj2]; rfl
  exact h1.symm.trans ((h j hj).trans h2)

theorem state_eta16 {s : State} (hs : s.length = 16) :
    s = [s.getD 0 0#8, s.getD 1 0#8, s.getD 2 0#8, s.getD 3 0#8,
         s.getD 4 0#8, s.getD 5 0#8, s.getD 6 0#8, s.getD 7 0#8,
         s.getD 8 0#8, s.getD 9 0#8, s.getD 10 0#8, s.getD 11 0#8,
         s.getD 12 0#8, s.getD 13 0#8, s.getD 14 0#8, s.getD 15 0#8] := by
  apply state_eq_of_getD hs rfl
  intro j hj
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _
  | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ => rfl
  | _ + 16, hj => omega

/-! ## Pure Index-Routing Lemmas for `deltaSwap2` and `deltaSwap1` -/

private theorem ite_true {c : Prop} [Decidable c] {α : Sort _} {t e : α} (h : c) :
    (if c then t else e) = t := by
  split
  · rfl
  · contradiction

private theorem ite_false {c : Prop} [Decidable c] {α : Sort _} {t e : α} (h : ¬ c) :
    (if c then t else e) = e := by
  split
  · contradiction
  · rfl

private theorem dite_true {c : Prop} [Decidable c] {α : Sort _} {t : c → α} {e : ¬ c → α} (h : c) :
    (if hc : c then t hc else e hc) = t h := by
  split
  · rfl
  · contradiction

private theorem dite_false {c : Prop} [Decidable c] {α : Sort _} {t : c → α} {e : ¬ c → α} (h : ¬ c) :
    (if hc : c then t hc else e hc) = e h := by
  split
  · contradiction
  · rfl

private theorem getLsbD_deltaSwap2_fst (a b mask : BitVec 64) (shift : Nat) (k : Fin 64) :
    (deltaSwap2 a b shift mask).1.getLsbD k.val =
      if mask.getLsbD k.val then b.getLsbD (k.val + shift) else a.getLsbD k.val := by
  simp only [deltaSwap2, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  have hadd : shift + k.val = k.val + shift := Nat.add_comm shift k.val
  try rw [hadd]
  cases a.getLsbD k.val <;> cases b.getLsbD (k.val + shift) <;> cases mask.getLsbD k.val <;> rfl

private theorem getLsbD_deltaSwap2_snd (a b mask : BitVec 64) (shift : Nat) (k : Fin 64) :
    (deltaSwap2 a b shift mask).2.getLsbD k.val =
      if decide (shift ≤ k.val) && mask.getLsbD (k.val - shift) then a.getLsbD (k.val - shift)
      else b.getLsbD k.val := by
  simp only [deltaSwap2, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and,
    BitVec.getLsbD_ushiftRight, k.isLt, decide_true, Bool.true_and]
  by_cases hs : k.val < shift
  · have hle : ¬ (shift ≤ k.val) := by omega
    simp [hs, hle]
  · have hle : shift ≤ k.val := by omega
    have h1 : shift + (k.val - shift) = k.val := by omega
    have h2 : (k.val - shift) + shift = k.val := by omega
    simp only [hs, decide_false, Bool.not_false, Bool.true_and, hle, decide_true]
    try rw [h1]
    try rw [h2]
    cases b.getLsbD k.val <;> cases a.getLsbD (k.val - shift) <;>
      cases mask.getLsbD (k.val - shift) <;> rfl

private def routeSwap2Fst {α : Type} (fa fb : Fin 64 → α) (shift : Nat) (mask : BitVec 64)
    (hmask : ∀ k : Fin 64, mask.getLsbD k.val = true → k.val + shift < 64) (k : Fin 64) : α :=
  if h : mask.getLsbD k.val = true then fb ⟨k.val + shift, hmask k h⟩ else fa k

private def routeSwap2Snd {α : Type} (fa fb : Fin 64 → α) (shift : Nat) (mask : BitVec 64)
    (k : Fin 64) : α :=
  if h : shift ≤ k.val ∧ mask.getLsbD (k.val - shift) = true then
    fa ⟨k.val - shift, by omega⟩
  else fb k

private theorem route_deltaSwap2 {α : Type} (f : α → Bool) (fa fb : Fin 64 → α)
    (a b : BitVec 64) (shift : Nat) (mask : BitVec 64)
    (hmask : ∀ k : Fin 64, mask.getLsbD k.val = true → k.val + shift < 64)
    (ha : ∀ k : Fin 64, a.getLsbD k.val = f (fa k))
    (hb : ∀ k : Fin 64, b.getLsbD k.val = f (fb k)) :
    (∀ k : Fin 64, (deltaSwap2 a b shift mask).1.getLsbD k.val =
      f (routeSwap2Fst fa fb shift mask hmask k)) ∧
    (∀ k : Fin 64, (deltaSwap2 a b shift mask).2.getLsbD k.val =
      f (routeSwap2Snd fa fb shift mask k)) := by
  refine ⟨fun k => ?_, fun k => ?_⟩
  · rw [getLsbD_deltaSwap2_fst]
    unfold routeSwap2Fst
    by_cases hm : mask.getLsbD k.val = true
    · rw [ite_true hm, dite_true hm]
      exact hb ⟨k.val + shift, hmask k hm⟩
    · rw [ite_false hm, dite_false hm]
      exact ha k
  · rw [getLsbD_deltaSwap2_snd]
    unfold routeSwap2Snd
    by_cases h : shift ≤ k.val ∧ mask.getLsbD (k.val - shift) = true
    · have hcond : (decide (shift ≤ k.val) && mask.getLsbD (k.val - shift)) = true := by
        rcases h with ⟨hle, hm⟩; simp [hle, hm]
      rw [hcond, ite_true rfl, dite_true h]
      exact ha ⟨k.val - shift, by omega⟩
    · have hcond : (decide (shift ≤ k.val) && mask.getLsbD (k.val - shift)) = false := by
        cases hle : decide (shift ≤ k.val) <;> simp_all
      rw [hcond, ite_false Bool.false_ne_true, dite_false h]
      exact hb k

private def routeSwap1 {α : Type} (fa : Fin 64 → α) (shift : Nat) (mask : BitVec 64)
    (hmask : ∀ k : Fin 64, mask.getLsbD k.val = true → k.val + shift < 64) (k : Fin 64) : α :=
  if h1 : mask.getLsbD k.val = true then
    fa ⟨k.val + shift, hmask k h1⟩
  else if h2 : shift ≤ k.val ∧ mask.getLsbD (k.val - shift) = true then
    fa ⟨k.val - shift, by omega⟩
  else fa k

private theorem getLsbD_deltaSwap1_eq (a mask : BitVec 64) (shift : Nat) (k : Fin 64)
    (hdisj : ¬ (mask.getLsbD k.val = true ∧
      shift ≤ k.val ∧ mask.getLsbD (k.val - shift) = true)) :
    (deltaSwap1 a shift mask).getLsbD k.val =
      if mask.getLsbD k.val = true then a.getLsbD (k.val + shift)
      else if shift ≤ k.val ∧ mask.getLsbD (k.val - shift) = true then a.getLsbD (k.val - shift)
      else a.getLsbD k.val := by
  simp only [deltaSwap1, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and,
    BitVec.getLsbD_ushiftRight, k.isLt, decide_true, Bool.true_and]
  have hadd0 : shift + k.val = k.val + shift := Nat.add_comm shift k.val
  try rw [hadd0]
  by_cases hm1 : mask.getLsbD k.val = true
  · rw [ite_true hm1]
    by_cases hs : k.val < shift
    · simp only [hm1, Bool.and_true, hs, decide_true, Bool.not_true, Bool.false_and, Bool.xor_false]
      cases a.getLsbD k.val <;> cases a.getLsbD (k.val + shift) <;> rfl
    · have hle : shift ≤ k.val := by omega
      have hm2 : mask.getLsbD (k.val - shift) = false := by
        cases h : mask.getLsbD (k.val - shift) <;> simp_all
      simp only [hm1, Bool.and_true, hs, decide_false, Bool.not_false, hm2,
        Bool.and_false, Bool.xor_false]
      cases a.getLsbD k.val <;> cases a.getLsbD (k.val + shift) <;> rfl
  · rw [ite_false hm1]
    have hm1f : mask.getLsbD k.val = false := by cases h : mask.getLsbD k.val <;> simp_all
    by_cases h2 : shift ≤ k.val ∧ mask.getLsbD (k.val - shift) = true
    · rw [ite_true h2]
      rcases h2 with ⟨hle, hm2⟩
      have hs : ¬ (k.val < shift) := by omega
      have h1 : shift + (k.val - shift) = k.val := by omega
      have h2' : (k.val - shift) + shift = k.val := by omega
      simp only [hm1f, Bool.and_false, Bool.xor_false, hs, decide_false, Bool.not_false,
        Bool.true_and, hm2, Bool.and_true]
      try rw [h1]
      try rw [h2']
      cases a.getLsbD k.val <;> cases a.getLsbD (k.val - shift) <;> rfl
    · rw [ite_false h2]
      by_cases hs : k.val < shift
      · simp only [hm1f, Bool.and_false, hs, decide_true, Bool.not_true, Bool.false_and,
          Bool.xor_false]
      · have hle : shift ≤ k.val := by omega
        have hm2 : mask.getLsbD (k.val - shift) = false := by
          cases h : mask.getLsbD (k.val - shift) <;> simp_all
        simp only [hm1f, Bool.and_false, hs, decide_false, Bool.not_false, hm2,
          Bool.xor_false]

private theorem route_deltaSwap1 {α : Type} (f : α → Bool) (fa : Fin 64 → α)
    (a : BitVec 64) (shift : Nat) (mask : BitVec 64)
    (hmask : ∀ k : Fin 64, mask.getLsbD k.val = true → k.val + shift < 64)
    (hdisj : ∀ k : Fin 64,
      ¬ (mask.getLsbD k.val = true ∧ shift ≤ k.val ∧ mask.getLsbD (k.val - shift) = true))
    (ha : ∀ k : Fin 64, a.getLsbD k.val = f (fa k)) :
    ∀ k : Fin 64, (deltaSwap1 a shift mask).getLsbD k.val = f (routeSwap1 fa shift mask hmask k) := by
  intro k
  rw [getLsbD_deltaSwap1_eq a mask shift k (hdisj k)]
  unfold routeSwap1
  by_cases hm1 : mask.getLsbD k.val = true
  · rw [ite_true hm1, dite_true hm1]
    exact ha ⟨k.val + shift, hmask k hm1⟩
  · rw [ite_false hm1, dite_false hm1]
    by_cases h2 : shift ≤ k.val ∧ mask.getLsbD (k.val - shift) = true
    · rw [ite_true h2, dite_true h2]
      exact ha ⟨k.val - shift, by omega⟩
    · rw [ite_false h2, dite_false h2]
      exact ha k

/-! ## `readReordered`, `bitslice`, `writeReorderedPair`, and `invBitslice` -/

private theorem getLsbD_zext8_shl (b : BitVec 8) (sh : Nat) (k : Fin 64) :
    ((b.zeroExtend 64) <<< sh).getLsbD k.val =
      if sh ≤ k.val ∧ k.val < sh + 8 then b.getLsbD (k.val - sh) else false := by
  simp only [BitVec.zeroExtend, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    k.isLt, decide_true, Bool.true_and]
  by_cases hlt : k.val < sh
  · have hcond : ¬ (sh ≤ k.val ∧ k.val < sh + 8) := by omega
    rw [ite_false hcond]
    simp [hlt]
  · by_cases hhi : k.val < sh + 8
    · have hcond : sh ≤ k.val ∧ k.val < sh + 8 := ⟨by omega, hhi⟩
      rw [ite_true hcond]
      have hsub : k.val - sh < 64 := by omega
      simp [hlt, hsub]
    · have hcond : ¬ (sh ≤ k.val ∧ k.val < sh + 8) := by omega
      rw [ite_false hcond]
      simp [hlt, BitVec.getLsbD_of_ge b (k.val - sh) (by omega)]

private theorem getLsbD_zext8_zero (b : BitVec 8) (k : Fin 64) :
    (b.zeroExtend 64).getLsbD k.val = if k.val < 8 then b.getLsbD k.val else false := by
  simpa using getLsbD_zext8_shl b 0 k

private theorem getLsbD_readReordered (s : State) (off : Nat) (k : Fin 64) :
    (readReordered s off).getLsbD k.val =
      (s.getD (off + (k.val / 16) + 8 * ((k.val / 8) % 2)) 0#8).getLsbD (k.val % 8) := by
  have hk := k.isLt
  simp only [readReordered, BitVec.getLsbD_or, getLsbD_zext8_zero, getLsbD_zext8_shl]
  by_cases h8 : k.val < 8
  · rw [ite_true h8, ite_false (by omega), ite_false (by omega), ite_false (by omega),
        ite_false (by omega), ite_false (by omega), ite_false (by omega), ite_false (by omega)]
    have d1 : off + (k.val / 16) + 8 * ((k.val / 8) % 2) = off + 0 := by omega
    have d2 : k.val % 8 = k.val := by omega
    rw [d1, d2]; simp
  · by_cases h16 : k.val < 16
    · rw [ite_false h8, ite_false (by omega), ite_false (by omega), ite_false (by omega),
          ite_true ⟨by omega, h16⟩, ite_false (by omega), ite_false (by omega), ite_false (by omega)]
      have d1 : off + (k.val / 16) + 8 * ((k.val / 8) % 2) = off + 0x8 := by omega
      have d2 : k.val - 0x08 = k.val % 8 := by omega
      rw [d1, d2]; simp
    · by_cases h24 : k.val < 24
      · rw [ite_false h8, ite_true ⟨by omega, h24⟩, ite_false (by omega), ite_false (by omega),
            ite_false (by omega), ite_false (by omega), ite_false (by omega), ite_false (by omega)]
        have d1 : off + (k.val / 16) + 8 * ((k.val / 8) % 2) = off + 0x1 := by omega
        have d2 : k.val - 0x10 = k.val % 8 := by omega
        rw [d1, d2]; simp
      · by_cases h32 : k.val < 32
        · rw [ite_false h8, ite_false (by omega), ite_false (by omega), ite_false (by omega),
              ite_false (by omega), ite_true ⟨by omega, h32⟩, ite_false (by omega), ite_false (by omega)]
          have d1 : off + (k.val / 16) + 8 * ((k.val / 8) % 2) = off + 0x9 := by omega
          have d2 : k.val - 0x18 = k.val % 8 := by omega
          rw [d1, d2]; simp
        · by_cases h40 : k.val < 40
          · rw [ite_false h8, ite_false (by omega), ite_true ⟨by omega, h40⟩, ite_false (by omega),
                ite_false (by omega), ite_false (by omega), ite_false (by omega), ite_false (by omega)]
            have d1 : off + (k.val / 16) + 8 * ((k.val / 8) % 2) = off + 0x2 := by omega
            have d2 : k.val - 0x20 = k.val % 8 := by omega
            rw [d1, d2]; simp
          · by_cases h48 : k.val < 48
            · rw [ite_false h8, ite_false (by omega), ite_false (by omega), ite_false (by omega),
                  ite_false (by omega), ite_false (by omega), ite_true ⟨by omega, h48⟩, ite_false (by omega)]
              have d1 : off + (k.val / 16) + 8 * ((k.val / 8) % 2) = off + 0xa := by omega
              have d2 : k.val - 0x28 = k.val % 8 := by omega
              rw [d1, d2]; simp
            · by_cases h56 : k.val < 56
              · rw [ite_false h8, ite_false (by omega), ite_false (by omega), ite_true ⟨by omega, h56⟩,
                    ite_false (by omega), ite_false (by omega), ite_false (by omega), ite_false (by omega)]
                have d1 : off + (k.val / 16) + 8 * ((k.val / 8) % 2) = off + 0x3 := by omega
                have d2 : k.val - 0x30 = k.val % 8 := by omega
                rw [d1, d2]; simp
              · rw [ite_false h8, ite_false (by omega), ite_false (by omega), ite_false (by omega),
                    ite_false (by omega), ite_false (by omega), ite_false (by omega), ite_true ⟨by omega, hk⟩]
                have d1 : off + (k.val / 16) + 8 * ((k.val / 8) % 2) = off + 0xb := by omega
                have d2 : k.val - 0x38 = k.val % 8 := by omega
                rw [d1, d2]; simp

private theorem mask_m0_ok : ∀ k : Fin 64,
    (0x5555555555555555#64).getLsbD k.val = true → k.val + 1 < 64 := by decide

private theorem mask_m1_ok : ∀ k : Fin 64,
    (0x3333333333333333#64).getLsbD k.val = true → k.val + 2 < 64 := by decide

private theorem mask_m2_ok : ∀ k : Fin 64,
    (0x0f0f0f0f0f0f0f0f#64).getLsbD k.val = true → k.val + 4 < 64 := by decide

/-- Pure 3-stage `delta_swap_2` word network shared by `bitslice` and `invBitslice`. -/
private def swap3StageWords (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) : FsState :=
  let m0 := 0x5555555555555555#64
  let (t1, t0) := deltaSwap2 w1 w0 1 m0
  let (t3, t2) := deltaSwap2 w3 w2 1 m0
  let (t5, t4) := deltaSwap2 w5 w4 1 m0
  let (t7, t6) := deltaSwap2 w7 w6 1 m0
  let m1 := 0x3333333333333333#64
  let (t2, t0) := deltaSwap2 t2 t0 2 m1
  let (t3, t1) := deltaSwap2 t3 t1 2 m1
  let (t6, t4) := deltaSwap2 t6 t4 2 m1
  let (t7, t5) := deltaSwap2 t7 t5 2 m1
  let m2 := 0x0f0f0f0f0f0f0f0f#64
  let (t4, t0) := deltaSwap2 t4 t0 4 m2
  let (t5, t1) := deltaSwap2 t5 t1 4 m2
  let (t6, t2) := deltaSwap2 t6 t2 4 m2
  let (t7, t3) := deltaSwap2 t7 t3 4 m2
  ⟨t0, t1, t2, t3, t4, t5, t6, t7⟩

/-- Pure 3-stage `delta_swap_2` index router shared by `bitslice` and `invBitslice`. -/
private def swap3StageRoute {α : Type}
    (r0 r1 r2 r3 r4 r5 r6 r7 : Fin 64 → α) : Nat → Fin 64 → α :=
  let m0 := 0x5555555555555555#64
  let a1 := routeSwap2Fst r1 r0 1 m0 mask_m0_ok
  let a0 := routeSwap2Snd r1 r0 1 m0
  let a3 := routeSwap2Fst r3 r2 1 m0 mask_m0_ok
  let a2 := routeSwap2Snd r3 r2 1 m0
  let a5 := routeSwap2Fst r5 r4 1 m0 mask_m0_ok
  let a4 := routeSwap2Snd r5 r4 1 m0
  let a7 := routeSwap2Fst r7 r6 1 m0 mask_m0_ok
  let a6 := routeSwap2Snd r7 r6 1 m0
  let m1 := 0x3333333333333333#64
  let b2 := routeSwap2Fst a2 a0 2 m1 mask_m1_ok
  let b0 := routeSwap2Snd a2 a0 2 m1
  let b3 := routeSwap2Fst a3 a1 2 m1 mask_m1_ok
  let b1 := routeSwap2Snd a3 a1 2 m1
  let b6 := routeSwap2Fst a6 a4 2 m1 mask_m1_ok
  let b4 := routeSwap2Snd a6 a4 2 m1
  let b7 := routeSwap2Fst a7 a5 2 m1 mask_m1_ok
  let b5 := routeSwap2Snd a7 a5 2 m1
  let m2 := 0x0f0f0f0f0f0f0f0f#64
  let c4 := routeSwap2Fst b4 b0 4 m2 mask_m2_ok
  let c0 := routeSwap2Snd b4 b0 4 m2
  let c5 := routeSwap2Fst b5 b1 4 m2 mask_m2_ok
  let c1 := routeSwap2Snd b5 b1 4 m2
  let c6 := routeSwap2Fst b6 b2 4 m2 mask_m2_ok
  let c2 := routeSwap2Snd b6 b2 4 m2
  let c7 := routeSwap2Fst b7 b3 4 m2 mask_m2_ok
  let c3 := routeSwap2Snd b7 b3 4 m2
  fun p => match p with
    | 0 => c0 | 1 => c1 | 2 => c2 | 3 => c3
    | 4 => c4 | 5 => c5 | 6 => c6 | _ => c7

private theorem swap3Stage_correct {α : Type} (f : α → Bool)
    (r0 r1 r2 r3 r4 r5 r6 r7 : Fin 64 → α)
    (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64)
    (h0 : ∀ k, w0.getLsbD k.val = f (r0 k)) (h1 : ∀ k, w1.getLsbD k.val = f (r1 k))
    (h2 : ∀ k, w2.getLsbD k.val = f (r2 k)) (h3 : ∀ k, w3.getLsbD k.val = f (r3 k))
    (h4 : ∀ k, w4.getLsbD k.val = f (r4 k)) (h5 : ∀ k, w5.getLsbD k.val = f (r5 k))
    (h6 : ∀ k, w6.getLsbD k.val = f (r6 k)) (h7 : ∀ k, w7.getLsbD k.val = f (r7 k)) :
    ∀ (p : Fin 8) (k : Fin 64),
      ((swap3StageWords w0 w1 w2 w3 w4 w5 w6 w7).getSlice p.val).getLsbD k.val =
        f (swap3StageRoute r0 r1 r2 r3 r4 r5 r6 r7 p.val k) := by
  dsimp only [swap3StageWords, swap3StageRoute]
  obtain ⟨ha1, ha0⟩ := route_deltaSwap2 f r1 r0 w1 w0 1 _ mask_m0_ok h1 h0
  obtain ⟨ha3, ha2⟩ := route_deltaSwap2 f r3 r2 w3 w2 1 _ mask_m0_ok h3 h2
  obtain ⟨ha5, ha4⟩ := route_deltaSwap2 f r5 r4 w5 w4 1 _ mask_m0_ok h5 h4
  obtain ⟨ha7, ha6⟩ := route_deltaSwap2 f r7 r6 w7 w6 1 _ mask_m0_ok h7 h6
  obtain ⟨hb2, hb0⟩ := route_deltaSwap2 f _ _ _ _ 2 _ mask_m1_ok ha2 ha0
  obtain ⟨hb3, hb1⟩ := route_deltaSwap2 f _ _ _ _ 2 _ mask_m1_ok ha3 ha1
  obtain ⟨hb6, hb4⟩ := route_deltaSwap2 f _ _ _ _ 2 _ mask_m1_ok ha6 ha4
  obtain ⟨hb7, hb5⟩ := route_deltaSwap2 f _ _ _ _ 2 _ mask_m1_ok ha7 ha5
  obtain ⟨hc4, hc0⟩ := route_deltaSwap2 f _ _ _ _ 4 _ mask_m2_ok hb4 hb0
  obtain ⟨hc5, hc1⟩ := route_deltaSwap2 f _ _ _ _ 4 _ mask_m2_ok hb5 hb1
  obtain ⟨hc6, hc2⟩ := route_deltaSwap2 f _ _ _ _ 4 _ mask_m2_ok hb6 hb2
  obtain ⟨hc7, hc3⟩ := route_deltaSwap2 f _ _ _ _ 4 _ mask_m2_ok hb7 hb3
  intro ⟨p, hp⟩ k
  match p, hp with
  | 0, _ => exact hc0 k
  | 1, _ => exact hc1 k
  | 2, _ => exact hc2 k
  | 3, _ => exact hc3 k
  | 4, _ => exact hc4 k
  | 5, _ => exact hc5 k
  | 6, _ => exact hc6 k
  | 7, _ => exact hc7 k
  | _ + 8, hp => omega

private def initReadRoute (lane off : Nat) (k : Fin 64) : Nat × Nat × Nat :=
  (lane, off + (k.val / 16) + 8 * ((k.val / 8) % 2), k.val % 8)

private def bitsliceRoute : Nat → Fin 64 → Nat × Nat × Nat :=
  swap3StageRoute
    (initReadRoute 0 0) (initReadRoute 1 0) (initReadRoute 2 0) (initReadRoute 3 0)
    (initReadRoute 0 4) (initReadRoute 1 4) (initReadRoute 2 4) (initReadRoute 3 4)

private theorem bitsliceRoute_eq :
    ∀ (p : Fin 8) (r c lane : Fin 4),
      bitsliceRoute p.val ⟨16 * r.val + 4 * c.val + lane.val, by omega⟩ =
        (lane.val, r.val + 4 * c.val, p.val) := by decide

private theorem bitslice_eq_swap3StageWords (bs : Blocks4) :
    bitslice bs = swap3StageWords
      (readReordered bs.b0 0) (readReordered bs.b1 0)
      (readReordered bs.b2 0) (readReordered bs.b3 0)
      (readReordered bs.b0 4) (readReordered bs.b1 4)
      (readReordered bs.b2 4) (readReordered bs.b3 4) := rfl

/-- Bit-index characterization of `bitslice`: slice `p`, bit `16 * r + 4 * c + lane` holds bit `p`
of byte `r + 4 * c` of block `lane`. -/
theorem getLsbD_bitslice (bs : Blocks4) (p r c lane : Nat)
    (hp : p < 8) (hr : r < 4) (hc : c < 4) (hl : lane < 4) :
    ((bitslice bs).getSlice p).getLsbD (16 * r + 4 * c + lane) =
      ((bs.getLane lane).getD (r + 4 * c) 0#8).getLsbD p := by
  let f : Nat × Nat × Nat → Bool := fun ⟨l, j, b⟩ => ((bs.getLane l).getD j 0#8).getLsbD b
  have hswap := swap3Stage_correct f
    (initReadRoute 0 0) (initReadRoute 1 0) (initReadRoute 2 0) (initReadRoute 3 0)
    (initReadRoute 0 4) (initReadRoute 1 4) (initReadRoute 2 4) (initReadRoute 3 4)
    (readReordered bs.b0 0) (readReordered bs.b1 0) (readReordered bs.b2 0) (readReordered bs.b3 0)
    (readReordered bs.b0 4) (readReordered bs.b1 4) (readReordered bs.b2 4) (readReordered bs.b3 4)
    (fun k => getLsbD_readReordered bs.b0 0 k) (fun k => getLsbD_readReordered bs.b1 0 k)
    (fun k => getLsbD_readReordered bs.b2 0 k) (fun k => getLsbD_readReordered bs.b3 0 k)
    (fun k => getLsbD_readReordered bs.b0 4 k) (fun k => getLsbD_readReordered bs.b1 4 k)
    (fun k => getLsbD_readReordered bs.b2 4 k) (fun k => getLsbD_readReordered bs.b3 4 k)
    ⟨p, hp⟩ ⟨16 * r + 4 * c + lane, by omega⟩
  have hroute := congrArg f (bitsliceRoute_eq ⟨p, hp⟩ ⟨r, hr⟩ ⟨c, hc⟩ ⟨lane, hl⟩)
  rw [bitslice_eq_swap3StageWords]
  exact hswap.trans hroute

private def writePairShift : Fin 16 → Bool × Nat
  | ⟨0, _⟩ => (false, 0x00) | ⟨1, _⟩ => (false, 0x10)
  | ⟨2, _⟩ => (false, 0x20) | ⟨3, _⟩ => (false, 0x30)
  | ⟨4, _⟩ => (true, 0x00)  | ⟨5, _⟩ => (true, 0x10)
  | ⟨6, _⟩ => (true, 0x20)  | ⟨7, _⟩ => (true, 0x30)
  | ⟨8, _⟩ => (false, 0x08) | ⟨9, _⟩ => (false, 0x18)
  | ⟨10, _⟩ => (false, 0x28) | ⟨11, _⟩ => (false, 0x38)
  | ⟨12, _⟩ => (true, 0x08) | ⟨13, _⟩ => (true, 0x18)
  | ⟨14, _⟩ => (true, 0x28) | ⟨15, _⟩ => (true, 0x38)
  | ⟨_ + 16, h⟩ => absurd h (by omega)

private theorem writePairShift_snd_lt :
    ∀ (j : Fin 16) (p : Fin 8), (writePairShift j).2 + p.val < 64 := by decide

private theorem getLsbD_writeReorderedPair (cLo cHi : BitVec 64) (j : Fin 16) (p : Fin 8) :
    ((writeReorderedPair cLo cHi).getD j.val 0#8).getLsbD p.val =
      (if (writePairShift j).1 then cHi else cLo).getLsbD ((writePairShift j).2 + p.val) := by
  rcases j with ⟨j, hj⟩
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _
  | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ =>
    simp [writeReorderedPair, writePairShift, BitVec.truncate,
      BitVec.getLsbD_ushiftRight, p.isLt, Nat.add_comm]
  | _ + 16, hj => omega

private def invBitsliceWordRoute : Nat → Fin 64 → Nat × Nat :=
  swap3StageRoute
    (fun k => (0, k.val)) (fun k => (1, k.val)) (fun k => (2, k.val)) (fun k => (3, k.val))
    (fun k => (4, k.val)) (fun k => (5, k.val)) (fun k => (6, k.val)) (fun k => (7, k.val))

private def invBitsliceByteRoute (lane : Fin 4) (j : Fin 16) (p : Fin 8) : Nat × Nat :=
  let wordIdx := if (writePairShift j).1 then lane.val + 4 else lane.val
  invBitsliceWordRoute wordIdx ⟨(writePairShift j).2 + p.val, writePairShift_snd_lt j p⟩

private theorem invBitsliceByteRoute_eq :
    ∀ (lane : Fin 4) (j : Fin 16) (p : Fin 8),
      invBitsliceByteRoute lane j p = (p.val, 16 * (j.val % 4) + 4 * (j.val / 4) + lane.val) := by
  decide

private theorem invBitslice_eq_swap3StageWords (st : FsState) :
    invBitslice st =
      let u := swap3StageWords st.s0 st.s1 st.s2 st.s3 st.s4 st.s5 st.s6 st.s7
      ⟨writeReorderedPair u.s0 u.s4,
       writeReorderedPair u.s1 u.s5,
       writeReorderedPair u.s2 u.s6,
       writeReorderedPair u.s3 u.s7⟩ := rfl

/-- Bit-index characterization of `invBitslice`: bit `p` of byte `j` of lane `lane` comes from
slice `p`, bit `16 * (j % 4) + 4 * (j / 4) + lane` of `st`. -/
theorem getLsbD_invBitslice (st : FsState) (lane j p : Nat)
    (hl : lane < 4) (hj : j < 16) (hp : p < 8) :
    (((invBitslice st).getLane lane).getD j 0#8).getLsbD p =
      (st.getSlice p).getLsbD (16 * (j % 4) + 4 * (j / 4) + lane) := by
  let f : Nat × Nat → Bool := fun ⟨s, k⟩ => (st.getSlice s).getLsbD k
  let u := swap3StageWords st.s0 st.s1 st.s2 st.s3 st.s4 st.s5 st.s6 st.s7
  have hswap := swap3Stage_correct f
    (fun k => (0, k.val)) (fun k => (1, k.val)) (fun k => (2, k.val)) (fun k => (3, k.val))
    (fun k => (4, k.val)) (fun k => (5, k.val)) (fun k => (6, k.val)) (fun k => (7, k.val))
    st.s0 st.s1 st.s2 st.s3 st.s4 st.s5 st.s6 st.s7
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have hlane : (Blocks4.mk (writeReorderedPair u.s0 u.s4) (writeReorderedPair u.s1 u.s5)
      (writeReorderedPair u.s2 u.s6) (writeReorderedPair u.s3 u.s7)).getLane lane =
      writeReorderedPair (u.getSlice lane) (u.getSlice (lane + 4)) := by
    match lane, hl with
    | 0, _ | 1, _ | 2, _ | 3, _ => rfl
    | _ + 4, hl => omega
  rw [invBitslice_eq_swap3StageWords, hlane, getLsbD_writeReorderedPair _ _ ⟨j, hj⟩ ⟨p, hp⟩]
  have hroute := congrArg f (invBitsliceByteRoute_eq ⟨lane, hl⟩ ⟨j, hj⟩ ⟨p, hp⟩)
  cases hhi : (writePairShift ⟨j, hj⟩).1
  · have hw := hswap ⟨lane, by omega⟩ ⟨(writePairShift ⟨j, hj⟩).2 + p, writePairShift_snd_lt ⟨j, hj⟩ ⟨p, hp⟩⟩
    rw [ite_false Bool.false_ne_true]
    dsimp only [invBitsliceByteRoute, invBitsliceWordRoute] at hroute
    rw [hhi, ite_false Bool.false_ne_true] at hroute
    exact hw.trans hroute
  · have hw := hswap ⟨lane + 4, by omega⟩ ⟨(writePairShift ⟨j, hj⟩).2 + p, writePairShift_snd_lt ⟨j, hj⟩ ⟨p, hp⟩⟩
    rw [ite_true rfl]
    dsimp only [invBitsliceByteRoute, invBitsliceWordRoute] at hroute
    rw [hhi, ite_true rfl] at hroute
    exact hw.trans hroute

@[simp] theorem wf_invBitslice (st : FsState) : Blocks4.Wf (invBitslice st) := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- `invBitslice` is the left inverse of `bitslice` on 16-byte block batches. -/
theorem invBitslice_bitslice {bs : Blocks4} (hwf : Blocks4.Wf bs) :
    invBitslice (bitslice bs) = bs := by
  have hlane : ∀ (lane : Nat) (hl : lane < 4),
      ((invBitslice (bitslice bs)).getLane lane).length = 16 ∧
      (bs.getLane lane).length = 16 := by
    intro lane hl
    have hw := wf_invBitslice (bitslice bs)
    match lane, hl with
    | 0, _ => exact ⟨hw.1, hwf.1⟩
    | 1, _ => exact ⟨hw.2.1, hwf.2.1⟩
    | 2, _ => exact ⟨hw.2.2.1, hwf.2.2.1⟩
    | 3, _ => exact ⟨hw.2.2.2, hwf.2.2.2⟩
    | _ + 4, hl => omega
  have heq : ∀ (lane : Nat) (hl : lane < 4),
      (invBitslice (bitslice bs)).getLane lane = bs.getLane lane := by
    intro lane hl
    obtain ⟨hl1, hl2⟩ := hlane lane hl
    apply state_eq_of_getD hl1 hl2
    intro j hj
    apply BitVec.eq_of_getLsbD_eq
    intro p hp
    rw [getLsbD_invBitslice _ lane j p hl hj hp,
      getLsbD_bitslice bs p (j % 4) (j / 4) lane hp (by omega) (by omega) hl]
    have hmod : j % 4 + 4 * (j / 4) = j := by omega
    rw [hmod]
  ext1
  · exact heq 0 (by omega)
  · exact heq 1 (by omega)
  · exact heq 2 (by omega)
  · exact heq 3 (by omega)

/-- `bitslice` is the left inverse of `invBitslice` on all `FsState`s. -/
theorem bitslice_invBitslice (st : FsState) : bitslice (invBitslice st) = st := by
  have hslice : ∀ (p : Nat) (hp : p < 8),
      (bitslice (invBitslice st)).getSlice p = st.getSlice p := by
    intro p hp
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    have hr : k / 16 < 4 := by omega
    have hc : (k / 4) % 4 < 4 := by omega
    have hl : k % 4 < 4 := by omega
    have hk_eq : 16 * (k / 16) + 4 * ((k / 4) % 4) + k % 4 = k := by omega
    rw [← hk_eq, getLsbD_bitslice _ p (k / 16) ((k / 4) % 4) (k % 4) hp hr hc hl,
      getLsbD_invBitslice st (k % 4) ((k / 16) + 4 * ((k / 4) % 4)) p hl (by omega) hp]
    have hj1 : ((k / 16) + 4 * ((k / 4) % 4)) % 4 = k / 16 := by omega
    have hj2 : ((k / 16) + 4 * ((k / 4) % 4)) / 4 = (k / 4) % 4 := by omega
    rw [hj1, hj2]
  ext1
  · exact hslice 0 (by omega)
  · exact hslice 1 (by omega)
  · exact hslice 2 (by omega)
  · exact hslice 3 (by omega)
  · exact hslice 4 (by omega)
  · exact hslice 5 (by omega)
  · exact hslice 6 (by omega)
  · exact hslice 7 (by omega)

/-- Extensionality criterion for proving `st = bitslice bs`: check slice `p`, bit `16*r + 4*c + lane`. -/
theorem eq_bitslice_of_getLsbD (st : FsState) (bs : Blocks4)
    (h : ∀ (p r c lane : Nat), p < 8 → r < 4 → c < 4 → lane < 4 →
      (st.getSlice p).getLsbD (16 * r + 4 * c + lane) =
        ((bs.getLane lane).getD (r + 4 * c) 0#8).getLsbD p) :
    st = bitslice bs := by
  have hslice : ∀ (p : Nat) (hp : p < 8), st.getSlice p = (bitslice bs).getSlice p := by
    intro p hp
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    have hk_eq : 16 * (k / 16) + 4 * ((k / 4) % 4) + k % 4 = k := by omega
    rw [← hk_eq, h p (k / 16) ((k / 4) % 4) (k % 4) hp (by omega) (by omega) (by omega),
      getLsbD_bitslice bs p (k / 16) ((k / 4) % 4) (k % 4) hp (by omega) (by omega) (by omega)]
  ext1
  · exact hslice 0 (by omega)
  · exact hslice 1 (by omega)
  · exact hslice 2 (by omega)
  · exact hslice 3 (by omega)
  · exact hslice 4 (by omega)
  · exact hslice 5 (by omega)
  · exact hslice 6 (by omega)
  · exact hslice 7 (by omega)

/-! ## `ShiftRows` Powers and Commutation with `bitslice` -/

/-- `ShiftRows^q`: row `r` shifts left by `(q * r) mod 4`. -/
@[expose] def shiftRowsPow (q : Nat) (s : State) : State :=
  List.ofFn fun i : Fin 16 =>
    s.getD ((i.val % 4) + 4 * (((i.val / 4) + q * (i.val % 4)) % 4)) 0#8

/-- `InvShiftRows^q = ShiftRows^((4 - q mod 4) mod 4)`. -/
@[expose] def invShiftRowsPow (q : Nat) (s : State) : State :=
  shiftRowsPow ((4 - q % 4) % 4) s

@[simp] theorem length_shiftRowsPow (q : Nat) (s : State) :
    (shiftRowsPow q s).length = 16 := by
  simp [shiftRowsPow]

@[simp] theorem length_invShiftRowsPow (q : Nat) (s : State) :
    (invShiftRowsPow q s).length = 16 := by
  simp [invShiftRowsPow]

theorem getD_shiftRowsPow (q : Nat) (s : State) (r c : Nat) (hr : r < 4) (hc : c < 4) :
    (shiftRowsPow q s).getD (r + 4 * c) 0#8 = s.getD (r + 4 * ((c + q * r) % 4)) 0#8 := by
  have hi : r + 4 * c < (shiftRowsPow q s).length := by simp; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simp only [shiftRowsPow, List.getElem_ofFn, Option.getD_some]
  have h1 : (r + 4 * c) % 4 = r := by omega
  have h2 : (r + 4 * c) / 4 = c := by omega
  rw [h1, h2]

theorem shiftRowsPow_mod (q : Nat) (s : State) :
    shiftRowsPow (q % 4) s = shiftRowsPow q s := by
  apply state_eq_of_getD (by simp) (by simp)
  intro j hj
  have hj_eq : (j % 4) + 4 * (j / 4) = j := by omega
  rw [← hj_eq, getD_shiftRowsPow _ _ _ _ (by omega) (by omega),
    getD_shiftRowsPow _ _ _ _ (by omega) (by omega)]
  have hmod : ((j / 4) + (q % 4) * (j % 4)) % 4 = ((j / 4) + q * (j % 4)) % 4 := by
    have hq : q = 4 * (q / 4) + q % 4 := by omega
    conv_rhs => rw [hq]
    have : (j / 4) + (4 * (q / 4) + q % 4) * (j % 4) =
        ((j / 4) + (q % 4) * (j % 4)) + 4 * ((q / 4) * (j % 4)) := by ring
    omega
  rw [hmod]

theorem shiftRowsPow_zero {s : State} (hs : s.length = 16) : shiftRowsPow 0 s = s := by
  rw [state_eta16 hs]; rfl

theorem shiftRowsPow_one (s : State) : shiftRowsPow 1 s = shiftRows s := by
  apply state_eq_of_getD (by simp) (by simp [shiftRows])
  intro j hj
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _
  | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ => rfl
  | _ + 16, hj => omega

theorem invShiftRowsPow_one (s : State) : invShiftRowsPow 1 s = invShiftRows s := by
  apply state_eq_of_getD (by simp) (by simp [invShiftRows])
  intro j hj
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _
  | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ => rfl
  | _ + 16, hj => omega

theorem shiftRowsPow_shiftRowsPow (q1 q2 : Nat) (s : State) :
    shiftRowsPow q1 (shiftRowsPow q2 s) = shiftRowsPow ((q1 + q2) % 4) s := by
  rw [shiftRowsPow_mod (q1 + q2)]
  apply state_eq_of_getD (by simp) (by simp)
  intro j hj
  have hj_eq : (j % 4) + 4 * (j / 4) = j := by omega
  rw [← hj_eq, getD_shiftRowsPow _ _ _ _ (by omega) (by omega),
    getD_shiftRowsPow _ _ _ _ (by omega) (by omega),
    getD_shiftRowsPow _ _ _ _ (by omega) (by omega)]
  have hmul : (q1 + q2) * (j % 4) = q1 * (j % 4) + q2 * (j % 4) := Nat.add_mul q1 q2 (j % 4)
  have hcol : (((j / 4 + q1 * (j % 4)) % 4) + q2 * (j % 4)) % 4 =
      ((j / 4) + (q1 + q2) * (j % 4)) % 4 := by omega
  rw [hcol]

theorem shiftRowsPow_subBytes (q : Nat) {s : State} (hs : s.length = 16) :
    shiftRowsPow q (subBytes s) = subBytes (shiftRowsPow q s) := by
  simp only [← shiftRowsPow_mod q]
  have hq : q % 4 < 4 := by omega
  generalize q % 4 = a at hq
  rw [state_eta16 hs]
  match a, hq with
  | 0, _ | 1, _ | 2, _ | 3, _ => rfl
  | _ + 4, hq => omega

theorem shiftRowsPow_invSubBytes (q : Nat) {s : State} (hs : s.length = 16) :
    shiftRowsPow q (invSubBytes s) = invSubBytes (shiftRowsPow q s) := by
  simp only [← shiftRowsPow_mod q]
  have hq : q % 4 < 4 := by omega
  generalize q % 4 = a at hq
  rw [state_eta16 hs]
  match a, hq with
  | 0, _ | 1, _ | 2, _ | 3, _ => rfl
  | _ + 4, hq => omega

theorem shiftRowsPow_addRoundKey (q : Nat) (a b : State) :
    shiftRowsPow q (addRoundKey a b) = addRoundKey (shiftRowsPow q a) (shiftRowsPow q b) := by
  apply state_eq_of_getD (by simp) (by simp [addRoundKey])
  intro j hj
  have hj_eq : (j % 4) + 4 * (j / 4) = j := by omega
  have getD_ark : ∀ (x y : State) (i : Nat), i < 16 →
      (addRoundKey x y).getD i 0#8 = x.getD i 0#8 ^^^ y.getD i 0#8 := by
    intro x y i hi
    have hlen : i < (addRoundKey x y).length := by simp [addRoundKey]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
    simp only [addRoundKey, List.getElem_ofFn, Option.getD_some]
  rw [← hj_eq, getD_shiftRowsPow _ _ _ _ (by omega) (by omega),
    getD_ark _ _ _ (by omega), getD_ark _ _ _ (by omega),
    getD_shiftRowsPow _ _ _ _ (by omega) (by omega),
    getD_shiftRowsPow _ _ _ _ (by omega) (by omega)]

private theorem sr_m1a_ok : ∀ k : Fin 64,
    (0x00f000ff000f0000#64).getLsbD k.val = true → k.val + 8 < 64 := by decide
private theorem sr_m1a_disj : ∀ k : Fin 64,
    ¬ ((0x00f000ff000f0000#64).getLsbD k.val = true ∧
      8 ≤ k.val ∧ (0x00f000ff000f0000#64).getLsbD (k.val - 8) = true) := by decide

private theorem sr_m1b_ok : ∀ k : Fin 64,
    (0x0f0f00000f0f0000#64).getLsbD k.val = true → k.val + 4 < 64 := by decide
private theorem sr_m1b_disj : ∀ k : Fin 64,
    ¬ ((0x0f0f00000f0f0000#64).getLsbD k.val = true ∧
      4 ≤ k.val ∧ (0x0f0f00000f0f0000#64).getLsbD (k.val - 4) = true) := by decide

private theorem sr_m2_ok : ∀ k : Fin 64,
    (0x00ff000000ff0000#64).getLsbD k.val = true → k.val + 8 < 64 := by decide
private theorem sr_m2_disj : ∀ k : Fin 64,
    ¬ ((0x00ff000000ff0000#64).getLsbD k.val = true ∧
      8 ≤ k.val ∧ (0x00ff000000ff0000#64).getLsbD (k.val - 8) = true) := by decide

private theorem sr_m3a_ok : ∀ k : Fin 64,
    (0x000f00ff00f00000#64).getLsbD k.val = true → k.val + 8 < 64 := by decide
private theorem sr_m3a_disj : ∀ k : Fin 64,
    ¬ ((0x000f00ff00f00000#64).getLsbD k.val = true ∧
      8 ≤ k.val ∧ (0x000f00ff00f00000#64).getLsbD (k.val - 8) = true) := by decide

private def sr1Route : Fin 64 → Fin 64 :=
  routeSwap1 (routeSwap1 id 8 0x00f000ff000f0000#64 sr_m1a_ok) 4 0x0f0f00000f0f0000#64 sr_m1b_ok

private def sr2Route : Fin 64 → Fin 64 :=
  routeSwap1 id 8 0x00ff000000ff0000#64 sr_m2_ok

private def sr3Route : Fin 64 → Fin 64 :=
  routeSwap1 (routeSwap1 id 8 0x000f00ff00f00000#64 sr_m3a_ok) 4 0x0f0f00000f0f0000#64 sr_m1b_ok

private theorem sr1Route_eq : ∀ (r c lane : Fin 4),
    (sr1Route ⟨16 * r.val + 4 * c.val + lane.val, by omega⟩).val =
      16 * r.val + 4 * ((c.val + 1 * r.val) % 4) + lane.val := by decide

private theorem sr2Route_eq : ∀ (r c lane : Fin 4),
    (sr2Route ⟨16 * r.val + 4 * c.val + lane.val, by omega⟩).val =
      16 * r.val + 4 * ((c.val + 2 * r.val) % 4) + lane.val := by decide

private theorem sr3Route_eq : ∀ (r c lane : Fin 4),
    (sr3Route ⟨16 * r.val + 4 * c.val + lane.val, by omega⟩).val =
      16 * r.val + 4 * ((c.val + 3 * r.val) % 4) + lane.val := by decide

private theorem getSlice_map (f : BitVec 64 → BitVec 64) (st : FsState) (p : Nat) (hp : p < 8) :
    (st.map f).getSlice p = f (st.getSlice p) := by
  match p, hp with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl
  | _ + 8, hp => omega

private theorem getLane_map (f : State → State) (bs : Blocks4) (lane : Nat) (hl : lane < 4) :
    (bs.map f).getLane lane = f (bs.getLane lane) := by
  match lane, hl with
  | 0, _ | 1, _ | 2, _ | 3, _ => rfl
  | _ + 4, hl => omega

theorem shiftRows1_bitslice (bs : Blocks4) :
    shiftRows1 (bitslice bs) = bitslice (bs.map (shiftRowsPow 1)) := by
  apply eq_bitslice_of_getLsbD
  intro p r c lane hp hr hc hl
  rw [shiftRows1, getSlice_map _ _ p hp]
  let x := (bitslice bs).getSlice p
  have hstep1 := route_deltaSwap1 (fun k : Fin 64 => x.getLsbD k.val) id x 8
    0x00f000ff000f0000#64 sr_m1a_ok sr_m1a_disj (fun _ => rfl)
  have hstep2 := route_deltaSwap1 (fun k : Fin 64 => x.getLsbD k.val) _ _ 4
    0x0f0f00000f0f0000#64 sr_m1b_ok sr_m1b_disj hstep1
    ⟨16 * r + 4 * c + lane, by omega⟩
  have hroute := sr1Route_eq ⟨r, hr⟩ ⟨c, hc⟩ ⟨lane, hl⟩
  rw [hstep2]
  dsimp only [sr1Route] at hroute
  rw [hroute, getLsbD_bitslice bs p r ((c + 1 * r) % 4) lane hp hr (by omega) hl,
    getLane_map _ bs lane hl, getD_shiftRowsPow 1 _ r c hr hc]

theorem shiftRows2_bitslice (bs : Blocks4) :
    shiftRows2 (bitslice bs) = bitslice (bs.map (shiftRowsPow 2)) := by
  apply eq_bitslice_of_getLsbD
  intro p r c lane hp hr hc hl
  rw [shiftRows2, getSlice_map _ _ p hp]
  let x := (bitslice bs).getSlice p
  have hstep := route_deltaSwap1 (fun k : Fin 64 => x.getLsbD k.val) id x 8
    0x00ff000000ff0000#64 sr_m2_ok sr_m2_disj (fun _ => rfl)
    ⟨16 * r + 4 * c + lane, by omega⟩
  have hroute := sr2Route_eq ⟨r, hr⟩ ⟨c, hc⟩ ⟨lane, hl⟩
  rw [hstep]
  dsimp only [sr2Route] at hroute
  rw [hroute, getLsbD_bitslice bs p r ((c + 2 * r) % 4) lane hp hr (by omega) hl,
    getLane_map _ bs lane hl, getD_shiftRowsPow 2 _ r c hr hc]

theorem shiftRows3_bitslice (bs : Blocks4) :
    shiftRows3 (bitslice bs) = bitslice (bs.map (shiftRowsPow 3)) := by
  apply eq_bitslice_of_getLsbD
  intro p r c lane hp hr hc hl
  rw [shiftRows3, getSlice_map _ _ p hp]
  let x := (bitslice bs).getSlice p
  have hstep1 := route_deltaSwap1 (fun k : Fin 64 => x.getLsbD k.val) id x 8
    0x000f00ff00f00000#64 sr_m3a_ok sr_m3a_disj (fun _ => rfl)
  have hstep2 := route_deltaSwap1 (fun k : Fin 64 => x.getLsbD k.val) _ _ 4
    0x0f0f00000f0f0000#64 sr_m1b_ok sr_m1b_disj hstep1
    ⟨16 * r + 4 * c + lane, by omega⟩
  have hroute := sr3Route_eq ⟨r, hr⟩ ⟨c, hc⟩ ⟨lane, hl⟩
  rw [hstep2]
  dsimp only [sr3Route] at hroute
  rw [hroute, getLsbD_bitslice bs p r ((c + 3 * r) % 4) lane hp hr (by omega) hl,
    getLane_map _ bs lane hl, getD_shiftRowsPow 3 _ r c hr hc]

theorem invShiftRows1_bitslice (bs : Blocks4) :
    invShiftRows1 (bitslice bs) = bitslice (bs.map (invShiftRowsPow 1)) :=
  shiftRows3_bitslice bs

theorem invShiftRows2_bitslice (bs : Blocks4) :
    invShiftRows2 (bitslice bs) = bitslice (bs.map (invShiftRowsPow 2)) :=
  shiftRows2_bitslice bs

theorem invShiftRows3_bitslice (bs : Blocks4) :
    invShiftRows3 (bitslice bs) = bitslice (bs.map (invShiftRowsPow 3)) :=
  shiftRows1_bitslice bs

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Packing
