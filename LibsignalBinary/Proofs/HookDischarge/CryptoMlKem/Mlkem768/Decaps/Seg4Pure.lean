/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode12 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode1

/-!
# `decapsulate_compressed_key` (`B04`) — Segment 4 Pure Helpers (`Seg4Pure`)

Pure and spatial helpers for Segment 4 of `decapsulate_compressed_key`:
1. `WordRangeMem` (`32 × 4`-byte spilled `m'` word table at `[sp + 8 .. sp + 136)`) and
   `ByteRangeMem` (`32`-byte staging buffer at `[sp + 4432 .. sp + 4464)`).
2. Permuted `m'` spill index table `msgSlotIdx` / `msgWordFn`.
3. Modular-reduced `deserialize_12` polynomial `modTHatPoly16` and bridges to
   `Poly.Serialize.Decode12.neonDeserialize12Mod8h` and `Spec.byteDecodeMod 12`.
4. `dk` (`2400` B) spatial split into `skPke`, `pk0`, `pk1`, `pk2`, `rho`, `hPk`, `z`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure

open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  byteDecodeMod byteDecodeRaw mlkemQ
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  ext_lane16 lane16 lane16_pack8x16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode1 (
  byteDecodeRaw_lt_two_pow
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode12 (
  lane16_neonDeserialize12Mod8h_eq_byteDecodeMod loadVec12 neonDeserialize12Mod8h
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (polyVecNat)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (
  PolyBounded16 PolyRepresents
)

/-! ## 1. `WordRangeMem` (`n × 4` B) & `ByteRangeMem` (`n × 1` B) -/

@[expose] def WordRangeMem : Nat → BitVec 64 → (Nat → BitVec 32) → SepProp
  | 0, _, _ => emp
  | n + 1, ptr, f => WordRangeMem n ptr f ∗ ((ptr + BitVec.ofNat 64 (4 * n)) ↦₃₂ f n)

theorem wordRangeMem_congr {n : Nat} {ptr : BitVec 64} {f g : Nat → BitVec 32}
    (h : ∀ k, k < n → f k = g k) : WordRangeMem n ptr f = WordRangeMem n ptr g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [WordRangeMem, ih (fun k hk => h k (by omega)), h n (by omega)]

theorem wordRangeMem_entails_memRegion :
    ∀ (n : Nat) (ptr : BitVec 64) (f : Nat → BitVec 32),
      4 * n ≤ 2 ^ 64 →
      WordRangeMem n ptr f ⊢ memRegion ptr (4 * n)
  | 0, ptr, _, _ => by rw [Nat.mul_zero, memRegion_zero]; exact Entails.refl _
  | n + 1, ptr, f, hle => by
    have ih := wordRangeMem_entails_memRegion n ptr f (by omega)
    have hc : ((ptr + BitVec.ofNat 64 (4 * n)) ↦₃₂ f n) ⊢
        memRegion (ptr + BitVec.ofNat 64 (4 * n)) 4 := by
      rw [pointsTo32_eq_pointsToBytes]
      simpa [unpack32_length] using
        pointsToBytes_entails_memRegion (ptr + BitVec.ofNat 64 (4 * n)) (unpack32 (f n))
    have hjoin : memRegion ptr (4 * n) ∗ memRegion (ptr + BitVec.ofNat 64 (4 * n)) 4 =
        memRegion ptr (4 * (n + 1)) := by
      simpa [Nat.mul_add] using
        (memRegion_split ptr (4 * n) 4 (by omega)).symm
    dsimp only [WordRangeMem]
    rw [← hjoin]
    exact sepConj_mono ih hc

theorem sepWP_elim_wordRangeMem {prog : Program} {target : BitVec 64} {s : State}
    {post : State → SepProp → Prop} :
    ∀ (n : Nat) (ptr : BitVec 64) {R0 : SepProp},
      4 * n ≤ 2 ^ 64 →
      (∀ f : Nat → BitVec 32, SepWP prog target s (WordRangeMem n ptr f ∗ R0) post) →
      SepWP prog target s (memRegion ptr (4 * n) ∗ R0) post
  | 0, ptr, R0, _, h => by
    rw [Nat.mul_zero, memRegion_zero, emp_sepConj]
    simpa [WordRangeMem, emp_sepConj] using h (fun _ => 0#32)
  | n + 1, ptr, R0, hle, h => by
    have hsp : memRegion ptr (4 * (n + 1)) =
        memRegion ptr (4 * n) ∗ memRegion (ptr + BitVec.ofNat 64 (4 * n)) 4 := by
      simpa [Nat.mul_add] using memRegion_split ptr (4 * n) 4 (by omega)
    rw [hsp, sepConj_assoc]
    refine sepWP_elim_wordRangeMem n ptr (by omega) fun f => ?_
    rw [← sepConj_assoc, sepConj_comm (WordRangeMem n ptr f), sepConj_assoc]
    refine SepWP.memRegion4_cell (ptr + BitVec.ofNat 64 (4 * n)) (fun w => ?_) rfl
    have hupd : WordRangeMem (n + 1) ptr (Function.update f n w) =
        WordRangeMem n ptr f ∗ ((ptr + BitVec.ofNat 64 (4 * n)) ↦₃₂ w) := by
      simp only [WordRangeMem, Function.update_self]
      congr 1
      exact wordRangeMem_congr fun k hk => by rw [Function.update_of_ne (by omega)]
    rw [← sepConj_assoc, sepConj_comm ((ptr + BitVec.ofNat 64 (4 * n)) ↦₃₂ w), ← hupd]
    exact h (Function.update f n w)

theorem SepLoad32.wordRange :
    ∀ {n k : Nat} {ea ptr : BitVec 64} {f : Nat → BitVec 32},
      k < n → ptr + BitVec.ofNat 64 (4 * k) = ea →
      SepLoad32 ea (WordRangeMem n ptr f) (f k)
  | n + 1, k, ea, ptr, f, hk, ha => by
    dsimp only [WordRangeMem]
    by_cases hkn : k = n
    · subst hkn; exact SepLoad32.right (SepLoad32.here ha)
    · exact SepLoad32.left (SepLoad32.wordRange (by omega) ha)

theorem SepStore32.wordRange :
    ∀ {n k : Nat} {ea ptr : BitVec 64} {f : Nat → BitVec 32} {val : BitVec 32},
      k < n → ptr + BitVec.ofNat 64 (4 * k) = ea →
      SepStore32 ea val (WordRangeMem n ptr f) (WordRangeMem n ptr (Function.update f k val))
  | n + 1, k, ea, ptr, f, val, hk, ha => by
    dsimp only [WordRangeMem]
    by_cases hkn : k = n
    · subst hkn
      rw [Function.update_self,
        wordRangeMem_congr (f := Function.update f k val) (g := f)
          (fun j hj => by rw [Function.update_of_ne (by omega)])]
      exact SepStore32.right (SepStore32.here ha)
    · rw [Function.update_of_ne (Ne.symm hkn)]
      exact SepStore32.left (SepStore32.wordRange (by omega) ha)

@[expose] def ByteRangeMem : Nat → BitVec 64 → (Nat → BitVec 8) → SepProp
  | 0, _, _ => emp
  | n + 1, ptr, g => ByteRangeMem n ptr g ∗ ((ptr + BitVec.ofNat 64 n) ↦₈ g n)

theorem byteRangeMem_congr {n : Nat} {ptr : BitVec 64} {f g : Nat → BitVec 8}
    (h : ∀ k, k < n → f k = g k) : ByteRangeMem n ptr f = ByteRangeMem n ptr g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ByteRangeMem, ih (fun k hk => h k (by omega)), h n (by omega)]

theorem SepStore8.byteRange :
    ∀ {n k : Nat} {ea ptr : BitVec 64} {g : Nat → BitVec 8} {val : BitVec 8},
      k < n → ptr + BitVec.ofNat 64 k = ea →
      SepStore8 ea val (ByteRangeMem n ptr g) (ByteRangeMem n ptr (Function.update g k val))
  | n + 1, k, ea, ptr, g, val, hk, ha => by
    dsimp only [ByteRangeMem]
    by_cases hkn : k = n
    · subst hkn
      rw [Function.update_self,
        byteRangeMem_congr (f := Function.update g k val) (g := g)
          (fun j hj => by rw [Function.update_of_ne (by omega)])]
      exact SepStore8.right (SepStore8.here ha)
    · rw [Function.update_of_ne (Ne.symm hkn)]
      exact SepStore8.left (SepStore8.byteRange (by omega) ha)

theorem byteRangeMem_eq_pointsToBytes :
    ∀ (bs : List (BitVec 8)) (ptr : BitVec 64),
      ByteRangeMem bs.length ptr (fun k => bs.getD k 0#8) = (ptr ↦ₛ bs)
  | [], ptr => by simp [ByteRangeMem]
  | x :: xs, ptr => by
    have hshift : ∀ (n : Nat) (f : Nat → BitVec 8),
        ByteRangeMem (n + 1) ptr f =
          (ptr ↦₈ f 0) ∗ ByteRangeMem n (ptr + 1#64) (fun k => f (k + 1)) := by
      intro n f
      induction n with
      | zero =>
        simp [ByteRangeMem, show ptr + BitVec.ofNat 64 0 = ptr by bv_omega, emp_sepConj, sepConj_emp]
      | succ n ih =>
        change ByteRangeMem (n + 1) ptr f ∗ ((ptr + BitVec.ofNat 64 (n + 1)) ↦₈ f (n + 1)) =
          (ptr ↦₈ f 0) ∗ (ByteRangeMem n (ptr + 1#64) (fun k => f (k + 1)) ∗
            ((ptr + 1#64 + BitVec.ofNat 64 n) ↦₈ f (n + 1)))
        rw [ih, sepConj_assoc,
          show ptr + 1#64 + BitVec.ofNat 64 n = ptr + BitVec.ofNat 64 (n + 1) by bv_omega]
    rw [List.length_cons, hshift]
    simpa [List.getD_cons_zero, List.getD_cons_succ, pointsToBytes_cons] using
      congrArg ((ptr ↦₈ x) ∗ ·) (byteRangeMem_eq_pointsToBytes xs (ptr + 1#64))

theorem sepWP_elim_byteRangeMem {prog : Program} {target : BitVec 64} {s : State}
    {post : State → SepProp → Prop} (n : Nat) (ptr : BitVec 64) {R0 : SepProp}
    (hle : n ≤ 2 ^ 64)
    (h : ∀ g : Nat → BitVec 8, SepWP prog target s (ByteRangeMem n ptr g ∗ R0) post) :
    SepWP prog target s (memRegion ptr n ∗ R0) post := by
  refine SepWP.memRegion_bytes ptr n hle rfl fun bs hbs => ?_
  rw [← byteRangeMem_eq_pointsToBytes bs ptr, hbs]
  exact h (fun k => bs.getD k 0#8)

/-! ## 2. Permuted `m'` Spill Word Table & Modular `deserialize_12` (`modTHatPoly16`) -/

@[expose] def msgSlotIdx : Array Nat :=
  #[1, 0, 3, 2, 4, 5, 7, 6, 8, 9, 11, 10, 12, 13, 14, 15,
    17, 16, 18, 19, 21, 20, 22, 23, 25, 24, 29, 26, 27, 31, 30, 28]

@[expose] def msgWordFn (m' : List (BitVec 8)) (slot : Nat) : BitVec 32 :=
  (m'.getD (msgSlotIdx.getD slot 0) 0#8).zeroExtend 32

@[expose] def modTHatPoly16 (bs : List (BitVec 8)) : Array (BitVec 16) :=
  (byteDecodeMod 12 bs).map (BitVec.ofNat 16)

private theorem loadVec12_slice24_eq (bs : List (BitVec 8)) (k off : Nat)
    (h : off + 12 ≤ 24) (hbs : 24 * (k + 1) ≤ bs.length) :
    loadVec12 ((bs.drop (24 * k)).take 24) off = loadVec12 bs (24 * k + off) := by
  have hbyte (i : Nat) (hi : i < 12) :
      (((bs.drop (24 * k)).take 24).getD (off + i) 0#8) = bs.getD (24 * k + off + i) 0#8 := by
    have hlt24 : off + i < 24 := by omega
    have hlt_len : off + i < (bs.drop (24 * k)).length := by simp; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hlt24, List.getElem?_drop,
      Nat.add_assoc]
  have hbyte0 : (((bs.drop (24 * k)).take 24).getD off 0#8) = bs.getD (24 * k + off) 0#8 := by
    simpa using hbyte 0 (by decide)
  unfold loadVec12
  simp only [hbyte0, hbyte 1 (by decide), hbyte 2 (by decide), hbyte 3 (by decide),
    hbyte 4 (by decide), hbyte 5 (by decide), hbyte 6 (by decide), hbyte 7 (by decide),
    hbyte 8 (by decide), hbyte 9 (by decide), hbyte 10 (by decide), hbyte 11 (by decide)]

theorem modDeser12_loadVec12_pair {bs : List (BitVec 8)} (hbs : bs.length = 384)
    (k : Nat) (hk : k < 16) :
    neonDeserialize12Mod8h (loadVec12 bs (24 * k)) = polyVecNat (modTHatPoly16 bs) (2 * k) ∧
    neonDeserialize12Mod8h (loadVec12 bs (24 * k + 12)) =
      polyVecNat (modTHatPoly16 bs) (2 * k + 1) := by
  have hmod_sz : (byteDecodeMod 12 bs).size = 256 := by simp [byteDecodeMod, byteDecodeRaw]
  have hlen : 24 * (k + 1) ≤ bs.length := by omega
  have he0 := loadVec12_slice24_eq bs k 0 (by decide) hlen
  have he1 := loadVec12_slice24_eq bs k 12 (by decide) hlen
  rw [Nat.add_zero] at he0
  refine ⟨ext_lane16 fun j => ?_, ext_lane16 fun j => ?_⟩
  · obtain ⟨h0, _⟩ := lane16_neonDeserialize12Mod8h_eq_byteDecodeMod bs k hk hlen j
    rw [he0] at h0
    have hj : 16 * k + j.val < 256 := by omega
    rw [h0, polyVecNat, lane16_pack8x16]
    simp [modTHatPoly16, Array.getD, hmod_sz, show 8 * (2 * k) = 16 * k by omega, hj]
  · obtain ⟨_, h1⟩ := lane16_neonDeserialize12Mod8h_eq_byteDecodeMod bs k hk hlen j
    rw [he1] at h1
    have hj : 16 * k + (8 + j.val) < 256 := by omega
    rw [h1, polyVecNat, lane16_pack8x16]
    simp [modTHatPoly16, Array.getD, hmod_sz,
      show 8 * (2 * k + 1) + j.val = 16 * k + (8 + j.val) by omega, hj]

theorem modTHatPoly16_spec (bs : List (BitVec 8)) :
    PolyBounded16 3328 (modTHatPoly16 bs) ∧
    PolyRepresents (modTHatPoly16 bs) (byteDecodeMod 12 bs) := by
  have hraw_sz : (byteDecodeRaw 12 bs).size = 256 := by simp [byteDecodeRaw]
  have hmod_sz : (byteDecodeMod 12 bs).size = 256 := by simp [byteDecodeMod, byteDecodeRaw]
  have ht_sz : (modTHatPoly16 bs).size = 256 := by simp [modTHatPoly16, hmod_sz]
  refine ⟨⟨ht_sz, fun i hi => ?_⟩, ⟨ht_sz, fun i hi => ?_⟩⟩
  · have hget : (modTHatPoly16 bs).getD i 0#16 =
        BitVec.ofNat 16 ((byteDecodeMod 12 bs).getD i 0) := by
      simp [modTHatPoly16, Array.getD, hmod_sz, hi]
    have hmod_lt : (byteDecodeMod 12 bs).getD i 0 < 3329 := by
      have heq : (byteDecodeMod 12 bs).getD i 0 = (byteDecodeRaw 12 bs).getD i 0 % mlkemQ := by
        simp [byteDecodeMod, Array.getD, hraw_sz, hi]
      rw [heq]; exact Nat.mod_lt _ (by decide)
    rw [hget]
    set c := (byteDecodeMod 12 bs).getD i 0
    have htoInt : (BitVec.ofNat 16 c).toInt = (c : Int) := by
      simp [BitVec.toInt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : c < 65536),
        show 2 * c < 65536 by omega]
    omega
  · have hget : (modTHatPoly16 bs).getD i 0#16 =
        BitVec.ofNat 16 ((byteDecodeMod 12 bs).getD i 0) := by
      simp [modTHatPoly16, Array.getD, hmod_sz, hi]
    have hmod_lt : (byteDecodeMod 12 bs).getD i 0 < 3329 := by
      have heq : (byteDecodeMod 12 bs).getD i 0 = (byteDecodeRaw 12 bs).getD i 0 % mlkemQ := by
        simp [byteDecodeMod, Array.getD, hraw_sz, hi]
      rw [heq]; exact Nat.mod_lt _ (by decide)
    rw [hget]
    set c := (byteDecodeMod 12 bs).getD i 0
    have htoInt : (BitVec.ofNat 16 c).toInt = (c : Int) := by
      simp [BitVec.toInt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : c < 65536),
        show 2 * c < 65536 by omega]
    rw [htoInt]

/-! ## 3. `dk` (`2400` B) Spatial Split into `skPke`, `pk[0..2]`, `rho`, `hPk`, `z` -/

theorem dk_seg4_split (dkA : BitVec 64) {dk : List (BitVec 8)} (hdk : dk.length = 2400) :
    (dkA ↦ₛ dk) =
      (dkA ↦ₛ dk.take 1152) ∗
      ((dkA + 1152#64) ↦ₛ (dk.drop 1152).take 384) ∗
      ((dkA + 1536#64) ↦ₛ (dk.drop 1536).take 384) ∗
      ((dkA + 1920#64) ↦ₛ (dk.drop 1920).take 384) ∗
      ((dkA + 2304#64) ↦ₛ (dk.drop 2304).take 32) ∗
      ((dkA + 2336#64) ↦ₛ (dk.drop 2336).take 32) ∗
      ((dkA + 2368#64) ↦ₛ (dk.drop 2368).take 32) := by
  have h0 : dk = dk.take 1152 ++ dk.drop 1152 := (List.take_append_drop 1152 dk).symm
  have h1 : dk.drop 1152 = (dk.drop 1152).take 384 ++ dk.drop 1536 := by
    simpa [List.drop_drop] using (List.take_append_drop 384 (dk.drop 1152)).symm
  have h2 : dk.drop 1536 = (dk.drop 1536).take 384 ++ dk.drop 1920 := by
    simpa [List.drop_drop] using (List.take_append_drop 384 (dk.drop 1536)).symm
  have h3 : dk.drop 1920 = (dk.drop 1920).take 384 ++ dk.drop 2304 := by
    simpa [List.drop_drop] using (List.take_append_drop 384 (dk.drop 1920)).symm
  have h4 : dk.drop 2304 = (dk.drop 2304).take 32 ++ dk.drop 2336 := by
    simpa [List.drop_drop] using (List.take_append_drop 32 (dk.drop 2304)).symm
  have h5 : dk.drop 2336 = (dk.drop 2336).take 32 ++ (dk.drop 2368).take 32 := by
    have ht : (dk.drop 2368).take 32 = dk.drop 2368 := List.take_of_length_le (by simp [hdk])
    rw [ht]; simpa [List.drop_drop] using (List.take_append_drop 32 (dk.drop 2336)).symm
  have hl0 : (dk.take 1152).length = 1152 := by simp [hdk]
  have hl1 : ((dk.drop 1152).take 384).length = 384 := by simp [hdk]
  have hl2 : ((dk.drop 1536).take 384).length = 384 := by simp [hdk]
  have hl3 : ((dk.drop 1920).take 384).length = 384 := by simp [hdk]
  have hl4 : ((dk.drop 2304).take 32).length = 32 := by simp [hdk]
  have hl5 : ((dk.drop 2336).take 32).length = 32 := by simp [hdk]
  conv_lhs => rw [h0, h1, h2, h3, h4, h5]
  simp only [pointsToBytes_append, hl0, hl1, hl2, hl3, hl4, hl5,
    show dkA + 1152#64 + BitVec.ofNat 64 384 = dkA + 1536#64 by bv_omega,
    show dkA + 1536#64 + BitVec.ofNat 64 384 = dkA + 1920#64 by bv_omega,
    show dkA + 1920#64 + BitVec.ofNat 64 384 = dkA + 2304#64 by bv_omega,
    show dkA + 2304#64 + BitVec.ofNat 64 32 = dkA + 2336#64 by bv_omega,
    show dkA + 2336#64 + BitVec.ofNat 64 32 = dkA + 2368#64 by bv_omega]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure
