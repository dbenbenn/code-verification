/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.Encaps1Total -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalSpqrV1.States
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKemCorrect
public import LibsignalBinary.Specifications.CryptoGames.KEM.MlKem
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode1

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.MlKemEncaps2Fips -- proof-setup: allow-public-import

/-!
# Totality, Length, and Wrapper Properties of `mlkem768Incremental` and `kyber1024*`

1. Output byte-length lemmas for `Spec.Keccak` and `Spec.MlKem`, showing `toByteVec` neither
   truncates nor pads (`(mlkem768Incremental.* ...).toList = ...`,
   `kyber1024Encaps = kyber1024EncapsWith sampleNtt`,
   `kyber1024Decaps = kyber1024DecapsWith sampleNtt`).
2. Re-exports `kyber1024EncapsVec` and `kyber1024DecapsVec` (`List.Vector` wrappers matching
   `PqxdhPrims.encaps` / `PqxdhPrims.decaps`) with `.toList` bridge lemmas.
3. Unconditional `Encaps1Total mlkem768Incremental` and
   `(encaps1 (fromSeed s).1.toList r).isSome = true`, discharging
   `MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds mlkem768Incremental`.
4. `byteDecodeRaw`/`byteEncode` roundtrip on `< 2^12` polynomials, `validPkBytes` totality on
   `fromSeed` outputs, and `issue1275NeedsFlip = false` on `polyToCenteredI16Bytes (samplePolyCbd2 bs)`.
5. Re-exports `MlKemEncaps2Fips` (`mlkem768Encaps2Fips`, `EsWellFormed`, `esWellFormed_of_encaps1`,
   `mlkem768Incremental_encaps2_of_encaps1`, and `mlkem768Incremental_encaps_eq_indCpaEncryptWith`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.MlKemCorrectProofs

open CryptoVerification.LibsignalSpqrV1 (
  Bytes MlKem pk1Off pk2Off
  CIPHERTEXT1_SIZE CIPHERTEXT2_SIZE HEADER_SIZE ENCAPSULATION_KEY_SIZE
  ENCAPSULATION_STATE_SIZE DECAPSULATION_KEY_SIZE KEY_GENERATION_SEED_SIZE SHARED_SECRET_SIZE
  bytesToVector? issue1275NeedsFlip
  potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275
  ek_matches_header validate_pk_bytes generate encaps1 encaps2 decaps
)
open CryptoVerification.SpqrV1Sync.SendTotal (Encaps1Total)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak (
  keccakSponge sha3_256List sha3_512List shake256List
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  mlkemQ Poly zeroPoly polyAdd bytesToBits bitsToBytes byteEncode byteDecodeRaw
  compressAndEncode samplePolyCbd2 sampleNtt polyToCenteredI16Bytes neonCompressSerialize4
  mlkem768Encaps2List indCpaEncryptWith mlkem768KeyPairWith mlkem768Encaps1With mlkem768DecapsWith
  mlkem768ValidPk kyber1024EncapsWith kyber1024DecapsWith
  toByteVec mlkem768Incremental kyber1024Encaps kyber1024Decaps
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Common (
  bitsToBytes_length byteEncode_length getElem_bitsToBytes_of_and_one
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode1 (
  byteDecodeRaw_lt_two_pow
)

/-! ## 1. `toByteVec` & Exact Byte-Length Identities -/

theorem toByteVec_toList_of_length {n : Nat} {bs : List (BitVec 8)} (h : bs.length = n) :
    (toByteVec n bs).toList = bs := by
  unfold toByteVec
  change ((List.range n).map fun i => bs.getD i 0#8) = bs
  apply List.ext_getElem
  · simp [h]
  · intro i hi1 hi2
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2]
    rfl

@[simp] theorem sha3_256List_length (msg : List (BitVec 8)) :
    (sha3_256List msg).length = 32 := by
  simp [sha3_256List, keccakSponge]

@[simp] theorem sha3_512List_length (msg : List (BitVec 8)) :
    (sha3_512List msg).length = 64 := by
  simp [sha3_512List, keccakSponge]

@[simp] theorem shake256List_length (outLen : Nat) (msg : List (BitVec 8)) :
    (shake256List outLen msg).length = outLen := by
  simp [shake256List, keccakSponge]

@[simp] theorem compressAndEncode_length (d : Nat) (f : Poly) :
    (compressAndEncode d f).length = 32 * d := by
  simp [compressAndEncode]

@[simp] theorem neonCompressSerialize4_length (re : Array (BitVec 16)) :
    (neonCompressSerialize4 re).length = 128 := by
  simp [neonCompressSerialize4]

private theorem flatten_map_length {α : Type _} {xs : List α} {f : α → List (BitVec 8)} {m : Nat}
    (hf : ∀ x ∈ xs, (f x).length = m) :
    ((xs.map f).flatten).length = xs.length * m := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons,
      hf x List.mem_cons_self, ih (fun y hy => hf y (List.mem_cons_of_mem x hy))]
    rw [Nat.succ_mul, Nat.add_comm]

@[simp] theorem polyToCenteredI16Bytes_length (p : Poly) :
    (polyToCenteredI16Bytes p).length = 512 := by
  unfold polyToCenteredI16Bytes
  rw [flatten_map_length (m := 2) (fun _ _ => rfl), List.length_range]

theorem flatten_range3_length {f : Nat → List (BitVec 8)} {m : Nat}
    (hf : ∀ i, i < 3 → (f i).length = m) :
    (((List.range 3).map f).flatten).length = 3 * m := by
  rw [flatten_map_length (fun i hi => hf i (List.mem_range.mp hi)), List.length_range]

theorem flatten_range4_length {f : Nat → List (BitVec 8)} {m : Nat}
    (hf : ∀ i, i < 4 → (f i).length = m) :
    (((List.range 4).map f).flatten).length = 4 * m := by
  rw [flatten_map_length (fun i hi => hf i (List.mem_range.mp hi)), List.length_range]

theorem indCpaEncryptWith_lengths (sampler : List (BitVec 8) → Poly) (k dU dV : Nat)
    (pk m coins : List (BitVec 8)) :
    (indCpaEncryptWith sampler k dU dV pk m coins).1.length = k * (32 * dU) ∧
    (indCpaEncryptWith sampler k dU dV pk m coins).2.1.length = 32 * dV := by
  unfold indCpaEncryptWith
  dsimp only
  refine ⟨?_, by simp⟩
  rw [flatten_map_length (m := 32 * dU) (fun _ _ => by simp), List.length_range]

theorem mlkem768KeyPairWith_length (sampler : List (BitVec 8) → Poly) (seed64 : List (BitVec 8))
    (hseed : 64 ≤ seed64.length) :
    (mlkem768KeyPairWith sampler seed64).length = 2400 := by
  unfold mlkem768KeyPairWith
  dsimp only
  have hdk : (((List.range 3).map fun i =>
      byteEncode 12 (((Spec.sampleVecCbd2 3 ((sha3_512List (seed64.take 32 ++ [3#8])).drop 32 |>.take 32) 0).map
        Spec.polyNtt).getD i zeroPoly)).flatten).length = 3 * 384 :=
    flatten_range3_length (fun _ _ => by simp)
  have hpk2 : (((List.range 3).map fun i =>
      byteEncode 12 ((Array.ofFn (n := 3) fun ⟨i, _⟩ =>
        polyAdd
          (Spec.vecDotNtt 3
            ((Spec.sampleMatrixWith sampler 3 ((sha3_512List (seed64.take 32 ++ [3#8])).take 32) true).getD i #[])
            ((Spec.sampleVecCbd2 3 ((sha3_512List (seed64.take 32 ++ [3#8])).drop 32 |>.take 32) 0).map Spec.polyNtt))
          (((Spec.sampleVecCbd2 3 ((sha3_512List (seed64.take 32 ++ [3#8])).drop 32 |>.take 32) 3).map
            Spec.polyNtt).getD i zeroPoly)).getD i zeroPoly)).flatten).length = 3 * 384 :=
    flatten_range3_length (fun _ _ => by simp)
  simp only [List.length_append, hdk, hpk2, List.length_take, List.length_drop,
    sha3_512List_length, sha3_256List_length]
  omega

@[simp] theorem mlkem768Encaps2List_length (es ek : List (BitVec 8)) :
    (mlkem768Encaps2List es ek).length = 128 := by
  simp [mlkem768Encaps2List]

@[simp] theorem mlkem768DecapsWith_length (sampler : List (BitVec 8) → Poly)
    (dk2400 ct1_960 ct2_128 : List (BitVec 8)) :
    (mlkem768DecapsWith sampler dk2400 ct1_960 ct2_128).length = 32 := by
  unfold mlkem768DecapsWith
  dsimp only
  split <;> simp

@[simp] theorem kyber1024EncapsWith_ct_length (sampler : List (BitVec 8) → Poly)
    (pk1568 rand32 : List (BitVec 8)) :
    (kyber1024EncapsWith sampler pk1568 rand32).1.length = 1568 := by
  unfold kyber1024EncapsWith
  dsimp only
  have h := indCpaEncryptWith_lengths sampler 4 11 5 (pk1568.take 1568)
    (sha3_256List (rand32.take 32))
    ((sha3_512List (sha3_256List (rand32.take 32) ++ sha3_256List (pk1568.take 1568))).drop 32 |>.take 32)
  rw [List.length_append, h.1, h.2]

@[simp] theorem kyber1024EncapsWith_ss_length (sampler : List (BitVec 8) → Poly)
    (pk1568 rand32 : List (BitVec 8)) :
    (kyber1024EncapsWith sampler pk1568 rand32).2.length = 32 := by
  unfold kyber1024EncapsWith
  simp

@[simp] theorem kyber1024DecapsWith_length (sampler : List (BitVec 8) → Poly)
    (sk3168 ct1568 : List (BitVec 8)) :
    (kyber1024DecapsWith sampler sk3168 ct1568).length = 32 := by
  unfold kyber1024DecapsWith
  dsimp only
  split <;> simp

@[simp] theorem mlkem768Incremental_keyPair_toList (seed : List.Vector (BitVec 8) 64) :
    (mlkem768Incremental.keyPair seed).toList = mlkem768KeyPairWith sampleNtt seed.toList :=
  toByteVec_toList_of_length (mlkem768KeyPairWith_length sampleNtt seed.toList (by simp))

@[simp] theorem mlkem768Incremental_encaps2_toList
    (es : List.Vector (BitVec 8) 2080) (ek : List.Vector (BitVec 8) 1152) :
    (mlkem768Incremental.encaps2 es ek).toList = mlkem768Encaps2List es.toList ek.toList :=
  toByteVec_toList_of_length (mlkem768Encaps2List_length es.toList ek.toList)

@[simp] theorem mlkem768Incremental_decaps_toList
    (dk : List.Vector (BitVec 8) 2400) (ct1 : List.Vector (BitVec 8) 960)
    (ct2 : List.Vector (BitVec 8) 128) :
    (mlkem768Incremental.decaps dk ct1 ct2).toList =
      mlkem768DecapsWith sampleNtt dk.toList ct1.toList ct2.toList :=
  toByteVec_toList_of_length (mlkem768DecapsWith_length sampleNtt dk.toList ct1.toList ct2.toList)

private theorem toByteVec_pair_eq (p : List (BitVec 8) × List (BitVec 8))
    (h1 : p.1.length = 1568) (h2 : p.2.length = 32) :
    (let (ct, ss) := p; ((toByteVec 1568 ct).toList, (toByteVec 32 ss).toList)) = p := by
  rcases p with ⟨ct, ss⟩
  exact congrArg₂ Prod.mk (toByteVec_toList_of_length h1) (toByteVec_toList_of_length h2)

theorem kyber1024Encaps_eq_with (pk rand : List (BitVec 8)) :
    kyber1024Encaps pk rand = kyber1024EncapsWith sampleNtt pk rand :=
  toByteVec_pair_eq (kyber1024EncapsWith sampleNtt pk rand)
    (kyber1024EncapsWith_ct_length sampleNtt pk rand)
    (kyber1024EncapsWith_ss_length sampleNtt pk rand)

theorem kyber1024Encaps_fst_eq (pk rand : List (BitVec 8)) :
    (kyber1024Encaps pk rand).1 = (kyber1024EncapsWith sampleNtt pk rand).1 :=
  congrArg Prod.fst (kyber1024Encaps_eq_with pk rand)

theorem kyber1024Encaps_snd_eq (pk rand : List (BitVec 8)) :
    (kyber1024Encaps pk rand).2 = (kyber1024EncapsWith sampleNtt pk rand).2 :=
  congrArg Prod.snd (kyber1024Encaps_eq_with pk rand)

theorem kyber1024Decaps_eq_with (sk ct : List (BitVec 8)) :
    kyber1024Decaps sk ct = kyber1024DecapsWith sampleNtt sk ct :=
  toByteVec_toList_of_length (kyber1024DecapsWith_length sampleNtt sk ct)

/-! ## 2. Typed `List.Vector` Wrappers for `PqxdhPrims` (`kyber1024EncapsVec` / `kyber1024DecapsVec`) -/

export CryptoGames.MLKEM (kyber1024EncapsVec kyber1024DecapsVec)

private theorem vector_mk_toList {α : Type} {n : Nat} (l : List α) (hl : l.length = n) :
    List.Vector.toList (n := n) ⟨l, hl⟩ = l := rfl

theorem kyber1024EncapsVec_fst_toList
    (pk : List.Vector (BitVec 8) 1568) (rand : List.Vector (BitVec 8) 32) :
    (kyber1024EncapsVec pk rand).1.toList = (kyber1024Encaps pk.toList rand.toList).1 :=
  vector_mk_toList _ _

theorem kyber1024EncapsVec_snd_toList
    (pk : List.Vector (BitVec 8) 1568) (rand : List.Vector (BitVec 8) 32) :
    (kyber1024EncapsVec pk rand).2.toList = (kyber1024Encaps pk.toList rand.toList).2 :=
  vector_mk_toList _ _

theorem kyber1024DecapsVec_toList
    (sk : List.Vector (BitVec 8) 3168) (ct : List.Vector (BitVec 8) 1568) :
    (kyber1024DecapsVec sk ct).toList = kyber1024Decaps sk.toList ct.toList :=
  vector_mk_toList _ _

/-! ## 3. Unconditional `Encaps1Total` & `MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds` -/

theorem mlkem768Encaps1With_isSome_of_le (sampler : List (BitVec 8) → Poly)
    {hdr rand32 : List (BitVec 8)} (hhdr : 64 ≤ hdr.length) :
    (mlkem768Encaps1With sampler hdr rand32).isSome = true := by
  unfold mlkem768Encaps1With
  have hlt : ¬(hdr.length < 64) := by omega
  simp [hlt]

theorem mlkem768Encaps1With_lengths_of_le (sampler : List (BitVec 8) → Poly)
    {hdr rand32 : List (BitVec 8)} (hhdr : 64 ≤ hdr.length) (hrand : 32 ≤ rand32.length) :
    ∃ ct1 es ss,
      mlkem768Encaps1With sampler hdr rand32 = some (ct1, es, ss) ∧
      ct1.length = 960 ∧ es.length = 2080 ∧ ss.length = 32 := by
  unfold mlkem768Encaps1With
  have hlt : ¬(hdr.length < 64) := by omega
  simp only [hlt, ↓reduceIte]
  refine ⟨_, _, _, rfl, ?_, ?_, ?_⟩
  · rw [flatten_range3_length (m := 320) (fun _ _ => by simp)]
  · have hr3 : (((List.range 3).map fun i =>
        polyToCenteredI16Bytes
          (((Spec.sampleVecCbd2 3
              ((sha3_512List (rand32.take 32 ++ (hdr.drop 32 |>.take 32))).drop 32 |>.take 32) 0).map
            Spec.polyNtt).getD i zeroPoly)).flatten).length = 3 * 512 :=
      flatten_range3_length (fun _ _ => by simp)
    simp only [List.length_append, hr3, polyToCenteredI16Bytes_length, List.length_take]
    omega
  · simp [List.length_take]

theorem mlkem768Incremental_encaps1_isSome_of_le
    {hdr : Bytes} (rand : List.Vector (BitVec 8) 32) (hhdr : 64 ≤ hdr.length) :
    (mlkem768Incremental.encaps1 hdr rand).isSome = true := by
  change ((mlkem768Encaps1With sampleNtt hdr rand.toList).map _).isSome = true
  rw [Option.isSome_map]
  exact mlkem768Encaps1With_isSome_of_le sampleNtt hhdr

/-- `Encaps1Total mlkem768Incremental` holds unconditionally (`0` termination premises). -/
theorem mlkem768Incremental_encaps1Total : Encaps1Total mlkem768Incremental := by
  intro hdr rand hhdr
  exact mlkem768Incremental_encaps1_isSome_of_le rand (by omega)

/-- `encaps1` succeeds on every `fromSeed` header and 32-byte randomness unconditionally. -/
theorem mlkem768Incremental_encaps1_fromSeed_isSome
    (s : List.Vector (BitVec 8) 64) (r : List.Vector (BitVec 8) 32) :
    (mlkem768Incremental.encaps1 (mlkem768Incremental.fromSeed s).1.toList r).isSome = true :=
  mlkem768Incremental_encaps1_isSome_of_le r (by simp)

/-- Exact two-conjunct totality witness matching
`StatementBinaryHarnessCore.MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds mlkem768Incremental`. -/
theorem mlkem768Incremental_encaps1SucceedsOn64ByteHeaderAndSeeds :
    Encaps1Total mlkem768Incremental ∧
    ∀ (s : List.Vector (BitVec 8) 64) (r : List.Vector (BitVec 8) 32),
      (mlkem768Incremental.encaps1 (mlkem768Incremental.fromSeed s).1.toList r).isSome = true :=
  ⟨mlkem768Incremental_encaps1Total, mlkem768Incremental_encaps1_fromSeed_isSome⟩

/-! ## 4. `byteDecodeRaw`/`byteEncode` Roundtrip, `validPkBytes` on `fromSeed`, & `CorrectWith` -/

private theorem array_getD_ofFn {α : Type _} {n : Nat} (f : Fin n → α) (i : Nat) (d : α)
    (hi : i < n) : (Array.ofFn f).getD i d = f ⟨i, hi⟩ := by
  unfold Array.getD
  split
  · rename_i h
    change (Array.ofFn f)[i]'h = f ⟨i, hi⟩
    exact Array.getElem_ofFn h
  · rename_i h
    exact False.elim (h (by simp [hi]))

private theorem toArray_getD_eq {α : Type _} (xs : List α) (i : Nat) (d : α) :
    xs.toArray.getD i d = xs.getD i d := by
  unfold Array.getD
  rw [List.getD_eq_getElem?_getD]
  split
  · rename_i h
    have hi : i < xs.length := by simpa using h
    change xs.toArray[i]'h = xs[i]?.getD d
    rw [List.getElem_toArray, List.getElem?_eq_getElem hi]
    rfl
  · rename_i h
    have hi : xs.length ≤ i := by simpa using h
    rw [List.getElem?_eq_none hi]
    rfl

private theorem getElem_byteEncode_bit (d : Nat) (poly : Poly) (k b : Nat)
    (hk : k < 32 * d) (hb : b < 8) :
    ((byteEncode d poly).getD k 0#8)[b] =
      Nat.testBit (poly.getD ((8 * k + b) / d) 0) ((8 * k + b) % d) := by
  unfold byteEncode
  have hk' : k < (Array.ofFn (n := 256 * d) fun ⟨idx, _⟩ =>
      (poly.getD (idx / d) 0 >>> (idx % d)) &&& 1).size / 8 := by
    rw [Array.size_ofFn]; omega
  rw [getElem_bitsToBytes_of_and_one _
    (fun idx => poly.getD (idx / d) 0 >>> (idx % d))
    (fun idx hidx => by
      rw [Array.size_ofFn] at hidx
      exact array_getD_ofFn _ _ _ hidx)
    k b hk' hb]
  rw [Nat.testBit_shiftRight, Nat.add_zero]

private theorem bytesToBits_byteEncode_getD (d : Nat) (hd : 0 < d) (poly : Poly)
    (j r : Nat) (hj : j < 256) (hr : r < d) :
    (bytesToBits (byteEncode d poly)).getD (j * d + r) 0 = (poly.getD j 0 >>> r) &&& 1 := by
  have hm : j * d + r < 256 * d := by
    calc j * d + r < j * d + d := by omega
      _ = (j + 1) * d := (Nat.succ_mul j d).symm
      _ ≤ 256 * d := Nat.mul_le_mul_right d (by omega)
  have hlen : 8 * (byteEncode d poly).length = 256 * d := by
    rw [byteEncode_length]; omega
  have hm' : j * d + r < 8 * (byteEncode d poly).length := by omega
  unfold bytesToBits
  rw [array_getD_ofFn _ _ _ hm']
  dsimp only
  rw [toArray_getD_eq]
  set m := j * d + r
  have hk : m / 8 < 32 * d := by omega
  have hb : m % 8 < 8 := Nat.mod_lt m (by decide)
  have hbit := getElem_byteEncode_bit d poly (m / 8) (m % 8) hk hb
  have hm_eq : 8 * (m / 8) + m % 8 = d * j + r := by
    calc 8 * (m / 8) + m % 8 = m := Nat.div_add_mod m 8
      _ = j * d + r := rfl
      _ = d * j + r := by rw [Nat.mul_comm j d]
  rw [hm_eq, Nat.mul_add_div hd, Nat.div_eq_of_lt hr, Nat.add_zero,
    Nat.mul_add_mod, Nat.mod_eq_of_lt hr] at hbit
  apply Nat.eq_of_testBit_eq
  intro b
  rcases b with _ | b
  · rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftRight,
      Nat.add_zero, Nat.add_zero, BitVec.testBit_toNat, BitVec.getLsbD_eq_getElem hb, hbit]
  · have h1 : Nat.testBit 1 (b + 1) = false := by rw [Nat.testBit_succ]; simp
    rw [Nat.testBit_and, Nat.testBit_and, h1]
    simp

private theorem fold_reconstruct (v : Nat) :
    ∀ n : Nat, (List.range n).foldl (fun acc r => acc ||| (((v >>> r) &&& 1) <<< r)) 0 = v % 2 ^ n
  | 0 => by simp [Nat.mod_one]
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, fold_reconstruct v n]
    apply Nat.eq_of_testBit_eq
    intro b
    rw [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
      Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_shiftRight, Nat.add_zero]
    by_cases hbn : b < n
    · have hbn1 : b < n + 1 := by omega
      have hle : ¬(n ≤ b) := by omega
      simp [hbn, hbn1, hle]
    · by_cases heq : b = n
      · subst heq
        simp
      · have hgt : n < b := by omega
        have hbn1 : ¬(b < n + 1) := by omega
        have hle : n ≤ b := by omega
        rcases hsub : b - n with _ | k
        · omega
        · have h1 : Nat.testBit 1 (k + 1) = false := by rw [Nat.testBit_succ]; simp
          simp [hbn, hbn1, hle, h1]

private theorem foldl_congr_range {n : Nat} (f g : Nat → Nat → Nat) (init : Nat)
    (hfg : ∀ acc r, r < n → f acc r = g acc r) :
    (List.range n).foldl f init = (List.range n).foldl g init := by
  have hmem : ∀ (xs : List Nat) (acc : Nat), (∀ r ∈ xs, r < n) → xs.foldl f acc = xs.foldl g acc := by
    intro xs
    induction xs with
    | nil => intro _ _; rfl
    | cons r rs ih =>
      intro acc hm
      simp only [List.foldl_cons]
      rw [hfg acc r (hm r List.mem_cons_self)]
      exact ih _ (fun x hx => hm x (List.mem_cons_of_mem r hx))
  exact hmem (List.range n) init (fun _ hr => List.mem_range.mp hr)

/-- Exact coefficient roundtrip: `byteDecodeRaw d (byteEncode d poly)` recovers `poly[j] mod 2^d`. -/
theorem byteDecodeRaw_byteEncode_getD (d : Nat) (hd : 0 < d) (poly : Poly)
    (j : Nat) (hj : j < 256) :
    (byteDecodeRaw d (byteEncode d poly)).getD j 0 = poly.getD j 0 % 2 ^ d := by
  unfold byteDecodeRaw
  rw [array_getD_ofFn _ _ _ hj]
  dsimp only
  rw [foldl_congr_range _ (fun acc r => acc ||| (((poly.getD j 0 >>> r) &&& 1) <<< r)) 0
    (fun acc r hr => by rw [bytesToBits_byteEncode_getD d hd poly j r hj hr])]
  exact fold_reconstruct (poly.getD j 0) d

private theorem polyAdd_getD_lt_mlkemQ (a b : Poly) (j : Nat) (hj : j < 256) :
    (polyAdd a b).getD j 0 < mlkemQ := by
  unfold polyAdd
  rw [array_getD_ofFn _ _ _ hj]
  exact Nat.mod_lt _ (by decide)

private theorem drop_take_mid {α : Type _} (a b c : List α) :
    ((a ++ b ++ c).drop a.length).take b.length = b := by
  rw [List.append_assoc, List.drop_left, List.take_left]

/-- Every keypair generated by `mlkem768Incremental.fromSeed` passes `validPkBytes` unconditionally. -/
theorem mlkem768Incremental_validPkBytes_fromSeed (seed : List.Vector (BitVec 8) 64) :
    mlkem768Incremental.validPkBytes
      (mlkem768Incremental.fromSeed seed).1.toList
      (mlkem768Incremental.fromSeed seed).2.1.toList = true := by
  rw [MlKem.fromSeed_hdr, MlKem.fromSeed_ek, mlkem768Incremental_keyPair_toList]
  unfold mlkem768KeyPairWith
  dsimp only
  set g := sha3_512List (seed.toList.take 32 ++ [3#8])
  set rho := g.take 32
  set sigma := (g.drop 32).take 32
  set aMat := Spec.sampleMatrixWith sampleNtt 3 rho true
  set sHat := (Spec.sampleVecCbd2 3 sigma 0).map Spec.polyNtt
  set eHat := (Spec.sampleVecCbd2 3 sigma 3).map Spec.polyNtt
  set tHat : Array Poly := Array.ofFn (n := 3) fun ⟨i, _⟩ =>
    polyAdd (Spec.vecDotNtt 3 (aMat.getD i #[]) sHat) (eHat.getD i zeroPoly)
  set dkPke := ((List.range 3).map fun i => byteEncode 12 (sHat.getD i zeroPoly)).flatten
  set p0 := byteEncode 12 (tHat.getD 0 zeroPoly)
  set p1 := byteEncode 12 (tHat.getD 1 zeroPoly)
  set p2 := byteEncode 12 (tHat.getD 2 zeroPoly)
  have hpk2_eq : ((List.range 3).map fun i => byteEncode 12 (tHat.getD i zeroPoly)).flatten =
      p0 ++ p1 ++ p2 := by
    have hr3 : List.range 3 = [0, 1, 2] := rfl
    rw [hr3]; simp [p0, p1, p2, List.append_assoc]
  rw [hpk2_eq]
  set pk2 := p0 ++ p1 ++ p2
  set hPk := sha3_256List (pk2 ++ rho)
  set z := (seed.toList.drop 32).take 32
  have hdk_len : dkPke.length = 1152 := by
    dsimp only [dkPke]
    rw [flatten_range3_length (m := 384) (fun _ _ => by simp)]
  have hp0_len : p0.length = 384 := by simp [p0]
  have hp1_len : p1.length = 384 := by simp [p1]
  have hp2_len : p2.length = 384 := by simp [p2]
  have hpk2_len : pk2.length = 1152 := by simp [pk2, hp0_len, hp1_len, hp2_len]
  have hrho_len : rho.length = 32 := by simp [rho, g]
  have hhPk_len : hPk.length = 32 := by simp [hPk]
  have hek_slice : ((dkPke ++ (pk2 ++ rho) ++ hPk ++ z).drop pk2Off).take 1152 = pk2 := by
    have hassoc : dkPke ++ (pk2 ++ rho) ++ hPk ++ z = dkPke ++ pk2 ++ (rho ++ hPk ++ z) := by
      simp [List.append_assoc]
    have hpk2Off_eq : pk2Off = dkPke.length := by unfold pk2Off; omega
    rw [hassoc, hpk2Off_eq, show (1152 : Nat) = pk2.length by omega]
    exact drop_take_mid dkPke pk2 (rho ++ hPk ++ z)
  have hhdr_slice : ((dkPke ++ (pk2 ++ rho) ++ hPk ++ z).drop pk1Off).take 64 = rho ++ hPk := by
    have hassoc : dkPke ++ (pk2 ++ rho) ++ hPk ++ z = (dkPke ++ pk2) ++ (rho ++ hPk) ++ z := by
      simp [List.append_assoc]
    have hl1 : (dkPke ++ pk2).length = pk1Off := by simp [pk1Off, hdk_len, hpk2_len]
    have hl2 : (rho ++ hPk).length = 64 := by simp [hrho_len, hhPk_len]
    rw [hassoc, ← hl1, ← hl2]
    exact drop_take_mid (dkPke ++ pk2) (rho ++ hPk) z
  rw [hhdr_slice, hek_slice]
  unfold MlKem.validPkBytes
  change ((rho ++ hPk).length == 64 && pk2.length == 1152 && mlkem768ValidPk (rho ++ hPk) pk2) = true
  have hhdr_len : (rho ++ hPk).length = 64 := by simp [hrho_len, hhPk_len]
  unfold mlkem768ValidPk
  simp only [hhdr_len, hpk2_len, beq_self_eq_true, bne_self_eq_false, Bool.or_self, Bool.true_and]
  have htake_rho : (rho ++ hPk).take 32 = rho := by
    rw [show (32 : Nat) = rho.length by omega, List.take_left]
  have hdrop_hPk : ((rho ++ hPk).drop 32).take 32 = hPk := by
    rw [show (32 : Nat) = rho.length by omega, List.drop_left,
      show rho.length = hPk.length by omega, List.take_length]
  rw [htake_rho, hdrop_hPk]
  have hhash : (sha3_256List (pk2 ++ rho) == hPk) = true := beq_self_eq_true _
  rw [hhash, Bool.true_and]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  have hslice_i : ((pk2.drop (384 * i)).take 384) = byteEncode 12 (tHat.getD i zeroPoly) := by
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · dsimp only [pk2]
      rw [Nat.mul_zero, List.drop_zero, List.append_assoc,
        show (384 : Nat) = p0.length by omega, List.take_left]
    · dsimp only [pk2]
      rw [Nat.mul_one, show (384 : Nat) = p0.length by omega, List.append_assoc, List.drop_left,
        show p0.length = p1.length by omega, List.take_left]
    · have hp01 : (p0 ++ p1).length = 384 * 2 := by simp [hp0_len, hp1_len]
      dsimp only [pk2]
      rw [← hp01, List.drop_left, show (384 : Nat) = p2.length by omega, List.take_length]
  rw [hslice_i]
  apply List.all_eq_true.mpr
  intro j hj
  rw [List.mem_range] at hj
  rw [byteDecodeRaw_byteEncode_getD 12 (by decide) (tHat.getD i zeroPoly) j hj]
  have hltQ : (tHat.getD i zeroPoly).getD j 0 < mlkemQ := by
    dsimp only [tHat]
    rw [array_getD_ofFn _ _ _ hi]
    exact polyAdd_getD_lt_mlkemQ _ _ j hj
  have hlt4096 : (tHat.getD i zeroPoly).getD j 0 < 2 ^ 12 := by unfold mlkemQ at hltQ; omega
  rw [Nat.mod_eq_of_lt hlt4096]
  exact decide_eq_true hltQ

@[simp] theorem ek_matches_header_mlkem768Incremental_fromSeed
    (seed : List.Vector (BitVec 8) 64) :
    ek_matches_header mlkem768Incremental
      (mlkem768Incremental.fromSeed seed).2.1.toList
      (mlkem768Incremental.fromSeed seed).1.toList = true :=
  mlkem768Incremental_validPkBytes_fromSeed seed

private def cbd2WordOk (w : BitVec 16) : Prop :=
  w = 0x0000#16 ∨ w = 0xffff#16 ∨ w = 0x0001#16 ∨ w = 0x0002#16 ∨ w = 0xfffe#16

private theorem cbd2_ab_wordOk (a b : Nat) (ha : a ≤ 2) (hb : b ≤ 2) :
    cbd2WordOk (let c := ((a + mlkemQ - b) % mlkemQ) % mlkemQ
      let s : Int := if c ≤ 1664 then (c : Int) else (c : Int) - 3329
      BitVec.ofInt 16 s) := by
  unfold cbd2WordOk
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with rfl | rfl | rfl <;>
    rcases (show b = 0 ∨ b = 1 ∨ b = 2 by omega) with rfl | rfl | rfl <;>
    decide

private theorem issue1275NeedsFlip_words :
    ∀ (ws : List (BitVec 16)), (∀ w ∈ ws, cbd2WordOk w) →
      issue1275NeedsFlip
        ((ws.map fun (w : BitVec 16) => [w.truncate 8, (w >>> 8).truncate 8]).flatten) = false
  | [], _ => rfl
  | w :: rest, h => by
    simp only [List.map_cons, List.flatten_cons, List.cons_append, List.nil_append]
    rcases h w List.mem_cons_self with rfl | rfl | rfl | rfl | rfl
    · unfold issue1275NeedsFlip
      exact issue1275NeedsFlip_words rest (fun x hx => h x (List.mem_cons_of_mem _ hx))
    · unfold issue1275NeedsFlip
      exact issue1275NeedsFlip_words rest (fun x hx => h x (List.mem_cons_of_mem _ hx))
    · rfl
    · rfl
    · rfl

private theorem bytesToBits_getD_le_one (bs : List (BitVec 8)) (k : Nat) :
    (bytesToBits bs).getD k 0 ≤ 1 := by
  unfold bytesToBits
  by_cases hk : k < 8 * bs.length
  · rw [array_getD_ofFn _ _ _ hk]
    dsimp only
    rw [Nat.and_one_is_mod]
    omega
  · unfold Array.getD
    split
    · rename_i h; simp at h; omega
    · omega

/-- The big-endian detection scan `issue1275NeedsFlip` returns `false` on `polyToCenteredI16Bytes (samplePolyCbd2 bs)`. -/
theorem issue1275NeedsFlip_polyToCenteredI16Bytes_cbd2 (bs : List (BitVec 8)) :
    issue1275NeedsFlip (polyToCenteredI16Bytes (samplePolyCbd2 bs)) = false := by
  let wordAt (i : Nat) : BitVec 16 :=
    let c := (samplePolyCbd2 bs).getD i 0 % mlkemQ
    let s : Int := if c ≤ 1664 then (c : Int) else (c : Int) - 3329
    BitVec.ofInt 16 s
  have hrewrite : polyToCenteredI16Bytes (samplePolyCbd2 bs) =
      (((List.range 256).map wordAt).map fun (w : BitVec 16) =>
        [w.truncate 8, (w >>> 8).truncate 8]).flatten := by
    unfold polyToCenteredI16Bytes
    rw [List.map_map]
    rfl
  rw [hrewrite]
  apply issue1275NeedsFlip_words
  intro w hw
  rcases List.mem_map.mp hw with ⟨i, hi_mem, rfl⟩
  have hi : i < 256 := List.mem_range.mp hi_mem
  dsimp only [wordAt]
  unfold samplePolyCbd2
  rw [array_getD_ofFn _ _ _ hi]
  have hb0 := bytesToBits_getD_le_one bs (4 * i)
  have hb1 := bytesToBits_getD_le_one bs (4 * i + 1)
  have hb2 := bytesToBits_getD_le_one bs (4 * i + 2)
  have hb3 := bytesToBits_getD_le_one bs (4 * i + 3)
  exact cbd2_ab_wordOk
    ((bytesToBits bs).getD (4 * i) 0 + (bytesToBits bs).getD (4 * i + 1) 0)
    ((bytesToBits bs).getD (4 * i + 2) 0 + (bytesToBits bs).getD (4 * i + 3) 0)
    (by omega) (by omega)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.MlKemCorrectProofs
