/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem
public import LibsignalBinary.Specifications.CryptoGames.Hash.Keccak

/-!
# FIPS 203 ML-KEM-768 (Incremental) and Round-3 CRYSTALS-Kyber-1024 Specification

**Trusted: definitions used by the statement.** Direct specification of NIST FIPS 203 incremental
ML-KEM-768 (`mlkem768Incremental : CryptoVerification.LibsignalSpqrV1.MlKem`, matching
`libcrux-ml-kem` `0.0.10` including its NEON `i16` `encapsulate2` pipeline), Round-3
CRYSTALS-Kyber-1024 (`kyber1024EncapsVec`, `kyber1024DecapsVec`, matching `libcrux`
`variant::Kyber`), and the `SampleNTT` (`sample_from_xof`) matrix/entry seed-termination predicates
(`Shake128SeedTerminates`, `Shake128MatrixTerminates`, `Mlkem768FromSeedTerminates`,
`Mlkem768Encaps1Terminates`, `Mlkem768DecapsTerminates`, `Kyber1024EncapsTerminates`,
`Kyber1024DecapsTerminates`). See `Computational/docs/TRUSTED_BASE.md`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoGames.MLKEM

open CryptoVerification.LibsignalSpqrV1 (MlKem Bytes)
open CryptoGames.SHA3 (
  keccakAbsorb keccakSqueezeBlocks sha3_256List sha3_512List shake256List
)

/-- Prime modulus `q = 3329` of Kyber / ML-KEM. -/
abbrev mlkemQ : Nat := 3329

/-- Degree-256 polynomial represented as 256 coefficients in `[0, 3328]`. -/
abbrev Poly := Array Nat

/-- Degree-256 signed `i16` polynomial (`SIMD128Vector[16]`) for exact `EncapsState` lane ops. -/
abbrev Poly16 := Array (BitVec 16)

/-- Zero polynomial (`256` zeros). -/
def zeroPoly : Poly := Array.replicate 256 0

/-- 7-bit bit-reversal `BitRev_7(k)` for `k < 128` (FIPS 203 §4.2.2). -/
def bitRev7 (k : Nat) : Nat :=
  ((k &&& 1) <<< 6) |||
  (((k >>> 1) &&& 1) <<< 5) |||
  (((k >>> 2) &&& 1) <<< 4) |||
  (((k >>> 3) &&& 1) <<< 3) |||
  (((k >>> 4) &&& 1) <<< 2) |||
  (((k >>> 5) &&& 1) <<< 1) |||
  ((k >>> 6) &&& 1)

/-- Standard FIPS 203 Appendix A table `ζ^{BitRev_7(k)} mod 3329` (`ζ = 17`, `k ∈ 0..128`). -/
def fipsZetas : Array Nat :=
  Array.ofFn (n := 128) fun ⟨k, _⟩ => (17 ^ bitRev7 k) % mlkemQ

/-- `libcrux` Montgomery-scaled signed `i16` zetas `(ζ^{BitRev_7(k)} · 2^16) mod^± 3329`. -/
def zetasTimesMontgomeryR : Array (BitVec 16) :=
  Array.ofFn (n := 128) fun ⟨k, _⟩ =>
    let u := (fipsZetas.getD k 0 * 65536) % mlkemQ
    let s : Int := if u ≤ 1664 then (u : Int) else (u : Int) - 3329
    BitVec.ofInt 16 s

/-- Pointwise polynomial addition mod `3329`. -/
def polyAdd (a b : Poly) : Poly :=
  Array.ofFn (n := 256) fun ⟨i, _⟩ => (a.getD i 0 + b.getD i 0) % mlkemQ

/-- Pointwise polynomial subtraction mod `3329`. -/
def polySub (a b : Poly) : Poly :=
  Array.ofFn (n := 256) fun ⟨i, _⟩ => (a.getD i 0 + mlkemQ - (b.getD i 0 % mlkemQ)) % mlkemQ

/-- One stage of FIPS 203 Algorithm 9 (`NTT`) at stride `len`. -/
def nttStage (len kInit : Nat) (f : Poly) : Poly × Nat :=
  let nBlocks := 256 / (2 * len)
  (List.range nBlocks).foldl
    (fun (cur, k) blk =>
      let start := blk * 2 * len
      let zeta := fipsZetas.getD k 0
      let next := (List.range len).foldl
        (fun arr off =>
          let j := start + off
          let fj := arr.getD j 0
          let fjl := arr.getD (j + len) 0
          let t := (zeta * fjl) % mlkemQ
          let a' := (fj + t) % mlkemQ
          let b' := (fj + mlkemQ - t) % mlkemQ
          (arr.set! j a').set! (j + len) b')
        cur
      (next, k + 1))
    (f, kInit)

/-- FIPS 203 Algorithm 9: forward `NTT` over `ℤ_3329[X]/(X^256 + 1)`. -/
def polyNtt (f : Poly) : Poly :=
  let (f, k) := nttStage 128 1 f
  let (f, k) := nttStage 64 k f
  let (f, k) := nttStage 32 k f
  let (f, k) := nttStage 16 k f
  let (f, k) := nttStage 8 k f
  let (f, k) := nttStage 4 k f
  let (f, _) := nttStage 2 k f
  f

/-- One stage of FIPS 203 Algorithm 10 (`NTT⁻¹`) at stride `len`. -/
def invNttStage (len kInit : Nat) (f : Poly) : Poly × Nat :=
  let nBlocks := 256 / (2 * len)
  (List.range nBlocks).foldl
    (fun (cur, k) blk =>
      let start := blk * 2 * len
      let zeta := fipsZetas.getD k 0
      let next := (List.range len).foldl
        (fun arr off =>
          let j := start + off
          let t := arr.getD j 0
          let fjl := arr.getD (j + len) 0
          let a' := (t + fjl) % mlkemQ
          let b' := (zeta * (fjl + mlkemQ - t)) % mlkemQ
          (arr.set! j a').set! (j + len) b')
        cur
      (next, k - 1))
    (f, kInit)

/-- FIPS 203 Algorithm 10: inverse `NTT⁻¹` (`3303 = 128⁻¹ mod 3329`). -/
def polyInvNtt (f : Poly) : Poly :=
  let (f, k) := invNttStage 2 127 f
  let (f, k) := invNttStage 4 k f
  let (f, k) := invNttStage 8 k f
  let (f, k) := invNttStage 16 k f
  let (f, k) := invNttStage 32 k f
  let (f, k) := invNttStage 64 k f
  let (f, _) := invNttStage 128 k f
  f.map fun c => (c * 3303) % mlkemQ

/-- FIPS 203 Algorithm 11 (`MultiplyNTTs`): degree-1 base-case multiplication in the NTT domain. -/
def polyNttMul (f g : Poly) : Poly :=
  Array.ofFn (n := 256) fun ⟨idx, _⟩ =>
    let p := idx / 2
    let a0 := f.getD (2 * p) 0
    let a1 := f.getD (2 * p + 1) 0
    let b0 := g.getD (2 * p) 0
    let b1 := g.getD (2 * p + 1) 0
    let baseZeta := fipsZetas.getD (64 + p / 2) 0
    let gamma := if p % 2 == 0 then baseZeta else (mlkemQ - baseZeta) % mlkemQ
    if idx % 2 == 0 then
      (a0 * b0 + ((a1 * b1) % mlkemQ) * gamma) % mlkemQ
    else
      (a0 * b1 + a1 * b0) % mlkemQ

/-- FIPS 203 Algorithm 3 (`BytesToBits`, LSB-first). -/
def bytesToBits (bs : List (BitVec 8)) : Array Nat :=
  let n := bs.length
  let arr := bs.toArray
  Array.ofFn (n := 8 * n) fun ⟨idx, _⟩ =>
    ((arr.getD (idx / 8) 0#8).toNat >>> (idx % 8)) &&& 1

/-- FIPS 203 Algorithm 4 (`BitsToBytes`, LSB-first). -/
def bitsToBytes (bits : Array Nat) : List (BitVec 8) :=
  (List.range (bits.size / 8)).map fun byteIdx =>
    let v :=
      (bits.getD (8 * byteIdx + 0) 0 <<< 0) |||
      (bits.getD (8 * byteIdx + 1) 0 <<< 1) |||
      (bits.getD (8 * byteIdx + 2) 0 <<< 2) |||
      (bits.getD (8 * byteIdx + 3) 0 <<< 3) |||
      (bits.getD (8 * byteIdx + 4) 0 <<< 4) |||
      (bits.getD (8 * byteIdx + 5) 0 <<< 5) |||
      (bits.getD (8 * byteIdx + 6) 0 <<< 6) |||
      (bits.getD (8 * byteIdx + 7) 0 <<< 7)
    BitVec.ofNat 8 v

/-- FIPS 203 Algorithm 5 (`ByteEncode_d` producing `32 * d` bytes). -/
def byteEncode (d : Nat) (f : Poly) : List (BitVec 8) :=
  let bits := Array.ofFn (n := 256 * d) fun ⟨idx, _⟩ =>
    let coeff := f.getD (idx / d) 0
    (coeff >>> (idx % d)) &&& 1
  bitsToBytes bits

/-- Unreduced `ByteDecode_d` (`256` integers in `[0, 2^d - 1]`; used directly for `validPk` `d = 12`
domain check and reduced mod `3329` for `ByteDecode_12`). -/
def byteDecodeRaw (d : Nat) (bs : List (BitVec 8)) : Poly :=
  let bits := bytesToBits bs
  Array.ofFn (n := 256) fun ⟨i, _⟩ =>
    (List.range d).foldl (fun acc k => acc ||| (bits.getD (i * d + k) 0 <<< k)) 0

/-- FIPS 203 Algorithm 6 (`ByteDecode_d` reduced mod `3329`). -/
def byteDecodeMod (d : Nat) (bs : List (BitVec 8)) : Poly :=
  (byteDecodeRaw d bs).map (· % mlkemQ)

/-- FIPS 203 §4.2.1 `Compress_d(x) = ⌈(2^d / q) · x⌋ mod 2^d`. -/
def compressCoeff (d x : Nat) : Nat :=
  ((((x % mlkemQ) <<< d) + 1664) / mlkemQ) % (1 <<< d)

/-- FIPS 203 §4.2.1 `Decompress_d(y) = ⌈(q / 2^d) · y⌋`. -/
def decompressCoeff (d y : Nat) : Nat :=
  if d == 0 then 0 else ((y * mlkemQ) + (1 <<< (d - 1))) >>> d

/-- Compress and `ByteEncode_d` a polynomial (`32 * d` bytes). -/
def compressAndEncode (d : Nat) (f : Poly) : List (BitVec 8) :=
  byteEncode d (f.map (compressCoeff d))

/-- `ByteDecode_d` and `Decompress_d` a `32 * d`-byte slice. -/
def decodeAndDecompress (d : Nat) (bs : List (BitVec 8)) : Poly :=
  (byteDecodeRaw d bs).map (decompressCoeff d)

/-- FIPS 203 Algorithm 7 (`SamplePolyCBD_2`, `128` bytes → `Poly`). -/
def samplePolyCbd2 (bs : List (BitVec 8)) : Poly :=
  let bits := bytesToBits bs
  Array.ofFn (n := 256) fun ⟨i, _⟩ =>
    let a := bits.getD (4 * i) 0 + bits.getD (4 * i + 1) 0
    let b := bits.getD (4 * i + 2) 0 + bits.getD (4 * i + 3) 0
    (a + mlkemQ - b) % mlkemQ

/-- Parse all `< 3329` 12-bit candidates from a byte list of length divisible by 3 (FIPS 203 Alg 6). -/
def parseRej12Candidates (bs : List (BitVec 8)) : List Nat :=
  let arr := bs.toArray
  let nTriples := arr.size / 3
  ((List.range nTriples).map fun t =>
    let b0 := (arr.getD (3 * t) 0#8).toNat
    let b1 := (arr.getD (3 * t + 1) 0#8).toNat
    let b2 := (arr.getD (3 * t + 2) 0#8).toNat
    let d1 := b0 + 256 * (b1 % 16)
    let d2 := (b1 / 16) + 16 * b2
    (if d1 < mlkemQ then [d1] else []) ++ (if d2 < mlkemQ then [d2] else [])).flatten

/-- Concatenate the first `nBlocks` 168-byte blocks of `SHAKE-128(seed34)`. -/
def shake128FirstBlocks (seed34 : List (BitVec 8)) (nBlocks : Nat) : List (BitVec 8) :=
  keccakSqueezeBlocks 21 nBlocks (keccakAbsorb 21 0x1f#8 seed34)

/-- Termination predicate for `SampleNTT` (`sample_from_xof`) on a single 34-byte XOF seed:
`SHAKE-128(seed34)` eventually yields at least 256 12-bit integers `< 3329`. -/
def Shake128SeedTerminates (seed34 : List (BitVec 8)) : Prop :=
  ∃ extraBlocks : Nat, 256 ≤ (parseRej12Candidates (shake128FirstBlocks seed34 (extraBlocks + 3))).length

/-- Matrix `SampleNTT` termination predicate for a 32-byte seed `ρ` at rank `k` (`k ∈ {3, 4}`). -/
def Shake128MatrixTerminates (rho : List (BitVec 8)) (k : Nat) : Prop :=
  ∀ i j : Nat, i < k → j < k →
    Shake128SeedTerminates (rho.take 32 ++ [BitVec.ofNat 8 i, BitVec.ofNat 8 j])

/-- Exact `SampleNTT` termination condition for `mlkem768::incremental::from_seed(seed)`. -/
def Mlkem768FromSeedTerminates (seed : List.Vector (BitVec 8) 64) : Prop :=
  let rho := (sha3_512List (seed.toList.take 32 ++ [3#8])).take 32
  Shake128MatrixTerminates rho 3

/-- Exact `SampleNTT` termination condition for `mlkem768::incremental::encapsulate1(hdr, rand)`. -/
def Mlkem768Encaps1Terminates (hdr : Bytes) : Prop :=
  hdr.length < 64 ∨ Shake128MatrixTerminates (hdr.take 32) 3

/-- Exact `SampleNTT` termination condition for `mlkem768::incremental::decapsulate_compressed_key`. -/
def Mlkem768DecapsTerminates (dk : List.Vector (BitVec 8) 2400) : Prop :=
  Shake128MatrixTerminates ((dk.toList.drop 2304).take 32) 3

/-- Exact `SampleNTT` termination condition for `mlkem1024::kyber::encapsulate(pk, rand)`. -/
def Kyber1024EncapsTerminates (pk : List (BitVec 8)) : Prop :=
  Shake128MatrixTerminates ((pk.drop 1536).take 32) 4

/-- Exact `SampleNTT` termination condition for `mlkem1024::kyber::decapsulate(sk, ct)`. -/
def Kyber1024DecapsTerminates (sk : List (BitVec 8)) : Prop :=
  Shake128MatrixTerminates ((sk.drop 3072).take 32) 4

/-- Unbounded FIPS 203 Algorithm 6 `SampleNTT` using `Classical.choose` when `Shake128SeedTerminates`
holds (since 168 is a multiple of 3, every `extra` with `≥ 256` accepted candidates yields the
exact same first 256 coefficients). -/
noncomputable def sampleNtt (seed34 : List (BitVec 8)) : Poly :=
  by
    classical
    exact
      if h : Shake128SeedTerminates seed34 then
        let extra := Classical.choose h
        ((parseRej12Candidates (shake128FirstBlocks seed34 (extra + 3))).take 256).toArray
      else
        zeroPoly

/-- Sample the `k × k` matrix in NTT form (`transpose = true` gives `A[j][i] = XOF(ρ || i || j)`,
i.e. `Â`; `transpose = false` gives `A_T[i][j] = XOF(ρ || i || j)`, i.e. `Âᵀ`). -/
def sampleMatrixWith (sampler : List (BitVec 8) → Poly) (k : Nat)
    (rho : List (BitVec 8)) (transpose : Bool) : Array (Array Poly) :=
  let rho32 := rho.take 32
  Array.ofFn (n := k) fun ⟨r, _⟩ =>
    Array.ofFn (n := k) fun ⟨c, _⟩ =>
      let (i, j) := if transpose then (c, r) else (r, c)
      sampler (rho32 ++ [BitVec.ofNat 8 i, BitVec.ofNat 8 j])

/-- Dot product `∑_{j=0}^{k-1} (a[j] ∘ b[j])` in the NTT domain. -/
def vecDotNtt (k : Nat) (a b : Array Poly) : Poly :=
  (List.range k).foldl
    (fun acc j => polyAdd acc (polyNttMul (a.getD j zeroPoly) (b.getD j zeroPoly)))
    zeroPoly

/-- Sample `k` CBD_2 polynomials from `SHAKE-256(sigma || [ds + i])` (`128` bytes each). -/
def sampleVecCbd2 (k : Nat) (sigma : List (BitVec 8)) (ds : Nat) : Array Poly :=
  let sig32 := sigma.take 32
  Array.ofFn (n := k) fun ⟨i, _⟩ =>
    samplePolyCbd2 (shake256List 128 (sig32 ++ [BitVec.ofNat 8 (ds + i)]))

/-- Encode a polynomial's canonical `[0, 3328]` coefficients as centered `[-1664, 1664]` signed
little-endian `i16` bytes (`512` bytes), matching `SIMD128Vector::barrett_reduce` + `to_bytes`. -/
def polyToCenteredI16Bytes (p : Poly) : List (BitVec 8) :=
  ((List.range 256).map fun i =>
    let c := p.getD i 0 % mlkemQ
    let s : Int := if c ≤ 1664 then (c : Int) else (c : Int) - 3329
    let w : BitVec 16 := BitVec.ofInt 16 s
    [w.truncate 8, (w >>> 8).truncate 8]).flatten

/-! ### Exact NEON `i16` Lane Arithmetic for `encapsulate2` -/

/-- ARM64 AdvSIMD 16-bit non-rounding `SQDMULH` (`SignedSatQ((2 * a * b) >> 16, 16)`). -/
def sqdmulh16 (a b : BitVec 16) : BitVec 16 :=
  if a == 0x8000#16 && b == 0x8000#16 then 0x7fff#16
  else (((a.signExtend 32 * b.signExtend 32) <<< 1).sshiftRight 16).truncate 16

/-- ARM64 AdvSIMD 32-bit non-rounding `SQDMULH` (`SignedSatQ((2 * a * b) >> 32, 32)`). -/
def sqdmulh32 (a b : BitVec 32) : BitVec 32 :=
  if a == 0x80000000#32 && b == 0x80000000#32 then 0x7fffffff#32
  else (((a.signExtend 64 * b.signExtend 64) <<< 1).sshiftRight 32).truncate 32

/-- `libcrux` NEON `barrett_reduce_int16x8_t` on one `i16` lane (`arithmetic.rs:65-77`). -/
def neonBarrettReduce16 (v : BitVec 16) : BitVec 16 :=
  let vec := sqdmulh16 v (BitVec.ofInt 16 20159) + 1024#16
  let quot := vec.sshiftRight 11
  v - quot * 3329#16

/-- `libcrux` NEON `montgomery_reduce_int16x8_t` on `(low, high)` (`arithmetic.rs:95-108`). -/
def neonMontgomeryReduce16 (low high : BitVec 16) : BitVec 16 :=
  let k := low * 62209#16
  let c := (sqdmulh16 k 3329#16).sshiftRight 1
  high - c

/-- `libcrux` NEON `montgomery_multiply_int16x8_t` (`arithmetic.rs:126-138`). -/
def neonMontgomeryMul16 (v c : BitVec 16) : BitVec 16 :=
  let low := v * c
  let high := (sqdmulh16 v c).sshiftRight 1
  neonMontgomeryReduce16 low high

/-- `libcrux` NEON `ntt_multiply` on two `Poly16` polynomials (`vector/neon/ntt.rs:182-244`). -/
def neonPolyNttMul16 (lhs rhs : Poly16) : Poly16 :=
  Array.ofFn (n := 256) fun ⟨idx, _⟩ =>
    let p := idx / 2
    let a0 := lhs.getD (2 * p) 0#16
    let a1 := lhs.getD (2 * p + 1) 0#16
    let b0 := rhs.getD (2 * p) 0#16
    let b1 := rhs.getD (2 * p + 1) 0#16
    let baseZ := zetasTimesMontgomeryR.getD (64 + p / 2) 0#16
    let z := if p % 2 == 0 then baseZ else -baseZ
    if idx % 2 == 0 then
      let a1b1 := neonMontgomeryMul16 a1 b1
      let prod32 : BitVec 32 :=
        a1b1.signExtend 32 * z.signExtend 32 + a0.signExtend 32 * b0.signExtend 32
      neonMontgomeryReduce16 (prod32.truncate 16) ((prod32 >>> 16).truncate 16)
    else
      let prod32 : BitVec 32 :=
        a0.signExtend 32 * b1.signExtend 32 + a1.signExtend 32 * b0.signExtend 32
      neonMontgomeryReduce16 (prod32.truncate 16) ((prod32 >>> 16).truncate 16)

/-- One stage of `libcrux` NEON `invert_ntt_montgomery` (`barrettFirst = true` at layers 1 and 4-7
plus the final pass, `false` at layers 2-3). -/
def neonInvNttStage16 (len kInit : Nat) (barrettFirst : Bool) (f : Poly16) :
    Poly16 × Nat :=
  let nBlocks := 256 / (2 * len)
  (List.range nBlocks).foldl
    (fun (cur, k) blk =>
      let start := blk * 2 * len
      let zeta := zetasTimesMontgomeryR.getD k 0#16
      let next := (List.range len).foldl
        (fun arr off =>
          let j := start + off
          let a := arr.getD j 0#16
          let b := arr.getD (j + len) 0#16
          let bMinusA := b - a
          let sum := a + b
          let a' := if barrettFirst then neonBarrettReduce16 sum else sum
          let b' := neonMontgomeryMul16 bMinusA zeta
          (arr.set! j a').set! (j + len) b')
        cur
      (next, k - 1))
    (f, kInit)

/-- `libcrux` NEON `invert_ntt_montgomery` (`invert_ntt.rs:223-252`; `barrett_reduce` is run at
layers 1 and 4..7 and at the final `poly_barrett_reduce`, not at layers 2 and 3). -/
def neonInvNttMontgomery16 (f : Poly16) : Poly16 :=
  let (f, k) := neonInvNttStage16 2 127 true f
  let (f, k) := neonInvNttStage16 4 k false f
  let (f, k) := neonInvNttStage16 8 k false f
  let (f, k) := neonInvNttStage16 16 k true f
  let (f, k) := neonInvNttStage16 32 k true f
  let (f, k) := neonInvNttStage16 64 k true f
  let (f, _) := neonInvNttStage16 128 k true f
  f.map neonBarrettReduce16

/-- Decode `512` little-endian bytes into `Poly16` (`256` `BitVec 16` lanes). -/
def bytesToPoly16 (bs : List (BitVec 8)) : Poly16 :=
  let arr := bs.toArray
  Array.ofFn (n := 256) fun ⟨i, _⟩ =>
    (arr.getD (2 * i) 0#8).zeroExtend 16 |||
    ((arr.getD (2 * i + 1) 0#8).zeroExtend 16 <<< 8)

/-- Exact `libcrux` NEON `compress_then_serialize_4` (`serialize.rs:259-279`, `compress.rs:48-94`). -/
def neonCompressSerialize4 (re : Poly16) : List (BitVec 8) :=
  let nibbles : Poly := Array.ofFn (n := 256) fun ⟨i, _⟩ =>
    let x := re.getD i 0#16
    let u16 := x + ((x.sshiftRight 15) &&& 3329#16)
    let u32 : BitVec 32 := u16.zeroExtend 32
    let comp := (u32 <<< 4) + 1664#32
    let qd := sqdmulh32 comp 10321340#32
    (((qd >>> 4).truncate 16) &&& 0x000f#16).toNat
  byteEncode 4 nibbles

/-- Exact `mlkem768::incremental::encapsulate2` on arbitrary `es` (`2080`B) and `ek` (`1152`B). -/
def mlkem768Encaps2List (es ek : List (BitVec 8)) : List (BitVec 8) :=
  let tHat : Array Poly16 := Array.ofFn (n := 3) fun ⟨i, _⟩ =>
    (byteDecodeRaw 12 ((ek.drop (384 * i)).take 384)).map fun c => BitVec.ofNat 16 c
  let rHat : Array Poly16 := Array.ofFn (n := 3) fun ⟨i, _⟩ =>
    bytesToPoly16 ((es.drop (512 * i)).take 512)
  let err2 : Poly16 := bytesToPoly16 ((es.drop 1536).take 512)
  let msgPoly : Poly16 :=
    (decodeAndDecompress 1 ((es.drop 2048).take 32)).map fun c => BitVec.ofNat 16 c
  let dot : Poly16 := (List.range 3).foldl
    (fun acc j =>
      let prod := neonPolyNttMul16 (tHat.getD j #[]) (rHat.getD j #[])
      Array.ofFn (n := 256) fun ⟨i, _⟩ => acc.getD i 0#16 + prod.getD i 0#16)
    (Array.replicate 256 0#16)
  let inv := neonInvNttMontgomery16 dot
  let v : Poly16 := Array.ofFn (n := 256) fun ⟨i, _⟩ =>
    let normal := neonMontgomeryMul16 (inv.getD i 0#16) 1441#16
    let sum1 := err2.getD i 0#16 + msgPoly.getD i 0#16
    neonBarrettReduce16 (normal + sum1)
  neonCompressSerialize4 v

/-! ### IND-CPA Building Blocks Parameterized by `sampler : List (BitVec 8) → Poly` -/

/-- Generic `IND-CPA.Encrypt` (`K = 3` (`d_u = 10, d_v = 4`) or `K = 4` (`d_u = 11, d_v = 5`),
`η_1 = η_2 = 2`). Returns `(c1, c2, rHat, e2)`. -/
def indCpaEncryptWith (sampler : List (BitVec 8) → Poly) (k dU dV : Nat)
    (pk m coins : List (BitVec 8)) : List (BitVec 8) × List (BitVec 8) × Array Poly × Poly :=
  let tBytesLen := 384 * k
  let tHat : Array Poly := Array.ofFn (n := k) fun ⟨i, _⟩ =>
    byteDecodeMod 12 ((pk.drop (384 * i)).take 384)
  let rho := (pk.drop tBytesLen).take 32
  let aTrans := sampleMatrixWith sampler k rho false
  let rHat := (sampleVecCbd2 k coins 0).map polyNtt
  let e1 := sampleVecCbd2 k coins k
  let e2 := samplePolyCbd2 (shake256List 128 (coins.take 32 ++ [BitVec.ofNat 8 (2 * k)]))
  let uVec : Array Poly := Array.ofFn (n := k) fun ⟨i, _⟩ =>
    polyAdd (polyInvNtt (vecDotNtt k (aTrans.getD i #[]) rHat)) (e1.getD i zeroPoly)
  let mPoly := decodeAndDecompress 1 (m.take 32)
  let vPoly := polyAdd (polyAdd (polyInvNtt (vecDotNtt k tHat rHat)) e2) mPoly
  let c1 := ((List.range k).map fun i => compressAndEncode dU (uVec.getD i zeroPoly)).flatten
  let c2 := compressAndEncode dV vPoly
  (c1, c2, rHat, e2)

/-- Generic `IND-CPA.Decrypt` (`K = 3` or `K = 4`). -/
def indCpaDecrypt (k dU dV : Nat) (skPke ct : List (BitVec 8)) : List (BitVec 8) :=
  let c1Block := 32 * dU
  let c1Len := k * c1Block
  let sHat : Array Poly := Array.ofFn (n := k) fun ⟨i, _⟩ =>
    byteDecodeMod 12 ((skPke.drop (384 * i)).take 384)
  let uHat : Array Poly := Array.ofFn (n := k) fun ⟨i, _⟩ =>
    polyNtt (decodeAndDecompress dU ((ct.drop (i * c1Block)).take c1Block))
  let vPoly := decodeAndDecompress dV ((ct.drop c1Len).take (32 * dV))
  let wPoly := polySub vPoly (polyInvNtt (vecDotNtt k sHat uHat))
  compressAndEncode 1 wPoly

/-! ### Incremental FIPS 203 ML-KEM-768 (`K = 3, d_u = 10, d_v = 4`) -/

/-- `KeyPairCompressedBytes::from_seed` (`2400` bytes) parameterized by `sampler`. -/
def mlkem768KeyPairWith (sampler : List (BitVec 8) → Poly)
    (seed64 : List (BitVec 8)) : List (BitVec 8) :=
  let d := seed64.take 32
  let z := (seed64.drop 32).take 32
  let g := sha3_512List (d ++ [3#8])
  let rho := g.take 32
  let sigma := (g.drop 32).take 32
  let aMat := sampleMatrixWith sampler 3 rho true
  let sHat := (sampleVecCbd2 3 sigma 0).map polyNtt
  let eHat := (sampleVecCbd2 3 sigma 3).map polyNtt
  let tHat : Array Poly := Array.ofFn (n := 3) fun ⟨i, _⟩ =>
    polyAdd (vecDotNtt 3 (aMat.getD i #[]) sHat) (eHat.getD i zeroPoly)
  let dkPke := ((List.range 3).map fun i => byteEncode 12 (sHat.getD i zeroPoly)).flatten
  let pk2 := ((List.range 3).map fun i => byteEncode 12 (tHat.getD i zeroPoly)).flatten
  let pk := pk2 ++ rho
  let hPk := sha3_256List pk
  dkPke ++ pk ++ hPk ++ z

/-- `mlkem768::incremental::encapsulate1` parameterized by `sampler`. -/
def mlkem768Encaps1With (sampler : List (BitVec 8) → Poly)
    (hdr : List (BitVec 8)) (rand32 : List (BitVec 8)) :
    Option (List (BitVec 8) × List (BitVec 8) × List (BitVec 8)) :=
  if hdr.length < 64 then none else
  let seed := hdr.take 32
  let pkHash := (hdr.drop 32).take 32
  let m := rand32.take 32
  let hashed := sha3_512List (m ++ pkHash)
  let ss := hashed.take 32
  let coins := (hashed.drop 32).take 32
  let aTrans := sampleMatrixWith sampler 3 seed false
  let rHat := (sampleVecCbd2 3 coins 0).map polyNtt
  let e1 := sampleVecCbd2 3 coins 3
  let e2 := samplePolyCbd2 (shake256List 128 (coins ++ [6#8]))
  let uVec : Array Poly := Array.ofFn (n := 3) fun ⟨i, _⟩ =>
    polyAdd (polyInvNtt (vecDotNtt 3 (aTrans.getD i #[]) rHat)) (e1.getD i zeroPoly)
  let ct1 := ((List.range 3).map fun i => compressAndEncode 10 (uVec.getD i zeroPoly)).flatten
  let esBytes :=
    ((List.range 3).map fun i => polyToCenteredI16Bytes (rHat.getD i zeroPoly)).flatten ++
    polyToCenteredI16Bytes e2 ++
    m
  some (ct1, esBytes, ss)

/-- `mlkem768::incremental::decapsulate_compressed_key` (`32` bytes) parameterized by `sampler`. -/
def mlkem768DecapsWith (sampler : List (BitVec 8) → Poly)
    (dk2400 ct1_960 ct2_128 : List (BitVec 8)) : List (BitVec 8) :=
  let skPke := dk2400.take 1152
  let pk := (dk2400.drop 1152).take 1184
  let hPk := (dk2400.drop 2336).take 32
  let z := (dk2400.drop 2368).take 32
  let ct := ct1_960.take 960 ++ ct2_128.take 128
  let m' := indCpaDecrypt 3 10 4 skPke ct
  let kr := sha3_512List (m' ++ hPk)
  let kGood := kr.take 32
  let r' := (kr.drop 32).take 32
  let kRej := shake256List 32 (z ++ ct)
  let (c1', c2', _, _) := indCpaEncryptWith sampler 3 10 4 pk m' r'
  if ct == c1' ++ c2' then kGood else kRej

/-- `mlkem768::incremental::validate_pk` (`hdr` 64B, `ek` 1152B). -/
def mlkem768ValidPk (hdr ek : List (BitVec 8)) : Bool :=
  if hdr.length != 64 || ek.length != 1152 then false else
  let seed := hdr.take 32
  let pkHash := (hdr.drop 32).take 32
  let pk := ek ++ seed
  let hashOk := sha3_256List pk == pkHash
  let domainOk := (List.range 3).all fun i =>
    let raw := byteDecodeRaw 12 ((ek.drop (384 * i)).take 384)
    (List.range 256).all fun j => decide (raw.getD j 0 < mlkemQ)
  hashOk && domainOk

/-! ### Round-3 CRYSTALS-Kyber-1024 (`K = 4, d_u = 11, d_v = 5`) -/

/-- `mlkem1024::kyber::encapsulate` (`(ct [1568B], ss [32B])`) parameterized by `sampler`. -/
def kyber1024EncapsWith (sampler : List (BitVec 8) → Poly)
    (pk1568 rand32 : List (BitVec 8)) : List (BitVec 8) × List (BitVec 8) :=
  let m := sha3_256List (rand32.take 32)
  let hPk := sha3_256List (pk1568.take 1568)
  let kr := sha3_512List (m ++ hPk)
  let kBar := kr.take 32
  let r := (kr.drop 32).take 32
  let (c1, c2, _, _) := indCpaEncryptWith sampler 4 11 5 (pk1568.take 1568) m r
  let ct := c1 ++ c2
  let ss := shake256List 32 (kBar ++ sha3_256List ct)
  (ct, ss)

/-- `mlkem1024::kyber::decapsulate` (`ss [32B]`) parameterized by `sampler`.
Models `libcrux` `variant::Kyber` (`ind_cca.rs:422-450`), which applies
`kdf(x, ct) = SHAKE-256_32(x ‖ SHA3-256(ct))` to both `kBar'` and `SHAKE-256_32(z ‖ ct)`
(`ssRej = SHAKE-256_32(SHAKE-256_32(z ‖ ct) ‖ SHA3-256(ct))`, vs `pqcrystals` Round-3
`KDF(z ‖ H(ct))`) before constant-time selection. -/
def kyber1024DecapsWith (sampler : List (BitVec 8) → Poly)
    (sk3168 ct1568 : List (BitVec 8)) : List (BitVec 8) :=
  let skPke := sk3168.take 1536
  let pk := (sk3168.drop 1536).take 1568
  let hPk := (sk3168.drop 3104).take 32
  let z := (sk3168.drop 3136).take 32
  let ct := ct1568.take 1568
  let m' := indCpaDecrypt 4 11 5 skPke ct
  let kr := sha3_512List (m' ++ hPk)
  let kBar' := kr.take 32
  let r' := (kr.drop 32).take 32
  let kRejPre := shake256List 32 (z ++ ct)
  let (c1', c2', _, _) := indCpaEncryptWith sampler 4 11 5 pk m' r'
  let hCt := sha3_256List ct
  let ssGood := shake256List 32 (kBar' ++ hCt)
  let ssRej := shake256List 32 (kRejPre ++ hCt)
  if ct == c1' ++ c2' then ssGood else ssRej

/-! ### Top-Level Unbounded Specifications -/

/-- Pack the first `n` bytes of `bs` (zero-padded if shorter) into `List.Vector (BitVec 8) n`. -/
def toByteVec (n : Nat) (bs : List (BitVec 8)) : List.Vector (BitVec 8) n :=
  ⟨(List.range n).map fun i => bs.getD i 0#8, by simp⟩

/-- Closed instantiation of `CryptoVerification.LibsignalSpqrV1.MlKem`.
`encaps2` matches bit-exact `mlkem768Encaps2List` (`libcrux`'s NEON `i16` NTT/Barrett pipeline,
since malformed `err2 = 0x7fff` inputs wrap in `i16`). -/
noncomputable def mlkem768Incremental : MlKem where
  keyPair seed := toByteVec 2400 (mlkem768KeyPairWith sampleNtt seed.toList)
  encaps1 hdr rand :=
    (mlkem768Encaps1With sampleNtt hdr rand.toList).map fun (ct1, es, ss) =>
      (toByteVec 960 ct1, toByteVec 2080 es, toByteVec 32 ss)
  encaps2 es ek := toByteVec 128 (mlkem768Encaps2List es.toList ek.toList)
  decaps dk ct1 ct2 :=
    toByteVec 32 (mlkem768DecapsWith sampleNtt dk.toList ct1.toList ct2.toList)
  validPk hdr ek := mlkem768ValidPk hdr ek

/-- Closed Round-3 CRYSTALS-Kyber-1024 encapsulation (`List (BitVec 8)` view). -/
noncomputable def kyber1024Encaps (pk rand : List (BitVec 8)) :
    List (BitVec 8) × List (BitVec 8) :=
  let (ct, ss) := kyber1024EncapsWith sampleNtt pk rand
  ((toByteVec 1568 ct).toList, (toByteVec 32 ss).toList)

/-- Closed Round-3 CRYSTALS-Kyber-1024 decapsulation (`List (BitVec 8)` view). -/
noncomputable def kyber1024Decaps (sk ct : List (BitVec 8)) : List (BitVec 8) :=
  (toByteVec 32 (kyber1024DecapsWith sampleNtt sk ct)).toList

/-- Typed `List.Vector` Round-3 CRYSTALS-Kyber-1024 encapsulation matching `PqxdhPrims.encaps`. -/
noncomputable def kyber1024EncapsVec
    (pk : List.Vector (BitVec 8) 1568) (rand : List.Vector (BitVec 8) 32) :
    List.Vector (BitVec 8) 1568 × List.Vector (BitVec 8) 32 :=
  (⟨(kyber1024Encaps pk.toList rand.toList).1, by simp [kyber1024Encaps, toByteVec]⟩,
   ⟨(kyber1024Encaps pk.toList rand.toList).2, by simp [kyber1024Encaps, toByteVec]⟩)

/-- Typed `List.Vector` Round-3 CRYSTALS-Kyber-1024 decapsulation matching `PqxdhPrims.decaps`. -/
noncomputable def kyber1024DecapsVec
    (sk : List.Vector (BitVec 8) 3168) (ct : List.Vector (BitVec 8) 1568) :
    List.Vector (BitVec 8) 32 :=
  ⟨kyber1024Decaps sk.toList ct.toList, by simp [kyber1024Decaps, toByteVec]⟩

end CryptoGames.MLKEM
