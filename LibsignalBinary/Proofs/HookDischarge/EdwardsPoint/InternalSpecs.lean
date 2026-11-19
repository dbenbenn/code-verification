/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase

/-!
# Internal Subroutine Specifications

Multi-block `DalekBlockOk` / `DalekBlockConstOk` contracts for `dalekCliMultiLib`:
- Layer 0: `memcpy` (`B36`, RW and RO), `subtle::black_box::<u8>` (`B00`),
  `<[u8] as subtle::ConstantTimeEq>::ct_eq` (`B24`).
- Layer 2 (`FieldElement51`): `mul` (`B22`, RW and RO-rhs), `pow2k` (`B11`),
  `to_bytes` (`B12`, RW and RO), `pow22501` (`B04`), `sqrt_ratio_i` (`B03`).
- Layer 3 (`Scalar52` and `Scalar`): `montgomery_mul` (`B06`, RW and RO-rhs), `Scalar52::mul`
  (`B07`, core and `< ℓ`), `Scalar::reduce` (`B16`), `from_bytes_mod_order` (`B01`),
  `from_bytes_mod_order_wide` (`B02`), `Scalar::mul` (`B21`, `B34`), `Scalar::add` (`B23`, `B35`),
  `as_radix_16` (`B15`, RW and RO).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj ProofLib
open VerifiedLibraries.Common (
  p25519 edOrderL sqrtM1 fpMul fpNeg fpSq fpPow leBytesToNat natToLeBytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (
  DalekBlockOk DalekBlockConstOk)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase (
  fe51ValOfBytes sc52ValOfBytes
  fe51_sqrt_m1 fe51SqrtM1Bytes sc52_l sc52LBytes sc52_rr sc52RRBytes)

/-! ## 1. Little-Endian Word Encoding & Field/Scalar Pure Helpers -/

/-- Encode a 64-bit word as 8 little-endian bytes. -/
@[expose] def encodeU64LE (w : BitVec 64) : List (BitVec 8) :=
  [ w.extractLsb' 0 8,
    w.extractLsb' 8 8,
    w.extractLsb' 16 8,
    w.extractLsb' 24 8,
    w.extractLsb' 32 8,
    w.extractLsb' 40 8,
    w.extractLsb' 48 8,
    w.extractLsb' 56 8 ]

/-- Encode a list of 64-bit words as little-endian bytes (`8 * ws.length` bytes). -/
@[expose] def encodeU64LEWords (ws : List (BitVec 64)) : List (BitVec 8) :=
  ws.flatMap encodeU64LE

/-- All 5 limbs of a 40-byte `FieldElement51` buffer are bounded by `bound`. -/
@[expose] def fe51LimbsBounded (bs : List (BitVec 8)) (bound : Nat) : Prop :=
  bs.length = 40 ∧
  (ByteSlice.readLE bs 0 8).toNat < bound ∧
  (ByteSlice.readLE bs 8 8).toNat < bound ∧
  (ByteSlice.readLE bs 16 8).toNat < bound ∧
  (ByteSlice.readLE bs 24 8).toNat < bound ∧
  (ByteSlice.readLE bs 32 8).toNat < bound

/-- Mathematical specification of `FieldElement51::sqrt_ratio_i(u, v)` over $\mathbb{F}_p$:
    returns `(was_nonzero_square, r)` where `r ∈ [0, p)` is even (`r % 2 = 0`). -/
@[expose] def sqrtRatioM1 (u v : Nat) : Bool × Nat :=
  let u := u % p25519
  let v := v % p25519
  let v3 := fpMul (fpSq v) v
  let v7 := fpMul (fpSq v3) v
  let r0 := fpMul (fpMul u v3) (fpPow (fpMul u v7) ((p25519 - 5) / 8))
  let check := fpMul v (fpSq r0)
  let correctSign := check == u
  let flippedSign := check == fpNeg u
  let flippedSignI := check == fpMul (fpNeg u) sqrtM1
  let rPrime := fpMul sqrtM1 r0
  let r1 := if flippedSign || flippedSignI then rPrime else r0
  let rEven := if r1 % 2 == 1 then fpNeg r1 else r1
  (correctSign || flippedSign, rEven)

/-- All 5 limbs of a 40-byte `Scalar52` buffer are bounded by `bound`. -/
@[expose] def sc52LimbsBounded (bs : List (BitVec 8)) (bound : Nat) : Prop :=
  bs.length = 40 ∧
  (ByteSlice.readLE bs 0 8).toNat < bound ∧
  (ByteSlice.readLE bs 8 8).toNat < bound ∧
  (ByteSlice.readLE bs 16 8).toNat < bound ∧
  (ByteSlice.readLE bs 24 8).toNat < bound ∧
  (ByteSlice.readLE bs 32 8).toNat < bound

/-- Signed radix-16 recoding (`[i8; 64]`) of a 32-byte scalar `a_bs` (`a_bs[31] ≤ 127`). -/
@[expose] def scalarRadix16Digits (a_bs : List (BitVec 8)) : List (BitVec 8) :=
  let rec go (idx : Nat) (carry : Int) (acc : List (BitVec 8)) : List (BitVec 8) :=
    match idx with
    | 0 => acc.reverse
    | k + 1 =>
      let i := 63 - k
      let byte := (a_bs.getD (i / 2) 0#8).toNat
      let botHalf : Int := if i % 2 == 0 then Int.ofNat (byte &&& 0x0f) else Int.ofNat (byte >>> 4)
      let d := botHalf + carry
      if i < 63 then
        let carry' : Int := (d + 8) / 16
        let digit' : Int := d - carry' * 16
        go k carry' (BitVec.ofInt 8 digit' :: acc)
      else
        go k 0 (BitVec.ofInt 8 d :: acc)
  go 64 0 []

private theorem scalarRadix16Digits_go_length (a_bs : List (BitVec 8)) :
    ∀ (idx : Nat) (carry : Int) (acc : List (BitVec 8)),
      (scalarRadix16Digits.go a_bs idx carry acc).length = acc.length + idx
  | 0, _, acc => by simp [scalarRadix16Digits.go]
  | k + 1, carry, acc => by
    unfold scalarRadix16Digits.go
    dsimp only
    split <;> simp only [scalarRadix16Digits_go_length, List.length_cons] <;> omega

theorem scalarRadix16Digits_length (a_bs : List (BitVec 8)) :
    (scalarRadix16Digits a_bs).length = 64 := by
  simpa [scalarRadix16Digits] using scalarRadix16Digits_go_length a_bs 64 0 []

/-! ## 2. Layer 0 Specifications (`memcpy`, `subtle::black_box::<u8>`, `ct_eq`) -/

/-- `memcpy` (`B36`, 99 insns, stack 0): copies `n` bytes from mutable/stack `src` (`x1`) to `dst`
    (`x0`), returning `dst`. -/
abbrev c_spec memcpySpec (dst src : ptr) (n : u64)
    (ghost dst_bs src_bs : List (BitVec 8)) : (ret : ptr)
  requires_cond dst_bs.length = n.toNat ∧ src_bs.length = n.toNat
  preserves     src ↦ₛ src_bs
  requires      dst ↦ₛ dst_bs
  ensures       (dst ↦ₛ src_bs) ∗ ⌜ret = dst⌝

abbrev MemcpyOk : Prop :=
  DalekBlockConstOk 36 memcpySpec

/-- Read-only-source variant of `memcpy` (`B36`, 99 insns, stack 0): copies `n` bytes from
    read-only `src` (`x1`, `↦ᵣ`) to `dst` (`x0`, `↦ₛ`), returning `dst`. -/
abbrev c_spec memcpyRoSpec (dst src : ptr) (n : u64)
    (ghost dst_bs src_bs : List (BitVec 8)) : (ret : ptr)
  requires_cond dst_bs.length = n.toNat ∧ src_bs.length = n.toNat
  preserves     src ↦ᵣ src_bs
  requires      dst ↦ₛ dst_bs
  ensures       (dst ↦ₛ src_bs) ∗ ⌜ret = dst⌝

abbrev MemcpyRoOk : Prop :=
  DalekBlockConstOk 36 memcpyRoSpec

/-- `subtle::black_box::<u8>` (`B00`, 5 insns, stack 16): returns `v` (`w0`) unchanged. -/
abbrev rust_spec blackBoxU8Spec (v : u8) : (ret : u8)
  stack   16
  ensures ⌜ret = v⌝

abbrev BlackBoxU8Ok : Prop :=
  DalekBlockConstOk 0 blackBoxU8Spec

/-- `<[u8] as subtle::ConstantTimeEq>::ct_eq` (`B24`, 210 insns, stack 64):
    constant-time equality of two 32-byte arrays (`x0`, `x1`), returning `Choice` (`1#8` if equal,
    `0#8` otherwise) in `w0`. -/
abbrev rust_spec slice32CtEqSpec (a : ptr) (b : ptr)
    (ghost a_bs b_bs : List (BitVec 8)) : (ret : u8)
  requires_cond a_bs.length = 32 ∧ b_bs.length = 32
  preserves     (a ↦ₛ a_bs) ∗ (b ↦ₛ b_bs)
  stack         64
  ensures       ⌜ret = if a_bs == b_bs then 1#8 else 0#8⌝

abbrev Slice32CtEqOk : Prop :=
  DalekBlockConstOk 24 slice32CtEqSpec

/-! ## 3. Layer 2 Specifications (`FieldElement51` Arithmetic mod $p = 2^{255}-19$) -/

/-- `<&FieldElement51 as Mul>::mul` (`B22`, 166 insns, stack 224): multiplies two 5-limb
    `FieldElement51` values at `a` (`x0`) and `b` (`x1`) into `out` (`x8` `sret`). -/
abbrev rust_spec fe51MulSpec (out : sret) (a : ptr) (b : ptr)
    (ghost out_bs a_bs b_bs : List (BitVec 8))
  requires_cond out_bs.length = 40 ∧ fe51LimbsBounded a_bs (2 ^ 54) ∧ fe51LimbsBounded b_bs (2 ^ 54)
  preserves     (a ↦ₛ a_bs) ∗ (b ↦ₛ b_bs)
  requires      out ↦ₛ out_bs
  stack         224
  ensures       ∃∗ res_bs : List (BitVec 8),
                  (out ↦ₛ res_bs) ∗
                  ⌜fe51LimbsBounded res_bs (2 ^ 52) ∧
                    fe51ValOfBytes res_bs % p25519 =
                      (fe51ValOfBytes a_bs * fe51ValOfBytes b_bs) % p25519⌝

abbrev Fe51MulOk : Prop :=
  DalekBlockConstOk 22 fe51MulSpec

/-- Read-only-rhs variant of `<&FieldElement51 as Mul>::mul` (`B22`), used when multiplying by
    `.rodata` constants (`EDWARDS_D`, `EDWARDS_D2`, `SQRT_M1`, or read-only `AffineNielsPoint`). -/
abbrev rust_spec fe51MulRoRightSpec (out : sret) (a : ptr) (b : ptr)
    (ghost out_bs a_bs b_bs : List (BitVec 8))
  requires_cond out_bs.length = 40 ∧ fe51LimbsBounded a_bs (2 ^ 54) ∧ fe51LimbsBounded b_bs (2 ^ 54)
  preserves     (a ↦ₛ a_bs) ∗ (b ↦ᵣ b_bs)
  requires      out ↦ₛ out_bs
  stack         224
  ensures       ∃∗ res_bs : List (BitVec 8),
                  (out ↦ₛ res_bs) ∗
                  ⌜fe51LimbsBounded res_bs (2 ^ 52) ∧
                    fe51ValOfBytes res_bs % p25519 =
                      (fe51ValOfBytes a_bs * fe51ValOfBytes b_bs) % p25519⌝

abbrev Fe51MulRoRightOk : Prop :=
  DalekBlockConstOk 22 fe51MulRoRightSpec

/-- `FieldElement51::pow2k` (`B11`, 100 insns, stack 96): squares `a` (`x0`) `k` (`w1`,
    `0 < k < 256`) times into `out` (`x8` `sret`). -/
abbrev rust_spec fe51Pow2kSpec (out : sret) (a : ptr) (k : u32)
    (ghost out_bs a_bs : List (BitVec 8))
  requires_cond out_bs.length = 40 ∧ fe51LimbsBounded a_bs (2 ^ 54) ∧ 0 < k.toNat ∧ k.toNat < 256
  preserves     a ↦ₛ a_bs
  requires      out ↦ₛ out_bs
  stack         96
  ensures       ∃∗ res_bs : List (BitVec 8),
                  (out ↦ₛ res_bs) ∗
                  ⌜fe51LimbsBounded res_bs (2 ^ 52) ∧
                    fe51ValOfBytes res_bs % p25519 =
                      fpPow (fe51ValOfBytes a_bs % p25519) (2 ^ k.toNat)⌝

abbrev Fe51Pow2kOk : Prop :=
  DalekBlockConstOk 11 fe51Pow2kSpec

/-- `FieldElement51::to_bytes` (`B12`, 94 insns, stack 0): canonicalizes `a` (`x0`) modulo
    $p = 2^{255}-19$ into 32 little-endian bytes at `out` (`x8` `sret`). -/
abbrev rust_spec fe51ToBytesSpec (out : sret) (a : ptr)
    (ghost out_bs a_bs : List (BitVec 8))
  requires_cond out_bs.length = 32 ∧ fe51LimbsBounded a_bs (2 ^ 54)
  preserves     a ↦ₛ a_bs
  requires      out ↦ₛ out_bs
  ensures       out ↦ₛ natToLeBytes 32 (fe51ValOfBytes a_bs % p25519)

abbrev Fe51ToBytesOk : Prop :=
  DalekBlockConstOk 12 fe51ToBytesSpec

/-- Read-only-input variant of `FieldElement51::to_bytes` (`B12`, 94 insns, stack 0), used when
    canonicalizing `.rodata` constants (`fe51MinusOneBytes`). -/
abbrev rust_spec fe51ToBytesRoSpec (out : sret) (self : ptr)
    (ghost out_bs self_bs : List (BitVec 8))
  requires_cond out_bs.length = 32 ∧ fe51LimbsBounded self_bs (2 ^ 54)
  preserves     self ↦ᵣ self_bs
  requires      out ↦ₛ out_bs
  stack         0
  ensures       out ↦ₛ natToLeBytes 32 (fe51ValOfBytes self_bs % p25519)

abbrev Fe51ToBytesRoOk : Prop :=
  DalekBlockConstOk 12 fe51ToBytesRoSpec

/-- `FieldElement51::pow22501` (`B04`, 101 insns, stack 1040): computes
    `(a^(2^250 - 1), a^11)` for `a` (`x1`) into the 80-byte tuple at `out` (`x0`). -/
abbrev rust_spec fe51Pow22501Spec (out : ptr) (a : ptr)
    (ghost out_bs a_bs : List (BitVec 8))
  requires_cond out_bs.length = 80 ∧ fe51LimbsBounded a_bs (2 ^ 54)
  preserves     a ↦ₛ a_bs
  requires      out ↦ₛ out_bs
  stack         1040
  ensures       ∃∗ t19_bs : List (BitVec 8), ∃∗ t3_bs : List (BitVec 8),
                  (out ↦ₛ (t19_bs ++ t3_bs)) ∗
                  ⌜fe51LimbsBounded t19_bs (2 ^ 52) ∧
                    fe51LimbsBounded t3_bs (2 ^ 52) ∧
                    fe51ValOfBytes t19_bs % p25519 =
                      fpPow (fe51ValOfBytes a_bs % p25519) (2 ^ 250 - 1) ∧
                    fe51ValOfBytes t3_bs % p25519 =
                      fpPow (fe51ValOfBytes a_bs % p25519) 11⌝

abbrev Fe51Pow22501Ok : Prop :=
  DalekBlockConstOk 4 fe51Pow22501Spec

/-- `FieldElement51::sqrt_ratio_i` (`B03`, 653 insns, stack 1712): computes `(Choice, r)` for
    `u` (`x1`) and `v` (`x2`) into the 48-byte return slot at `out` (`x0`), where `out[0]` is the
    `Choice` byte (`1#8` or `0#8`) and `out[8..48]` is the 40-byte `FieldElement51` result `r`. -/
abbrev rust_spec fe51SqrtRatioISpec
    (ctx mpl : Obj.MultiPlacement)
    (out : ptr) (u : ptr) (v : ptr)
    (ghost out_bs u_bs v_bs : List (BitVec 8))
  requires_cond out_bs.length = 48 ∧ fe51LimbsBounded u_bs (2 ^ 54) ∧ fe51LimbsBounded v_bs (2 ^ 54)
  preserves     (u ↦ₛ u_bs) ∗ (v ↦ₛ v_bs) ∗ (fe51_sqrt_m1 mpl ↦ᵣ fe51SqrtM1Bytes)
  requires      out ↦ₛ out_bs
  stack         1712
  ensures       ∃∗ pad_bs : List (BitVec 8), ∃∗ r_bs : List (BitVec 8),
                  let sr := sqrtRatioM1 (fe51ValOfBytes u_bs % p25519) (fe51ValOfBytes v_bs % p25519)
                  (out ↦ₛ ((if sr.1 then 1#8 else 0#8) :: pad_bs ++ r_bs)) ∗
                  ⌜pad_bs.length = 7 ∧
                    fe51LimbsBounded r_bs (2 ^ 52) ∧
                    fe51ValOfBytes r_bs % p25519 = sr.2⌝

abbrev Fe51SqrtRatioIOk : Prop :=
  DalekBlockOk 3 fe51SqrtRatioISpec

/-! ## 4. Layer 3 Specifications (`Scalar52` & `Scalar` Arithmetic mod $\ell$) -/

/-- `Scalar52::montgomery_mul` (`B06`, 329 insns, stack 256): Montgomery multiplication
    $(a \cdot b \cdot 2^{-260}) \bmod \ell$ into `out` (`x0`). -/
abbrev rust_spec sc52MontgomeryMulCoreSpec (out : ptr) (a : ptr) (b : ptr)
    (ghost out_bs a_bs b_bs : List (BitVec 8))
  requires_cond out_bs.length = 40 ∧
                sc52LimbsBounded a_bs (2 ^ 52) ∧ sc52LimbsBounded b_bs (2 ^ 52) ∧
                sc52ValOfBytes a_bs * sc52ValOfBytes b_bs < 2 ^ 260 * edOrderL
  preserves     (a ↦ₛ a_bs) ∗ (b ↦ₛ b_bs)
  requires      out ↦ₛ out_bs
  stack         256
  ensures       ∃∗ res_bs : List (BitVec 8),
                  (out ↦ₛ res_bs) ∗
                  ⌜sc52LimbsBounded res_bs (2 ^ 52) ∧
                    sc52ValOfBytes res_bs < edOrderL ∧
                    (sc52ValOfBytes res_bs * 2 ^ 260) % edOrderL =
                      (sc52ValOfBytes a_bs * sc52ValOfBytes b_bs) % edOrderL⌝

abbrev Sc52MontgomeryMulCoreOk : Prop :=
  DalekBlockConstOk 6 sc52MontgomeryMulCoreSpec

/-- Read-only-rhs variant of `Scalar52::montgomery_mul` (`B06`, 329 insns, stack 256), used when
    `Scalar::from_bytes_mod_order_wide` multiplies by `.rodata` `R` / `RR`. -/
abbrev rust_spec sc52MontgomeryMulRoRightSpec (out : ptr) (a : ptr) (b : ptr)
    (ghost out_bs a_bs b_bs : List (BitVec 8))
  requires_cond out_bs.length = 40 ∧
                sc52LimbsBounded a_bs (2 ^ 52) ∧ sc52LimbsBounded b_bs (2 ^ 52) ∧
                sc52ValOfBytes a_bs * sc52ValOfBytes b_bs < 2 ^ 260 * edOrderL
  preserves     (a ↦ₛ a_bs) ∗ (b ↦ᵣ b_bs)
  requires      out ↦ₛ out_bs
  stack         256
  ensures       ∃∗ res_bs : List (BitVec 8),
                  (out ↦ₛ res_bs) ∗
                  ⌜sc52LimbsBounded res_bs (2 ^ 52) ∧
                    sc52ValOfBytes res_bs < edOrderL ∧
                    (sc52ValOfBytes res_bs * 2 ^ 260) % edOrderL =
                      (sc52ValOfBytes a_bs * sc52ValOfBytes b_bs) % edOrderL⌝

abbrev Sc52MontgomeryMulRoRightOk : Prop :=
  DalekBlockConstOk 6 sc52MontgomeryMulRoRightSpec

/-- General product-bound contract for `Scalar52::mul` (`B07`, 662 insns, stack 288):
    accepts any 52-bit-bounded inputs satisfying `a * b < 2^260 * ℓ` (used by `<&Scalar as Mul>::mul`
    on unreduced 256-bit `Scalar`s). -/
abbrev rust_spec sc52MulCoreSpec (out : ptr) (a : ptr) (b : ptr)
    (ghost out_bs a_bs b_bs : List (BitVec 8))
  requires_cond out_bs.length = 40 ∧
                sc52LimbsBounded a_bs (2 ^ 52) ∧ sc52LimbsBounded b_bs (2 ^ 52) ∧
                sc52ValOfBytes a_bs * sc52ValOfBytes b_bs < 2 ^ 260 * edOrderL
  preserves     (a ↦ₛ a_bs) ∗ (b ↦ₛ b_bs)
  requires      out ↦ₛ out_bs
  stack         288
  ensures       ∃∗ res_bs : List (BitVec 8),
                  (out ↦ₛ res_bs) ∗
                  ⌜sc52LimbsBounded res_bs (2 ^ 52) ∧
                    sc52ValOfBytes res_bs =
                      (sc52ValOfBytes a_bs * sc52ValOfBytes b_bs) % edOrderL⌝

abbrev Sc52MulCoreOk : Prop :=
  DalekBlockConstOk 7 sc52MulCoreSpec

/-- Canonical `< ℓ` specialization of `Scalar52::mul` (`B07`, 662 insns, stack 288). -/
abbrev rust_spec sc52MulSpec (out : ptr) (a : ptr) (b : ptr)
    (ghost out_bs a_bs b_bs : List (BitVec 8))
  requires_cond out_bs.length = 40 ∧
                sc52LimbsBounded a_bs (2 ^ 52) ∧ sc52LimbsBounded b_bs (2 ^ 52) ∧
                sc52ValOfBytes a_bs < edOrderL ∧ sc52ValOfBytes b_bs < edOrderL
  preserves     (a ↦ₛ a_bs) ∗ (b ↦ₛ b_bs)
  requires      out ↦ₛ out_bs
  stack         288
  ensures       ∃∗ res_bs : List (BitVec 8),
                  (out ↦ₛ res_bs) ∗
                  ⌜sc52LimbsBounded res_bs (2 ^ 52) ∧
                    sc52ValOfBytes res_bs =
                      (sc52ValOfBytes a_bs * sc52ValOfBytes b_bs) % edOrderL⌝

abbrev Sc52MulOk : Prop :=
  DalekBlockConstOk 7 sc52MulSpec

/-- `Scalar::reduce` (`B16`, 427 insns, stack 208): reduces a 32-byte `Scalar` at `a` (`x1`)
    modulo $\ell$ into `out` (`x0`). -/
abbrev rust_spec scalarReduceSpec (out : ptr) (a : ptr)
    (ghost out_bs a_bs : List (BitVec 8))
  requires_cond out_bs.length = 32 ∧ a_bs.length = 32
  preserves     a ↦ₛ a_bs
  requires      out ↦ₛ out_bs
  stack         208
  ensures       out ↦ₛ natToLeBytes 32 (leBytesToNat a_bs % edOrderL)

abbrev ScalarReduceOk : Prop :=
  DalekBlockConstOk 16 scalarReduceSpec

/-- `Scalar::from_bytes_mod_order` (`B01`, 3 insns, stack 208): reduces a 32-byte array at
    `a` (`x0`) modulo $\ell$ into `out` (`x8` `sret`). -/
abbrev rust_spec scalarFromBytesModOrderSpec (out : sret) (a : ptr)
    (ghost out_bs a_bs : List (BitVec 8))
  requires_cond out_bs.length = 32 ∧ a_bs.length = 32
  preserves     a ↦ₛ a_bs
  requires      out ↦ₛ out_bs
  stack         208
  ensures       out ↦ₛ natToLeBytes 32 (leBytesToNat a_bs % edOrderL)

abbrev ScalarFromBytesModOrderOk : Prop :=
  DalekBlockConstOk 1 scalarFromBytesModOrderSpec

/-- `Scalar::from_bytes_mod_order_wide` (`B02`, 277 insns, stack 448): reduces a 64-byte array
    at `a` (`x0`) modulo $\ell$ into `out` (`x8` `sret`). -/
abbrev rust_spec scalarFromBytesModOrderWideSpec
    (ctx mpl : Obj.MultiPlacement)
    (out : sret) (a : ptr)
    (ghost out_bs a_bs : List (BitVec 8))
  requires_cond out_bs.length = 32 ∧ a_bs.length = 64
  preserves     (a ↦ₛ a_bs) ∗ (sc52_l mpl ↦ᵣ sc52LBytes) ∗ (sc52_rr mpl ↦ᵣ sc52RRBytes)
  requires      out ↦ₛ out_bs
  stack         448
  ensures       out ↦ₛ natToLeBytes 32 (leBytesToNat a_bs % edOrderL)

abbrev ScalarFromBytesModOrderWideOk : Prop :=
  DalekBlockOk 2 scalarFromBytesModOrderWideSpec

/-- `<&Scalar as Mul>::mul` (`B21`, 147 insns, stack 448) and `<Scalar as Mul>::mul` (`B34`,
    1 insn): multiplies two 32-byte `Scalar`s at `a` (`x0`) and `b` (`x1`) modulo $\ell$ into
    `out` (`x8` `sret`). -/
abbrev rust_spec scalarMulSpec (out : sret) (a : ptr) (b : ptr)
    (ghost out_bs a_bs b_bs : List (BitVec 8))
  requires_cond out_bs.length = 32 ∧ a_bs.length = 32 ∧ b_bs.length = 32
  preserves     (a ↦ₛ a_bs) ∗ (b ↦ₛ b_bs)
  requires      out ↦ₛ out_bs
  stack         448
  ensures       out ↦ₛ natToLeBytes 32 ((leBytesToNat a_bs * leBytesToNat b_bs) % edOrderL)

abbrev ScalarMulRefOk : Prop :=
  DalekBlockConstOk 21 scalarMulSpec

abbrev ScalarMulValOk : Prop :=
  DalekBlockConstOk 34 scalarMulSpec

/-- `<&Scalar as Add>::add` (`B23`, 197 insns, stack 80) and `<Scalar as Add>::add` (`B35`,
    1 insn): adds two canonical 32-byte `Scalar`s at `a` (`x0`) and `b` (`x1`) modulo $\ell$ into
    `out` (`x8` `sret`). -/
abbrev rust_spec scalarAddSpec (out : sret) (a : ptr) (b : ptr)
    (ghost out_bs a_bs b_bs : List (BitVec 8))
  requires_cond out_bs.length = 32 ∧ a_bs.length = 32 ∧ b_bs.length = 32 ∧
                leBytesToNat a_bs < edOrderL ∧ leBytesToNat b_bs < edOrderL
  preserves     (a ↦ₛ a_bs) ∗ (b ↦ₛ b_bs)
  requires      out ↦ₛ out_bs
  stack         80
  ensures       out ↦ₛ natToLeBytes 32 ((leBytesToNat a_bs + leBytesToNat b_bs) % edOrderL)

abbrev ScalarAddRefOk : Prop :=
  DalekBlockConstOk 23 scalarAddSpec

abbrev ScalarAddValOk : Prop :=
  DalekBlockConstOk 35 scalarAddSpec

/-- `Scalar::as_radix_16` (`B15`, 173 insns, stack 0): recodes a 32-byte scalar at `a` (`x1`,
    with `a[31] ≤ 127`) into 64 signed radix-16 digits (`∈ [-8, 8]`) at `out` (`x0`). -/
abbrev rust_spec scalarAsRadix16Spec (out : ptr) (a : ptr)
    (ghost out_bs a_bs : List (BitVec 8))
  requires_cond out_bs.length = 64 ∧ a_bs.length = 32 ∧ (a_bs.getD 31 0#8).toNat ≤ 127
  preserves     a ↦ₛ a_bs
  requires      out ↦ₛ out_bs
  ensures       out ↦ₛ scalarRadix16Digits a_bs

abbrev ScalarAsRadix16Ok : Prop :=
  DalekBlockConstOk 15 scalarAsRadix16Spec

/-- Read-only-rhs variant of `Scalar::as_radix_16` (`B15`, 173 insns, stack 0), used when
    `EdwardsPoint::is_torsion_free` passes `.rodata` `constants::BASEPOINT_ORDER_PRIVATE` (`↦ᵣ`). -/
abbrev rust_spec scalarAsRadix16RoSpec (out : ptr) (a : ptr)
    (ghost out_bs a_bs : List (BitVec 8))
  requires_cond out_bs.length = 64 ∧ a_bs.length = 32 ∧ (a_bs.getD 31 0#8).toNat ≤ 127
  preserves     a ↦ᵣ a_bs
  requires      out ↦ₛ out_bs
  ensures       out ↦ₛ scalarRadix16Digits a_bs

abbrev ScalarAsRadix16RoOk : Prop :=
  DalekBlockConstOk 15 scalarAsRadix16RoSpec

end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs
