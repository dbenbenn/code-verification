/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase

/-!
# `.rodata` Constant and Table Lookup Lemmas

Kernel-checked (`decide +kernel`) byte lengths, 64-bit little-endian word reads
(`ByteSlice.readLE` and `pack64`), and radix evaluation for the 11 `.rodata` / `.data.rel.ro`
constants of `curve25519-dalek` `5.0.0`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.RoTables

open Arm64 Arm64.Obj ProofLib
open VerifiedLibraries.Common (p25519 edOrderL edD edD2 sqrtM1 leBytesToNat natToLeBytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase (
  checkWords64 fe51Val fe51ValOfBytes sc52Val sc52ValOfBytes
  fe51OneBytes fe51EdwardsDBytes fe51MinusOneBytes fe51SqrtM1Bytes
  sc52LBytes sc52RRBytes fe51EdwardsD2Bytes basepointOrderBytes
  oddMultiplesBasepointBytes ed25519BasepointTableBytes)

/-! ## 1. Generic Linear 8-Byte Word Table Checker -/

theorem readLE_cons8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (rest : List (BitVec 8)) (off n : Nat) :
    ByteSlice.readLE (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest) (off + 8) n =
    ByteSlice.readLE rest off n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ByteSlice.readLE_succ, ByteSlice.readLE_succ, ih,
      show off + 8 + n = (off + n) + 8 by omega]
    rfl

theorem of_checkWords64 {bs : List (BitVec 8)} {expected : Nat → BitVec 64} {idx rem k : Nat}
    (h : checkWords64 bs expected idx rem = true) (hk : k < rem) :
    ByteSlice.readLE bs (8 * k) 8 = expected (idx + k) := by
  induction rem generalizing bs idx k with
  | zero => omega
  | succ rem ih =>
    unfold checkWords64 at h
    rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, rest⟩⟩⟩⟩⟩⟩⟩⟩
    all_goals try contradiction
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases k with _ | k
    · rw [Nat.mul_zero, Nat.add_zero, ← ByteSlice.pack64_eq_readLE_8]
      exact h.1
    · have hrec := @ih rest (idx + 1) k h.2 (by omega)
      rw [show idx + 1 + k = idx + (k + 1) by omega] at hrec
      rw [show 8 * (k + 1) = 8 * k + 8 by omega, readLE_cons8]
      exact hrec

/-! ## 2. Byte Lengths of `.rodata` Constants & Relocated Pointer Cell -/

theorem fe51OneBytes_length : fe51OneBytes.length = 40 := by decide +kernel
theorem fe51EdwardsDBytes_length : fe51EdwardsDBytes.length = 40 := by decide +kernel
theorem fe51MinusOneBytes_length : fe51MinusOneBytes.length = 40 := by decide +kernel
theorem fe51SqrtM1Bytes_length : fe51SqrtM1Bytes.length = 40 := by decide +kernel
theorem sc52LBytes_length : sc52LBytes.length = 40 := by decide +kernel
theorem sc52RRBytes_length : sc52RRBytes.length = 40 := by decide +kernel
theorem fe51EdwardsD2Bytes_length : fe51EdwardsD2Bytes.length = 40 := by decide +kernel
theorem basepointOrderBytes_length : basepointOrderBytes.length = 32 := by decide +kernel
theorem oddMultiplesBasepointBytes_length : oddMultiplesBasepointBytes.length = 7680 := by
  decide +kernel
theorem ed25519BasepointTableBytes_length : ed25519BasepointTableBytes.length = 30720 := by
  decide +kernel

theorem bytesLE8_length (v : BitVec 64) : (Obj.bytesLE 8 v).length = 8 := rfl

theorem bytesLE8_readLE (v : BitVec 64) : ByteSlice.readLE (Obj.bytesLE 8 v) 0 8 = v := by
  have h : Obj.bytesLE 8 v = ByteSlice.unpackLE 8 v := rfl
  rw [h, ByteSlice.readLE_unpackLE_64 8 v v.isLt]

/-! ## 3. `FieldElement51` `.rodata` Constants (`2^51` Radix) -/

theorem fe51One_readLE_0 : ByteSlice.readLE fe51OneBytes 0 8 = 1#64 := by decide +kernel
theorem fe51One_readLE_8 : ByteSlice.readLE fe51OneBytes 8 8 = 0#64 := by decide +kernel
theorem fe51One_readLE_16 : ByteSlice.readLE fe51OneBytes 16 8 = 0#64 := by decide +kernel
theorem fe51One_readLE_24 : ByteSlice.readLE fe51OneBytes 24 8 = 0#64 := by decide +kernel
theorem fe51One_readLE_32 : ByteSlice.readLE fe51OneBytes 32 8 = 0#64 := by decide +kernel
theorem fe51One_val : fe51ValOfBytes fe51OneBytes = 1 := by decide +kernel

theorem fe51EdwardsD_readLE_0 : ByteSlice.readLE fe51EdwardsDBytes 0 8 = 929955233495203#64 := by
  decide +kernel
theorem fe51EdwardsD_readLE_8 : ByteSlice.readLE fe51EdwardsDBytes 8 8 = 466365720129213#64 := by
  decide +kernel
theorem fe51EdwardsD_readLE_16 : ByteSlice.readLE fe51EdwardsDBytes 16 8 = 1662059464998953#64 := by
  decide +kernel
theorem fe51EdwardsD_readLE_24 : ByteSlice.readLE fe51EdwardsDBytes 24 8 = 2033849074728123#64 := by
  decide +kernel
theorem fe51EdwardsD_readLE_32 : ByteSlice.readLE fe51EdwardsDBytes 32 8 = 1442794654840575#64 := by
  decide +kernel
theorem fe51EdwardsD_val : fe51ValOfBytes fe51EdwardsDBytes = edD := by decide +kernel

theorem fe51MinusOne_readLE_0 : ByteSlice.readLE fe51MinusOneBytes 0 8 = 2251799813685228#64 := by
  decide +kernel
theorem fe51MinusOne_readLE_8 : ByteSlice.readLE fe51MinusOneBytes 8 8 = 2251799813685247#64 := by
  decide +kernel
theorem fe51MinusOne_readLE_16 : ByteSlice.readLE fe51MinusOneBytes 16 8 = 2251799813685247#64 := by
  decide +kernel
theorem fe51MinusOne_readLE_24 : ByteSlice.readLE fe51MinusOneBytes 24 8 = 2251799813685247#64 := by
  decide +kernel
theorem fe51MinusOne_readLE_32 : ByteSlice.readLE fe51MinusOneBytes 32 8 = 2251799813685247#64 := by
  decide +kernel
theorem fe51MinusOne_val : fe51ValOfBytes fe51MinusOneBytes = p25519 - 1 := by decide +kernel

theorem fe51SqrtM1_readLE_0 : ByteSlice.readLE fe51SqrtM1Bytes 0 8 = 1718705420411056#64 := by
  decide +kernel
theorem fe51SqrtM1_readLE_8 : ByteSlice.readLE fe51SqrtM1Bytes 8 8 = 234908883556509#64 := by
  decide +kernel
theorem fe51SqrtM1_readLE_16 : ByteSlice.readLE fe51SqrtM1Bytes 16 8 = 2233514472574048#64 := by
  decide +kernel
theorem fe51SqrtM1_readLE_24 : ByteSlice.readLE fe51SqrtM1Bytes 24 8 = 2117202627021982#64 := by
  decide +kernel
theorem fe51SqrtM1_readLE_32 : ByteSlice.readLE fe51SqrtM1Bytes 32 8 = 765476049583133#64 := by
  decide +kernel
theorem fe51SqrtM1_val : fe51ValOfBytes fe51SqrtM1Bytes = sqrtM1 := by decide +kernel

theorem fe51EdwardsD2_readLE_0 :
    ByteSlice.readLE fe51EdwardsD2Bytes 0 8 = 1859910466990425#64 := by decide +kernel
theorem fe51EdwardsD2_readLE_8 :
    ByteSlice.readLE fe51EdwardsD2Bytes 8 8 = 932731440258426#64 := by decide +kernel
theorem fe51EdwardsD2_readLE_16 :
    ByteSlice.readLE fe51EdwardsD2Bytes 16 8 = 1072319116312658#64 := by decide +kernel
theorem fe51EdwardsD2_readLE_24 :
    ByteSlice.readLE fe51EdwardsD2Bytes 24 8 = 1815898335770999#64 := by decide +kernel
theorem fe51EdwardsD2_readLE_32 :
    ByteSlice.readLE fe51EdwardsD2Bytes 32 8 = 633789495995903#64 := by decide +kernel
theorem fe51EdwardsD2_val : fe51ValOfBytes fe51EdwardsD2Bytes = edD2 := by
  decide +kernel

/-! ## 4. `Scalar52` and `BASEPOINT_ORDER` `.rodata` Constants -/

theorem basepointOrderBytes_val : leBytesToNat basepointOrderBytes = edOrderL := by
  decide +kernel
theorem basepointOrderBytes_eq : basepointOrderBytes = natToLeBytes 32 edOrderL := by
  decide +kernel
theorem basepointOrderBytes_getD31 : (basepointOrderBytes.getD 31 0#8).toNat = 16 := by
  decide +kernel

/-- `sc52LBytes` (`curve25519_dalek:.rodata..Lanon.16`) is `constants::RR = R^2 mod ℓ` (`2^520 mod ℓ`). -/
theorem sc52L_readLE_0 : ByteSlice.readLE sc52LBytes 0 8 = 0x0009d265e952d13b#64 := by
  decide +kernel
theorem sc52L_readLE_8 : ByteSlice.readLE sc52LBytes 8 8 = 0x000d63c715bea69f#64 := by
  decide +kernel
theorem sc52L_readLE_16 : ByteSlice.readLE sc52LBytes 16 8 = 0x0005be65cb687604#64 := by
  decide +kernel
theorem sc52L_readLE_24 : ByteSlice.readLE sc52LBytes 24 8 = 0x0003dceec73d217f#64 := by
  decide +kernel
theorem sc52L_readLE_32 : ByteSlice.readLE sc52LBytes 32 8 = 0x000009411b7c309a#64 := by
  decide +kernel
theorem sc52L_val : sc52ValOfBytes sc52LBytes = (2 ^ 260 * 2 ^ 260) % edOrderL := by
  decide +kernel

/-- `sc52RRBytes` (`curve25519_dalek:.rodata..Lanon.17`) is `constants::R = R mod ℓ` (`2^260 mod ℓ`). -/
theorem sc52RR_readLE_0 : ByteSlice.readLE sc52RRBytes 0 8 = 0x000f48bd6721e6ed#64 := by
  decide +kernel
theorem sc52RR_readLE_8 : ByteSlice.readLE sc52RRBytes 8 8 = 0x0003bab5ac67e45a#64 := by
  decide +kernel
theorem sc52RR_readLE_16 : ByteSlice.readLE sc52RRBytes 16 8 = 0x000fffffeb35e51b#64 := by
  decide +kernel
theorem sc52RR_readLE_24 : ByteSlice.readLE sc52RRBytes 24 8 = 0x000fffffffffffff#64 := by
  decide +kernel
theorem sc52RR_readLE_32 : ByteSlice.readLE sc52RRBytes 32 8 = 0x00000fffffffffff#64 := by
  decide +kernel
theorem sc52RR_val : sc52ValOfBytes sc52RRBytes = (2 ^ 260) % edOrderL := by
  decide +kernel

end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.RoTables
