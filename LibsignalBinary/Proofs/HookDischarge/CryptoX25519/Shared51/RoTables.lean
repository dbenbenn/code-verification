/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase

/-!
# `.rodata` Constant and Table Lookup Lemmas

Kernel-checked (`decide +kernel`) byte lengths, 64-bit little-endian word reads
(`ByteSlice.readLE` and `pack64`), and radix evaluations for the three `.rodata`
constants of `x25519CliMultiLib`:
- `fe51OneBytes` (`FieldElement51::ONE = 1`)
- `fe51MontA24Bytes` (`MONTGOMERY_A_PLUS_TWO_OVER_FOUR = 121666 = a24 + 1`)
- `ed25519BasepointTableBytes` (`ED25519_BASEPOINT_TABLE_INNER_DOC_HIDDEN`, 30,720 bytes)
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.RoTables

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.CommonBase (
  a24 checkWords64 fe51Val fe51ValOfBytes
  fe51OneBytes fe51MontA24Bytes ed25519BasepointTableBytes)

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

/-! ## 2. Byte Lengths of `.rodata` Constants -/

theorem fe51OneBytes_length : fe51OneBytes.length = 40 := by decide +kernel
theorem fe51MontA24Bytes_length : fe51MontA24Bytes.length = 40 := by decide +kernel

set_option maxHeartbeats 800000 in
theorem ed25519BasepointTableBytes_length : ed25519BasepointTableBytes.length = 30720 := by
  decide +kernel

/-! ## 3. `FieldElement51` `.rodata` Constants (`2^51` Radix) -/

theorem fe51One_readLE_0 : ByteSlice.readLE fe51OneBytes 0 8 = 1#64 := by decide +kernel
theorem fe51One_readLE_8 : ByteSlice.readLE fe51OneBytes 8 8 = 0#64 := by decide +kernel
theorem fe51One_readLE_16 : ByteSlice.readLE fe51OneBytes 16 8 = 0#64 := by decide +kernel
theorem fe51One_readLE_24 : ByteSlice.readLE fe51OneBytes 24 8 = 0#64 := by decide +kernel
theorem fe51One_readLE_32 : ByteSlice.readLE fe51OneBytes 32 8 = 0#64 := by decide +kernel
theorem fe51One_val : fe51ValOfBytes fe51OneBytes = 1 := by decide +kernel

theorem fe51MontA24_readLE_0 : ByteSlice.readLE fe51MontA24Bytes 0 8 = 121666#64 := by
  decide +kernel
theorem fe51MontA24_readLE_8 : ByteSlice.readLE fe51MontA24Bytes 8 8 = 0#64 := by
  decide +kernel
theorem fe51MontA24_readLE_16 : ByteSlice.readLE fe51MontA24Bytes 16 8 = 0#64 := by
  decide +kernel
theorem fe51MontA24_readLE_24 : ByteSlice.readLE fe51MontA24Bytes 24 8 = 0#64 := by
  decide +kernel
theorem fe51MontA24_readLE_32 : ByteSlice.readLE fe51MontA24Bytes 32 8 = 0#64 := by
  decide +kernel
theorem fe51MontA24_val : fe51ValOfBytes fe51MontA24Bytes = a24 + 1 := by
  decide +kernel

end LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Shared51.RoTables
