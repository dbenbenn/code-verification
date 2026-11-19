/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.StdStartup.MemOps
public import ProofLib.SepLogic.WP.StepsProcess
public import ProofLib.SepLogic.ByteRegion
public import VerifiedLibraries.Common.Spec.Curve25519
public import LibsignalBinary.Heap.SpecBudget
import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhHooksCommon
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhModelLink
public import LibsignalBinary.Specifications.SignalPqxdh.Model
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Crypto.DalekEdNeg
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Crypto.MlkemPk

/-!
# Byte-Exact & Algebraic `<EdwardsPoint as Neg>::neg` Hook Discharge (`LibsignalBinary.Proofs.HookDischarge.Crypto.EdwardsNeg`)

Real-bytes machine-code verification and Curve25519 field/point soundness for
`<curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Neg>::neg`
(`_RNvXso_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPointNtNtNtCskxtBwYRO61I_4core3ops5arith3Neg3neg`,
`edwardsPointNegWords` / `edwardsPointNegInstrs`: `57` 32-bit instruction words = `228` bytes, `0` B
stack, `0` external calls, `0` `.rodata` loads; emitted by pinned `rustc 1.98.1`
`aarch64-unknown-linux-musl` release profile in `curve25519-dalek` `5.0.0`):

1. **Pure 5×51-bit byte function & Curve25519 soundness (`dalekEdNegBytes` / `dalekEdNegVec`):**
   Models the exact 5-limb radix-$2^{51}$ biased negation `FieldElement51::neg` on `X` (bytes
   `0..40`) and `T` (bytes `120..160`) while copying `Y` (`40..80`) and `Z` (`80..120`) verbatim,
   and proves (`dalekEdNegBytes_bounded`, `dalekEdNegBytes_edExtOfBytes`, `dalekEdNegVec_sound`)
   that for any 160-byte `EdwardsPoint` with `X, T` limbs `< 2 ^ 54` and `Y, Z` limbs `< 2 ^ 52`,
   all 20 output limbs are reduced `< 2 ^ 52` and the resulting point in
   `VerifiedLibraries.Common.EdExtPoint` equals `edExtNeg (edExtOfBytes bs)`
   (`(-X mod p25519, Y mod p25519, Z mod p25519, -T mod p25519)`).
2. **Exact machine-code consumer bridges (`0` B real stack):**
   - Minimal unstacked `edwardsPointNegUnstackedSpec byVal` (`0` B stack),
   - Exact `CliExt.pureByteFunctionSpec dalekEdNegVec byVal` (`CliExternsFixed.lean:506`, for both
     `byVal = false` and `byVal = true`, plus `keepsFs`, `withVmPreserved`, `withFsPred`,
     `.inImage`, and `ProcessFieldsPreserved`),
   - Exact `cryptoLeafStubSpec` mirror (`cryptoLeafStubSpecWithStack` at any `hookStack`,
     specialized to `pqxdhHookStack = 4096` and `extHookStack = 16384`; `rfl`/defeq-equal by body
     to `E2E.Pqxdh.Shared.cryptoLeafStubSpec (fun bs => E2E.vecU8 (dalekEdNegVec (E2E.u8Vec 160 bs))) 160 160`
     in `IsCanonical.lean:182`, `SessionStateCallees.lean:1821`, and `CliHookSatPlaced.lean:983`),
   - Direct Curve25519 `EdExtPoint` Hoare contract (`edwardsPointNegEdExtSpec`).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.Crypto.EdwardsNeg

open Arm64 ProofLib
open ProofLib.StdStartup (hasInstrs)
open Arm64.Process (pureWordsProg pureWordsProg_hasWords)
open VerifiedLibraries.Common (p25519 fpNeg EdExtPoint)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession.CliExt (pureByteFunctionSpec inputAfter)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs withStack
  subroutine_ok_drop_keepsFs subroutine_ok_withStack
  subroutine_ok_withStack_keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop (withFsPred
  subroutine_ok_withFsPred_of_keepsFs)
open LibsignalBinary.Proofs.HookDischarge.Crypto.DalekEdNeg (packFe51Bytes fe51NegBytesAt
  dalekEdNegBytes packFe51Bytes_length fe51NegBytesAt_length dalekEdNegBytes_length dalekEdNegVec)
open LibsignalBinary.Proofs.HookDischarge.Crypto.MlkemPk (hasInstrs_of_hasWords
  subroutine_ok_keepsFs_withVmPreserved_of_pureWords)

/-! ## 1. Exact Machine Code (`57` Words = `228` Bytes, `0` B Stack) -/

/-- Exact `57`-word (`228`-byte, `0`-byte stack) machine code for
    `<curve25519_dalek::edwards::EdwardsPoint as core::ops::arith::Neg>::neg` from
    `libcurve25519_dalek` (`rustc 1.98.1` `aarch64-unknown-linux-musl`). -/
@[expose] def edwardsPointNegWords : List (BitVec 32) :=
  [ 0xa9402c0a#32, 0x928025e9#32, 0xf940100d#32, 0xb27ccbee#32,
    0xf2e00fe9#32, 0xa9413c0c#32, 0x52800262#32, 0xcb0d01cd#32,
    0xcb0a012a#32, 0xcb0b01cb#32, 0xd373fdb0#32, 0x9240c951#32,
    0x9240c972#32, 0xcb0c01cc#32, 0x8b4ace4a#32, 0xf9402412#32,
    0x9ba24610#32, 0xa9490c11#32, 0x9240c981#32, 0xf9002512#32,
    0x3cc28000#32, 0x8b4bcc2b#32, 0xa9471001#32, 0xcb0301c3#32,
    0x3cc38001#32, 0x3c828100#32, 0xd373fc72#32, 0xcb0f01cf#32,
    0x9240c9ad#32, 0xcb040129#32, 0x3c838101#32, 0x9240c9e5#32,
    0x9240c924#32, 0x9ba21252#32, 0x8b4cccac#32, 0xad428400#32,
    0xa9002910#32, 0x8b4fcdad#32, 0xa901310b#32, 0xcb1101cb#32,
    0xa9074901#32, 0xa9480001#32, 0xf900110d#32, 0x9240c96d#32,
    0xad028500#32, 0xcb0101ca#32, 0xcb0001cf#32, 0x9240c94e#32,
    0x9240c9ec#32, 0x8b4fcdad#32, 0x8b49cdc9#32, 0x8b4acd8a#32,
    0x9240c86c#32, 0xa9082909#32, 0x8b4bcd89#32, 0xa909250d#32,
    0xd65f03c0#32 ]

/-- Exact `57`-instruction (`228`-byte, `0`-byte stack) sequence decoded from
    `edwardsPointNegWords`. -/
@[expose] def edwardsPointNegInstrs : List Instr :=
  [ -- [ 0] +0x00: ldp x10, x11, [x0]
    .ldp .W64 false (.gpr 0x0a#5) (.gpr 0x0b#5) (.Offset .x0 0x0#64),
    -- [ 1] +0x04: movn x9, #0x12f
    .moveWide .W64 .MOVN (.gpr 0x09#5) 0x012f#16 0,
    -- [ 2] +0x08: ldr x13, [x0, #0x20]
    .ldr .W64 .X64 false (.gpr 0x0d#5) (.Offset .x0 0x20#64),
    -- [ 3] +0x0c: orr x14, xzr, #0x7ffffffffffff0
    .logicalImm .W64 .ORR (.gpr 0x0e#5) .xzr 0x007ffffffffffff0#64,
    -- [ 4] +0x10: movk x9, #0x7f, lsl #48
    .moveWide .W64 .MOVK (.gpr 0x09#5) 0x007f#16 48,
    -- [ 5] +0x14: ldp x12, x15, [x0, #0x10]
    .ldp .W64 false (.gpr 0x0c#5) (.gpr 0x0f#5) (.Offset .x0 0x10#64),
    -- [ 6] +0x18: mov w2, #0x13
    .moveWide .W32 .MOVZ (.gpr 0x02#5) 0x0013#16 0,
    -- [ 7] +0x1c: sub x13, x14, x13
    .addSubShift .W64 .SUB (.gpr 0x0d#5) (.gpr 0x0e#5) (.gpr 0x0d#5) .LSL 0,
    -- [ 8] +0x20: sub x10, x9, x10
    .addSubShift .W64 .SUB (.gpr 0x0a#5) (.gpr 0x09#5) (.gpr 0x0a#5) .LSL 0,
    -- [ 9] +0x24: sub x11, x14, x11
    .addSubShift .W64 .SUB (.gpr 0x0b#5) (.gpr 0x0e#5) (.gpr 0x0b#5) .LSL 0,
    -- [10] +0x28: lsr x16, x13, #51
    .bitfield .W64 .UBFM (.gpr 0x10#5) (.gpr 0x0d#5) 51 63,
    -- [11] +0x2c: and x17, x10, #0x7ffffffffffff
    .logicalImm .W64 .AND (.gpr 0x11#5) (.gpr 0x0a#5) 0x0007ffffffffffff#64,
    -- [12] +0x30: and x18, x11, #0x7ffffffffffff
    .logicalImm .W64 .AND (.gpr 0x12#5) (.gpr 0x0b#5) 0x0007ffffffffffff#64,
    -- [13] +0x34: sub x12, x14, x12
    .addSubShift .W64 .SUB (.gpr 0x0c#5) (.gpr 0x0e#5) (.gpr 0x0c#5) .LSL 0,
    -- [14] +0x38: add x10, x18, x10, lsr #51
    .addSubShift .W64 .ADD (.gpr 0x0a#5) (.gpr 0x12#5) (.gpr 0x0a#5) .LSR 51,
    -- [15] +0x3c: ldr x18, [x0, #0x48]
    .ldr .W64 .X64 false (.gpr 0x12#5) (.Offset .x0 0x48#64),
    -- [16] +0x40: umaddl x16, w16, w2, x17
    .dataProc3 .W64 .UMADDL (.gpr 0x10#5) (.gpr 0x10#5) (.gpr 0x02#5) (.gpr 0x11#5),
    -- [17] +0x44: ldp x17, x3, [x0, #0x90]
    .ldp .W64 false (.gpr 0x11#5) (.gpr 0x03#5) (.Offset .x0 0x90#64),
    -- [18] +0x48: and x1, x12, #0x7ffffffffffff
    .logicalImm .W64 .AND (.gpr 0x01#5) (.gpr 0x0c#5) 0x0007ffffffffffff#64,
    -- [19] +0x4c: str x18, [x8, #0x48]
    .str .X64 (.gpr 0x12#5) (.Offset .x8 0x48#64),
    -- [20] +0x50: ldur q0, [x0, #0x28]
    .ldrSimd .Q128 0x00#5 (.UnscaledOffset .x0 0x28#64),
    -- [21] +0x54: add x11, x1, x11, lsr #51
    .addSubShift .W64 .ADD (.gpr 0x0b#5) (.gpr 0x01#5) (.gpr 0x0b#5) .LSR 51,
    -- [22] +0x58: ldp x1, x4, [x0, #0x70]
    .ldp .W64 false (.gpr 0x01#5) (.gpr 0x04#5) (.Offset .x0 0x70#64),
    -- [23] +0x5c: sub x3, x14, x3
    .addSubShift .W64 .SUB (.gpr 0x03#5) (.gpr 0x0e#5) (.gpr 0x03#5) .LSL 0,
    -- [24] +0x60: ldur q1, [x0, #0x38]
    .ldrSimd .Q128 0x01#5 (.UnscaledOffset .x0 0x38#64),
    -- [25] +0x64: stur q0, [x8, #0x28]
    .strSimd .Q128 0x00#5 (.UnscaledOffset .x8 0x28#64),
    -- [26] +0x68: lsr x18, x3, #51
    .bitfield .W64 .UBFM (.gpr 0x12#5) (.gpr 0x03#5) 51 63,
    -- [27] +0x6c: sub x15, x14, x15
    .addSubShift .W64 .SUB (.gpr 0x0f#5) (.gpr 0x0e#5) (.gpr 0x0f#5) .LSL 0,
    -- [28] +0x70: and x13, x13, #0x7ffffffffffff
    .logicalImm .W64 .AND (.gpr 0x0d#5) (.gpr 0x0d#5) 0x0007ffffffffffff#64,
    -- [29] +0x74: sub x9, x9, x4
    .addSubShift .W64 .SUB (.gpr 0x09#5) (.gpr 0x09#5) (.gpr 0x04#5) .LSL 0,
    -- [30] +0x78: stur q1, [x8, #0x38]
    .strSimd .Q128 0x01#5 (.UnscaledOffset .x8 0x38#64),
    -- [31] +0x7c: and x5, x15, #0x7ffffffffffff
    .logicalImm .W64 .AND (.gpr 0x05#5) (.gpr 0x0f#5) 0x0007ffffffffffff#64,
    -- [32] +0x80: and x4, x9, #0x7ffffffffffff
    .logicalImm .W64 .AND (.gpr 0x04#5) (.gpr 0x09#5) 0x0007ffffffffffff#64,
    -- [33] +0x84: umaddl x18, w18, w2, x4
    .dataProc3 .W64 .UMADDL (.gpr 0x12#5) (.gpr 0x12#5) (.gpr 0x02#5) (.gpr 0x04#5),
    -- [34] +0x88: add x12, x5, x12, lsr #51
    .addSubShift .W64 .ADD (.gpr 0x0c#5) (.gpr 0x05#5) (.gpr 0x0c#5) .LSR 51,
    -- [35] +0x8c: ldp q0, q1, [x0, #0x50]
    .ldpSimd .Q128 0x00#5 0x01#5 (.Offset .x0 0x50#64),
    -- [36] +0x90: stp x16, x10, [x8]
    .stp .W64 (.gpr 0x10#5) (.gpr 0x0a#5) (.Offset .x8 0x0#64),
    -- [37] +0x94: add x13, x13, x15, lsr #51
    .addSubShift .W64 .ADD (.gpr 0x0d#5) (.gpr 0x0d#5) (.gpr 0x0f#5) .LSR 51,
    -- [38] +0x98: stp x11, x12, [x8, #0x10]
    .stp .W64 (.gpr 0x0b#5) (.gpr 0x0c#5) (.Offset .x8 0x10#64),
    -- [39] +0x9c: sub x11, x14, x17
    .addSubShift .W64 .SUB (.gpr 0x0b#5) (.gpr 0x0e#5) (.gpr 0x11#5) .LSL 0,
    -- [40] +0xa0: stp x1, x18, [x8, #0x70]
    .stp .W64 (.gpr 0x01#5) (.gpr 0x12#5) (.Offset .x8 0x70#64),
    -- [41] +0xa4: ldp x1, x0, [x0, #0x80]
    .ldp .W64 false (.gpr 0x01#5) .x0 (.Offset .x0 0x80#64),
    -- [42] +0xa8: str x13, [x8, #0x20]
    .str .X64 (.gpr 0x0d#5) (.Offset .x8 0x20#64),
    -- [43] +0xac: and x13, x11, #0x7ffffffffffff
    .logicalImm .W64 .AND (.gpr 0x0d#5) (.gpr 0x0b#5) 0x0007ffffffffffff#64,
    -- [44] +0xb0: stp q0, q1, [x8, #0x50]
    .stpSimd .Q128 0x00#5 0x01#5 (.Offset .x8 0x50#64),
    -- [45] +0xb4: sub x10, x14, x1
    .addSubShift .W64 .SUB (.gpr 0x0a#5) (.gpr 0x0e#5) (.gpr 0x01#5) .LSL 0,
    -- [46] +0xb8: sub x15, x14, x0
    .addSubShift .W64 .SUB (.gpr 0x0f#5) (.gpr 0x0e#5) .x0 .LSL 0,
    -- [47] +0xbc: and x14, x10, #0x7ffffffffffff
    .logicalImm .W64 .AND (.gpr 0x0e#5) (.gpr 0x0a#5) 0x0007ffffffffffff#64,
    -- [48] +0xc0: and x12, x15, #0x7ffffffffffff
    .logicalImm .W64 .AND (.gpr 0x0c#5) (.gpr 0x0f#5) 0x0007ffffffffffff#64,
    -- [49] +0xc4: add x13, x13, x15, lsr #51
    .addSubShift .W64 .ADD (.gpr 0x0d#5) (.gpr 0x0d#5) (.gpr 0x0f#5) .LSR 51,
    -- [50] +0xc8: add x9, x14, x9, lsr #51
    .addSubShift .W64 .ADD (.gpr 0x09#5) (.gpr 0x0e#5) (.gpr 0x09#5) .LSR 51,
    -- [51] +0xcc: add x10, x12, x10, lsr #51
    .addSubShift .W64 .ADD (.gpr 0x0a#5) (.gpr 0x0c#5) (.gpr 0x0a#5) .LSR 51,
    -- [52] +0xd0: and x12, x3, #0x7ffffffffffff
    .logicalImm .W64 .AND (.gpr 0x0c#5) (.gpr 0x03#5) 0x0007ffffffffffff#64,
    -- [53] +0xd4: stp x9, x10, [x8, #0x80]
    .stp .W64 (.gpr 0x09#5) (.gpr 0x0a#5) (.Offset .x8 0x80#64),
    -- [54] +0xd8: add x9, x12, x11, lsr #51
    .addSubShift .W64 .ADD (.gpr 0x09#5) (.gpr 0x0c#5) (.gpr 0x0b#5) .LSR 51,
    -- [55] +0xdc: stp x13, x9, [x8, #0x90]
    .stp .W64 (.gpr 0x0d#5) (.gpr 0x09#5) (.Offset .x8 0x90#64),
    -- [56] +0xe0: ret
    .ret .lr ]

/-! ## 2. Pure 5×51-Bit Negation Model & Curve25519 Soundness -/

/-- Radix-$2^{51}$ integer value $\sum_{i=0}^4 \ell_i \cdot 2^{51 i}$ of five 64-bit limbs. -/
@[expose] def fe51Val (l0 l1 l2 l3 l4 : BitVec 64) : Nat :=
  l0.toNat + 2 ^ 51 * l1.toNat + 2 ^ 102 * l2.toNat + 2 ^ 153 * l3.toNat + 2 ^ 204 * l4.toNat

/-- All 5 limbs of a `FieldElement51` at byte offset `off` in `bs` are `< bound`. -/
@[expose] def fe51LimbsBoundedAt (bs : List (BitVec 8)) (off bound : Nat) : Prop :=
  (ByteSlice.readLE bs off 8).toNat < bound ∧
  (ByteSlice.readLE bs (off + 8) 8).toNat < bound ∧
  (ByteSlice.readLE bs (off + 16) 8).toNat < bound ∧
  (ByteSlice.readLE bs (off + 24) 8).toNat < bound ∧
  (ByteSlice.readLE bs (off + 32) 8).toNat < bound

/-- Radix-$2^{51}$ integer value of the `FieldElement51` at byte offset `off` in `bs`. -/
@[expose] def fe51ValAt (bs : List (BitVec 8)) (off : Nat) : Nat :=
  fe51Val
    (ByteSlice.readLE bs off 8)
    (ByteSlice.readLE bs (off + 8) 8)
    (ByteSlice.readLE bs (off + 16) 8)
    (ByteSlice.readLE bs (off + 24) 8)
    (ByteSlice.readLE bs (off + 32) 8)

/-- A 160-byte `EdwardsPoint` buffer has 4 limb-bounded `FieldElement51` coordinates `(X, Y, Z, T)`
    at offsets `0, 40, 80, 120`. -/
@[expose] def fe51Point4Bounded (bs : List (BitVec 8)) (bound : Nat) : Prop :=
  bs.length = 160 ∧
  fe51LimbsBoundedAt bs 0 bound ∧
  fe51LimbsBoundedAt bs 40 bound ∧
  fe51LimbsBoundedAt bs 80 bound ∧
  fe51LimbsBoundedAt bs 120 bound

/-- Extract the 4 field coordinates `(X, Y, Z, T) mod p25519` of a 160-byte `EdwardsPoint` buffer. -/
@[expose] def edExtOfBytes (bs : List (BitVec 8)) : EdExtPoint :=
  ⟨fe51ValAt bs 0 % p25519,
   fe51ValAt bs 40 % p25519,
   fe51ValAt bs 80 % p25519,
   fe51ValAt bs 120 % p25519⟩

/-- Extended twisted Edwards point negation `-(X, Y, Z, T) = (-X mod p, Y mod p, Z mod p, -T mod p)`. -/
@[expose] def edExtNeg (P : EdExtPoint) : EdExtPoint :=
  ⟨fpNeg P.X, P.Y % p25519, P.Z % p25519, fpNeg P.T⟩

private theorem readLE_append_left (xs ys : List (BitVec 8)) :
    ∀ (n : Nat), n ≤ xs.length → ByteSlice.readLE (xs ++ ys) 0 n = ByteSlice.readLE xs 0 n
  | 0, _ => rfl
  | n + 1, hn => by
    have hn' : n < xs.length := by omega
    simp only [ByteSlice.readLE, readLE_append_left xs ys n (by omega), Nat.zero_add,
      List.getD_eq_getElem?_getD, List.getElem?_append_left hn']

private theorem readLE_append_right (xs ys : List (BitVec 8)) (off : Nat) :
    ∀ (n : Nat), ByteSlice.readLE (xs ++ ys) (xs.length + off) n = ByteSlice.readLE ys off n
  | 0 => rfl
  | n + 1 => by
    simp only [ByteSlice.readLE, readLE_append_right xs ys off n, List.getD_eq_getElem?_getD]
    rw [show xs.length + off + n = xs.length + (off + n) by omega,
        List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

private theorem readLE_append_left_off (xs ys : List (BitVec 8)) (off n : Nat)
    (h : off + n ≤ xs.length) :
    ByteSlice.readLE (xs ++ ys) off n = ByteSlice.readLE xs off n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have hk : off + k < xs.length := by omega
    simp only [ByteSlice.readLE, ih (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_append_left hk]

private theorem readLE_append_right8 (w : BitVec 64) (ys : List (BitVec 8)) (off off' : Nat)
    (h : 8 + off = off') :
    ByteSlice.readLE (ByteSlice.unpackLE 8 w ++ ys) off' 8 = ByteSlice.readLE ys off 8 := by
  subst h
  simpa using readLE_append_right (ByteSlice.unpackLE 8 w) ys off 8

@[local simp] private theorem readLE_packFe51Bytes_0 (w0 w1 w2 w3 w4 : BitVec 64) :
    ByteSlice.readLE (packFe51Bytes w0 w1 w2 w3 w4) 0 8 = w0 := by
  unfold packFe51Bytes
  simp only [List.append_assoc]
  rw [readLE_append_left (ByteSlice.unpackLE 8 w0) _ 8 (by simp), ByteSlice.readLE_unpackLE_64 8 w0]

@[local simp] private theorem readLE_packFe51Bytes_8 (w0 w1 w2 w3 w4 : BitVec 64) :
    ByteSlice.readLE (packFe51Bytes w0 w1 w2 w3 w4) 8 8 = w1 := by
  unfold packFe51Bytes
  simp only [List.append_assoc]
  rw [readLE_append_right8 w0 _ 0 8 rfl,
      readLE_append_left (ByteSlice.unpackLE 8 w1) _ 8 (by simp), ByteSlice.readLE_unpackLE_64 8 w1]

@[local simp] private theorem readLE_packFe51Bytes_16 (w0 w1 w2 w3 w4 : BitVec 64) :
    ByteSlice.readLE (packFe51Bytes w0 w1 w2 w3 w4) 16 8 = w2 := by
  unfold packFe51Bytes
  simp only [List.append_assoc]
  rw [readLE_append_right8 w0 _ 8 16 rfl, readLE_append_right8 w1 _ 0 8 rfl,
      readLE_append_left (ByteSlice.unpackLE 8 w2) _ 8 (by simp), ByteSlice.readLE_unpackLE_64 8 w2]

@[local simp] private theorem readLE_packFe51Bytes_24 (w0 w1 w2 w3 w4 : BitVec 64) :
    ByteSlice.readLE (packFe51Bytes w0 w1 w2 w3 w4) 24 8 = w3 := by
  unfold packFe51Bytes
  simp only [List.append_assoc]
  rw [readLE_append_right8 w0 _ 16 24 rfl, readLE_append_right8 w1 _ 8 16 rfl,
      readLE_append_right8 w2 _ 0 8 rfl,
      readLE_append_left (ByteSlice.unpackLE 8 w3) _ 8 (by simp), ByteSlice.readLE_unpackLE_64 8 w3]

@[local simp] private theorem readLE_packFe51Bytes_32 (w0 w1 w2 w3 w4 : BitVec 64) :
    ByteSlice.readLE (packFe51Bytes w0 w1 w2 w3 w4) 32 8 = w4 := by
  unfold packFe51Bytes
  simp only [List.append_assoc]
  rw [readLE_append_right8 w0 _ 24 32 rfl, readLE_append_right8 w1 _ 16 24 rfl,
      readLE_append_right8 w2 _ 8 16 rfl, readLE_append_right8 w3 _ 0 8 rfl,
      ByteSlice.readLE_unpackLE_64 8 w4]

private theorem readLE_dalekEdNegBytes_q0 {bs : List (BitVec 8)} {k : Nat} (hk : k + 8 ≤ 40) :
    ByteSlice.readLE (dalekEdNegBytes bs) k 8 = ByteSlice.readLE (fe51NegBytesAt bs 0) k 8 := by
  unfold dalekEdNegBytes
  simp only [List.append_assoc]
  exact readLE_append_left_off (fe51NegBytesAt bs 0) _ k 8 (by simpa using hk)

private theorem readLE_dalekEdNegBytes_q1 {bs : List (BitVec 8)} {k : Nat} (hk : k + 8 ≤ 40) :
    ByteSlice.readLE (dalekEdNegBytes bs) (40 + k) 8 =
      ByteSlice.readLE
        (packFe51Bytes
          (ByteSlice.readLE bs 40 8) (ByteSlice.readLE bs 48 8)
          (ByteSlice.readLE bs 56 8) (ByteSlice.readLE bs 64 8)
          (ByteSlice.readLE bs 72 8)) k 8 := by
  unfold dalekEdNegBytes
  simp only [List.append_assoc]
  rw [show 40 + k = (fe51NegBytesAt bs 0).length + k by rw [fe51NegBytesAt_length],
      readLE_append_right (fe51NegBytesAt bs 0) _ k 8]
  exact readLE_append_left_off _ _ k 8 (by simpa using hk)

private theorem readLE_dalekEdNegBytes_q2 {bs : List (BitVec 8)} {k : Nat} (hk : k + 8 ≤ 40) :
    ByteSlice.readLE (dalekEdNegBytes bs) (80 + k) 8 =
      ByteSlice.readLE
        (packFe51Bytes
          (ByteSlice.readLE bs 80 8) (ByteSlice.readLE bs 88 8)
          (ByteSlice.readLE bs 96 8) (ByteSlice.readLE bs 104 8)
          (ByteSlice.readLE bs 112 8)) k 8 := by
  unfold dalekEdNegBytes
  simp only [List.append_assoc]
  rw [show 80 + k = (fe51NegBytesAt bs 0).length + (40 + k) by rw [fe51NegBytesAt_length]; omega,
      readLE_append_right (fe51NegBytesAt bs 0) _ (40 + k) 8,
      show 40 + k =
        (packFe51Bytes (ByteSlice.readLE bs 40 8) (ByteSlice.readLE bs 48 8)
          (ByteSlice.readLE bs 56 8) (ByteSlice.readLE bs 64 8)
          (ByteSlice.readLE bs 72 8)).length + k by rw [packFe51Bytes_length],
      readLE_append_right _ _ k 8]
  exact readLE_append_left_off _ _ k 8 (by simpa using hk)

private theorem readLE_dalekEdNegBytes_q3 {bs : List (BitVec 8)} {k : Nat} (_hk : k + 8 ≤ 40) :
    ByteSlice.readLE (dalekEdNegBytes bs) (120 + k) 8 =
      ByteSlice.readLE (fe51NegBytesAt bs 120) k 8 := by
  unfold dalekEdNegBytes
  simp only [List.append_assoc]
  rw [show 120 + k = (fe51NegBytesAt bs 0).length + (80 + k) by rw [fe51NegBytesAt_length]; omega,
      readLE_append_right (fe51NegBytesAt bs 0) _ (80 + k) 8,
      show 80 + k =
        (packFe51Bytes (ByteSlice.readLE bs 40 8) (ByteSlice.readLE bs 48 8)
          (ByteSlice.readLE bs 56 8) (ByteSlice.readLE bs 64 8)
          (ByteSlice.readLE bs 72 8)).length + (40 + k) by rw [packFe51Bytes_length]; omega,
      readLE_append_right _ _ (40 + k) 8,
      show 40 + k =
        (packFe51Bytes (ByteSlice.readLE bs 80 8) (ByteSlice.readLE bs 88 8)
          (ByteSlice.readLE bs 96 8) (ByteSlice.readLE bs 104 8)
          (ByteSlice.readLE bs 112 8)).length + k by rw [packFe51Bytes_length],
      readLE_append_right _ _ k 8]

private theorem mask51_toNat (d : BitVec 64) :
    (d &&& 2251799813685247#64).toNat = d.toNat % 2 ^ 51 := by
  rw [BitVec.toNat_and, show (2251799813685247#64).toNat = 2 ^ 51 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

private theorem lsr51_toNat (d : BitVec 64) :
    (d >>> 51).toNat = d.toNat / 2 ^ 51 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem zext_trunc32_lsr51 (d : BitVec 64) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (d >>> 51)) = d >>> 51 := by
  apply BitVec.eq_of_toNat_eq
  have hd : d.toNat < 2 ^ 64 := d.isLt
  simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth, lsr51_toNat]
  omega

private theorem mul19_lsr51_toNat (d0 d4 : BitVec 64) :
    ((d0 &&& 2251799813685247#64) + (d4 >>> 51) * 19#64).toNat =
      d0.toNat % 2 ^ 51 + (d4.toNat / 2 ^ 51) * 19 := by
  have hd4 : d4.toNat < 2 ^ 64 := d4.isLt
  rw [BitVec.toNat_add, BitVec.toNat_mul, mask51_toNat, lsr51_toNat,
      show (19#64).toNat = 19 from rfl]
  omega

private theorem add_mask51_lsr51_toNat (di dprev : BitVec 64) :
    ((di &&& 2251799813685247#64) + (dprev >>> 51)).toNat =
      di.toNat % 2 ^ 51 + dprev.toNat / 2 ^ 51 := by
  have hprev : dprev.toNat < 2 ^ 64 := dprev.isLt
  rw [BitVec.toNat_add, mask51_toNat, lsr51_toNat]
  omega

private theorem fe51Reduce_bounded (d0 d1 d2 d3 d4 : BitVec 64) :
    ((d0 &&& 2251799813685247#64) + (d4 >>> 51) * 19#64).toNat < 2 ^ 52 ∧
    ((d1 &&& 2251799813685247#64) + (d0 >>> 51)).toNat < 2 ^ 52 ∧
    ((d2 &&& 2251799813685247#64) + (d1 >>> 51)).toNat < 2 ^ 52 ∧
    ((d3 &&& 2251799813685247#64) + (d2 >>> 51)).toNat < 2 ^ 52 ∧
    ((d4 &&& 2251799813685247#64) + (d3 >>> 51)).toNat < 2 ^ 52 := by
  have h0 := d0.isLt; have h1 := d1.isLt; have h2 := d2.isLt; have h3 := d3.isLt; have h4 := d4.isLt
  rw [mul19_lsr51_toNat, add_mask51_lsr51_toNat, add_mask51_lsr51_toNat,
      add_mask51_lsr51_toNat, add_mask51_lsr51_toNat]
  omega

private theorem fe51Reduce_val_mod (d0 d1 d2 d3 d4 : BitVec 64) :
    fe51Val
      ((d0 &&& 2251799813685247#64) + (d4 >>> 51) * 19#64)
      ((d1 &&& 2251799813685247#64) + (d0 >>> 51))
      ((d2 &&& 2251799813685247#64) + (d1 >>> 51))
      ((d3 &&& 2251799813685247#64) + (d2 >>> 51))
      ((d4 &&& 2251799813685247#64) + (d3 >>> 51)) % p25519 =
    fe51Val d0 d1 d2 d3 d4 % p25519 := by
  have hid :
      fe51Val
        ((d0 &&& 2251799813685247#64) + (d4 >>> 51) * 19#64)
        ((d1 &&& 2251799813685247#64) + (d0 >>> 51))
        ((d2 &&& 2251799813685247#64) + (d1 >>> 51))
        ((d3 &&& 2251799813685247#64) + (d2 >>> 51))
        ((d4 &&& 2251799813685247#64) + (d3 >>> 51)) +
      p25519 * (d4.toNat / 2 ^ 51) =
      fe51Val d0 d1 d2 d3 d4 := by
    unfold fe51Val p25519
    rw [mul19_lsr51_toNat, add_mask51_lsr51_toNat, add_mask51_lsr51_toNat,
        add_mask51_lsr51_toNat, add_mask51_lsr51_toNat]
    omega
  rw [← hid, Nat.add_mul_mod_self_left]

private theorem fe51Neg_val_mod (l0 l1 l2 l3 l4 : BitVec 64)
    (h : l0.toNat < 2 ^ 54 ∧ l1.toNat < 2 ^ 54 ∧ l2.toNat < 2 ^ 54 ∧
         l3.toNat < 2 ^ 54 ∧ l4.toNat < 2 ^ 54) :
    fe51Val
      (36028797018963664#64 - l0)
      (36028797018963952#64 - l1)
      (36028797018963952#64 - l2)
      (36028797018963952#64 - l3)
      (36028797018963952#64 - l4) % p25519 =
    fpNeg (fe51Val l0 l1 l2 l3 l4 % p25519) := by
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  have hs0 : (36028797018963664#64 - l0).toNat = 36028797018963664 - l0.toNat := by
    rw [BitVec.toNat_sub_of_le (by change l0.toNat ≤ 36028797018963664; omega)]; rfl
  have hs1 : (36028797018963952#64 - l1).toNat = 36028797018963952 - l1.toNat := by
    rw [BitVec.toNat_sub_of_le (by change l1.toNat ≤ 36028797018963952; omega)]; rfl
  have hs2 : (36028797018963952#64 - l2).toNat = 36028797018963952 - l2.toNat := by
    rw [BitVec.toNat_sub_of_le (by change l2.toNat ≤ 36028797018963952; omega)]; rfl
  have hs3 : (36028797018963952#64 - l3).toNat = 36028797018963952 - l3.toNat := by
    rw [BitVec.toNat_sub_of_le (by change l3.toNat ≤ 36028797018963952; omega)]; rfl
  have hs4 : (36028797018963952#64 - l4).toNat = 36028797018963952 - l4.toNat := by
    rw [BitVec.toNat_sub_of_le (by change l4.toNat ≤ 36028797018963952; omega)]; rfl
  have hval :
      fe51Val
        (36028797018963664#64 - l0)
        (36028797018963952#64 - l1)
        (36028797018963952#64 - l2)
        (36028797018963952#64 - l3)
        (36028797018963952#64 - l4) =
      16 * p25519 - fe51Val l0 l1 l2 l3 l4 := by
    unfold fe51Val p25519
    rw [hs0, hs1, hs2, hs3, hs4]
    omega
  rw [hval]
  unfold VerifiedLibraries.Common.fpNeg
  have hlt : fe51Val l0 l1 l2 l3 l4 < 16 * p25519 := by
    unfold fe51Val p25519; omega
  have hdiv : fe51Val l0 l1 l2 l3 l4 =
      p25519 * (fe51Val l0 l1 l2 l3 l4 / p25519) + fe51Val l0 l1 l2 l3 l4 % p25519 :=
    (Nat.div_add_mod _ _).symm
  have hq : fe51Val l0 l1 l2 l3 l4 / p25519 ≤ 15 := by
    unfold p25519 at hlt ⊢; omega
  have hmod_lt : fe51Val l0 l1 l2 l3 l4 % p25519 < p25519 :=
    Nat.mod_lt _ (by unfold p25519; omega)
  have hmod2 : (fe51Val l0 l1 l2 l3 l4 % p25519) % p25519 = fe51Val l0 l1 l2 l3 l4 % p25519 :=
    Nat.mod_eq_of_lt hmod_lt
  rw [hmod2]
  have hrew : 16 * p25519 - fe51Val l0 l1 l2 l3 l4 =
      (p25519 - fe51Val l0 l1 l2 l3 l4 % p25519) +
        p25519 * (15 - fe51Val l0 l1 l2 l3 l4 / p25519) := by
    unfold p25519 at hdiv hq hmod_lt ⊢
    omega
  rw [hrew, Nat.add_mul_mod_self_left]

/-- Output limb bound (`< 2 ^ 52`) for `dalekEdNegBytes bs` whenever `Y` and `Z` limbs are `< 2 ^ 52`
    (`X` and `T` outputs are `< 2 ^ 52` unconditionally). -/
theorem dalekEdNegBytes_bounded (bs : List (BitVec 8))
    (hY : fe51LimbsBoundedAt bs 40 (2 ^ 52))
    (hZ : fe51LimbsBoundedAt bs 80 (2 ^ 52)) :
    fe51Point4Bounded (dalekEdNegBytes bs) (2 ^ 52) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · dsimp only [fe51LimbsBoundedAt]
    rw [readLE_dalekEdNegBytes_q0 (k := 0) (by decide),
        readLE_dalekEdNegBytes_q0 (k := 8) (by decide),
        readLE_dalekEdNegBytes_q0 (k := 16) (by decide),
        readLE_dalekEdNegBytes_q0 (k := 24) (by decide),
        readLE_dalekEdNegBytes_q0 (k := 32) (by decide)]
    unfold fe51NegBytesAt
    simp only [readLE_packFe51Bytes_0, readLE_packFe51Bytes_8, readLE_packFe51Bytes_16,
      readLE_packFe51Bytes_24, readLE_packFe51Bytes_32]
    exact fe51Reduce_bounded _ _ _ _ _
  · dsimp only [fe51LimbsBoundedAt] at hY ⊢
    rw [readLE_dalekEdNegBytes_q1 (k := 0) (by decide),
        show 40 + 8 = 40 + 8 from rfl, readLE_dalekEdNegBytes_q1 (k := 8) (by decide),
        show 40 + 16 = 40 + 16 from rfl, readLE_dalekEdNegBytes_q1 (k := 16) (by decide),
        show 40 + 24 = 40 + 24 from rfl, readLE_dalekEdNegBytes_q1 (k := 24) (by decide),
        show 40 + 32 = 40 + 32 from rfl, readLE_dalekEdNegBytes_q1 (k := 32) (by decide)]
    simp only [readLE_packFe51Bytes_0, readLE_packFe51Bytes_8, readLE_packFe51Bytes_16,
      readLE_packFe51Bytes_24, readLE_packFe51Bytes_32]
    exact hY
  · dsimp only [fe51LimbsBoundedAt] at hZ ⊢
    rw [readLE_dalekEdNegBytes_q2 (k := 0) (by decide),
        readLE_dalekEdNegBytes_q2 (k := 8) (by decide),
        readLE_dalekEdNegBytes_q2 (k := 16) (by decide),
        readLE_dalekEdNegBytes_q2 (k := 24) (by decide),
        readLE_dalekEdNegBytes_q2 (k := 32) (by decide)]
    simp only [readLE_packFe51Bytes_0, readLE_packFe51Bytes_8, readLE_packFe51Bytes_16,
      readLE_packFe51Bytes_24, readLE_packFe51Bytes_32]
    exact hZ
  · dsimp only [fe51LimbsBoundedAt]
    rw [readLE_dalekEdNegBytes_q3 (k := 0) (by decide),
        readLE_dalekEdNegBytes_q3 (k := 8) (by decide),
        readLE_dalekEdNegBytes_q3 (k := 16) (by decide),
        readLE_dalekEdNegBytes_q3 (k := 24) (by decide),
        readLE_dalekEdNegBytes_q3 (k := 32) (by decide)]
    unfold fe51NegBytesAt
    simp only [readLE_packFe51Bytes_0, readLE_packFe51Bytes_8, readLE_packFe51Bytes_16,
      readLE_packFe51Bytes_24, readLE_packFe51Bytes_32]
    exact fe51Reduce_bounded _ _ _ _ _

/-- Algebraic Curve25519 soundness: `dalekEdNegBytes bs` represents `edExtNeg (edExtOfBytes bs)` in
    `VerifiedLibraries.Common.EdExtPoint` whenever `X` and `T` limbs are `< 2 ^ 54`. -/
theorem dalekEdNegBytes_edExtOfBytes (bs : List (BitVec 8))
    (hX : fe51LimbsBoundedAt bs 0 (2 ^ 54))
    (hT : fe51LimbsBoundedAt bs 120 (2 ^ 54)) :
    edExtOfBytes (dalekEdNegBytes bs) = edExtNeg (edExtOfBytes bs) := by
  dsimp only [edExtOfBytes, edExtNeg, fe51ValAt]
  rw [readLE_dalekEdNegBytes_q0 (k := 0) (by decide),
      readLE_dalekEdNegBytes_q0 (k := 8) (by decide),
      readLE_dalekEdNegBytes_q0 (k := 16) (by decide),
      readLE_dalekEdNegBytes_q0 (k := 24) (by decide),
      readLE_dalekEdNegBytes_q0 (k := 32) (by decide),
      readLE_dalekEdNegBytes_q1 (k := 0) (by decide),
      readLE_dalekEdNegBytes_q1 (k := 8) (by decide),
      readLE_dalekEdNegBytes_q1 (k := 16) (by decide),
      readLE_dalekEdNegBytes_q1 (k := 24) (by decide),
      readLE_dalekEdNegBytes_q1 (k := 32) (by decide),
      readLE_dalekEdNegBytes_q2 (k := 0) (by decide),
      readLE_dalekEdNegBytes_q2 (k := 8) (by decide),
      readLE_dalekEdNegBytes_q2 (k := 16) (by decide),
      readLE_dalekEdNegBytes_q2 (k := 24) (by decide),
      readLE_dalekEdNegBytes_q2 (k := 32) (by decide),
      readLE_dalekEdNegBytes_q3 (k := 0) (by decide),
      readLE_dalekEdNegBytes_q3 (k := 8) (by decide),
      readLE_dalekEdNegBytes_q3 (k := 16) (by decide),
      readLE_dalekEdNegBytes_q3 (k := 24) (by decide),
      readLE_dalekEdNegBytes_q3 (k := 32) (by decide)]
  unfold fe51NegBytesAt
  simp only [readLE_packFe51Bytes_0, readLE_packFe51Bytes_8, readLE_packFe51Bytes_16,
    readLE_packFe51Bytes_24, readLE_packFe51Bytes_32, Nat.zero_add]
  rw [fe51Reduce_val_mod, fe51Neg_val_mod _ _ _ _ _ hX,
      fe51Reduce_val_mod, fe51Neg_val_mod _ _ _ _ _ hT]
  congr 1 <;> exact (Nat.mod_mod _ _).symm

/-- Combined Curve25519 soundness for `dalekEdNegVec`. -/
theorem dalekEdNegVec_sound (v : List.Vector (BitVec 8) 160)
    (hX : fe51LimbsBoundedAt v.toList 0 (2 ^ 54))
    (hY : fe51LimbsBoundedAt v.toList 40 (2 ^ 52))
    (hZ : fe51LimbsBoundedAt v.toList 80 (2 ^ 52))
    (hT : fe51LimbsBoundedAt v.toList 120 (2 ^ 54)) :
    fe51Point4Bounded (dalekEdNegVec v).toList (2 ^ 52) ∧
      edExtOfBytes (dalekEdNegVec v).toList = edExtNeg (edExtOfBytes v.toList) :=
  ⟨dalekEdNegBytes_bounded v.toList hY hZ, dalekEdNegBytes_edExtOfBytes v.toList hX hT⟩

/-! ## 3. Byte-Exact Stepping Proof (`0` B Stack) -/

private class HasLenGe (bs : List (BitVec 8)) (n : outParam Nat) : Prop where
  le_length : n ≤ bs.length

private theorem write64_length_eq (bs : List (BitVec 8)) (off : Nat) (v : BitVec 64) :
    (ByteSlice.write64 bs off v).length = min off bs.length + 8 + (bs.length - (off + 8)) := by
  simp only [ByteSlice.write64, ByteSlice.writeLE, ByteSlice.write, List.length_append,
    List.length_take, List.length_drop, ByteSlice.unpackLE_length]

private instance instHasLenGeWrite64 (bs : List (BitVec 8)) (off : Nat) (v : BitVec 64) (n : Nat)
    [h : HasLenGe bs n] : HasLenGe (ByteSlice.write64 bs off v) n where
  le_length := by
    have hle := h.le_length
    rw [write64_length_eq]
    omega

private theorem readLE_write64_of_disjoint (bs : List (BitVec 8)) (off1 off2 : Nat) (v : BitVec 64)
    (hdisj : off1 + 8 ≤ off2 ∨ off2 + 8 ≤ off1) (hlen : off1 ≤ bs.length) :
    ByteSlice.readLE (ByteSlice.write64 bs off1 v) off2 8 = ByteSlice.readLE bs off2 8 := by
  apply ByteSlice.readLE_congr
  intro i hi
  rw [ByteSlice.getD_write64 bs off1 v (off2 + i) 0#8 hlen]
  have : ¬(off1 ≤ off2 + i ∧ off2 + i < off1 + 8) := by omega
  simp [this]

private theorem readLE_write64_self' (bs : List (BitVec 8)) (off n : Nat) (v : BitVec 64)
    [h : HasLenGe bs n]
    (h1 : decide (off ≤ n) = true) :
    ByteSlice.readLE (ByteSlice.write64 bs off v) off 8 = v :=
  ByteSlice.readLE_write64_self bs off v (Nat.le_trans (of_decide_eq_true h1) h.le_length)

private theorem readLE_write64_ne (bs : List (BitVec 8)) (off1 off2 n : Nat) (v : BitVec 64)
    [h : HasLenGe bs n]
    (h1 : decide (off1 ≤ n ∧ (off1 + 8 ≤ off2 ∨ off2 + 8 ≤ off1)) = true) :
    ByteSlice.readLE (ByteSlice.write64 bs off1 v) off2 8 = ByteSlice.readLE bs off2 8 := by
  have hdec := of_decide_eq_true h1
  exact readLE_write64_of_disjoint bs off1 off2 v hdec.2 (Nat.le_trans hdec.1 h.le_length)

/-- Two 160-byte buffers with identical 8-byte little-endian words at offsets `0, 8, ..., 152` are
    byte-for-byte equal. -/
private theorem eq_of_length_160_words_eq {xs ys : List (BitVec 8)}
    (hx : xs.length = 160) (hy : ys.length = 160)
    (h0 : ByteSlice.readLE xs 0 8 = ByteSlice.readLE ys 0 8)
    (h8 : ByteSlice.readLE xs 8 8 = ByteSlice.readLE ys 8 8)
    (h16 : ByteSlice.readLE xs 16 8 = ByteSlice.readLE ys 16 8)
    (h24 : ByteSlice.readLE xs 24 8 = ByteSlice.readLE ys 24 8)
    (h32 : ByteSlice.readLE xs 32 8 = ByteSlice.readLE ys 32 8)
    (h40 : ByteSlice.readLE xs 40 8 = ByteSlice.readLE ys 40 8)
    (h48 : ByteSlice.readLE xs 48 8 = ByteSlice.readLE ys 48 8)
    (h56 : ByteSlice.readLE xs 56 8 = ByteSlice.readLE ys 56 8)
    (h64 : ByteSlice.readLE xs 64 8 = ByteSlice.readLE ys 64 8)
    (h72 : ByteSlice.readLE xs 72 8 = ByteSlice.readLE ys 72 8)
    (h80 : ByteSlice.readLE xs 80 8 = ByteSlice.readLE ys 80 8)
    (h88 : ByteSlice.readLE xs 88 8 = ByteSlice.readLE ys 88 8)
    (h96 : ByteSlice.readLE xs 96 8 = ByteSlice.readLE ys 96 8)
    (h104 : ByteSlice.readLE xs 104 8 = ByteSlice.readLE ys 104 8)
    (h112 : ByteSlice.readLE xs 112 8 = ByteSlice.readLE ys 112 8)
    (h120 : ByteSlice.readLE xs 120 8 = ByteSlice.readLE ys 120 8)
    (h128 : ByteSlice.readLE xs 128 8 = ByteSlice.readLE ys 128 8)
    (h136 : ByteSlice.readLE xs 136 8 = ByteSlice.readLE ys 136 8)
    (h144 : ByteSlice.readLE xs 144 8 = ByteSlice.readLE ys 144 8)
    (h152 : ByteSlice.readLE xs 152 8 = ByteSlice.readLE ys 152 8) :
    xs = ys := by
  apply List.ext_getElem (hx.trans hy.symm)
  intro i hi1 hi2
  have hi : i < 160 := by omega
  have hbyte : ∀ off (hw : ByteSlice.readLE xs off 8 = ByteSlice.readLE ys off 8),
      off ≤ i → i < off + 8 → xs[i] = ys[i] := by
    intro off hw hlo hhi
    have hj : i - off < 8 := by omega
    have hsum : off + (i - off) = i := by omega
    have hex := congrArg (fun w => w.extractLsb' (8 * (i - off)) 8) hw
    rw [ByteSlice.extractLsb'_readLE xs off 8 (i - off) (by decide),
        ByteSlice.extractLsb'_readLE ys off 8 (i - off) (by decide)] at hex
    simp only [hj, ↓reduceIte, hsum, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2, Option.getD_some] at hex
    exact hex
  by_cases c1 : i < 8; · exact hbyte 0 h0 (by omega) c1
  by_cases c2 : i < 16; · exact hbyte 8 h8 (by omega) c2
  by_cases c3 : i < 24; · exact hbyte 16 h16 (by omega) c3
  by_cases c4 : i < 32; · exact hbyte 24 h24 (by omega) c4
  by_cases c5 : i < 40; · exact hbyte 32 h32 (by omega) c5
  by_cases c6 : i < 48; · exact hbyte 40 h40 (by omega) c6
  by_cases c7 : i < 56; · exact hbyte 48 h48 (by omega) c7
  by_cases c8 : i < 64; · exact hbyte 56 h56 (by omega) c8
  by_cases c9 : i < 72; · exact hbyte 64 h64 (by omega) c9
  by_cases c10 : i < 80; · exact hbyte 72 h72 (by omega) c10
  by_cases c11 : i < 88; · exact hbyte 80 h80 (by omega) c11
  by_cases c12 : i < 96; · exact hbyte 88 h88 (by omega) c12
  by_cases c13 : i < 104; · exact hbyte 96 h96 (by omega) c13
  by_cases c14 : i < 112; · exact hbyte 104 h104 (by omega) c14
  by_cases c15 : i < 120; · exact hbyte 112 h112 (by omega) c15
  by_cases c16 : i < 128; · exact hbyte 120 h120 (by omega) c16
  by_cases c17 : i < 136; · exact hbyte 128 h128 (by omega) c17
  by_cases c18 : i < 144; · exact hbyte 136 h136 (by omega) c18
  by_cases c19 : i < 152; · exact hbyte 144 h144 (by omega) c19
  exact hbyte 152 h152 (by omega) hi

private theorem fetch_at {P : Program} {base off : BitVec 64} {ls : List Instr} {inst : Instr}
    (i : Nat) (h : hasInstrs P base ls)
    (hi : ls[i]? = some inst := by rfl)
    (hoff : BitVec.ofNat 64 (4 * i) = off := by rfl) :
    P.fetch (base + off) = some inst := by
  have hlt : i < ls.length := (List.getElem?_eq_some_iff.mp hi).1
  have hf := h.fetch_off i off hlt hoff
  rw [List.getElem?_eq_getElem hlt] at hi
  cases hi
  exact hf

private theorem fetch_at0 {P : Program} {base : BitVec 64} {ls : List Instr} {inst : Instr}
    (h : hasInstrs P base ls) (hi : ls[0]? = some inst := by rfl) :
    P.fetch base = some inst := by
  simpa using fetch_at 0 h hi rfl

private def FsTracePreserved (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧ sf.trace = s0.trace

private theorem FsTracePreserved.rfl (s : State) : FsTracePreserved s s :=
  ⟨Eq.refl _, Eq.refl _⟩

@[local simp] private theorem FsTracePreserved_writeReg64 (s0 s : State) (r : Reg) (v : BitVec 64) :
    FsTracePreserved s0 (s.writeReg64 r v) ↔ FsTracePreserved s0 s := by
  cases s; cases r <;> rfl

@[local simp] private theorem FsTracePreserved_writeReg32 (s0 s : State) (r : Reg) (v : BitVec 32) :
    FsTracePreserved s0 (s.writeReg32 r v) ↔ FsTracePreserved s0 s := by
  cases s; cases r <;> rfl

@[local simp] private theorem FsTracePreserved_writeVReg128 (s0 s : State) (v : BitVec 5)
    (val : BitVec 128) :
    FsTracePreserved s0 (s.writeVReg128 v val) ↔ FsTracePreserved s0 s := by
  cases s; rfl

@[local simp] private theorem FsTracePreserved_advancePC (s0 s : State) :
    FsTracePreserved s0 s.advancePC ↔ FsTracePreserved s0 s := by
  cases s; rfl

@[local simp] private theorem FsTracePreserved_setPC (s0 s : State) (pc : BitVec 64) :
    FsTracePreserved s0 (s.setPC pc) ↔ FsTracePreserved s0 s := by
  cases s; rfl

@[local simp] private theorem FsTracePreserved_setMem (s0 s : State) (m : Memory) :
    FsTracePreserved s0 (s.setMem m) ↔ FsTracePreserved s0 s := by
  cases s; rfl

private theorem fs_eq_of_preserved {s0 sf : State} (h : FsTracePreserved s0 sf) :
    sf.fs = s0.fs := h.1

private theorem trace_eq_of_preserved {s0 sf : State} (h : FsTracePreserved s0 sf) :
    sf.trace = s0.trace := h.2

private theorem pureWordsProg_hasWords_edNeg (entry : BitVec 64) :
    (pureWordsProg entry edwardsPointNegWords).hasWords entry edwardsPointNegWords :=
  pureWordsProg_hasWords (by decide +kernel) (by
    change ((List.range edwardsPointNegWords.length).all fun i =>
      (pureWordsProg 0#64 edwardsPointNegWords).readWordOff (4 * i) ==
        edwardsPointNegWords[i]?) = true
    decide +kernel)

theorem pureWordsProg_noSvcMsr_edNeg (entry : BitVec 64) :
    (pureWordsProg entry edwardsPointNegWords).allInstrs
      (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true :=
  Program.allInstrs_of_code_eq (prog := pureWordsProg 0#64 edwardsPointNegWords) rfl
    (by prove_all_instrs)

theorem pureWordsProg_hasInstrs_edNeg (entry : BitVec 64) :
    hasInstrs (pureWordsProg entry edwardsPointNegWords) entry edwardsPointNegInstrs :=
  hasInstrs_of_hasWords (pureWordsProg_hasWords_edNeg entry)

/-- Minimal `0`-byte-stack contract for `<EdwardsPoint as Neg>::neg`, parameterized by `byVal` so
    `withStack (edwardsPointNegUnstackedSpec byVal) extHookStack` is definitionally (`rfl`)
    `CliExt.pureByteFunctionSpec dalekEdNegVec byVal`. -/
@[expose] def edwardsPointNegUnstackedSpec (byVal : Bool) :
    Spec (BitVec 64 × List.Vector (BitVec 8) 160 × BitVec 64) where
  pre := fun (inA, v, ret) s =>
    ⌜s.readReg64 .x0 = inA ∧ s.readReg64 .x8 = ret⌝ ∗ (inA ↦ₛ v.toList) ∗ memRegion ret 160
  post := fun (inA, v, ret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ inputAfter byVal inA v ∗ (ret ↦ₛ (dalekEdNegVec v).toList)

/-- `withStack (edwardsPointNegUnstackedSpec byVal) extHookStack` is definitionally (`rfl`)
    `CliExt.pureByteFunctionSpec dalekEdNegVec byVal` (`CliExternsFixed.lean:506`). -/
theorem withStack_edwardsPointNegUnstackedSpec_extHookStack (byVal : Bool) :
    withStack (edwardsPointNegUnstackedSpec byVal) extHookStack =
      pureByteFunctionSpec dalekEdNegVec byVal := rfl

private theorem inputAfter_false {n : Nat} (p : BitVec 64) (v : List.Vector (BitVec 8) n) :
    inputAfter false p v = (p ↦ₛ v.toList) := rfl

private theorem inputAfter_true {n : Nat} (p : BitVec 64) (v : List.Vector (BitVec 8) n) :
    inputAfter true p v = memRegion p n := rfl

set_option maxHeartbeats 800000 in
/-- Minimal `0`-byte-stack `keepsFs` proof for `edwardsPointNegInstrs` (`byVal = false`). -/
theorem edwardsPointNeg_unstacked_false_keepsFs_ok {P : Program} {addr : BitVec 64}
    (hcode : hasInstrs P addr edwardsPointNegInstrs) :
    subroutine_ok P addr (keepsFs (edwardsPointNegUnstackedSpec false)) := by
  apply subroutine_ok_of_sepWP_init
  intro ⟨inA, v, ret⟩ R s0 hpc hrun hpre _hsp
  dsimp only [keepsFs, edwardsPointNegUnstackedSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx8⟩, hpre⟩ := hpre
  rw [memRegion_eq_exists_bytes ret 160 (by decide), sepConj_comm (inA ↦ₛ v.toList),
      sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hpre
  obtain ⟨out_bs, hpre⟩ := hpre
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hout_len, hpre⟩ := hpre
  have hin_len : v.toList.length = 160 := List.Vector.toList_length v
  refine ⟨(ret ↦ₛ out_bs) ∗ (inA ↦ₛ v.toList), by rwa [← sepConj_assoc] at hpre, ?_⟩
  have hf0 := fetch_at0 hcode
  have hf1 := fetch_at 1 (off := 0x04#64) hcode
  have hf2 := fetch_at 2 (off := 0x08#64) hcode
  have hf3 := fetch_at 3 (off := 0x0c#64) hcode
  have hf4 := fetch_at 4 (off := 0x10#64) hcode
  have hf5 := fetch_at 5 (off := 0x14#64) hcode
  have hf6 := fetch_at 6 (off := 0x18#64) hcode
  have hf7 := fetch_at 7 (off := 0x1c#64) hcode
  have hf8 := fetch_at 8 (off := 0x20#64) hcode
  have hf9 := fetch_at 9 (off := 0x24#64) hcode
  have hf10 := fetch_at 10 (off := 0x28#64) hcode
  have hf11 := fetch_at 11 (off := 0x2c#64) hcode
  have hf12 := fetch_at 12 (off := 0x30#64) hcode
  have hf13 := fetch_at 13 (off := 0x34#64) hcode
  have hf14 := fetch_at 14 (off := 0x38#64) hcode
  have hf15 := fetch_at 15 (off := 0x3c#64) hcode
  have hf16 := fetch_at 16 (off := 0x40#64) hcode
  have hf17 := fetch_at 17 (off := 0x44#64) hcode
  have hf18 := fetch_at 18 (off := 0x48#64) hcode
  have hf19 := fetch_at 19 (off := 0x4c#64) hcode
  have hf20 := fetch_at 20 (off := 0x50#64) hcode
  have hf21 := fetch_at 21 (off := 0x54#64) hcode
  have hf22 := fetch_at 22 (off := 0x58#64) hcode
  have hf23 := fetch_at 23 (off := 0x5c#64) hcode
  have hf24 := fetch_at 24 (off := 0x60#64) hcode
  have hf25 := fetch_at 25 (off := 0x64#64) hcode
  have hf26 := fetch_at 26 (off := 0x68#64) hcode
  have hf27 := fetch_at 27 (off := 0x6c#64) hcode
  have hf28 := fetch_at 28 (off := 0x70#64) hcode
  have hf29 := fetch_at 29 (off := 0x74#64) hcode
  have hf30 := fetch_at 30 (off := 0x78#64) hcode
  have hf31 := fetch_at 31 (off := 0x7c#64) hcode
  have hf32 := fetch_at 32 (off := 0x80#64) hcode
  have hf33 := fetch_at 33 (off := 0x84#64) hcode
  have hf34 := fetch_at 34 (off := 0x88#64) hcode
  have hf35 := fetch_at 35 (off := 0x8c#64) hcode
  have hf36 := fetch_at 36 (off := 0x90#64) hcode
  have hf37 := fetch_at 37 (off := 0x94#64) hcode
  have hf38 := fetch_at 38 (off := 0x98#64) hcode
  have hf39 := fetch_at 39 (off := 0x9c#64) hcode
  have hf40 := fetch_at 40 (off := 0xa0#64) hcode
  have hf41 := fetch_at 41 (off := 0xa4#64) hcode
  have hf42 := fetch_at 42 (off := 0xa8#64) hcode
  have hf43 := fetch_at 43 (off := 0xac#64) hcode
  have hf44 := fetch_at 44 (off := 0xb0#64) hcode
  have hf45 := fetch_at 45 (off := 0xb4#64) hcode
  have hf46 := fetch_at 46 (off := 0xb8#64) hcode
  have hf47 := fetch_at 47 (off := 0xbc#64) hcode
  have hf48 := fetch_at 48 (off := 0xc0#64) hcode
  have hf49 := fetch_at 49 (off := 0xc4#64) hcode
  have hf50 := fetch_at 50 (off := 0xc8#64) hcode
  have hf51 := fetch_at 51 (off := 0xcc#64) hcode
  have hf52 := fetch_at 52 (off := 0xd0#64) hcode
  have hf53 := fetch_at 53 (off := 0xd4#64) hcode
  have hf54 := fetch_at 54 (off := 0xd8#64) hcode
  have hf55 := fetch_at 55 (off := 0xdc#64) hcode
  have hf56 := fetch_at 56 (off := 0xe0#64) hcode
  wp_steps 57
  apply SepWP.done
  · simp [wp_norm, arm64_norm]
  · exact hrun
  · refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm], ?_⟩
    · have : HasLenGe out_bs 160 := ⟨by omega⟩
      have hsub {m : Memory} {bs' : List (BitVec 8)}
          (hm' : m ⊨ ((ret ↦ₛ bs') ∗ (inA ↦ₛ v.toList)) ∗ R)
          (heq : bs' = dalekEdNegBytes v.toList) :
          m ⊨ ((ret ↦ₛ (dalekEdNegVec v).toList) ∗ (inA ↦ₛ v.toList)) ∗ R := by
        rw [show (dalekEdNegVec v).toList = dalekEdNegBytes v.toList from rfl, ← heq]
        exact hm'
      replace hm := hsub hm (by
        refine eq_of_length_160_words_eq
          (by simp only [write64_length_eq, hout_len]; decide)
          (dalekEdNegBytes_length v.toList)
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne,
            readLE_dalekEdNegBytes_q0, fe51NegBytesAt, readLE_packFe51Bytes_0, zext_trunc32_lsr51,
            Nat.zero_add]
        · simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne,
            readLE_dalekEdNegBytes_q0, fe51NegBytesAt, readLE_packFe51Bytes_8, Nat.zero_add]
        · simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne,
            readLE_dalekEdNegBytes_q0, fe51NegBytesAt, readLE_packFe51Bytes_16, Nat.zero_add]
        · simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne,
            readLE_dalekEdNegBytes_q0, fe51NegBytesAt, readLE_packFe51Bytes_24, Nat.zero_add]
        · simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne,
            readLE_dalekEdNegBytes_q0, fe51NegBytesAt, readLE_packFe51Bytes_32, Nat.zero_add]
        · rw [readLE_dalekEdNegBytes_q1 (k := 0) (by decide)]
          simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne,
            readLE_packFe51Bytes_0]
        · rw [readLE_dalekEdNegBytes_q1 (k := 8) (by decide)]
          simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne,
            readLE_packFe51Bytes_8]
        · rw [readLE_dalekEdNegBytes_q1 (k := 16) (by decide)]
          simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne,
            readLE_packFe51Bytes_16]
        · rw [readLE_dalekEdNegBytes_q1 (k := 24) (by decide)]
          simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne,
            readLE_packFe51Bytes_24]
        · rw [readLE_dalekEdNegBytes_q1 (k := 32) (by decide)]
          simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne,
            readLE_packFe51Bytes_32]
        · rw [readLE_dalekEdNegBytes_q2 (k := 0) (by decide)]
          simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne,
            readLE_packFe51Bytes_0]
        · rw [readLE_dalekEdNegBytes_q2 (k := 8) (by decide)]
          simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne,
            readLE_packFe51Bytes_8]
        · rw [readLE_dalekEdNegBytes_q2 (k := 16) (by decide)]
          simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne,
            readLE_packFe51Bytes_16]
        · rw [readLE_dalekEdNegBytes_q2 (k := 24) (by decide)]
          simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne,
            readLE_packFe51Bytes_24]
        · rw [readLE_dalekEdNegBytes_q2 (k := 32) (by decide)]
          simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne,
            readLE_packFe51Bytes_32]
        · rw [readLE_dalekEdNegBytes_q3 (k := 0) (by decide)]
          simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne,
            fe51NegBytesAt, readLE_packFe51Bytes_0, zext_trunc32_lsr51]
        · rw [readLE_dalekEdNegBytes_q3 (k := 8) (by decide)]
          simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne,
            fe51NegBytesAt, readLE_packFe51Bytes_8]
        · rw [readLE_dalekEdNegBytes_q3 (k := 16) (by decide)]
          simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne,
            fe51NegBytesAt, readLE_packFe51Bytes_16]
        · rw [readLE_dalekEdNegBytes_q3 (k := 24) (by decide)]
          simp (disch := decide) only [↓readLE_write64_self', ↓readLE_write64_ne,
            fe51NegBytesAt, readLE_packFe51Bytes_24]
        · rw [readLE_dalekEdNegBytes_q3 (k := 32) (by decide)]
          simp (disch := decide) only [↓readLE_write64_self',
            fe51NegBytesAt, readLE_packFe51Bytes_32])
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨fs_eq_of_preserved (by simp [FsTracePreserved.rfl]), ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨trace_eq_of_preserved (by simp [FsTracePreserved.rfl]), ?_⟩
      rw [inputAfter_false]
      exact Satisfies.mono (by sep_entail) hm
    · simp (config := { decide := true }) [CalleeSavedPreserved, wp_norm, arm64_norm]

private theorem unstacked_false_simulates_byVal (byVal : Bool) :
    SpecSimulates
      (keepsFs (edwardsPointNegUnstackedSpec false))
      (keepsFs (edwardsPointNegUnstackedSpec byVal)) := by
  refine SpecSimulates.of_map fun ⟨inA, v, ret⟩ R s0 hpre => ?_
  refine ⟨(inA, v, ret), R, hpre, fun sf _hret _hcc hpost => ?_⟩
  dsimp only [keepsFs, edwardsPointNegUnstackedSpec] at hpost ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  obtain ⟨hfs, hpost⟩ := hpost
  refine ⟨hfs, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  obtain ⟨htr, hpost⟩ := hpost
  refine ⟨htr, ?_⟩
  cases byVal
  · exact hpost
  · rw [inputAfter_false] at hpost
    rw [inputAfter_true]
    have hent : (inA ↦ₛ v.toList) ⊢ memRegion inA 160 := by
      simpa [List.Vector.toList_length v] using pointsToBytes_entails_memRegion inA v.toList
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent)) hpost

/-- Minimal `0`-byte-stack `keepsFs` proof for any `byVal : Bool`. -/
theorem edwardsPointNeg_unstacked_keepsFs_ok {P : Program} {addr : BitVec 64}
    (byVal : Bool) (hcode : hasInstrs P addr edwardsPointNegInstrs) :
    subroutine_ok P addr (keepsFs (edwardsPointNegUnstackedSpec byVal)) :=
  (unstacked_false_simulates_byVal byVal).subroutine_ok
    (edwardsPointNeg_unstacked_false_keepsFs_ok hcode)

/-- Minimal `0`-byte-stack proof for any `byVal : Bool`. -/
theorem edwardsPointNeg_unstacked_ok {P : Program} {addr : BitVec 64}
    (byVal : Bool) (hcode : hasInstrs P addr edwardsPointNegInstrs) :
    subroutine_ok P addr (edwardsPointNegUnstackedSpec byVal) :=
  subroutine_ok_drop_keepsFs (edwardsPointNeg_unstacked_keepsFs_ok byVal hcode)

/-! ## 4. Exact Consumer Contract Bridges (`CliExt.pureByteFunctionSpec` & `cryptoLeafStubSpec`) -/

/-- Arbitrary-stack `keepsFs` discharge for `edwardsPointNegUnstackedSpec byVal`. -/
theorem edwardsPointNeg_withStack_keepsFs_ok {P : Program} {addr : BitVec 64}
    (byVal : Bool) (hookStack : Nat) (hcode : hasInstrs P addr edwardsPointNegInstrs) :
    subroutine_ok P addr
      (keepsFs (withStack (edwardsPointNegUnstackedSpec byVal) hookStack)) :=
  subroutine_ok_withStack_keepsFs hookStack (edwardsPointNeg_unstacked_keepsFs_ok byVal hcode)

/-- Exact `CliExt.pureByteFunctionSpec dalekEdNegVec byVal` (`CliExternsFixed.lean:506`, used with
    `byVal = true` in `CliHookSatExt.lean:415` and `byVal = false` in `CliExternsWitness.lean:136`)
    `keepsFs` discharge from `hasInstrs`. -/
theorem edwardsPointNeg_pureByteFunctionSpec_keepsFs_ok {P : Program} {addr : BitVec 64}
    (byVal : Bool) (hcode : hasInstrs P addr edwardsPointNegInstrs) :
    subroutine_ok P addr (keepsFs (pureByteFunctionSpec dalekEdNegVec byVal)) :=
  edwardsPointNeg_withStack_keepsFs_ok byVal extHookStack hcode

/-- Exact `CliExt.pureByteFunctionSpec dalekEdNegVec byVal` discharge from `hasInstrs`. -/
theorem edwardsPointNeg_pureByteFunctionSpec_ok {P : Program} {addr : BitVec 64}
    (byVal : Bool) (hcode : hasInstrs P addr edwardsPointNegInstrs) :
    subroutine_ok P addr (pureByteFunctionSpec dalekEdNegVec byVal) :=
  subroutine_ok_drop_keepsFs (edwardsPointNeg_pureByteFunctionSpec_keepsFs_ok byVal hcode)

/-- Exact `CliExt.pureByteFunctionSpec dalekEdNegVec byVal` discharge from
    `P.hasWords addr edwardsPointNegWords`. -/
theorem edwardsPointNeg_pureByteFunctionSpec_words_ok {P : Program} {addr : BitVec 64}
    (byVal : Bool) (hc : P.hasWords addr edwardsPointNegWords) :
    subroutine_ok P addr (pureByteFunctionSpec dalekEdNegVec byVal) :=
  edwardsPointNeg_pureByteFunctionSpec_ok byVal (hasInstrs_of_hasWords hc)

/-- Full `ProcessFieldsPreserved` discharge for `pureByteFunctionSpec dalekEdNegVec byVal` on a
    hook-free program `P`. -/
theorem edwardsPointNeg_pureByteFunctionProcessSpec_ok {P : Program} {addr : BitVec 64}
    (byVal : Bool) (hc : P.hasWords addr edwardsPointNegWords)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr
      { pureByteFunctionSpec dalekEdNegVec byVal with
        post := fun x s0 sf =>
          ⌜ProcessFieldsPreserved s0 sf⌝ ∗
            (pureByteFunctionSpec dalekEdNegVec byVal).post x s0 sf } :=
  subroutine_ok_lift_pureWords_process
    (edwardsPointNeg_pureByteFunctionSpec_ok byVal (pureWordsProg_hasInstrs_edNeg addr))
    (pureWordsProg_noSvcMsr_edNeg addr) hc h_no_ext
    (h_pre_mem := by intro _ s _; cases s; rfl)
    (h_post_mem := by intro _ s0 sf _ _; cases s0; cases sf; rfl)

/-- Process- and VM-preserving `keepsFs` bridge for `pureByteFunctionSpec dalekEdNegVec byVal`. -/
theorem edwardsPointNeg_pureByteFunctionBudgetSpec_keepsFs_ok {P : Program} {addr : BitVec 64}
    (byVal : Bool) (hc : P.hasWords addr edwardsPointNegWords)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr (keepsFs (withVmPreserved (pureByteFunctionSpec dalekEdNegVec byVal))) :=
  subroutine_ok_keepsFs_withVmPreserved_of_pureWords
    (edwardsPointNeg_pureByteFunctionSpec_ok byVal (pureWordsProg_hasInstrs_edNeg addr))
    (pureWordsProg_noSvcMsr_edNeg addr) hc h_no_ext

/-- Process- and VM-preserving bridge (`withVmPreserved (pureByteFunctionSpec dalekEdNegVec byVal)`). -/
theorem edwardsPointNeg_pureByteFunctionBudgetSpec_ok {P : Program} {addr : BitVec 64}
    (byVal : Bool) (hc : P.hasWords addr edwardsPointNegWords)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr (withVmPreserved (pureByteFunctionSpec dalekEdNegVec byVal)) :=
  subroutine_ok_drop_keepsFs (edwardsPointNeg_pureByteFunctionBudgetSpec_keepsFs_ok byVal hc h_no_ext)

/-- Process- and VM-preserving `keepsFs` bridge (`0` B stack) for `edwardsPointNegUnstackedSpec byVal`. -/
theorem edwardsPointNeg_unstackedBudgetSpec_keepsFs_ok {P : Program} {addr : BitVec 64}
    (byVal : Bool) (hc : P.hasWords addr edwardsPointNegWords)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr (keepsFs (withVmPreserved (edwardsPointNegUnstackedSpec byVal))) :=
  subroutine_ok_keepsFs_withVmPreserved_of_pureWords
    (edwardsPointNeg_unstacked_ok byVal (pureWordsProg_hasInstrs_edNeg addr))
    (pureWordsProg_noSvcMsr_edNeg addr) hc h_no_ext

/-- `withFsPred Pfs (withVmPreserved (edwardsPointNegUnstackedSpec byVal))` bridge (`0` B stack) on a
    hook-free `P`. -/
theorem edwardsPointNeg_unstackedBudgetSpec_withFsPred_ok {P : Program} {addr : BitVec 64}
    (Pfs : FsState → Prop) (byVal : Bool) (hc : P.hasWords addr edwardsPointNegWords)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr (withFsPred Pfs (withVmPreserved (edwardsPointNegUnstackedSpec byVal))) :=
  subroutine_ok_withFsPred_of_keepsFs Pfs
    (edwardsPointNeg_unstackedBudgetSpec_keepsFs_ok byVal hc h_no_ext)

/-- `withFsPred Pfs (withVmPreserved (pureByteFunctionSpec dalekEdNegVec byVal))` bridge on a
    hook-free `P`. -/
theorem edwardsPointNeg_pureByteFunctionBudgetSpec_withFsPred_ok {P : Program} {addr : BitVec 64}
    (Pfs : FsState → Prop) (byVal : Bool) (hc : P.hasWords addr edwardsPointNegWords)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr
      (withFsPred Pfs (withVmPreserved (pureByteFunctionSpec dalekEdNegVec byVal))) :=
  subroutine_ok_withFsPred_of_keepsFs Pfs
    (edwardsPointNeg_pureByteFunctionBudgetSpec_keepsFs_ok byVal hc h_no_ext)

/-! ## 5. Direct Curve25519 `EdExtPoint` Machine-Code Specification & Proof -/

/-- Direct Curve25519 `EdExtPoint` contract (`0` B stack): negating a limb-bounded 160-byte
    `EdwardsPoint` at `inA` into `ret` produces a `< 2 ^ 52` limb-bounded 160-byte buffer
    representing `edExtNeg (edExtOfBytes v.toList)`. -/
@[expose] def edwardsPointNegEdExtSpec :
    Spec (BitVec 64 × List.Vector (BitVec 8) 160 × BitVec 64) where
  pre := fun (inA, v, ret) s =>
    ⌜s.readReg64 .x0 = inA ∧
      s.readReg64 .x8 = ret ∧
      fe51LimbsBoundedAt v.toList 0 (2 ^ 54) ∧
      fe51LimbsBoundedAt v.toList 40 (2 ^ 52) ∧
      fe51LimbsBoundedAt v.toList 80 (2 ^ 52) ∧
      fe51LimbsBoundedAt v.toList 120 (2 ^ 54)⌝ ∗
      (inA ↦ₛ v.toList) ∗ memRegion ret 160
  post := fun (inA, v, ret) s0 sf =>
    ∃∗ res_bs : List (BitVec 8),
      ⌜sf.trace = s0.trace ∧
        fe51Point4Bounded res_bs (2 ^ 52) ∧
        edExtOfBytes res_bs = edExtNeg (edExtOfBytes v.toList)⌝ ∗
        (inA ↦ₛ v.toList) ∗ (ret ↦ₛ res_bs)

private theorem unstacked_simulates_edExtSpec :
    SpecSimulates
      (keepsFs (edwardsPointNegUnstackedSpec false))
      (keepsFs edwardsPointNegEdExtSpec) := by
  refine SpecSimulates.of_map fun ⟨inA, v, ret⟩ R s0 hpre => ?_
  dsimp only [keepsFs, edwardsPointNegEdExtSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx8, hX, hY, hZ, hT⟩, hpre⟩ := hpre
  refine ⟨(inA, v, ret), R, ?_, fun sf _hret _hcc hpost => ?_⟩
  · dsimp only [keepsFs, edwardsPointNegUnstackedSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx8⟩, hpre⟩
  · dsimp only [keepsFs, edwardsPointNegUnstackedSpec,
      edwardsPointNegEdExtSpec] at hpost ⊢
    rw [inputAfter_false] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    obtain ⟨hfs, hpost⟩ := hpost
    refine ⟨hfs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨htr, hpost⟩ := hpost
    have ⟨hbnd, hext⟩ := dalekEdNegVec_sound v hX hY hZ hT
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨(dalekEdNegVec v).toList, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨htr, hbnd, hext⟩, hpost⟩

/-- Machine-code Curve25519 `EdExtPoint` correctness for `edwardsPointNegWords` (`0` B stack). -/
theorem edwardsPointNeg_edExtSpec_words_ok {P : Program} {addr : BitVec 64}
    (hc : P.hasWords addr edwardsPointNegWords) :
    subroutine_ok P addr edwardsPointNegEdExtSpec :=
  subroutine_ok_drop_keepsFs
    (unstacked_simulates_edExtSpec.subroutine_ok
      (edwardsPointNeg_unstacked_false_keepsFs_ok (hasInstrs_of_hasWords hc)))

end LibsignalBinary.Proofs.HookDischarge.Crypto.EdwardsNeg
