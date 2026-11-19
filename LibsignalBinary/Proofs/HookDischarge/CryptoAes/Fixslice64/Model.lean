/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Spec.Aes256

/-!
# 64-Bit Fixsliced AES-256 Model (`CryptoAes.Fixslice64.Model`)

Direct pure `BitVec 64` transcription of `aes` 0.9.1 `src/soft/fixslice64.rs` in the default
non-`compact` 64-bit configuration (`cpubits! { 64 => soft/fixslice64.rs }`):
- `FsState` (`[u64; 8]`), `Blocks4` (`BatchBlocks`), `FsKeys256` (`[u64; 120]`);
- `bitslice` and `invBitslice` (`read_reordered`, `write_reordered`, `delta_swap_2`);
- `subBytesFs`, `subBytesNots`, and `invSubBytesFs`;
- `shiftRows1..3`, `invShiftRows1..3`, `mixColumns0..3`, and `invMixColumns0..3`;
- `xorColumnsFs`, `aes256KeyScheduleFs`, `aes256EncryptFs`, and `aes256DecryptFs`.
-/

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model

open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Spec.Aes256 (State)

/-! ## Core State, 4-Block Batch, and Round-Key Structures -/

/-- A 512-bit fixsliced state (`[u64; 8]` in `aes::soft::fixslice64`).
Word `s0..s7` holds bit-position `0..7` (LSB to MSB) across four 16-byte blocks:
bit `16 * r + 4 * c + lane` of slice `p` stores bit `p` of byte `r + 4 * c` of block `lane`. -/
@[ext] structure FsState where
  s0 : BitVec 64
  s1 : BitVec 64
  s2 : BitVec 64
  s3 : BitVec 64
  s4 : BitVec 64
  s5 : BitVec 64
  s6 : BitVec 64
  s7 : BitVec 64
  deriving Repr

/-- Zero-initialized fixsliced state (`State::default()`). -/
@[expose] def FsState.zero : FsState :=
  ⟨0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64⟩

/-- Slice lookup `0..7` on `FsState`. -/
@[expose] def FsState.getSlice (st : FsState) : Nat → BitVec 64
  | 0 => st.s0
  | 1 => st.s1
  | 2 => st.s2
  | 3 => st.s3
  | 4 => st.s4
  | 5 => st.s5
  | 6 => st.s6
  | 7 => st.s7
  | _ => 0#64

/-- Construct `FsState` from a slice index function. -/
@[expose] def FsState.ofSliceFn (f : Nat → BitVec 64) : FsState :=
  ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7⟩

/-- Map a unary `BitVec 64` operation across all 8 bit-slices. -/
@[expose] def FsState.map (f : BitVec 64 → BitVec 64) (st : FsState) : FsState :=
  ⟨f st.s0, f st.s1, f st.s2, f st.s3, f st.s4, f st.s5, f st.s6, f st.s7⟩

/-- Combine two `FsState` values slice-wise. -/
@[expose] def FsState.zipWith (f : BitVec 64 → BitVec 64 → BitVec 64) (a b : FsState) : FsState :=
  ⟨f a.s0 b.s0, f a.s1 b.s1, f a.s2 b.s2, f a.s3 b.s3,
   f a.s4 b.s4, f a.s5 b.s5, f a.s6 b.s6, f a.s7 b.s7⟩

/-- 8-element `u64` word list representation of `FsState` (matching `[u64; 8]` in memory). -/
@[expose] def FsState.toWords (st : FsState) : List (BitVec 64) :=
  [st.s0, st.s1, st.s2, st.s3, st.s4, st.s5, st.s6, st.s7]

/-- Parse an 8-element `u64` word list into `FsState`. -/
@[expose] def FsState.ofWords (ws : List (BitVec 64)) : FsState :=
  ⟨ws.getD 0 0#64, ws.getD 1 0#64, ws.getD 2 0#64, ws.getD 3 0#64,
   ws.getD 4 0#64, ws.getD 5 0#64, ws.getD 6 0#64, ws.getD 7 0#64⟩

/-- A batch of four 16-byte AES blocks (`BatchBlocks` in `fixslice64.rs`). -/
@[ext] structure Blocks4 where
  b0 : State
  b1 : State
  b2 : State
  b3 : State
  deriving Repr

/-- Lane lookup `0..3` on `Blocks4`. -/
@[expose] def Blocks4.getLane (bs : Blocks4) : Nat → State
  | 0 => bs.b0
  | 1 => bs.b1
  | 2 => bs.b2
  | 3 => bs.b3
  | _ => []

/-- Map a single-block transformation across all 4 lanes. -/
@[expose] def Blocks4.map (f : State → State) (bs : Blocks4) : Blocks4 :=
  ⟨f bs.b0, f bs.b1, f bs.b2, f bs.b3⟩

/-- Combine two 4-block batches lane-wise. -/
@[expose] def Blocks4.zipWith (f : State → State → State) (x y : Blocks4) : Blocks4 :=
  ⟨f x.b0 y.b0, f x.b1 y.b1, f x.b2 y.b2, f x.b3 y.b3⟩

/-- Replicate one 16-byte block across all 4 lanes (used by `aes256_key_schedule`). -/
@[expose] def Blocks4.replicate (s : State) : Blocks4 :=
  ⟨s, s, s, s⟩

/-- AES-256 fixsliced round keys (`FixsliceKeys256 = [u64; 120]`, i.e., 15 `FsState`s). -/
@[ext] structure FsKeys256 where
  rk0 : FsState
  rk1 : FsState
  rk2 : FsState
  rk3 : FsState
  rk4 : FsState
  rk5 : FsState
  rk6 : FsState
  rk7 : FsState
  rk8 : FsState
  rk9 : FsState
  rk10 : FsState
  rk11 : FsState
  rk12 : FsState
  rk13 : FsState
  rk14 : FsState
  deriving Repr

/-- Round-key lookup `0..14` on `FsKeys256`. -/
@[expose] def FsKeys256.getRound (ks : FsKeys256) : Nat → FsState
  | 0 => ks.rk0
  | 1 => ks.rk1
  | 2 => ks.rk2
  | 3 => ks.rk3
  | 4 => ks.rk4
  | 5 => ks.rk5
  | 6 => ks.rk6
  | 7 => ks.rk7
  | 8 => ks.rk8
  | 9 => ks.rk9
  | 10 => ks.rk10
  | 11 => ks.rk11
  | 12 => ks.rk12
  | 13 => ks.rk13
  | 14 => ks.rk14
  | _ => FsState.zero

/-- Flat 120-word `[u64; 120]` memory representation of `FsKeys256`. -/
@[expose] def FsKeys256.toWords (ks : FsKeys256) : List (BitVec 64) :=
  ks.rk0.toWords ++ ks.rk1.toWords ++ ks.rk2.toWords ++ ks.rk3.toWords ++ ks.rk4.toWords ++
  ks.rk5.toWords ++ ks.rk6.toWords ++ ks.rk7.toWords ++ ks.rk8.toWords ++ ks.rk9.toWords ++
  ks.rk10.toWords ++ ks.rk11.toWords ++ ks.rk12.toWords ++ ks.rk13.toWords ++ ks.rk14.toWords

/-! ## Rotations and Bit-Swap Helpers (`fixslice64.rs` lines 1152–1422) -/

/-- Right-rotate a 64-bit word (`ror(x, y)`). -/
@[expose] def ror64 (x : BitVec 64) (y : Nat) : BitVec 64 :=
  x.rotateRight y

/-- Rotation distance for `(rows, cols)` in 64-bit fixslicing (`(rows <<< 4) + (cols <<< 2)`). -/
@[expose] def rorDistance (rows cols : Nat) : Nat :=
  (rows <<< 4) + (cols <<< 2)

@[expose] def rotateRows1 (x : BitVec 64) : BitVec 64 :=
  ror64 x (rorDistance 1 0)

@[expose] def rotateRows2 (x : BitVec 64) : BitVec 64 :=
  ror64 x (rorDistance 2 0)

@[expose] def rotateRowsAndColumns11 (x : BitVec 64) : BitVec 64 :=
  (ror64 x (rorDistance 1 1) &&& 0x0fff0fff0fff0fff#64) |||
  (ror64 x (rorDistance 0 1) &&& 0xf000f000f000f000#64)

@[expose] def rotateRowsAndColumns12 (x : BitVec 64) : BitVec 64 :=
  (ror64 x (rorDistance 1 2) &&& 0x00ff00ff00ff00ff#64) |||
  (ror64 x (rorDistance 0 2) &&& 0xff00ff00ff00ff00#64)

@[expose] def rotateRowsAndColumns13 (x : BitVec 64) : BitVec 64 :=
  (ror64 x (rorDistance 1 3) &&& 0x000f000f000f000f#64) |||
  (ror64 x (rorDistance 0 3) &&& 0xfff0fff0fff0fff0#64)

@[expose] def rotateRowsAndColumns22 (x : BitVec 64) : BitVec 64 :=
  (ror64 x (rorDistance 2 2) &&& 0x00ff00ff00ff00ff#64) |||
  (ror64 x (rorDistance 1 2) &&& 0xff00ff00ff00ff00#64)

/-- Single-word masked bit swap (`delta_swap_1`). -/
@[expose] def deltaSwap1 (a : BitVec 64) (shift : Nat) (mask : BitVec 64) : BitVec 64 :=
  let t := (a ^^^ (a >>> shift)) &&& mask
  a ^^^ t ^^^ (t <<< shift)

/-- Two-word masked bit swap (`delta_swap_2`). -/
@[expose] def deltaSwap2 (a b : BitVec 64) (shift : Nat) (mask : BitVec 64) :
    BitVec 64 × BitVec 64 :=
  let t := (a ^^^ (b >>> shift)) &&& mask
  (a ^^^ t, b ^^^ (t <<< shift))

/-! ## Packing and Unpacking (`bitslice` and `inv_bitslice`, lines 1193–1345) -/

/-- `read_reordered(&input[off .. off + 12])` (`fixslice64.rs` lines 1209–1218). -/
@[expose] def readReordered (input : State) (off : Nat) : BitVec 64 :=
  ((input.getD (off + 0x0) 0#8).zeroExtend 64) |||
  (((input.getD (off + 0x1) 0#8).zeroExtend 64) <<< 0x10) |||
  (((input.getD (off + 0x2) 0#8).zeroExtend 64) <<< 0x20) |||
  (((input.getD (off + 0x3) 0#8).zeroExtend 64) <<< 0x30) |||
  (((input.getD (off + 0x8) 0#8).zeroExtend 64) <<< 0x08) |||
  (((input.getD (off + 0x9) 0#8).zeroExtend 64) <<< 0x18) |||
  (((input.getD (off + 0xa) 0#8).zeroExtend 64) <<< 0x28) |||
  (((input.getD (off + 0xb) 0#8).zeroExtend 64) <<< 0x38)

/-- Pack four 128-bit blocks into an `FsState` (`fixslice64::bitslice`). -/
@[expose] def bitslice (bs : Blocks4) : FsState :=
  let t0 := readReordered bs.b0 0
  let t4 := readReordered bs.b0 4
  let t1 := readReordered bs.b1 0
  let t5 := readReordered bs.b1 4
  let t2 := readReordered bs.b2 0
  let t6 := readReordered bs.b2 4
  let t3 := readReordered bs.b3 0
  let t7 := readReordered bs.b3 4
  let m0 := 0x5555555555555555#64
  let (t1, t0) := deltaSwap2 t1 t0 1 m0
  let (t3, t2) := deltaSwap2 t3 t2 1 m0
  let (t5, t4) := deltaSwap2 t5 t4 1 m0
  let (t7, t6) := deltaSwap2 t7 t6 1 m0
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

/-- Combine the two `write_reordered(c_lo, &mut out[0..12]); write_reordered(c_hi, &mut out[4..16])`
half-column writes into a 16-byte block (`fixslice64.rs` lines 1317–1340). -/
@[expose] def writeReorderedPair (cLo cHi : BitVec 64) : State :=
  [(cLo >>> 0x00).truncate 8,
   (cLo >>> 0x10).truncate 8,
   (cLo >>> 0x20).truncate 8,
   (cLo >>> 0x30).truncate 8,
   (cHi >>> 0x00).truncate 8,
   (cHi >>> 0x10).truncate 8,
   (cHi >>> 0x20).truncate 8,
   (cHi >>> 0x30).truncate 8,
   (cLo >>> 0x08).truncate 8,
   (cLo >>> 0x18).truncate 8,
   (cLo >>> 0x28).truncate 8,
   (cLo >>> 0x38).truncate 8,
   (cHi >>> 0x08).truncate 8,
   (cHi >>> 0x18).truncate 8,
   (cHi >>> 0x28).truncate 8,
   (cHi >>> 0x38).truncate 8]

/-- Unpack an `FsState` into four 128-bit blocks (`fixslice64::inv_bitslice`). -/
@[expose] def invBitslice (input : FsState) : Blocks4 :=
  let t0 := input.s0
  let t1 := input.s1
  let t2 := input.s2
  let t3 := input.s3
  let t4 := input.s4
  let t5 := input.s5
  let t6 := input.s6
  let t7 := input.s7
  let m0 := 0x5555555555555555#64
  let (t1, t0) := deltaSwap2 t1 t0 1 m0
  let (t3, t2) := deltaSwap2 t3 t2 1 m0
  let (t5, t4) := deltaSwap2 t5 t4 1 m0
  let (t7, t6) := deltaSwap2 t7 t6 1 m0
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
  ⟨writeReorderedPair t0 t4,
   writeReorderedPair t1 t5,
   writeReorderedPair t2 t6,
   writeReorderedPair t3 t7⟩

/-! ## Bitsliced `SubBytes`, `sub_bytes_nots`, and `InvSubBytes` (lines 591–948) -/

/-- Constant `0x63` (`0b0110_0011`) bit-slice mask XORed by `sub_bytes_nots`. -/
@[expose] def notsMask : FsState :=
  ⟨0xffffffffffffffff#64, 0xffffffffffffffff#64, 0#64, 0#64,
   0#64, 0xffffffffffffffff#64, 0xffffffffffffffff#64, 0#64⟩

/-- XOR the 4 NOT masks omitted from `sub_bytes` (`fixslice64::sub_bytes_nots`). -/
@[expose] def subBytesNots (st : FsState) : FsState :=
  st.zipWith (· ^^^ ·) notsMask

/-- Intermediate wire bundle 1 for `subBytesFs` (`sub_bytes`). -/
@[ext] structure SubBytesW1 where
  t0 : BitVec 64
  t14 : BitVec 64
  t16 : BitVec 64
  t2 : BitVec 64
  t7 : BitVec 64
  u0 : BitVec 64
  u3 : BitVec 64
  u6 : BitVec 64
  u7 : BitVec 64
  y10 : BitVec 64
  y11 : BitVec 64
  y12 : BitVec 64
  y13 : BitVec 64
  y14 : BitVec 64
  y15 : BitVec 64
  y16 : BitVec 64
  y17 : BitVec 64
  y18 : BitVec 64
  y19 : BitVec 64
  y20 : BitVec 64
  y21 : BitVec 64
  y6 : BitVec 64
  y7 : BitVec 64
  y8 : BitVec 64
  y9 : BitVec 64
  deriving Repr

/-- Intermediate wire bundle 2 for `subBytesFs` (`sub_bytes`). -/
@[ext] structure SubBytesW2 where
  t22 : BitVec 64
  t23 : BitVec 64
  t24 : BitVec 64
  t25 : BitVec 64
  t27 : BitVec 64
  t31 : BitVec 64
  u7 : BitVec 64
  y1 : BitVec 64
  y10 : BitVec 64
  y11 : BitVec 64
  y12 : BitVec 64
  y13 : BitVec 64
  y14 : BitVec 64
  y15 : BitVec 64
  y16 : BitVec 64
  y17 : BitVec 64
  y2 : BitVec 64
  y3 : BitVec 64
  y4 : BitVec 64
  y5 : BitVec 64
  y6 : BitVec 64
  y7 : BitVec 64
  y8 : BitVec 64
  y9 : BitVec 64
  deriving Repr

/-- Intermediate wire bundle 3 for `subBytesFs` (`sub_bytes`). -/
@[ext] structure SubBytesW3 where
  t29 : BitVec 64
  t33 : BitVec 64
  t37 : BitVec 64
  t41 : BitVec 64
  t44 : BitVec 64
  tc12 : BitVec 64
  tc6 : BitVec 64
  u7 : BitVec 64
  y11 : BitVec 64
  y12 : BitVec 64
  y14 : BitVec 64
  y15 : BitVec 64
  y17 : BitVec 64
  y3 : BitVec 64
  y4 : BitVec 64
  y6 : BitVec 64
  y9 : BitVec 64
  z12 : BitVec 64
  z13 : BitVec 64
  z14 : BitVec 64
  z17 : BitVec 64
  z8 : BitVec 64
  deriving Repr

/-- Intermediate wire bundle 4 for `subBytesFs` (`sub_bytes`). -/
@[ext] structure SubBytesW4 where
  s0 : BitVec 64
  s1 : BitVec 64
  s3 : BitVec 64
  tc12 : BitVec 64
  tc13 : BitVec 64
  tc20 : BitVec 64
  tc21 : BitVec 64
  tc8 : BitVec 64
  z0 : BitVec 64
  z12 : BitVec 64
  z14 : BitVec 64
  z17 : BitVec 64
  z2 : BitVec 64
  z8 : BitVec 64
  deriving Repr

/-- Stage 1/5 of `subBytesFs` (`fixslice64::sub_bytes`). -/
@[expose] def subBytesFsStage1 (inp : FsState) : SubBytesW1 :=
  let u7 := inp.s0
  let u6 := inp.s1
  let u5 := inp.s2
  let u4 := inp.s3
  let u3 := inp.s4
  let u2 := inp.s5
  let u1 := inp.s6
  let u0 := inp.s7
  let y14 := u3 ^^^ u5
  let y13 := u0 ^^^ u6
  let y12 := y13 ^^^ y14
  let t1 := u4 ^^^ y12
  let y15 := t1 ^^^ u5
  let t2 := y12 &&& y15
  let y6 := y15 ^^^ u7
  let y20 := t1 ^^^ u1
  let y9 := u0 ^^^ u3
  let y11 := y20 ^^^ y9
  let t12 := y9 &&& y11
  let y7 := u7 ^^^ y11
  let y8 := u0 ^^^ u5
  let t0 := u1 ^^^ u2
  let y10 := y15 ^^^ t0
  let y17 := y10 ^^^ y11
  let t13 := y14 &&& y17
  let t14 := t13 ^^^ t12
  let y19 := y10 ^^^ y8
  let t15 := y8 &&& y10
  let t16 := t15 ^^^ t12
  let y16 := t0 ^^^ y11
  let y21 := y13 ^^^ y16
  let t7 := y13 &&& y16
  let y18 := u0 ^^^ y16
  ⟨t0, t14, t16, t2, t7, u0, u3, u6, u7, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y6, y7, y8, y9⟩

/-- Stage 2/5 of `subBytesFs` (`fixslice64::sub_bytes`). -/
@[expose] def subBytesFsStage2 (inp : SubBytesW1) : SubBytesW2 :=
  let t0 := inp.t0
  let t14 := inp.t14
  let t16 := inp.t16
  let t2 := inp.t2
  let t7 := inp.t7
  let u0 := inp.u0
  let u3 := inp.u3
  let u6 := inp.u6
  let u7 := inp.u7
  let y10 := inp.y10
  let y11 := inp.y11
  let y12 := inp.y12
  let y13 := inp.y13
  let y14 := inp.y14
  let y15 := inp.y15
  let y16 := inp.y16
  let y17 := inp.y17
  let y18 := inp.y18
  let y19 := inp.y19
  let y20 := inp.y20
  let y21 := inp.y21
  let y6 := inp.y6
  let y7 := inp.y7
  let y8 := inp.y8
  let y9 := inp.y9
  let y1 := t0 ^^^ u7
  let y4 := y1 ^^^ u3
  let t5 := y4 &&& u7
  let t6 := t5 ^^^ t2
  let t18 := t6 ^^^ t16
  let t22 := t18 ^^^ y19
  let y2 := y1 ^^^ u0
  let t10 := y2 &&& y7
  let t11 := t10 ^^^ t7
  let t20 := t11 ^^^ t16
  let t24 := t20 ^^^ y18
  let y5 := y1 ^^^ u6
  let t8 := y5 &&& y1
  let t9 := t8 ^^^ t7
  let t19 := t9 ^^^ t14
  let t23 := t19 ^^^ y21
  let y3 := y5 ^^^ y8
  let t3 := y3 &&& y6
  let t4 := t3 ^^^ t2
  let t17 := t4 ^^^ y20
  let t21 := t17 ^^^ t14
  let t26 := t21 &&& t23
  let t27 := t24 ^^^ t26
  let t31 := t22 ^^^ t26
  let t25 := t21 ^^^ t22
  ⟨t22, t23, t24, t25, t27, t31, u7, y1, y10, y11, y12, y13, y14, y15, y16, y17, y2, y3, y4, y5, y6, y7, y8, y9⟩

/-- Stage 3/5 of `subBytesFs` (`fixslice64::sub_bytes`). -/
@[expose] def subBytesFsStage3 (inp : SubBytesW2) : SubBytesW3 :=
  let t22 := inp.t22
  let t23 := inp.t23
  let t24 := inp.t24
  let t25 := inp.t25
  let t27 := inp.t27
  let t31 := inp.t31
  let u7 := inp.u7
  let y1 := inp.y1
  let y10 := inp.y10
  let y11 := inp.y11
  let y12 := inp.y12
  let y13 := inp.y13
  let y14 := inp.y14
  let y15 := inp.y15
  let y16 := inp.y16
  let y17 := inp.y17
  let y2 := inp.y2
  let y3 := inp.y3
  let y4 := inp.y4
  let y5 := inp.y5
  let y6 := inp.y6
  let y7 := inp.y7
  let y8 := inp.y8
  let y9 := inp.y9
  let t28 := t25 &&& t27
  let t29 := t28 ^^^ t22
  let z14 := t29 &&& y2
  let z5 := t29 &&& y7
  let t30 := t23 ^^^ t24
  let t32 := t31 &&& t30
  let t33 := t32 ^^^ t24
  let t35 := t27 ^^^ t33
  let t36 := t24 &&& t35
  let t38 := t27 ^^^ t36
  let t39 := t29 &&& t38
  let t40 := t25 ^^^ t39
  let t43 := t29 ^^^ t40
  let z3 := t43 &&& y16
  let tc12 := z3 ^^^ z5
  let z12 := t43 &&& y13
  let z13 := t40 &&& y5
  let z4 := t40 &&& y1
  let tc6 := z3 ^^^ z4
  let t34 := t23 ^^^ t33
  let t37 := t36 ^^^ t34
  let t41 := t40 ^^^ t37
  let z8 := t41 &&& y10
  let z17 := t41 &&& y8
  let t44 := t33 ^^^ t37
  ⟨t29, t33, t37, t41, t44, tc12, tc6, u7, y11, y12, y14, y15, y17, y3, y4, y6, y9, z12, z13, z14, z17, z8⟩

/-- Stage 4/5 of `subBytesFs` (`fixslice64::sub_bytes`). -/
@[expose] def subBytesFsStage4 (inp : SubBytesW3) : SubBytesW4 :=
  let t29 := inp.t29
  let t33 := inp.t33
  let t37 := inp.t37
  let t41 := inp.t41
  let t44 := inp.t44
  let tc12 := inp.tc12
  let tc6 := inp.tc6
  let u7 := inp.u7
  let y11 := inp.y11
  let y12 := inp.y12
  let y14 := inp.y14
  let y15 := inp.y15
  let y17 := inp.y17
  let y3 := inp.y3
  let y4 := inp.y4
  let y6 := inp.y6
  let y9 := inp.y9
  let z12 := inp.z12
  let z13 := inp.z13
  let z14 := inp.z14
  let z17 := inp.z17
  let z8 := inp.z8
  let z0 := t44 &&& y15
  let z9 := t44 &&& y12
  let z10 := t37 &&& y3
  let z1 := t37 &&& y6
  let tc5 := z1 ^^^ z0
  let tc11 := tc6 ^^^ tc5
  let z11 := t33 &&& y4
  let t42 := t29 ^^^ t33
  let t45 := t42 ^^^ t41
  let z7 := t45 &&& y17
  let tc8 := z7 ^^^ tc6
  let z16 := t45 &&& y14
  let z6 := t42 &&& y11
  let tc16 := z6 ^^^ tc8
  let z15 := t42 &&& y9
  let tc20 := z15 ^^^ tc16
  let tc1 := z15 ^^^ z16
  let tc2 := z10 ^^^ tc1
  let tc21 := tc2 ^^^ z11
  let tc3 := z9 ^^^ tc2
  let s0 := tc3 ^^^ tc16
  let s3 := tc3 ^^^ tc11
  let s1 := s3 ^^^ tc16
  let tc13 := z13 ^^^ tc1
  let z2 := t33 &&& u7
  ⟨s0, s1, s3, tc12, tc13, tc20, tc21, tc8, z0, z12, z14, z17, z2, z8⟩

/-- Stage 5/5 of `subBytesFs` (`fixslice64::sub_bytes`). -/
@[expose] def subBytesFsStage5 (inp : SubBytesW4) : FsState :=
  let s0 := inp.s0
  let s1 := inp.s1
  let s3 := inp.s3
  let tc12 := inp.tc12
  let tc13 := inp.tc13
  let tc20 := inp.tc20
  let tc21 := inp.tc21
  let tc8 := inp.tc8
  let z0 := inp.z0
  let z12 := inp.z12
  let z14 := inp.z14
  let z17 := inp.z17
  let z2 := inp.z2
  let z8 := inp.z8
  let tc4 := z0 ^^^ z2
  let tc7 := z12 ^^^ tc4
  let tc9 := z8 ^^^ tc7
  let tc10 := tc8 ^^^ tc9
  let tc17 := z14 ^^^ tc10
  let s5 := tc21 ^^^ tc17
  let tc26 := tc17 ^^^ tc20
  let s2 := tc26 ^^^ z17
  let tc14 := tc4 ^^^ tc12
  let tc18 := tc13 ^^^ tc14
  let s6 := tc10 ^^^ tc18
  let s7 := z12 ^^^ tc18
  let s4 := tc14 ^^^ s3
  ⟨s7, s6, s5, s4, s3, s2, s1, s0⟩

/-- Boyar–Peralta–Calik bitsliced S-box (`fixslice64::sub_bytes`, 4 NOTs moved to key schedule). -/
@[expose] def subBytesFs (st : FsState) : FsState :=
  subBytesFsStage5 (subBytesFsStage4 (subBytesFsStage3 (subBytesFsStage2 (subBytesFsStage1 st))))

/-- Intermediate wire bundle 1 for `invSubBytesFs` (`inv_sub_bytes`). -/
@[ext] structure InvSubBytesW1 where
  m1 : BitVec 64
  m14 : BitVec 64
  m2 : BitVec 64
  m7 : BitVec 64
  m9 : BitVec 64
  r13 : BitVec 64
  t1 : BitVec 64
  t10 : BitVec 64
  t13 : BitVec 64
  t17 : BitVec 64
  t19 : BitVec 64
  t2 : BitVec 64
  t20 : BitVec 64
  t22 : BitVec 64
  t23 : BitVec 64
  t24 : BitVec 64
  t25 : BitVec 64
  t3 : BitVec 64
  t4 : BitVec 64
  t6 : BitVec 64
  t8 : BitVec 64
  t9 : BitVec 64
  u2 : BitVec 64
  u4 : BitVec 64
  u5 : BitVec 64
  u6 : BitVec 64
  y5 : BitVec 64
  deriving Repr

/-- Intermediate wire bundle 2 for `invSubBytesFs` (`inv_sub_bytes`). -/
@[ext] structure InvSubBytesW2 where
  m10 : BitVec 64
  m15 : BitVec 64
  m20 : BitVec 64
  m21 : BitVec 64
  m22 : BitVec 64
  m25 : BitVec 64
  m26 : BitVec 64
  t1 : BitVec 64
  t10 : BitVec 64
  t13 : BitVec 64
  t15 : BitVec 64
  t16 : BitVec 64
  t17 : BitVec 64
  t19 : BitVec 64
  t2 : BitVec 64
  t20 : BitVec 64
  t22 : BitVec 64
  t23 : BitVec 64
  t25 : BitVec 64
  t27 : BitVec 64
  t3 : BitVec 64
  t4 : BitVec 64
  t6 : BitVec 64
  t8 : BitVec 64
  t9 : BitVec 64
  y5 : BitVec 64
  deriving Repr

/-- Intermediate wire bundle 3 for `invSubBytesFs` (`inv_sub_bytes`). -/
@[ext] structure InvSubBytesW3 where
  m21 : BitVec 64
  m22 : BitVec 64
  m24 : BitVec 64
  m36 : BitVec 64
  m38 : BitVec 64
  m39 : BitVec 64
  m42 : BitVec 64
  m43 : BitVec 64
  m48 : BitVec 64
  m49 : BitVec 64
  m51 : BitVec 64
  m57 : BitVec 64
  m60 : BitVec 64
  p0 : BitVec 64
  p16 : BitVec 64
  t10 : BitVec 64
  t13 : BitVec 64
  t2 : BitVec 64
  t22 : BitVec 64
  t23 : BitVec 64
  t27 : BitVec 64
  t3 : BitVec 64
  t4 : BitVec 64
  t6 : BitVec 64
  t8 : BitVec 64
  t9 : BitVec 64
  deriving Repr

/-- Intermediate wire bundle 4 for `invSubBytesFs` (`inv_sub_bytes`). -/
@[ext] structure InvSubBytesW4 where
  m39 : BitVec 64
  m40 : BitVec 64
  m48 : BitVec 64
  m50 : BitVec 64
  m51 : BitVec 64
  m57 : BitVec 64
  m63 : BitVec 64
  p0 : BitVec 64
  p15 : BitVec 64
  p16 : BitVec 64
  p17 : BitVec 64
  p2 : BitVec 64
  p22 : BitVec 64
  p23 : BitVec 64
  p6 : BitVec 64
  p7 : BitVec 64
  s0 : BitVec 64
  s6 : BitVec 64
  t13 : BitVec 64
  t23 : BitVec 64
  t6 : BitVec 64
  t8 : BitVec 64
  deriving Repr

/-- Intermediate wire bundle 5 for `invSubBytesFs` (`inv_sub_bytes`). -/
@[ext] structure InvSubBytesW5 where
  p11 : BitVec 64
  p17 : BitVec 64
  p25 : BitVec 64
  s0 : BitVec 64
  s1 : BitVec 64
  s3 : BitVec 64
  s4 : BitVec 64
  s5 : BitVec 64
  s6 : BitVec 64
  s7 : BitVec 64
  deriving Repr

/-- Stage 1/6 of `invSubBytesFs` (`fixslice64::inv_sub_bytes`). -/
@[expose] def invSubBytesFsStage1 (inp : FsState) : InvSubBytesW1 :=
  let u7 := inp.s0
  let u6 := inp.s1
  let u5 := inp.s2
  let u4 := inp.s3
  let u3 := inp.s4
  let u2 := inp.s5
  let u1 := inp.s6
  let u0 := inp.s7
  let t23 := u0 ^^^ u3
  let t8 := u1 ^^^ t23
  let m2 := t23 &&& t8
  let t4 := u4 ^^^ t8
  let t22 := u1 ^^^ u3
  let t2 := u0 ^^^ u1
  let t1 := u3 ^^^ u4
  let t9 := u7 ^^^ t1
  let m7 := t22 &&& t9
  let t24 := u4 ^^^ u7
  let t10 := t2 ^^^ t24
  let m14 := t2 &&& t10
  let r5 := u6 ^^^ u7
  let t3 := t1 ^^^ r5
  let t13 := t2 ^^^ r5
  let t19 := t22 ^^^ r5
  let t17 := u2 ^^^ t19
  let t25 := u2 ^^^ t1
  let r13 := u1 ^^^ u6
  let t20 := t24 ^^^ r13
  let m9 := t20 &&& t17
  let r17 := u2 ^^^ u5
  let t6 := t22 ^^^ r17
  let m1 := t13 &&& t6
  let y5 := u0 ^^^ r17
  ⟨m1, m14, m2, m7, m9, r13, t1, t10, t13, t17, t19, t2, t20, t22, t23, t24, t25, t3, t4, t6, t8, t9, u2, u4, u5, u6, y5⟩

/-- Stage 2/6 of `invSubBytesFs` (`fixslice64::inv_sub_bytes`). -/
@[expose] def invSubBytesFsStage2 (inp : InvSubBytesW1) : InvSubBytesW2 :=
  let m1 := inp.m1
  let m14 := inp.m14
  let m2 := inp.m2
  let m7 := inp.m7
  let m9 := inp.m9
  let r13 := inp.r13
  let t1 := inp.t1
  let t10 := inp.t10
  let t13 := inp.t13
  let t17 := inp.t17
  let t19 := inp.t19
  let t2 := inp.t2
  let t20 := inp.t20
  let t22 := inp.t22
  let t23 := inp.t23
  let t24 := inp.t24
  let t25 := inp.t25
  let t3 := inp.t3
  let t4 := inp.t4
  let t6 := inp.t6
  let t8 := inp.t8
  let t9 := inp.t9
  let u2 := inp.u2
  let u4 := inp.u4
  let u5 := inp.u5
  let u6 := inp.u6
  let y5 := inp.y5
  let m4 := t19 &&& y5
  let m5 := m4 ^^^ m1
  let m17 := m5 ^^^ t24
  let r18 := u5 ^^^ u6
  let t27 := t1 ^^^ r18
  let t15 := t10 ^^^ t27
  let m11 := t1 &&& t15
  let m15 := m14 ^^^ m11
  let m21 := m17 ^^^ m15
  let m12 := t4 &&& t27
  let m13 := m12 ^^^ m11
  let t14 := t10 ^^^ r18
  let m3 := t14 ^^^ m1
  let m16 := m3 ^^^ m2
  let m20 := m16 ^^^ m13
  let r19 := u2 ^^^ u4
  let t16 := r13 ^^^ r19
  let t26 := t3 ^^^ t16
  let m6 := t3 &&& t16
  let m8 := t26 ^^^ m6
  let m18 := m8 ^^^ m7
  let m22 := m18 ^^^ m13
  let m25 := m22 &&& m20
  let m26 := m21 ^^^ m25
  let m10 := m9 ^^^ m6
  ⟨m10, m15, m20, m21, m22, m25, m26, t1, t10, t13, t15, t16, t17, t19, t2, t20, t22, t23, t25, t27, t3, t4, t6, t8, t9, y5⟩

/-- Stage 3/6 of `invSubBytesFs` (`fixslice64::inv_sub_bytes`). -/
@[expose] def invSubBytesFsStage3 (inp : InvSubBytesW2) : InvSubBytesW3 :=
  let m10 := inp.m10
  let m15 := inp.m15
  let m20 := inp.m20
  let m21 := inp.m21
  let m22 := inp.m22
  let m25 := inp.m25
  let m26 := inp.m26
  let t1 := inp.t1
  let t10 := inp.t10
  let t13 := inp.t13
  let t15 := inp.t15
  let t16 := inp.t16
  let t17 := inp.t17
  let t19 := inp.t19
  let t2 := inp.t2
  let t20 := inp.t20
  let t22 := inp.t22
  let t23 := inp.t23
  let t25 := inp.t25
  let t27 := inp.t27
  let t3 := inp.t3
  let t4 := inp.t4
  let t6 := inp.t6
  let t8 := inp.t8
  let t9 := inp.t9
  let y5 := inp.y5
  let m19 := m10 ^^^ m15
  let m23 := m19 ^^^ t25
  let m28 := m23 ^^^ m25
  let m24 := m22 ^^^ m23
  let m30 := m26 &&& m24
  let m39 := m23 ^^^ m30
  let m48 := m39 &&& y5
  let m57 := m39 &&& t19
  let m36 := m24 ^^^ m25
  let m31 := m20 &&& m23
  let m27 := m20 ^^^ m21
  let m32 := m27 &&& m31
  let m29 := m28 &&& m27
  let m37 := m21 ^^^ m29
  let m42 := m37 ^^^ m39
  let m52 := m42 &&& t15
  let m61 := m42 &&& t1
  let p0 := m52 ^^^ m61
  let p16 := m57 ^^^ m61
  let m60 := m37 &&& t20
  let m51 := m37 &&& t17
  let m33 := m27 ^^^ m25
  let m38 := m32 ^^^ m33
  let m43 := m37 ^^^ m38
  let m49 := m43 &&& t16
  ⟨m21, m22, m24, m36, m38, m39, m42, m43, m48, m49, m51, m57, m60, p0, p16, t10, t13, t2, t22, t23, t27, t3, t4, t6, t8, t9⟩

/-- Stage 4/6 of `invSubBytesFs` (`fixslice64::inv_sub_bytes`). -/
@[expose] def invSubBytesFsStage4 (inp : InvSubBytesW3) : InvSubBytesW4 :=
  let m21 := inp.m21
  let m22 := inp.m22
  let m24 := inp.m24
  let m36 := inp.m36
  let m38 := inp.m38
  let m39 := inp.m39
  let m42 := inp.m42
  let m43 := inp.m43
  let m48 := inp.m48
  let m49 := inp.m49
  let m51 := inp.m51
  let m57 := inp.m57
  let m60 := inp.m60
  let p0 := inp.p0
  let p16 := inp.p16
  let t10 := inp.t10
  let t13 := inp.t13
  let t2 := inp.t2
  let t22 := inp.t22
  let t23 := inp.t23
  let t27 := inp.t27
  let t3 := inp.t3
  let t4 := inp.t4
  let t6 := inp.t6
  let t8 := inp.t8
  let t9 := inp.t9
  let p6 := m49 ^^^ m60
  let p13 := m49 ^^^ m51
  let m58 := m43 &&& t3
  let m50 := m38 &&& t9
  let m59 := m38 &&& t22
  let p1 := m58 ^^^ m59
  let p7 := p0 ^^^ p1
  let m34 := m21 &&& m22
  let m35 := m24 &&& m34
  let m40 := m35 ^^^ m36
  let m41 := m38 ^^^ m40
  let m45 := m42 ^^^ m41
  let m53 := m45 &&& t27
  let p8 := m50 ^^^ m53
  let p23 := p7 ^^^ p8
  let m62 := m45 &&& t4
  let p14 := m49 ^^^ m62
  let s6 := p14 ^^^ p23
  let m54 := m41 &&& t10
  let p2 := m54 ^^^ m62
  let p22 := p2 ^^^ p7
  let s0 := p13 ^^^ p22
  let p17 := m58 ^^^ p2
  let p15 := m54 ^^^ m59
  let m63 := m41 &&& t2
  ⟨m39, m40, m48, m50, m51, m57, m63, p0, p15, p16, p17, p2, p22, p23, p6, p7, s0, s6, t13, t23, t6, t8⟩

/-- Stage 5/6 of `invSubBytesFs` (`fixslice64::inv_sub_bytes`). -/
@[expose] def invSubBytesFsStage5 (inp : InvSubBytesW4) : InvSubBytesW5 :=
  let m39 := inp.m39
  let m40 := inp.m40
  let m48 := inp.m48
  let m50 := inp.m50
  let m51 := inp.m51
  let m57 := inp.m57
  let m63 := inp.m63
  let p0 := inp.p0
  let p15 := inp.p15
  let p16 := inp.p16
  let p17 := inp.p17
  let p2 := inp.p2
  let p22 := inp.p22
  let p23 := inp.p23
  let p6 := inp.p6
  let p7 := inp.p7
  let s0 := inp.s0
  let s6 := inp.s6
  let t13 := inp.t13
  let t23 := inp.t23
  let t6 := inp.t6
  let t8 := inp.t8
  let m44 := m39 ^^^ m40
  let m46 := m44 &&& t6
  let p5 := m46 ^^^ m51
  let p18 := m63 ^^^ p5
  let p24 := p5 ^^^ p7
  let p12 := m46 ^^^ m48
  let s3 := p12 ^^^ p22
  let m55 := m44 &&& t13
  let p9 := m55 ^^^ m63
  let s7 := p9 ^^^ p16
  let m47 := m40 &&& t8
  let p3 := m47 ^^^ m50
  let p19 := p2 ^^^ p3
  let s5 := p19 ^^^ p24
  let p11 := p0 ^^^ p3
  let p26 := p9 ^^^ p11
  let m56 := m40 &&& t23
  let p4 := m48 ^^^ m56
  let p20 := p4 ^^^ p6
  let p29 := p15 ^^^ p20
  let s1 := p26 ^^^ p29
  let p10 := m57 ^^^ p4
  let p27 := p10 ^^^ p18
  let s4 := p23 ^^^ p27
  let p25 := p6 ^^^ p10
  ⟨p11, p17, p25, s0, s1, s3, s4, s5, s6, s7⟩

/-- Stage 6/6 of `invSubBytesFs` (`fixslice64::inv_sub_bytes`). -/
@[expose] def invSubBytesFsStage6 (inp : InvSubBytesW5) : FsState :=
  let p11 := inp.p11
  let p17 := inp.p17
  let p25 := inp.p25
  let s0 := inp.s0
  let s1 := inp.s1
  let s3 := inp.s3
  let s4 := inp.s4
  let s5 := inp.s5
  let s6 := inp.s6
  let s7 := inp.s7
  let p28 := p11 ^^^ p25
  let s2 := p17 ^^^ p28
  ⟨s7, s6, s5, s4, s3, s2, s1, s0⟩

/-- Bitsliced inverse S-box (`fixslice64::inv_sub_bytes`, exact inverse of `subBytesFs`). -/
@[expose] def invSubBytesFs (st : FsState) : FsState :=
  invSubBytesFsStage6 (invSubBytesFsStage5 (invSubBytesFsStage4 (invSubBytesFsStage3 (invSubBytesFsStage2 (invSubBytesFsStage1 st)))))

/-! ## Bitsliced `ShiftRows` and `InvShiftRows` Powers (lines 950–992) -/

@[expose] def shiftRows1 (st : FsState) : FsState :=
  st.map fun x =>
    deltaSwap1 (deltaSwap1 x 8 0x00f000ff000f0000#64) 4 0x0f0f00000f0f0000#64

@[expose] def shiftRows2 (st : FsState) : FsState :=
  st.map fun x => deltaSwap1 x 8 0x00ff000000ff0000#64

@[expose] def shiftRows3 (st : FsState) : FsState :=
  st.map fun x =>
    deltaSwap1 (deltaSwap1 x 8 0x000f00ff00f00000#64) 4 0x0f0f00000f0f0000#64

@[expose] def invShiftRows1 (st : FsState) : FsState := shiftRows3 st
@[expose] def invShiftRows2 (st : FsState) : FsState := shiftRows2 st
@[expose] def invShiftRows3 (st : FsState) : FsState := shiftRows1 st

/-! ## Fixsliced `MixColumns` and `InvMixColumns` Variants (lines 994–1150) -/

/-- Generic fixsliced `MixColumns` body parameterized by row-1 and row-2 rotations. -/
@[expose] def mixColumnsGen (rot1 rot2 : BitVec 64 → BitVec 64) (st : FsState) : FsState :=
  let b0 := rot1 st.s0; let c0 := st.s0 ^^^ b0
  let b1 := rot1 st.s1; let c1 := st.s1 ^^^ b1
  let b2 := rot1 st.s2; let c2 := st.s2 ^^^ b2
  let b3 := rot1 st.s3; let c3 := st.s3 ^^^ b3
  let b4 := rot1 st.s4; let c4 := st.s4 ^^^ b4
  let b5 := rot1 st.s5; let c5 := st.s5 ^^^ b5
  let b6 := rot1 st.s6; let c6 := st.s6 ^^^ b6
  let b7 := rot1 st.s7; let c7 := st.s7 ^^^ b7
  ⟨b0 ^^^ c7 ^^^ rot2 c0,
   b1 ^^^ c0 ^^^ c7 ^^^ rot2 c1,
   b2 ^^^ c1 ^^^ rot2 c2,
   b3 ^^^ c2 ^^^ c7 ^^^ rot2 c3,
   b4 ^^^ c3 ^^^ c7 ^^^ rot2 c4,
   b5 ^^^ c4 ^^^ rot2 c5,
   b6 ^^^ c5 ^^^ rot2 c6,
   b7 ^^^ c6 ^^^ rot2 c7⟩

@[expose] def mixColumns0 (st : FsState) : FsState := mixColumnsGen rotateRows1 rotateRows2 st
@[expose] def mixColumns1 (st : FsState) : FsState :=
  mixColumnsGen rotateRowsAndColumns11 rotateRowsAndColumns22 st
@[expose] def mixColumns2 (st : FsState) : FsState :=
  mixColumnsGen rotateRowsAndColumns12 rotateRows2 st
@[expose] def mixColumns3 (st : FsState) : FsState :=
  mixColumnsGen rotateRowsAndColumns13 rotateRowsAndColumns22 st

/-- Generic fixsliced `InvMixColumns` body parameterized by row-1 and row-2 rotations. -/
@[expose] def invMixColumnsGen (rot1 rot2 : BitVec 64 → BitVec 64) (st : FsState) : FsState :=
  let b0 := rot1 st.s0; let c0 := st.s0 ^^^ b0
  let b1 := rot1 st.s1; let c1 := st.s1 ^^^ b1
  let b2 := rot1 st.s2; let c2 := st.s2 ^^^ b2
  let b3 := rot1 st.s3; let c3 := st.s3 ^^^ b3
  let b4 := rot1 st.s4; let c4 := st.s4 ^^^ b4
  let b5 := rot1 st.s5; let c5 := st.s5 ^^^ b5
  let b6 := rot1 st.s6; let c6 := st.s6 ^^^ b6
  let b7 := rot1 st.s7; let c7 := st.s7 ^^^ b7
  let d0 := st.s0 ^^^ c7
  let d1 := st.s1 ^^^ c0 ^^^ c7
  let d2 := st.s2 ^^^ c1
  let d3 := st.s3 ^^^ c2 ^^^ c7
  let d4 := st.s4 ^^^ c3 ^^^ c7
  let d5 := st.s5 ^^^ c4
  let d6 := st.s6 ^^^ c5
  let d7 := st.s7 ^^^ c6
  let e0 := c0 ^^^ d6
  let e1 := c1 ^^^ d6 ^^^ d7
  let e2 := c2 ^^^ d0 ^^^ d7
  let e3 := c3 ^^^ d1 ^^^ d6
  let e4 := c4 ^^^ d2 ^^^ d6 ^^^ d7
  let e5 := c5 ^^^ d3 ^^^ d7
  let e6 := c6 ^^^ d4
  let e7 := c7 ^^^ d5
  ⟨d0 ^^^ e0 ^^^ rot2 e0,
   d1 ^^^ e1 ^^^ rot2 e1,
   d2 ^^^ e2 ^^^ rot2 e2,
   d3 ^^^ e3 ^^^ rot2 e3,
   d4 ^^^ e4 ^^^ rot2 e4,
   d5 ^^^ e5 ^^^ rot2 e5,
   d6 ^^^ e6 ^^^ rot2 e6,
   d7 ^^^ e7 ^^^ rot2 e7⟩

@[expose] def invMixColumns0 (st : FsState) : FsState := invMixColumnsGen rotateRows1 rotateRows2 st
@[expose] def invMixColumns1 (st : FsState) : FsState :=
  invMixColumnsGen rotateRowsAndColumns11 rotateRowsAndColumns22 st
@[expose] def invMixColumns2 (st : FsState) : FsState :=
  invMixColumnsGen rotateRowsAndColumns12 rotateRows2 st
@[expose] def invMixColumns3 (st : FsState) : FsState :=
  invMixColumnsGen rotateRowsAndColumns13 rotateRowsAndColumns22 st

/-! ## Round-Key Addition, `xor_columns`, Key Schedule, Encrypt, and Decrypt -/

/-- `add_round_key` (`fixslice64.rs` line 1362). -/
@[expose] def addRoundKeyFs (st rkey : FsState) : FsState :=
  st.zipWith (· ^^^ ·) rkey

/-- `add_round_constant_bit` (`fixslice64.rs` line 1370). -/
@[expose] def addRoundConstantBit (st : FsState) : Nat → FsState
  | 0 => { st with s0 := st.s0 ^^^ 0x00000000f0000000#64 }
  | 1 => { st with s1 := st.s1 ^^^ 0x00000000f0000000#64 }
  | 2 => { st with s2 := st.s2 ^^^ 0x00000000f0000000#64 }
  | 3 => { st with s3 := st.s3 ^^^ 0x00000000f0000000#64 }
  | 4 => { st with s4 := st.s4 ^^^ 0x00000000f0000000#64 }
  | 5 => { st with s5 := st.s5 ^^^ 0x00000000f0000000#64 }
  | 6 => { st with s6 := st.s6 ^^^ 0x00000000f0000000#64 }
  | 7 => { st with s7 := st.s7 ^^^ 0x00000000f0000000#64 }
  | _ => st

/-- Single-slice `xor_columns` step (`fixslice64.rs` lines 1184–1188). -/
@[expose] def xorColumnWord (prev cur : BitVec 64) (idxRor : Nat) : BitVec 64 :=
  let rk := prev ^^^ (0x000f000f000f000f#64 &&& ror64 cur idxRor)
  rk ^^^ (0xfff0fff0fff0fff0#64 &&& (rk <<< 4))
     ^^^ (0xff00ff00ff00ff00#64 &&& (rk <<< 8))
     ^^^ (0xf000f000f000f000#64 &&& (rk <<< 12))

/-- 8-slice `xor_columns` on `(rkeys[offset - idx_xor ..], rkeys[offset ..])` (`fixslice64.rs` line 1181). -/
@[expose] def xorColumnsFs (prev cur : FsState) (idxRor : Nat) : FsState :=
  prev.zipWith (fun p c => xorColumnWord p c idxRor) cur

/-- Even-round key-schedule step (`memshift32` + `sub_bytes` + `sub_bytes_nots` + `rcon` + `xor_columns(16, ror(1,3))`). -/
@[expose] def ksEvenStep (rkPrev2 rkPrev1 : FsState) (rconBit : Nat) : FsState :=
  let t := addRoundConstantBit (subBytesNots (subBytesFs rkPrev1)) rconBit
  xorColumnsFs rkPrev2 t (rorDistance 1 3)

/-- Odd-round key-schedule step (`memshift32` + `sub_bytes` + `sub_bytes_nots` + `xor_columns(16, ror(0,3))`). -/
@[expose] def ksOddStep (rkPrev2 rkPrev1 : FsState) : FsState :=
  let t := subBytesNots (subBytesFs rkPrev1)
  xorColumnsFs rkPrev2 t (rorDistance 0 3)

/-- Fully bitsliced AES-256 key schedule (`fixslice64::aes256_key_schedule`, lines 195–263). -/
@[expose] def aes256KeyScheduleFs (key : List (BitVec 8)) : FsKeys256 :=
  let k0 := key.take 16
  let k1 := key.drop 16
  let rk0 := bitslice (Blocks4.replicate k0)
  let rk1Raw := bitslice (Blocks4.replicate k1)
  let rk2Raw := ksEvenStep rk0 rk1Raw 0
  let rk3Raw := ksOddStep rk1Raw rk2Raw
  let rk4Raw := ksEvenStep rk2Raw rk3Raw 1
  let rk5Raw := ksOddStep rk3Raw rk4Raw
  let rk6Raw := ksEvenStep rk4Raw rk5Raw 2
  let rk7Raw := ksOddStep rk5Raw rk6Raw
  let rk8Raw := ksEvenStep rk6Raw rk7Raw 3
  let rk9Raw := ksOddStep rk7Raw rk8Raw
  let rk10Raw := ksEvenStep rk8Raw rk9Raw 4
  let rk11Raw := ksOddStep rk9Raw rk10Raw
  let rk12Raw := ksEvenStep rk10Raw rk11Raw 5
  let rk13Raw := ksOddStep rk11Raw rk12Raw
  let rk14Raw := ksEvenStep rk12Raw rk13Raw 6
  ⟨rk0,
   subBytesNots (invShiftRows1 rk1Raw),
   subBytesNots (invShiftRows2 rk2Raw),
   subBytesNots (invShiftRows3 rk3Raw),
   subBytesNots rk4Raw,
   subBytesNots (invShiftRows1 rk5Raw),
   subBytesNots (invShiftRows2 rk6Raw),
   subBytesNots (invShiftRows3 rk7Raw),
   subBytesNots rk8Raw,
   subBytesNots (invShiftRows1 rk9Raw),
   subBytesNots (invShiftRows2 rk10Raw),
   subBytesNots (invShiftRows3 rk11Raw),
   subBytesNots rk12Raw,
   subBytesNots (invShiftRows1 rk13Raw),
   subBytesNots rk14Raw⟩

/-- Select `mixColumns0..3` by parity `q % 4`. -/
@[expose] def mixColumnsQ : Nat → FsState → FsState
  | 0 => mixColumns0
  | 1 => mixColumns1
  | 2 => mixColumns2
  | _ => mixColumns3

/-- Select `invMixColumns0..3` by parity `q % 4`. -/
@[expose] def invMixColumnsQ : Nat → FsState → FsState
  | 0 => invMixColumns0
  | 1 => invMixColumns1
  | 2 => invMixColumns2
  | _ => invMixColumns3

/-- One fixsliced encryption round `r` (`1 ≤ r ≤ 13`), applying `sub_bytes`, `mix_columns_{r % 4}`,
and `add_round_key` (`fixslice64::aes256_encrypt`, lines 544–576). -/
@[expose] def encRoundFs (rkeys : FsKeys256) (r : Nat) (st : FsState) : FsState :=
  addRoundKeyFs (mixColumnsQ (r % 4) (subBytesFs st)) (rkeys.getRound r)

/-- Fully-fixsliced 4-block AES-256 encryption (`fixslice64::aes256_encrypt`, lines 536–587). -/
@[expose] def aes256EncryptFs (rkeys : FsKeys256) (blocks : Blocks4) : Blocks4 :=
  let st0 := addRoundKeyFs (bitslice blocks) rkeys.rk0
  let st13 := (List.range 13).foldl (fun st i => encRoundFs rkeys (i + 1) st) st0
  let stFinal := addRoundKeyFs (subBytesFs (shiftRows2 st13)) rkeys.rk14
  invBitslice stFinal

/-- One fixsliced decryption round `r` (`13` down to `1`), applying `add_round_key`,
`inv_mix_columns_{r % 4}`, and `inv_sub_bytes` (`fixslice64::aes256_decrypt`, lines 493–526). -/
@[expose] def decRoundFs (rkeys : FsKeys256) (r : Nat) (st : FsState) : FsState :=
  invSubBytesFs (invMixColumnsQ (r % 4) (addRoundKeyFs st (rkeys.getRound r)))

/-- Fully-fixsliced 4-block AES-256 decryption (`fixslice64::aes256_decrypt`, lines 478–531). -/
@[expose] def aes256DecryptFs (rkeys : FsKeys256) (blocks : Blocks4) : Blocks4 :=
  let st0 := invShiftRows2 (invSubBytesFs (addRoundKeyFs (bitslice blocks) rkeys.rk14))
  let st1 := (List.range 13).foldl (fun st i => decRoundFs rkeys (13 - i) st) st0
  invBitslice (addRoundKeyFs st1 rkeys.rk0)

/-! ## Sanity Vector Checks (`#guard`) -/

private def katKey : List (BitVec 8) :=
  [0x00#8, 0x01#8, 0x02#8, 0x03#8, 0x04#8, 0x05#8, 0x06#8, 0x07#8,
   0x08#8, 0x09#8, 0x0a#8, 0x0b#8, 0x0c#8, 0x0d#8, 0x0e#8, 0x0f#8,
   0x10#8, 0x11#8, 0x12#8, 0x13#8, 0x14#8, 0x15#8, 0x16#8, 0x17#8,
   0x18#8, 0x19#8, 0x1a#8, 0x1b#8, 0x1c#8, 0x1d#8, 0x1e#8, 0x1f#8]

private def katBlocks : Blocks4 :=
  ⟨[0x00#8, 0x11#8, 0x22#8, 0x33#8, 0x44#8, 0x55#8, 0x66#8, 0x77#8,
    0x88#8, 0x99#8, 0xaa#8, 0xbb#8, 0xcc#8, 0xdd#8, 0xee#8, 0xff#8],
   List.ofFn (fun i : Fin 16 => BitVec.ofNat 8 (i.val * 17)),
   List.ofFn (fun i : Fin 16 => BitVec.ofNat 8 (255 - i.val * 13)),
   List.ofFn (fun i : Fin 16 => BitVec.ofNat 8 (i.val * 7 + 3))⟩

private def katFipsC3Ct : State :=
  [0x8e#8, 0xa2#8, 0xb7#8, 0xca#8, 0x51#8, 0x67#8, 0x45#8, 0xbf#8,
   0xea#8, 0xfc#8, 0x49#8, 0x90#8, 0x4b#8, 0x49#8, 0x60#8, 0x89#8]

#guard (aes256EncryptFs (aes256KeyScheduleFs katKey) katBlocks).b0 == katFipsC3Ct

#guard
  let rks := aes256KeyScheduleFs katKey
  let dec := aes256DecryptFs rks (aes256EncryptFs rks katBlocks)
  dec.b0 == katBlocks.b0 && dec.b1 == katBlocks.b1 &&
  dec.b2 == katBlocks.b2 && dec.b3 == katBlocks.b3

#guard (aes256DecryptFs (aes256KeyScheduleFs katKey) ⟨katFipsC3Ct, katBlocks.b1, katBlocks.b2, katBlocks.b3⟩).b0 ==
  katBlocks.b0

end LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.Model
