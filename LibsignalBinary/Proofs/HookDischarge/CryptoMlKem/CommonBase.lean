/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.SepLogic.WP.StepsProcess
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import

/-!
# Shared Cross-Block Contracts and Process-Preservation Wrappers (`CommonBase`)

- `withNonSyscallPreserved`: adjoins `ProofLib.NonSyscallPreserved s0 sf` (giving `sf.trace = s0.trace`,
  `sf.fs = s0.fs`, `sf.mem.perm = s0.mem.perm`, `VmPreserved s0 sf`, and `MlKemRoOk` preservation)
  to any `Spec α`.
- Shared `Spec` definitions for `Layer0` (`B28`–`B31`: `memcpy`, `memset`, `bcmp`, `memcmp`) and
  `Keccak` (`B00` `keccak2::<72, 6>`, `B01` `keccak2::<136, 31>`, `B02` `keccak2::<136, 6>`,
  in both read-only `↦ᵣ` and read-write stack-buffer `↦ₛ` specializations).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  sha3_256List
  sha3_512List
  shake256List
)

/-! ## 1. `NonSyscallPreserved` Wrapper -/

/-- Adjoin `⌜ProofLib.NonSyscallPreserved s0 sf⌝` to `spec.post`. -/
@[expose] def withNonSyscallPreserved {α : Type} (spec : Spec α) : Spec α :=
  { spec with post := fun x s0 sf => ⌜ProofLib.NonSyscallPreserved s0 sf⌝ ∗ spec.post x s0 sf }

/-! ## 1b. Zero-Stack `Layer0` Memory-Operation Contracts (`B28`–`B31`) -/

/-- Zero-stack `B28` (`memcpy`) contract with read-only source `src ↦ᵣ bs` and
    `NonSyscallPreserved s0 sf`. -/
@[expose] def mlkemMemcpyROSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
      s0.readReg64 .x1 = src ∧
      (s0.readReg64 .x2).toNat = bs.length ∧
      bs.length < 2 ^ 64⌝ ∗
      memRegion dst bs.length ∗ (src ↦ᵣ bs)
  post := fun (dst, src, bs) s0 sf =>
    ⌜ProofLib.NonSyscallPreserved s0 sf ∧ sf.readReg64 .x0 = dst⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ᵣ bs)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Zero-stack `B28` (`memcpy`) contract with read-write source `src ↦ₛ bs` and
    `NonSyscallPreserved s0 sf`. -/
@[expose] def mlkemMemcpySpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
      s0.readReg64 .x1 = src ∧
      (s0.readReg64 .x2).toNat = bs.length ∧
      bs.length < 2 ^ 64⌝ ∗
      memRegion dst bs.length ∗ (src ↦ₛ bs)
  post := fun (dst, src, bs) s0 sf =>
    ⌜ProofLib.NonSyscallPreserved s0 sf ∧ sf.readReg64 .x0 = dst⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ₛ bs)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Zero-stack `B29` (`memset`) contract with `NonSyscallPreserved s0 sf`. -/
@[expose] def mlkemMemsetSpec : Spec (BitVec 64 × BitVec 8 × Nat) where
  pre := fun (ptr, c, len) s0 =>
    ⌜s0.readReg64 .x0 = ptr ∧
      (s0.readReg32 .x1).truncate 8 = c ∧
      (s0.readReg64 .x2).toNat = len ∧
      len < 2 ^ 64⌝ ∗
      memRegion ptr len
  post := fun (ptr, c, len) s0 sf =>
    ⌜ProofLib.NonSyscallPreserved s0 sf ∧ sf.readReg64 .x0 = ptr⌝ ∗
      (ptr ↦ₛ List.replicate len c)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Zero-stack `B30` (`bcmp`) / `B31` (`memcmp`) read-only contract preserving `mem`, `vregs`,
    and `NonSyscallPreserved s0 sf`. -/
@[expose] def mlkemBcmpROSpec :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) where
  pre := fun (p, q, bs, cs) s0 =>
    ⌜s0.readReg64 .x0 = p ∧
      s0.readReg64 .x1 = q ∧
      (s0.readReg64 .x2).toNat = bs.length ∧
      cs.length = bs.length ∧
      bs.length < 2 ^ 64⌝ ∗
      (p ↦ᵣ bs) ∗ (q ↦ᵣ cs)
  post := fun (p, q, bs, cs) s0 sf =>
    ⌜ProofLib.NonSyscallPreserved s0 sf ∧
      sf.mem = s0.mem ∧
      sf.vregs = s0.vregs ∧
      (sf.readReg32 .x0 = 0#32 ↔ bs = cs)⌝ ∗
      (p ↦ᵣ bs) ∗ (q ↦ᵣ cs)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Zero-stack `B30` (`bcmp`) mixed RW/RO specialization (`p ↦ₛ bs`, `q ↦ᵣ cs`), used by
    `validate_pk_bytes` (`B21`). -/
@[expose] def mlkemBcmpRW1ROSpec :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) where
  pre := fun (p, q, bs, cs) s0 =>
    ⌜s0.readReg64 .x0 = p ∧
      s0.readReg64 .x1 = q ∧
      (s0.readReg64 .x2).toNat = bs.length ∧
      cs.length = bs.length ∧
      bs.length < 2 ^ 64⌝ ∗
      (p ↦ₛ bs) ∗ (q ↦ᵣ cs)
  post := fun (p, q, bs, cs) s0 sf =>
    ⌜ProofLib.NonSyscallPreserved s0 sf ∧
      sf.mem = s0.mem ∧
      sf.vregs = s0.vregs ∧
      (sf.readReg32 .x0 = 0#32 ↔ bs = cs)⌝ ∗
      (p ↦ₛ bs) ∗ (q ↦ᵣ cs)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-! ## 2. 2-Way SIMD Keccak (`B00`, `B01`, `B02`) Shared Cross-Block Contracts -/

/-- Read-only 32-byte `&[&[u8]; 2]` fat-slice descriptor array at `slicesPtr`:
    `[(ptr0, len0), (ptr1, len1)]`. -/
@[expose] def Keccak2SlicesRO (slicesPtr ptr0 ptr1 : BitVec 64) (len0 len1 : Nat) : SepProp :=
  (slicesPtr ↦₆₄ᵣ ptr0) ∗
  ((slicesPtr + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 len0) ∗
  ((slicesPtr + 16#64) ↦₆₄ᵣ ptr1) ∗
  ((slicesPtr + 24#64) ↦₆₄ᵣ BitVec.ofNat 64 len1)

/-- Read-write 32-byte `&[&[u8]; 2]` fat-slice descriptor array at `slicesPtr`:
    `[(ptr0, len0), (ptr1, len1)]`. -/
@[expose] def Keccak2SlicesRW (slicesPtr ptr0 ptr1 : BitVec 64) (len0 len1 : Nat) : SepProp :=
  (slicesPtr ↦₆₄ ptr0) ∗
  ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 len0) ∗
  ((slicesPtr + 16#64) ↦₆₄ ptr1) ∗
  ((slicesPtr + 24#64) ↦₆₄ BitVec.ofNat 64 len1)

/-- Arguments to `B00` (`keccak2::<72, 6>`, 2-way `SHA3-512`) and `B02` (`keccak2::<136, 6>`,
    2-way `SHA3-256`). -/
structure Keccak2FixedArgs where
  slicesPtr : BitVec 64
  ptr0      : BitVec 64
  ptr1      : BitVec 64
  out0      : BitVec 64
  out1      : BitVec 64
  in0       : List (BitVec 8)
  in1       : List (BitVec 8)

/-- Arguments to `B01` (`keccak2::<136, 31>`, 2-way `SHAKE-256`). -/
structure Keccak2ShakeArgs where
  slicesPtr : BitVec 64
  ptr0      : BitVec 64
  ptr1      : BitVec 64
  out0      : BitVec 64
  out1      : BitVec 64
  outLen    : Nat
  in0       : List (BitVec 8)
  in1       : List (BitVec 8)

/-- `B00` (`libcrux_sha3::generic_keccak::simd128::keccak2::<72, 6>`, 2-way `SHA3-512`)
    read-only input specification (`in0.length = in1.length < 72`, `720`-byte stack frame;
    covers all 5 call sites in `B03`–`B07` where `inLen ∈ {33, 64}`). -/
@[expose] def keccak2_72_6_Spec (mpl : MultiPlacement) : Spec Keccak2FixedArgs where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.slicesPtr ∧
      s0.readReg64 .x1 = a.out0 ∧
      s0.readReg64 .x2 = a.out1 ∧
      a.in0.length = a.in1.length ∧
      a.in0.length < 72 ∧
      MlKemRoOk mpl s0.mem⌝ ∗
      Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
      (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗
      memRegion a.out0 64 ∗ memRegion a.out1 64 ∗
      stackAt s0.sp 720
  post := fun a s0 _sf =>
    Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
      (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗
      (a.out0 ↦ₛ sha3_512List a.in0) ∗ (a.out1 ↦ₛ sha3_512List a.in1) ∗
      stackAt s0.sp 720
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- `B00` aliased single-buffer RW specialization (`ptr0 = ptr1`, `in0 = in1`), derived from
    `keccak2_72_6_Spec` + `NoSvcLift` for stack-allocated `G(d || K)` and `G(m || H(pk))` calls. -/
@[expose] def keccak2_72_6_RW1Spec (mpl : MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (slicesPtr, ptr, out0, out1, msg) s0 =>
    ⌜s0.readReg64 .x0 = slicesPtr ∧
      s0.readReg64 .x1 = out0 ∧
      s0.readReg64 .x2 = out1 ∧
      msg.length < 72 ∧
      MlKemRoOk mpl s0.mem⌝ ∗
      Keccak2SlicesRW slicesPtr ptr ptr msg.length msg.length ∗
      (ptr ↦ₛ msg) ∗
      memRegion out0 64 ∗ memRegion out1 64 ∗
      stackAt s0.sp 720
  post := fun (slicesPtr, ptr, out0, out1, msg) s0 sf =>
    ⌜ProofLib.NonSyscallPreserved s0 sf⌝ ∗
      Keccak2SlicesRW slicesPtr ptr ptr msg.length msg.length ∗
      (ptr ↦ₛ msg) ∗
      (out0 ↦ₛ sha3_512List msg) ∗ (out1 ↦ₛ sha3_512List msg) ∗
      stackAt s0.sp 720
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- `B02` (`libcrux_sha3::generic_keccak::simd128::keccak2::<136, 6>`, 2-way `SHA3-256`)
    read-only input specification (`in0.length = in1.length < 2 ^ 32`, `1040`-byte stack frame). -/
@[expose] def keccak2_136_6_Spec (mpl : MultiPlacement) : Spec Keccak2FixedArgs where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.slicesPtr ∧
      s0.readReg64 .x1 = a.out0 ∧
      s0.readReg64 .x2 = a.out1 ∧
      a.in0.length = a.in1.length ∧
      a.in0.length < 2 ^ 32 ∧
      MlKemRoOk mpl s0.mem⌝ ∗
      Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
      (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗
      memRegion a.out0 32 ∗ memRegion a.out1 32 ∗
      stackAt s0.sp 1040
  post := fun a s0 _sf =>
    Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
      (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗
      (a.out0 ↦ₛ sha3_256List a.in0) ∗ (a.out1 ↦ₛ sha3_256List a.in1) ∗
      stackAt s0.sp 1040
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- `B02` aliased single-buffer RW specialization (`ptr0 = ptr1`, `in0 = in1`), used directly by
    `validate_pk_bytes` (`B21`), `from_seed` (`B05`), `kyber_decapsulate` (`B06`), and
    `kyber_encapsulate` (`B07`) when hashing a stack-allocated buffer. -/
@[expose] def keccak2_136_6_RW1Spec (mpl : MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (slicesPtr, ptr, out0, out1, msg) s0 =>
    ⌜s0.readReg64 .x0 = slicesPtr ∧
      s0.readReg64 .x1 = out0 ∧
      s0.readReg64 .x2 = out1 ∧
      msg.length < 2 ^ 32 ∧
      MlKemRoOk mpl s0.mem⌝ ∗
      Keccak2SlicesRW slicesPtr ptr ptr msg.length msg.length ∗
      (ptr ↦ₛ msg) ∗
      memRegion out0 32 ∗ memRegion out1 32 ∗
      stackAt s0.sp 1040
  post := fun (slicesPtr, ptr, out0, out1, msg) s0 sf =>
    ⌜ProofLib.NonSyscallPreserved s0 sf⌝ ∗
      Keccak2SlicesRW slicesPtr ptr ptr msg.length msg.length ∗
      (ptr ↦ₛ msg) ∗
      (out0 ↦ₛ sha3_256List msg) ∗ (out1 ↦ₛ sha3_256List msg) ∗
      stackAt s0.sp 1040
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- `B01` (`libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>`, 2-way `SHAKE-256`)
    read-only input specification (`in0.length = in1.length < 2 ^ 32`, `outLen = 32 ∨ outLen = 128`,
    `1136`-byte stack frame; covers all PRF `128`-byte and FO implicit-rejection `32`-byte calls
    across `B03`–`B07`). -/
@[expose] def keccak2_136_31_Spec (mpl : MultiPlacement) : Spec Keccak2ShakeArgs where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.slicesPtr ∧
      s0.readReg64 .x1 = a.out0 ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 a.outLen ∧
      s0.readReg64 .x3 = a.out1 ∧
      s0.readReg64 .x4 = BitVec.ofNat 64 a.outLen ∧
      a.in0.length = a.in1.length ∧
      a.in0.length < 2 ^ 32 ∧
      (a.outLen = 32 ∨ a.outLen = 128) ∧
      MlKemRoOk mpl s0.mem⌝ ∗
      Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
      (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗
      memRegion a.out0 a.outLen ∗ memRegion a.out1 a.outLen ∗
      stackAt s0.sp 1136
  post := fun a s0 _sf =>
    Keccak2SlicesRO a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
      (a.ptr0 ↦ᵣ a.in0) ∗ (a.ptr1 ↦ᵣ a.in1) ∗
      (a.out0 ↦ₛ shake256List a.outLen a.in0) ∗
      (a.out1 ↦ₛ shake256List a.outLen a.in1) ∗
      stackAt s0.sp 1136
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- `B01` distinct two-buffer RW specialization (`ptr0` and `ptr1` disjoint RW stack buffers),
    used for 2-way PRF calls `PRF(sigma || n0)` and `PRF(sigma || n1)`. -/
@[expose] def keccak2_136_31_RW2Spec (mpl : MultiPlacement) : Spec Keccak2ShakeArgs where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.slicesPtr ∧
      s0.readReg64 .x1 = a.out0 ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 a.outLen ∧
      s0.readReg64 .x3 = a.out1 ∧
      s0.readReg64 .x4 = BitVec.ofNat 64 a.outLen ∧
      a.in0.length = a.in1.length ∧
      a.in0.length < 2 ^ 32 ∧
      (a.outLen = 32 ∨ a.outLen = 128) ∧
      MlKemRoOk mpl s0.mem⌝ ∗
      Keccak2SlicesRW a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
      (a.ptr0 ↦ₛ a.in0) ∗ (a.ptr1 ↦ₛ a.in1) ∗
      memRegion a.out0 a.outLen ∗ memRegion a.out1 a.outLen ∗
      stackAt s0.sp 1136
  post := fun a s0 sf =>
    ⌜ProofLib.NonSyscallPreserved s0 sf⌝ ∗
      Keccak2SlicesRW a.slicesPtr a.ptr0 a.ptr1 a.in0.length a.in1.length ∗
      (a.ptr0 ↦ₛ a.in0) ∗ (a.ptr1 ↦ₛ a.in1) ∗
      (a.out0 ↦ₛ shake256List a.outLen a.in0) ∗
      (a.out1 ↦ₛ shake256List a.outLen a.in1) ∗
      stackAt s0.sp 1136
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- `B01` aliased single-buffer RW specialization (`ptr0 = ptr1`, `in0 = in1`), used for odd PRF
    calls and FO implicit-rejection `SHAKE-256(z || ct)`. -/
@[expose] def keccak2_136_31_RW1Spec (mpl : MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × Nat × List (BitVec 8)) where
  pre := fun (slicesPtr, ptr, out0, out1, outLen, msg) s0 =>
    ⌜s0.readReg64 .x0 = slicesPtr ∧
      s0.readReg64 .x1 = out0 ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 outLen ∧
      s0.readReg64 .x3 = out1 ∧
      s0.readReg64 .x4 = BitVec.ofNat 64 outLen ∧
      msg.length < 2 ^ 32 ∧
      (outLen = 32 ∨ outLen = 128) ∧
      MlKemRoOk mpl s0.mem⌝ ∗
      Keccak2SlicesRW slicesPtr ptr ptr msg.length msg.length ∗
      (ptr ↦ₛ msg) ∗
      memRegion out0 outLen ∗ memRegion out1 outLen ∗
      stackAt s0.sp 1136
  post := fun (slicesPtr, ptr, out0, out1, outLen, msg) s0 sf =>
    ⌜ProofLib.NonSyscallPreserved s0 sf⌝ ∗
      Keccak2SlicesRW slicesPtr ptr ptr msg.length msg.length ∗
      (ptr ↦ₛ msg) ∗
      (out0 ↦ₛ shake256List outLen msg) ∗
      (out1 ↦ₛ shake256List outLen msg) ∗
      stackAt s0.sp 1136
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
