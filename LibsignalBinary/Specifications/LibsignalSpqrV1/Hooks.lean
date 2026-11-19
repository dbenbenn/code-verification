/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem
public import LibsignalBinary.Specifications.LibsignalSpqrV1.TokenNames
public import LibsignalBinary.Specifications.LibsignalTripleRatchet

/-!
# SPQR V1: extern-stub contracts (`SpqrHooks`) and `TOKEN` cell symbols

**Checked by Lean.** Proof-side definitions for SPQR V1 extern-stub symbol names and `Spec`
contracts (`mlkemFromSeedSpec`, `mlkemPk1Spec`, `mlkemPk2Spec`, `mlkemEncaps1Spec`,
`mlkemEncaps2Spec`, `mlkemDecapsSpec`, `mlkemValidatePkSpec`, `libcruxHmacSpec`, plus
`onceCallName`) bundled as `SpqrHooks`. The two statement-used CPU feature-detection cell symbol
names `tokenStorageName` and `tokenName` (DEV-SPQR1) live in `TokenNames.lean` and are re-exported
here.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqrV1

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet

/-! ## 1. Extern Stub Symbols -/

/-- `<libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes>::from_seed`. -/
abbrev mlkemFromSeedName : String :=
  "<libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes>::from_seed"

/-- `<libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes>::pk1`. -/
abbrev mlkemPk1Name : String :=
  "<libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes>::pk1"

/-- `<libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes>::pk2`. -/
abbrev mlkemPk2Name : String :=
  "<libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes>::pk2"

/-- `libcrux_ml_kem::mlkem768::incremental::encapsulate1`. -/
abbrev mlkemEncaps1Name : String :=
  "libcrux_ml_kem::mlkem768::incremental::encapsulate1"

/-- `libcrux_ml_kem::mlkem768::incremental::validate_pk_bytes`. -/
abbrev mlkemValidatePkName : String :=
  "libcrux_ml_kem::mlkem768::incremental::validate_pk_bytes"

/-- `libcrux_hmac::hmac`. -/
abbrev libcruxHmacName : String :=
  "libcrux_hmac::hmac"

/-- `libcrux_ml_kem::mlkem768::incremental::encapsulate2`. -/
abbrev mlkemEncaps2Name : String :=
  "libcrux_ml_kem::mlkem768::incremental::encapsulate2"

/-- `libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key`. -/
abbrev mlkemDecapsName : String :=
  "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key"

/-- `<std::sys::sync::once::futex::Once>::call`.
Unreachable when the `TOKEN` `Once` state word holds `0#32` (`futex::Once::COMPLETE`). -/
abbrev onceCallName : String :=
  "<std::sys::sync::once::futex::Once>::call"

/-! ## 2. `TOKEN` & `STORAGE.0` Symbols -/

-- `tokenStorageName` and `tokenName` are defined in `TokenNames.lean` (`public import`ed above).

/-! ## 3. ML-KEM-768 Incremental Hook Specifications

`KeyPairCompressedBytes` is a 2400-byte array (`dk`), with `pk1` slicing `2304..2368` (`pk1Off`)
and `pk2` slicing `1152..2304` (`pk2Off`); `MlKem.fromSeed` has the same slice structure, making
`SpqrHooks.fromSeed_pk1` and `SpqrHooks.fromSeed_pk2` definitional equalities. -/

/-- Ghost state for `<KeyPairCompressedBytes>::from_seed`. -/
structure MlkemFromSeedCall where
  seedA : BitVec 64
  kpA : BitVec 64
  seed : List.Vector (BitVec 8) 64

/-- Spec for `<KeyPairCompressedBytes>::from_seed`.
* `x0 = seedA`: pointer to 64-byte seed (`[u8; 64]` passed by value via indirect pointer).
* `x8 = kpA`: sret pointer to 2400-byte `KeyPairCompressedBytes` buffer (`dk`). -/
def mlkemFromSeedSpec (K : MlKem) : Spec MlkemFromSeedCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.seedA ∧ s.readReg64 .x8 = x.kpA⌝ ∗
      (x.seedA ↦ₛ x.seed.toList) ∗ memRegion x.kpA 2400 ∗ stackAt s.sp extHookStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.seedA ↦ₛ x.seed.toList) ∗
      (x.kpA ↦ₛ (K.fromSeed x.seed).2.2.toList) ∗
      stackAt s0.sp extHookStack

/-- Ghost state for `<KeyPairCompressedBytes>::pk1` and `pk2`: `(kpA, kp)`. -/
structure MlkemKpRefCall where
  kpA : BitVec 64
  kp : List.Vector (BitVec 8) 2400

/-- Spec for `<KeyPairCompressedBytes>::pk1`.
* `x0 = kpA`: `&KeyPairCompressedBytes` (2400 bytes).
* Returns `x0 = kpA + pk1Off` (`&[u8; 64]` pointing to bytes `2304..2368` of `kp`). -/
def mlkemPk1Spec : Spec MlkemKpRefCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.kpA⌝ ∗ (x.kpA ↦ₛ x.kp.toList) ∗ stackAt s.sp extHookStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = x.kpA + BitVec.ofNat 64 pk1Off ∧ sf.trace = s0.trace⌝ ∗
      (x.kpA ↦ₛ x.kp.toList) ∗ stackAt s0.sp extHookStack

/-- Spec for `<KeyPairCompressedBytes>::pk2`.
* `x0 = kpA`: `&KeyPairCompressedBytes` (2400 bytes).
* Returns `x0 = kpA + pk2Off` (`&[u8; 1152]` pointing to bytes `1152..2304` of `kp`). -/
def mlkemPk2Spec : Spec MlkemKpRefCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.kpA⌝ ∗ (x.kpA ↦ₛ x.kp.toList) ∗ stackAt s.sp extHookStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = x.kpA + BitVec.ofNat 64 pk2Off ∧ sf.trace = s0.trace⌝ ∗
      (x.kpA ↦ₛ x.kp.toList) ∗ stackAt s0.sp extHookStack

/-- Ghost state for `encapsulate1`. -/
structure MlkemEncaps1Call where
  ret : BitVec 64
  hdrA : BitVec 64
  hdr : List (BitVec 8)
  randA : BitVec 64
  rand : List.Vector (BitVec 8) 32
  esA : BitVec 64
  ssA : BitVec 64

/-- Spec for `libcrux_ml_kem::mlkem768::incremental::encapsulate1`.
* `x8 = ret`: sret pointer to `Result<[u8; 960], Error>` (961 bytes, align 1:
  discriminant `0#8 = Ok`, `1#8 = Err` at `ret`; 960-byte `ct1` at `ret + 1#64` on `Ok`,
  or 1-byte `Error` at `ret + 1#64` plus 959 bytes padding on `Err`).
* `x0 = hdrA`, `x1 = hdr.length`: `pk1: &[u8]`.
* `x2 = randA`: `randomness: [u8; 32]` (passed by value via indirect pointer).
* `x3 = esA`, `x4 = 2080#64`: `state: &mut [u8]`.
* `x5 = ssA`, `x6 = 32#64`: `shared_secret: &mut [u8]`. -/
def mlkemEncaps1Spec (K : MlKem) : Spec MlkemEncaps1Call where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.ret ∧ s.readReg64 .x0 = x.hdrA ∧
      (s.readReg64 .x1).toNat = x.hdr.length ∧ s.readReg64 .x2 = x.randA ∧
      s.readReg64 .x3 = x.esA ∧ s.readReg64 .x4 = 2080#64 ∧
      s.readReg64 .x5 = x.ssA ∧ s.readReg64 .x6 = 32#64⌝ ∗
      (x.hdrA ↦ₛ x.hdr) ∗ (x.randA ↦ₛ x.rand.toList) ∗
      memRegion x.ret 961 ∗ memRegion x.esA 2080 ∗ memRegion x.ssA 32 ∗
      stackAt s.sp extHookStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.hdrA ↦ₛ x.hdr) ∗ (x.randA ↦ₛ x.rand.toList) ∗
      (match K.encaps1 x.hdr x.rand with
       | some (ct1, es, ss) =>
           (x.ret ↦₈ 0#8) ∗ ((x.ret + 1#64) ↦ₛ ct1.toList) ∗
           (x.esA ↦ₛ es.toList) ∗ (x.ssA ↦ₛ ss.toList)
       | none =>
           (x.ret ↦₈ 1#8) ∗ (∃∗ (err : BitVec 8), ((x.ret + 1#64) ↦₈ err)) ∗
           memRegion (x.ret + 2#64) 959 ∗
           memRegion x.esA 2080 ∗ memRegion x.ssA 32) ∗
      stackAt s0.sp extHookStack

/-- Ghost state for `encapsulate2`. -/
structure MlkemEncaps2Call where
  ret : BitVec 64
  esA : BitVec 64
  es : List.Vector (BitVec 8) 2080
  ekA : BitVec 64
  ek : List.Vector (BitVec 8) 1152

/-- Spec for `libcrux_ml_kem::mlkem768::incremental::encapsulate2`.
* `x8 = ret`: sret pointer to `[u8; 128]` (128 bytes, align 1).
* `x0 = esA`: `state: &[u8; 2080]`.
* `x1 = ekA`: `public_key_part: &[u8; 1152]`. -/
def mlkemEncaps2Spec (K : MlKem) : Spec MlkemEncaps2Call where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.ret ∧ s.readReg64 .x0 = x.esA ∧ s.readReg64 .x1 = x.ekA⌝ ∗
      (x.esA ↦ₛ x.es.toList) ∗ (x.ekA ↦ₛ x.ek.toList) ∗
      memRegion x.ret 128 ∗ stackAt s.sp extHookStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.esA ↦ₛ x.es.toList) ∗ (x.ekA ↦ₛ x.ek.toList) ∗
      (x.ret ↦ₛ (K.encaps2 x.es x.ek).toList) ∗
      stackAt s0.sp extHookStack

/-- Ghost state for `decapsulate_compressed_key`. -/
structure MlkemDecapsCall where
  ret : BitVec 64
  dkA : BitVec 64
  dk : List.Vector (BitVec 8) 2400
  ct1A : BitVec 64
  ct1 : List.Vector (BitVec 8) 960
  ct2A : BitVec 64
  ct2 : List.Vector (BitVec 8) 128

/-- Spec for `libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key`.
* `x8 = ret`: sret pointer to `[u8; 32]` (32 bytes, align 1).
* `x0 = dkA`: `private_key: &[u8; 2400]`.
* `x1 = ct1A`: `ciphertext1: &[u8; 960]`.
* `x2 = ct2A`: `ciphertext2: &[u8; 128]`. -/
def mlkemDecapsSpec (K : MlKem) : Spec MlkemDecapsCall where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.ret ∧ s.readReg64 .x0 = x.dkA ∧
      s.readReg64 .x1 = x.ct1A ∧ s.readReg64 .x2 = x.ct2A⌝ ∗
      (x.dkA ↦ₛ x.dk.toList) ∗ (x.ct1A ↦ₛ x.ct1.toList) ∗ (x.ct2A ↦ₛ x.ct2.toList) ∗
      memRegion x.ret 32 ∗ stackAt s.sp extHookStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.dkA ↦ₛ x.dk.toList) ∗ (x.ct1A ↦ₛ x.ct1.toList) ∗ (x.ct2A ↦ₛ x.ct2.toList) ∗
      (x.ret ↦ₛ (K.decaps x.dk x.ct1 x.ct2).toList) ∗
      stackAt s0.sp extHookStack

/-- Ghost state for `validate_pk_bytes`. -/
structure MlkemValidatePkCall where
  hdrA : BitVec 64
  hdr : List (BitVec 8)
  ekA : BitVec 64
  ek : List (BitVec 8)

/-- Spec for `libcrux_ml_kem::mlkem768::incremental::validate_pk_bytes`.
* `x0 = hdrA`, `x1 = hdr.length`: `pk1: &[u8]`.
* `x2 = ekA`, `x3 = ek.length`: `pk2: &[u8]`.
* Returns `Result<(), Error>` in low byte of `w0`: `0xff#8` (255, niche for `Ok(())`) iff
  `K.validPkBytes hdr ek = true` (length check, then `K.validPk`). -/
def mlkemValidatePkSpec (K : MlKem) : Spec MlkemValidatePkCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.hdrA ∧ (s.readReg64 .x1).toNat = x.hdr.length ∧
      s.readReg64 .x2 = x.ekA ∧ (s.readReg64 .x3).toNat = x.ek.length⌝ ∗
      (x.hdrA ↦ₛ x.hdr) ∗ (x.ekA ↦ₛ x.ek) ∗ stackAt s.sp extHookStack
  post := fun x s0 sf =>
    ⌜((sf.readReg64 .x0).setWidth 8 = 0xff#8 ↔ K.validPkBytes x.hdr x.ek = true) ∧
      sf.trace = s0.trace⌝ ∗
      (x.hdrA ↦ₛ x.hdr) ∗ (x.ekA ↦ₛ x.ek) ∗ stackAt s0.sp extHookStack

/-! ## 4. `libcrux_hmac::hmac` Hook Specification -/

/-- Ghost state for `libcrux_hmac::hmac`. -/
structure LibcruxHmacCall where
  ret : BitVec 64
  keyA : BitVec 64
  key : List (BitVec 8)
  dataA : BitVec 64
  data : List (BitVec 8)

/-- Spec for `libcrux_hmac::hmac`.
* `x8 = ret`: sret pointer to 24-byte `Vec<u8>`.
* `w0 = 0#32`: `Algorithm::Sha256`.
* `x1 = keyA`, `x2 = key.length`: `key: &[u8]`.
* `x3 = dataA`, `x4 = data.length`: `data: &[u8]`.
* `w5 = 1#32`, `x6 = 32#64`: `tag_length: Option<usize> = Some(32)`.
* Allocates a 32-byte `Vec<u8>` at `ret` containing `hmacWith F key data`; panics on OOM, or when
  `key.len()` or `data.len()` is ≥ 2^32 (`impl_hacl.rs:12,14`: `try_into::<u32>().unwrap()`). -/
def libcruxHmacSpec (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc) :
    Spec LibcruxHmacCall where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.ret ∧ (s.readReg64 .x0).setWidth 32 = 0#32 ∧
      s.readReg64 .x1 = x.keyA ∧ (s.readReg64 .x2).toNat = x.key.length ∧
      s.readReg64 .x3 = x.dataA ∧ (s.readReg64 .x4).toNat = x.data.length ∧
      (s.readReg64 .x5).setWidth 32 = 1#32 ∧ s.readReg64 .x6 = 32#64⌝ ∗
      (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
      memRegion x.ret 24 ∗ A.pool ∗ stackAt s.sp extHookStack
  post := fun x s0 sf =>
    ⌜x.key.length < 2 ^ 32 ∧ x.data.length < 2 ^ 32 ∧ sf.trace = s0.trace⌝ ∗
      (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
      vecU8 A x.ret (hmacWith F x.key x.data) ∗ A.pool ∗ stackAt s0.sp extHookStack
  onPanic := fun x s0 sf =>
    ⌜(allocFailedIn s0 sf ∨ 2 ^ 32 ≤ x.key.length ∨ 2 ^ 32 ≤ x.data.length) ∧
      s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## 5. Complete `SpqrHooks` Bundle -/

/-- **The contracts of the extern stubs reached on non-empty SPQR states** (used by
`Statements.lean`):
`HookSat` contracts on `abs` for the 7 `libcrux_ml_kem` incremental stubs and `libcrux_hmac::hmac`.
The compressed-keypair slice equations connecting `pk1` (`kp[2304..2368]`) and `pk2`
(`kp[1152..2304]`) to `K.fromSeed` are theorems (`SpqrHooks.fromSeed_pk1` / `fromSeed_pk2`, below),
not fields. -/
structure SpqrHooks (C : Crypto) (A : RustAlloc) (K : MlKem)
    (abs : String → Option (State → State)) : Prop where
  /-- `<KeyPairCompressedBytes>::from_seed`. -/
  fromSeed : HookSat abs mlkemFromSeedName (mlkemFromSeedSpec K)
  /-- `<KeyPairCompressedBytes>::pk1`. -/
  pk1 : HookSat abs mlkemPk1Name mlkemPk1Spec
  /-- `<KeyPairCompressedBytes>::pk2`. -/
  pk2 : HookSat abs mlkemPk2Name mlkemPk2Spec
  /-- `libcrux_ml_kem::mlkem768::incremental::encapsulate1`. -/
  encaps1 : HookSat abs mlkemEncaps1Name (mlkemEncaps1Spec K)
  /-- `libcrux_ml_kem::mlkem768::incremental::encapsulate2`. -/
  encaps2 : HookSat abs mlkemEncaps2Name (mlkemEncaps2Spec K)
  /-- `libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key`. -/
  decaps : HookSat abs mlkemDecapsName (mlkemDecapsSpec K)
  /-- `libcrux_ml_kem::mlkem768::incremental::validate_pk_bytes`. -/
  validatePk : HookSat abs mlkemValidatePkName (mlkemValidatePkSpec K)
  /-- `libcrux_hmac::hmac`, with OOM and length (≥ 2^32) panic allowance. -/
  hmac : HookSat abs libcruxHmacName (libcruxHmacSpec C.F A)

/-- Slice agreement for `KeyPairCompressedBytes::pk1`: bytes `2304..2368` (`pk1Off`) of the
2400-byte compressed keypair `dk = (K.fromSeed seed).2.2` equal `hdr = (K.fromSeed seed).1`. True
for every `K` (`MlKem.fromSeed_pk1`); stated on `SpqrHooks` so that proofs holding a hook bundle
`hSH` can write `hSH.fromSeed_pk1`. -/
theorem SpqrHooks.fromSeed_pk1 {C : Crypto} {A : RustAlloc} {K : MlKem}
    {abs : String → Option (State → State)} (_h : SpqrHooks C A K abs) (seed) :
    ((K.fromSeed seed).2.2.toList.drop 2304).take 64 = (K.fromSeed seed).1.toList :=
  K.fromSeed_pk1 seed

/-- Slice agreement for `KeyPairCompressedBytes::pk2`: bytes `1152..2304` (`pk2Off`) of the
2400-byte compressed keypair `dk = (K.fromSeed seed).2.2` equal `ek = (K.fromSeed seed).2.1`. True
for every `K` (`MlKem.fromSeed_pk2`). -/
theorem SpqrHooks.fromSeed_pk2 {C : Crypto} {A : RustAlloc} {K : MlKem}
    {abs : String → Option (State → State)} (_h : SpqrHooks C A K abs) (seed) :
    ((K.fromSeed seed).2.2.toList.drop 1152).take 1152 = (K.fromSeed seed).2.1.toList :=
  K.fromSeed_pk2 seed

end CryptoVerification.LibsignalSpqrV1
