/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Specifications.CryptoGames.KEM.Kyber1024KeyGen
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem
import LibsignalBinary.Proofs.SpqrV1.Vectors.Protocol
import LibsignalBinary.Proofs.SpqrV1.Vectors.Protocol2
meta import LibsignalBinary.Specifications.CryptoGames.KEM.Kyber1024KeyGen
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem
meta import LibsignalBinary.Proofs.SpqrV1.Vectors.Protocol
meta import LibsignalBinary.Proofs.SpqrV1.Vectors.Protocol2

/-!
# Compile-Time `#guard` Known-Answer & Differential Boundary Tests (`Spec/MlKemKat.lean`)

Cross-checks `Spec/MlKem.lean` (`mlkem768KeyPairWith`, `mlkem768ValidPk`, `mlkem768Encaps1With`,
`mlkem768Encaps2List`, `mlkem768DecapsWith`, `kyber1024EncapsWith`, `kyber1024DecapsWith`) byte-for-byte
against two committed Rust vector sources:
1. **`third_party/libsignal/libsignal-session/tools/spqr-vectors`** (`LibsignalBinary.Proofs.SpqrV1.Vectors.Protocol`):
   replays every recorded `libcrux_ml_kem::mlkem768::incremental` call (`.fromSeed`, `.encaps1`,
   `.encaps2`, `.decaps`, and `.validatePk` true/false) across `runInOrder`, `runReordered`,
   `runDropped`, and `tamperedRecvVectors`.
2. **`LibsignalBinary/Proofs/HookDischarge/CryptoMlKem/Spec/kat_gen`** (`cargo run --release --offline`):
   checks `SHA3-256` digests and full outputs against `libcrux-ml-kem = "=0.0.10"` for:
   - Round-3 CRYSTALS-Kyber-1024 (`K = 4, d_u = 11, d_v = 5`) roundtrip + corrupted-`ct` FO implicit rejection.
   - Incremental FIPS 203 ML-KEM-768 (`K = 3, d_u = 10, d_v = 4`) roundtrip + corrupted-`ct1`/`ct2` FO implicit rejection + non-canonical `encapsulate2` `es` bytes.
   - `mlkem768ValidPk` & `mlkem768Encaps1With` boundary checks: header length `63` vs `64`, `ek` length `1151` vs `1152`, tampered `H(ek || rho)`, and non-canonical `ek` coefficients `3328` (accepted) vs `3329` and `4095` (rejected even with recomputed matching `SHA3-256(ek || rho)`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKemKat

open CryptoGames.MLKEM (kyber1024KeyPairWith)
open CryptoVerification.SpqrV1.Vectors.Protocol (
  MlKemCallVec
  protocolRuns
  tamperedRecvVectors
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  kyber1024DecapsWith
  kyber1024EncapsWith
  mlkem768DecapsWith
  mlkem768Encaps1With
  mlkem768Encaps2List
  mlkem768KeyPairWith
  mlkem768ValidPk
  sampleNttFuel
  sha3_256List
)

/-! ## 1. Replay of All Committed `spqr-vectors` ML-KEM-768 Call Logs (`Vectors/Protocol.lean`) -/

private def checkSpqrMlkemCall (c : MlKemCallVec) : Bool :=
  match c with
  | .fromSeed seed hdr ek dk =>
    let dkOut := mlkem768KeyPairWith sampleNttFuel seed
    (dkOut == dk) && ((dkOut.drop 2304).take 64 == hdr) && ((dkOut.drop 1152).take 1152 == ek)
  | .encaps1 hdr rand ct1 es ss =>
    mlkem768Encaps1With sampleNttFuel hdr rand == some (ct1, es, ss)
  | .encaps2 es ek ct2 =>
    mlkem768Encaps2List es ek == ct2
  | .decaps dk ct1 ct2 ss =>
    mlkem768DecapsWith sampleNttFuel dk ct1 ct2 == ss
  | .validatePk hdr ek valid =>
    mlkem768ValidPk hdr ek == valid

private def allSpqrMlkemCalls : List MlKemCallVec :=
  (protocolRuns.flatMap fun r => r.steps.flatMap fun s => s.mlkemCalls) ++
  (tamperedRecvVectors.flatMap fun t => t.mlkemCalls)

private def checkSpqrMlkemCallVectors : Bool :=
  !allSpqrMlkemCalls.isEmpty && allSpqrMlkemCalls.all checkSpqrMlkemCall

#guard checkSpqrMlkemCallVectors

/-! ## 2. Committed `Spec/kat_gen` Vectors (`libcrux-ml-kem = "=0.0.10"`) -/

private def mkTestBytes (n : Nat) (mul add : BitVec 8) : List (BitVec 8) :=
  (List.range n).map fun i => BitVec.ofNat 8 i * mul + add

/-- Round-3 CRYSTALS-Kyber-1024 key generation (`CryptoGames.MLKEM.kyber1024KeyPairWith`),
    checked via `SHA3-256` against `Spec/kat_gen/src/main.rs`. -/
private def kyber1024TestKeyPair (seed64 : List (BitVec 8)) : List (BitVec 8) × List (BitVec 8) :=
  kyber1024KeyPairWith sampleNttFuel seed64

private def rustPk1024Sha3 : List (BitVec 8) :=
  [0x09#8, 0xcf#8, 0x49#8, 0x50#8, 0xa2#8, 0xbf#8, 0x13#8, 0xc5#8,
   0xa3#8, 0x4b#8, 0x44#8, 0xf9#8, 0x26#8, 0x9c#8, 0x65#8, 0x47#8,
   0x58#8, 0x07#8, 0x93#8, 0x87#8, 0x4e#8, 0xb4#8, 0x15#8, 0xfb#8,
   0x55#8, 0xde#8, 0x84#8, 0x54#8, 0x72#8, 0x13#8, 0xe8#8, 0x9b#8]

private def rustSk1024Sha3 : List (BitVec 8) :=
  [0x3b#8, 0xff#8, 0xcf#8, 0x1c#8, 0xf6#8, 0x74#8, 0x9e#8, 0x9d#8,
   0xa0#8, 0xd4#8, 0x29#8, 0x7a#8, 0xf0#8, 0xb4#8, 0x77#8, 0x44#8,
   0x37#8, 0x5f#8, 0x4f#8, 0x3b#8, 0xda#8, 0xea#8, 0xc0#8, 0x01#8,
   0x2c#8, 0xf4#8, 0xf3#8, 0xb1#8, 0x29#8, 0xe2#8, 0xe9#8, 0x9e#8]

private def rustCt1024Sha3 : List (BitVec 8) :=
  [0x35#8, 0xec#8, 0x5f#8, 0x15#8, 0xf2#8, 0xec#8, 0x99#8, 0x32#8,
   0xc7#8, 0x6e#8, 0x96#8, 0xb6#8, 0xbd#8, 0x7f#8, 0xf7#8, 0xab#8,
   0xf8#8, 0x3b#8, 0x6c#8, 0xee#8, 0x69#8, 0x04#8, 0x68#8, 0xe7#8,
   0x37#8, 0x54#8, 0x52#8, 0xfe#8, 0xfa#8, 0xa1#8, 0x3f#8, 0xb2#8]

private def rustSs1024Enc : List (BitVec 8) :=
  [0xd3#8, 0x9f#8, 0x74#8, 0x00#8, 0x37#8, 0x93#8, 0x1d#8, 0x78#8,
   0xf5#8, 0x64#8, 0x74#8, 0x5a#8, 0xf6#8, 0xd5#8, 0x15#8, 0x49#8,
   0x20#8, 0xd8#8, 0x7a#8, 0x2f#8, 0xf5#8, 0xd4#8, 0x3a#8, 0xd2#8,
   0xb7#8, 0x00#8, 0x0c#8, 0x52#8, 0x4e#8, 0x7e#8, 0x42#8, 0x54#8]

private def rustSs1024Rej : List (BitVec 8) :=
  [0x7f#8, 0x32#8, 0x88#8, 0x13#8, 0x4d#8, 0x53#8, 0x02#8, 0x85#8,
   0xf4#8, 0x03#8, 0x7e#8, 0xac#8, 0xae#8, 0xa9#8, 0x08#8, 0xcf#8,
   0xab#8, 0x18#8, 0xce#8, 0x00#8, 0xba#8, 0x16#8, 0x58#8, 0x3e#8,
   0xaf#8, 0x82#8, 0xf6#8, 0x53#8, 0x6d#8, 0x08#8, 0x22#8, 0xac#8]

private def rustDk768Sha3 : List (BitVec 8) :=
  [0x87#8, 0x07#8, 0x67#8, 0x7a#8, 0x86#8, 0x90#8, 0xfb#8, 0xd7#8,
   0xf3#8, 0xdb#8, 0xe5#8, 0x94#8, 0x60#8, 0xcf#8, 0x6e#8, 0xeb#8,
   0x8d#8, 0x4f#8, 0x46#8, 0x96#8, 0x87#8, 0xe5#8, 0xdb#8, 0x8c#8,
   0x16#8, 0xde#8, 0x01#8, 0x30#8, 0xe8#8, 0x11#8, 0x99#8, 0x95#8]

private def rustCt1_768Sha3 : List (BitVec 8) :=
  [0x62#8, 0xb2#8, 0x85#8, 0x21#8, 0xa1#8, 0x5a#8, 0xe6#8, 0x98#8,
   0x68#8, 0xe3#8, 0xb3#8, 0xc3#8, 0x6f#8, 0x2d#8, 0xa3#8, 0x37#8,
   0x36#8, 0x73#8, 0x54#8, 0xa0#8, 0xb4#8, 0xa0#8, 0x19#8, 0xaa#8,
   0xc3#8, 0x5a#8, 0x1b#8, 0x41#8, 0xbf#8, 0x43#8, 0xb3#8, 0x32#8]

private def rustEs768Sha3 : List (BitVec 8) :=
  [0x0f#8, 0x5c#8, 0x4b#8, 0xd0#8, 0x53#8, 0x75#8, 0xd2#8, 0xfa#8,
   0xcb#8, 0xed#8, 0xb2#8, 0x7f#8, 0x23#8, 0x47#8, 0x5d#8, 0x81#8,
   0xa0#8, 0x08#8, 0x57#8, 0x0d#8, 0xae#8, 0x84#8, 0x5c#8, 0x77#8,
   0x0a#8, 0xe7#8, 0x09#8, 0xb4#8, 0x0a#8, 0xb3#8, 0xea#8, 0xe3#8]

private def rustSs768Enc : List (BitVec 8) :=
  [0x1f#8, 0x0c#8, 0xd4#8, 0x15#8, 0x9c#8, 0x86#8, 0xa2#8, 0x76#8,
   0xa5#8, 0xab#8, 0x6e#8, 0x12#8, 0x0c#8, 0x1c#8, 0x6f#8, 0x2e#8,
   0x6f#8, 0x55#8, 0xa7#8, 0xfe#8, 0x96#8, 0x25#8, 0x5a#8, 0x64#8,
   0x24#8, 0x72#8, 0x60#8, 0x07#8, 0xf3#8, 0x0f#8, 0x9d#8, 0x2b#8]

private def rustSs768RejCt1 : List (BitVec 8) :=
  [0x05#8, 0xc1#8, 0xfb#8, 0xa1#8, 0xe8#8, 0xcd#8, 0x83#8, 0x95#8,
   0xd0#8, 0x32#8, 0xf8#8, 0xc9#8, 0x25#8, 0xd6#8, 0x1c#8, 0xe4#8,
   0x15#8, 0x8d#8, 0x70#8, 0x08#8, 0xc6#8, 0x61#8, 0x8b#8, 0xff#8,
   0xfe#8, 0xc7#8, 0x8a#8, 0xa2#8, 0xed#8, 0x69#8, 0x38#8, 0xe4#8]

private def rustSs768RejCt2 : List (BitVec 8) :=
  [0x9b#8, 0xdf#8, 0xea#8, 0x67#8, 0x5d#8, 0x91#8, 0x79#8, 0x79#8,
   0xcd#8, 0x2b#8, 0x32#8, 0xfc#8, 0x7c#8, 0x0d#8, 0x1e#8, 0x8c#8,
   0x0a#8, 0xef#8, 0x37#8, 0x0c#8, 0x7f#8, 0x30#8, 0xe1#8, 0x5c#8,
   0x81#8, 0xd0#8, 0x35#8, 0x94#8, 0x8f#8, 0x12#8, 0x8e#8, 0xfc#8]

private def rustCt2_768 : List (BitVec 8) :=
  [0x15#8, 0x44#8, 0xde#8, 0xaa#8, 0x02#8, 0x8d#8, 0x45#8, 0x90#8, 0xcc#8, 0x26#8, 0x11#8, 0xdd#8, 0x71#8, 0x6d#8, 0xea#8, 0x4d#8,
   0xb7#8, 0x0b#8, 0x11#8, 0x56#8, 0x66#8, 0x9c#8, 0x3f#8, 0xac#8, 0xd4#8, 0xdb#8, 0x7b#8, 0xec#8, 0x48#8, 0x6f#8, 0x40#8, 0x6f#8,
   0x72#8, 0xc5#8, 0xef#8, 0x03#8, 0xc3#8, 0x0e#8, 0x53#8, 0x78#8, 0xdf#8, 0x47#8, 0x59#8, 0x4e#8, 0xea#8, 0x7b#8, 0x4c#8, 0x31#8,
   0x17#8, 0x70#8, 0x80#8, 0x1e#8, 0xb5#8, 0x9a#8, 0x19#8, 0x84#8, 0x3d#8, 0xd0#8, 0xd4#8, 0xf7#8, 0x52#8, 0xe2#8, 0x10#8, 0x25#8,
   0x26#8, 0x0c#8, 0xe3#8, 0xeb#8, 0x03#8, 0xfd#8, 0x83#8, 0xc0#8, 0x41#8, 0x63#8, 0x4e#8, 0x31#8, 0x9d#8, 0xdf#8, 0xb1#8, 0xf1#8,
   0xf0#8, 0xc4#8, 0x9e#8, 0xd7#8, 0x4c#8, 0x05#8, 0x0b#8, 0x88#8, 0x9c#8, 0x28#8, 0x17#8, 0xc6#8, 0x3e#8, 0x9e#8, 0x36#8, 0x38#8,
   0x9b#8, 0xaf#8, 0x10#8, 0x14#8, 0xc6#8, 0x84#8, 0xab#8, 0x5e#8, 0x92#8, 0xa5#8, 0x26#8, 0xac#8, 0x3b#8, 0x23#8, 0x85#8, 0x92#8,
   0x79#8, 0xf0#8, 0x9f#8, 0xe8#8, 0x60#8, 0xf8#8, 0x88#8, 0x28#8, 0x2a#8, 0xcf#8, 0xf6#8, 0x54#8, 0x4d#8, 0x06#8, 0xbd#8, 0x35#8]

private def rustCt2NoncanonPort : List (BitVec 8) :=
  [0xaf#8, 0x5b#8, 0x52#8, 0x1d#8, 0xb9#8, 0xe4#8, 0x2c#8, 0x52#8, 0x22#8, 0x27#8, 0xa8#8, 0x9d#8, 0xfb#8, 0x0d#8, 0x4f#8, 0x0b#8,
   0xd2#8, 0xb7#8, 0x9d#8, 0x59#8, 0x75#8, 0xf2#8, 0x9d#8, 0x6d#8, 0x78#8, 0x39#8, 0x02#8, 0x42#8, 0x0e#8, 0x45#8, 0x8c#8, 0x7f#8,
   0xfb#8, 0xc1#8, 0x6c#8, 0xbb#8, 0xaa#8, 0xf0#8, 0xc7#8, 0xcd#8, 0x0a#8, 0xdf#8, 0xc5#8, 0xeb#8, 0x81#8, 0x0a#8, 0xf7#8, 0x42#8,
   0x0f#8, 0x09#8, 0x26#8, 0x9e#8, 0xb5#8, 0xfe#8, 0xe2#8, 0x12#8, 0xa9#8, 0xed#8, 0x9e#8, 0x18#8, 0x60#8, 0x73#8, 0x5c#8, 0x55#8,
   0x00#8, 0x69#8, 0xcf#8, 0xd5#8, 0x2a#8, 0x95#8, 0xdc#8, 0xea#8, 0x47#8, 0xe8#8, 0xd4#8, 0xe9#8, 0x05#8, 0x86#8, 0xe4#8, 0x1f#8,
   0x20#8, 0x0a#8, 0xc9#8, 0x71#8, 0xff#8, 0xac#8, 0x72#8, 0xc2#8, 0x39#8, 0xf4#8, 0x5e#8, 0x59#8, 0x59#8, 0xc3#8, 0x4d#8, 0x86#8,
   0xa5#8, 0x92#8, 0x11#8, 0x94#8, 0x89#8, 0xc0#8, 0x66#8, 0x67#8, 0xba#8, 0xb0#8, 0x18#8, 0xc9#8, 0xd7#8, 0xfd#8, 0x44#8, 0xd3#8,
   0xea#8, 0x7c#8, 0x5a#8, 0x46#8, 0x77#8, 0x3d#8, 0x54#8, 0x4f#8, 0x0f#8, 0x53#8, 0x47#8, 0xca#8, 0xb4#8, 0xca#8, 0x06#8, 0xa0#8]

private def checkKyber1024All : Bool :=
  let (pk1024, sk1024) := kyber1024TestKeyPair (mkTestBytes 64 37#8 0x5a#8)
  let rand := mkTestBytes 32 91#8 0xa3#8
  let (ct1024, ssEnc) := kyber1024EncapsWith sampleNttFuel pk1024 rand
  let ssDec := kyber1024DecapsWith sampleNttFuel sk1024 ct1024
  let badCt := (ct1024.headD 0#8 ^^^ 0x01#8) :: ct1024.tail
  let ssRej := kyber1024DecapsWith sampleNttFuel sk1024 badCt
  (sha3_256List pk1024 == rustPk1024Sha3) &&
  (sha3_256List sk1024 == rustSk1024Sha3) &&
  (sha3_256List ct1024 == rustCt1024Sha3) &&
  (ssEnc == rustSs1024Enc) &&
  (ssDec == rustSs1024Enc) &&
  (ssRej == rustSs1024Rej) &&
  (ssRej != ssEnc)

private def checkMlkem768All : Bool :=
  let dk768 := mlkem768KeyPairWith sampleNttFuel (mkTestBytes 64 53#8 0x19#8)
  let pk1 := (dk768.drop 2304).take 64
  let pk2 := (dk768.drop 1152).take 1152
  let rand := mkTestBytes 32 73#8 0xc7#8
  let noncanonEs := mkTestBytes 2080 131#8 0x7f#8
  let badHashPk1 := pk1.take 32 ++ [((pk1.getD 32 0#8) ^^^ 0x01#8)] ++ pk1.drop 33
  let pk2Coeff3329 := 0x01#8 :: ((pk2.getD 1 0#8 &&& 0xf0#8) ||| 0x0d#8) :: pk2.drop 2
  let hdrCoeff3329 := pk1.take 32 ++ sha3_256List (pk2Coeff3329 ++ pk1.take 32)
  let pk2Coeff4095 := 0xff#8 :: 0xff#8 :: pk2.drop 2
  let hdrCoeff4095 := pk1.take 32 ++ sha3_256List (pk2Coeff4095 ++ pk1.take 32)
  let pk2Coeff3328 := 0x00#8 :: ((pk2.getD 1 0#8 &&& 0xf0#8) ||| 0x0d#8) :: pk2.drop 2
  let hdrCoeff3328 := pk1.take 32 ++ sha3_256List (pk2Coeff3328 ++ pk1.take 32)
  let validChecks :=
    (sha3_256List dk768 == rustDk768Sha3) &&
    (mlkem768ValidPk pk1 pk2 == true) &&
    (mlkem768ValidPk (pk1.take 63) pk2 == false) &&
    (mlkem768ValidPk (pk1 ++ [0#8]) pk2 == false) &&
    (mlkem768ValidPk pk1 (pk2.take 1151) == false) &&
    (mlkem768ValidPk badHashPk1 pk2 == false) &&
    (mlkem768ValidPk hdrCoeff3329 pk2Coeff3329 == false) &&
    (mlkem768ValidPk hdrCoeff4095 pk2Coeff4095 == false) &&
    (mlkem768ValidPk hdrCoeff3328 pk2Coeff3328 == true) &&
    (mlkem768Encaps1With sampleNttFuel (pk1.take 63) rand).isNone
  match mlkem768Encaps1With sampleNttFuel pk1 rand with
  | none => false
  | some (ct1, es, ssEnc) =>
    let ct2 := mlkem768Encaps2List es pk2
    let ssDec := mlkem768DecapsWith sampleNttFuel dk768 ct1 ct2
    let badCt1 := (ct1.headD 0#8 ^^^ 0x80#8) :: ct1.tail
    let ssRej1 := mlkem768DecapsWith sampleNttFuel dk768 badCt1 ct2
    let badCt2 := ct2.take 127 ++ [((ct2.getD 127 0#8) ^^^ 0x01#8)]
    let ssRej2 := mlkem768DecapsWith sampleNttFuel dk768 ct1 badCt2
    let ct2Noncanon := mlkem768Encaps2List noncanonEs pk2
    validChecks &&
    (sha3_256List ct1 == rustCt1_768Sha3) &&
    (sha3_256List es == rustEs768Sha3) &&
    (ssEnc == rustSs768Enc) &&
    (ct2 == rustCt2_768) &&
    (ssDec == rustSs768Enc) &&
    (ssRej1 == rustSs768RejCt1) &&
    (ssRej2 == rustSs768RejCt2) &&
    (ct2Noncanon == rustCt2NoncanonPort)

#guard checkMlkem768All
#guard checkKyber1024All

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKemKat
