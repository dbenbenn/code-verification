/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalE2E.HooksCommon
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhInputs

/-!
# PQXDH and SPQR V1 Primitive Hooks

**Checked by Lean.** Proof-side external-call hooks for the PQXDH and SPQR V1 cryptographic
primitives (SHA-512 block compression, Kyber1024 encapsulation/decapsulation, and incremental
ML-KEM-768; `0` definitions in any headline closure, retained for untrusted ghost-table replay).
See `Computational/docs/TRUSTED_BASE.md`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.LibsignalAesCbc (toLEBytes returnToLinkRegister)
open CryptoVerification.LibsignalSpqrV1 (MlKem)

/-! ## The hooks -/

/-- The `n` bytes at `a`, as a vector. -/
def readVecN (m : Memory) (a : BitVec 64) (n : Nat) : List.Vector (BitVec 8) n :=
  ⟨m.readBytes a n, Memory.readBytes_length m a n⟩

/-- The SHA-512 chaining state stored at `a`: eight native little-endian `u64` words
(`sha2`'s `[u64; 8]`). -/
def readSha512State (m : Memory) (a : BitVec 64) : Sha512State :=
  List.Vector.ofFn fun i : Fin 8 => m.read64 (a + BitVec.ofNat 64 (8 * i.val))

/-- The 64 bytes of a SHA-512 chaining state as stored (each word little-endian). -/
def sha512StateBytesLE (h : Sha512State) : List (BitVec 8) :=
  h.toList.flatMap (toLEBytes 8)

/-- The 128-byte blocks of `bs` (a trailing partial block is dropped; the hook reads exactly
`128 n` bytes and `sha512Pad`'s output is a multiple of 128, so there is none). As `HMAC.chunks64`. -/
def chunks128 (bs : List (BitVec 8)) : List (List (BitVec 8)) :=
  List.ofFn fun i : Fin (bs.length / 128) => (bs.drop (128 * i.val)).take 128

/-- `sha2::sha512::compress512(state = x0, blocks.ptr = x1, blocks.len = x2)`: with `st` the eight
LE words at `x0` and `bs` the `128 · x2` bytes at `x1`,
`mem[x0 .. x0+64] := sha512StateBytesLE ((chunks128 bs).foldl F512 st)` (all inputs read before
writing); `pc := lr`. As `LibsignalHmac.compress256Hook` for SHA-256. -/
def compress512Hook (F512 : Sha512State → List (BitVec 8) → Sha512State) (s : State) :
    State :=
  let st := readSha512State s.mem (s.readReg64 .x0)
  let bs := s.mem.readBytes (s.readReg64 .x1) (128 * (s.readReg64 .x2).toNat)
  returnToLinkRegister (s.setMem (s.mem.writeBytes (s.readReg64 .x0)
    (sha512StateBytesLE ((chunks128 bs).foldl F512 st))))

/-- `kyber::encapsulate(&pk = x0, randomness = x1)` with `(ct, ss)` at the sret `x8`: the 1568-byte
ciphertext @0 and the 32-byte shared secret @`0x620` of `encaps mem[x0 .. +1568] mem[x1 .. +32]`;
`pc := lr`. The caller (`initialize_alice_session::<PqxdhRng>`) fills the 32 coin bytes from 32
`next_u32` calls, keeping the low byte of each (so coin `i` is tape byte `4 i` of that segment). -/
def kemEncapsHook (encaps : List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32 →
    List.Vector (BitVec 8) 1568 × List.Vector (BitVec 8) 32) (s : State) : State :=
  let r := s.readReg64 .x8
  let o := encaps (readVecN s.mem (s.readReg64 .x0) 1568) (readVecN s.mem (s.readReg64 .x1) 32)
  returnToLinkRegister (s.setMem ((s.mem.writeBytes r o.1.toList).writeBytes (r + 0x620#64) o.2.toList))

/-- `kyber::decapsulate(&sk = x0, &ct = x1)`: `mem[x8 .. +32] := decaps mem[x0 .. +3168]
mem[x1 .. +1568]`; `pc := lr`. -/
def kemDecapsHook (decaps : List.Vector (BitVec 8) 3168 → List.Vector (BitVec 8) 1568 →
    List.Vector (BitVec 8) 32) (s : State) : State :=
  returnToLinkRegister (s.setMem (s.mem.writeBytes (s.readReg64 .x8)
    (decaps (readVecN s.mem (s.readReg64 .x0) 3168)
      (readVecN s.mem (s.readReg64 .x1) 1568)).toList))

/-! ## The SPQR V1 hooks -/

/-- `<KeyPairCompressedBytes>::from_seed(&seed = x0)` with sret `x8`: writes the 2400-byte
compressed keypair `(K.fromSeed mem[x0 .. +64]).2.2` at `x8`. -/
def mlkemFromSeedHook (K : MlKem) : State → State :=
  retHook fun s =>
    s.setMem (s.mem.writeBytes (s.readReg64 .x8)
      (K.fromSeed (readVecN s.mem (s.readReg64 .x0) 64)).2.2.toList)

/-- `mlkem768::incremental::encapsulate1(pk1 = (x0, x1), &rand = x2, es = (x3, x4), ss = (x5, x6))`
with sret `x8`: if `es.len < 2080` (`x4`) or `ss.len < 32` (`x6`), writes
`Err(Error::InvalidOutputLength)` (`[1#8, 1#8]`) at `x8` leaving `es` and `ss` untouched;
otherwise on `some (ct1, es, ss)`, writes `0#8 :: ct1` at `x8`, `es` at `x3`, and `ss` at `x5`;
on `none`, writes `1#8` at `x8`. -/
def mlkemEncaps1Hook (K : MlKem) : State → State :=
  retHook fun s =>
    let ret := s.readReg64 .x8
    if (s.readReg64 .x4).toNat < 2080 || (s.readReg64 .x6).toNat < 32 then
      s.setMem (s.mem.writeBytes ret [1#8, 1#8])
    else
      let hdr := s.mem.readBytes (s.readReg64 .x0) (s.readReg64 .x1).toNat
      let rand := readVecN s.mem (s.readReg64 .x2) 32
      let esA := s.readReg64 .x3
      let ssA := s.readReg64 .x5
      let m := match K.encaps1 hdr rand with
        | some (ct1, es, ss) =>
          ((s.mem.writeBytes ret (0#8 :: ct1.toList)).writeBytes esA es.toList).writeBytes
            ssA ss.toList
        | none =>
          s.mem.writeBytes ret [1#8]
      s.setMem m

/-- `mlkem768::incremental::encapsulate2(&es = x0, &ek = x1)` with sret `x8`: writes the 128-byte
`ct2 = K.encaps2 mem[x0 .. +2080] mem[x1 .. +1152]` at `x8`. -/
def mlkemEncaps2Hook (K : MlKem) : State → State :=
  retHook fun s =>
    let es := readVecN s.mem (s.readReg64 .x0) 2080
    let ek := readVecN s.mem (s.readReg64 .x1) 1152
    s.setMem (s.mem.writeBytes (s.readReg64 .x8) (K.encaps2 es ek).toList)

/-- `mlkem768::incremental::decapsulate_compressed_key(&dk = x0, &ct1 = x1, &ct2 = x2)` with sret
`x8`: writes the 32-byte `K.decaps mem[x0 .. +2400] mem[x1 .. +960] mem[x2 .. +128]` at `x8`. -/
def mlkemDecapsHook (K : MlKem) : State → State :=
  retHook fun s =>
    let dk := readVecN s.mem (s.readReg64 .x0) 2400
    let ct1 := readVecN s.mem (s.readReg64 .x1) 960
    let ct2 := readVecN s.mem (s.readReg64 .x2) 128
    s.setMem (s.mem.writeBytes (s.readReg64 .x8) (K.decaps dk ct1 ct2).toList)

/-- `mlkem768::incremental::validate_pk_bytes(hdr = (x0, x1), ek = (x2, x3))`: returns `0xff#64`
in `x0` when `K.validPkBytes hdr ek = true`, and `0#64` otherwise. -/
def mlkemValidatePkHook (K : MlKem) : State → State :=
  retHook fun s =>
    let hdr := s.mem.readBytes (s.readReg64 .x0) (s.readReg64 .x1).toNat
    let ek := s.mem.readBytes (s.readReg64 .x2) (s.readReg64 .x3).toNat
    s.writeReg64 .x0 (if K.validPkBytes hdr ek then 0xff#64 else 0#64)

end CryptoVerification.E2E
