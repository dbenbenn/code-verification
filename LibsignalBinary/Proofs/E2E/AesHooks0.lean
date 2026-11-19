/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

-- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalE2E.HooksCommon
-- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalE2E.HooksMallocng
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.HooksCommonLegacy
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.IoHooksLegacy

/-!
# Untrusted AES-256-CBC Arg-Reading Helpers and Ghost Hooks

Arg-reading helpers (`aesInput`, `aesKey`, `aesIv`, `aesEncOut`, `aesDecOut`), legacy bump-heap
hook transitions (`aesEncHook0`, `aesDecHook0`), and shared-pool `mallocng` ghost replay transitions
(`aesEncFrameBytes`, `aesDecFrameBytes`, `aesEncHookMallocng`, `aesDecHookMallocng`) retained in
untrusted `Proofs/` for ghost-table replay proofs and legacy non-placed tests after
`aes_256_cbc_{encrypt,decrypt}` left `cliHookTablePlaced`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.E2E.AesHooks0

open Arm64 ProofLib
open CryptoGames.CBC (AesKey Block bytesToBlock)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.LibsignalSession (aesCbcEncrypt aesCbcDecrypt)
open CryptoVerification.LibsignalTripleRatchetRepr (errTag)
open CryptoVerification.SignalSession (unmodelled)
open CryptoVerification.E2E
  (bumpAddr? bumpThen allocPanicHook returnFreshVecU8 stepRustAlloc1 stepRustDealloc1 writeVecHeader)

/-- The AES call's input bytes (`x0`, length `x1`). -/
@[expose] def aesInput (s : State) : List (BitVec 8) :=
  s.mem.readBytes (s.readReg64 .x0) (s.readReg64 .x1).toNat

/-- The AES call's 32 key bytes (`x2`). -/
@[expose] def aesKey (s : State) : List (BitVec 8) := s.mem.readBytes (s.readReg64 .x2) 32

/-- The AES call's 16 IV (initialization vector) bytes (`x4`). -/
@[expose] def aesIv (s : State) : List (BitVec 8) := s.mem.readBytes (s.readReg64 .x4) 16

/-- The output of `aes_256_cbc_encrypt` on the call's arguments: the session model's
`aesCbcEncrypt`. -/
@[expose] def aesEncOut (E : AesKey → Block → Block) (s : State) : List (BitVec 8) :=
  aesCbcEncrypt E (bytesToKey32 (aesKey s)) (bytesToBlock (aesIv s)) (aesInput s)

/-- The output of `aes_256_cbc_decrypt` on the call's arguments: the session model's
`aesCbcDecrypt`. -/
@[expose] def aesDecOut (D : AesKey → Block → Block) (s : State) :
    Option (List (BitVec 8)) :=
  aesCbcDecrypt D (bytesToKey32 (aesKey s)) (bytesToBlock (aesIv s)) (aesInput s)

/-- `aes_256_cbc_encrypt(ptext = (x0, x1), key = (x2, x3), iv = (x4, x5))` with sret `x8`:
if `key.len != 32` (`x3`) or `iv.len != 16` (`x5`), writes `Err(BadKeyOrIv)` (`errTag` at `x8`,
zero allocations); else if `2 ^ 63 ≤ (x1.toNat / 16 + 1) * 16`, panics (`RawVec` capacity
overflow); else returns `Ok(aesEncOut E s)` in a fresh `Vec<u8>` at `x8`. -/
@[expose] def aesEncHook0 (E : AesKey → Block → Block) (s : State) :
    State :=
  if s.readReg64 .x3 != 32#64 || s.readReg64 .x5 != 16#64 then
    retHook (fun s => s.setMem (s.mem.write64 (s.readReg64 .x8) errTag)) s
  else if 2 ^ 63 ≤ ((s.readReg64 .x1).toNat / 16 + 1) * 16 then
    Rust.panicked s
  else
    returnFreshVecU8 (aesEncOut E s) s

/-- `aes_256_cbc_decrypt(ctext = (x0, x1), key = (x2, x3), iv = (x4, x5))` with sret `x8`:
1. If `ctext.is_empty()` or `ctext.len() % 16 != 0` (`x1`), returns `Err(BadCiphertext)` (`errTag`
   @0 and non-null `&'static str` placeholder `1` @8, zero allocations).
2. If `key.len != 32` (`x3`) or `iv.len != 16` (`x5`), returns `Err(BadKeyOrIv)` (`errTag` @0 and
   niche `0` @8, zero allocations).
3. If `2 ^ 63 ≤ ctext.len()`, panics (`RawVec` capacity overflow).
4. Otherwise allocates the output `Vec<u8>` before PKCS#7 unpadding: on OOM
   (`bumpAddr? s.mem ctLen 1 = none`), panics via `allocPanicHook`; on `some pt`, returns `pt` in a
   fresh `Vec<u8>` at `x8`; on `none` (invalid PKCS#7 padding), consumes the `ctLen`-byte heap
   block (matching `alloc` + no-op `dealloc` under DEV-E6) and returns `Err(BadCiphertext)`. -/
@[expose] def aesDecHook0 (D : AesKey → Block → Block) (s : State) :
    State :=
  let ctLen := (s.readReg64 .x1).toNat
  if ctLen == 0 || ctLen % 16 != 0 then
    retHook (fun s =>
      let r := s.readReg64 .x8
      s.setMem ((s.mem.write64 r errTag).write64 (r + 8#64) 1#64)) s
  else if s.readReg64 .x3 != 32#64 || s.readReg64 .x5 != 16#64 then
    retHook (fun s =>
      let r := s.readReg64 .x8
      s.setMem ((s.mem.write64 r errTag).write64 (r + 8#64) 0#64)) s
  else if 2 ^ 63 ≤ ctLen then
    Rust.panicked s
  else
    match aesDecOut D s with
    | some pt =>
      if (bumpAddr? s.mem ctLen 1).isNone then allocPanicHook s
      else returnFreshVecU8 pt s
    | none =>
      bumpThen ctLen 1
        (fun s _ =>
          retHook (fun s =>
            let r := s.readReg64 .x8
            s.setMem ((s.mem.write64 r errTag).write64 (r + 8#64) 1#64)) s)
        allocPanicHook s

/-- Own stack frame of `signal_crypto::aes_cbc::aes_256_cbc_encrypt` (`+0x00: stp x29, x30,
[sp, #-0x60]!` plus `+0x1c: sub sp, sp, #0xc50`): `0x60 + 0xc50 = 0xcb0 = 3248` bytes (`16`-byte
aligned; `3248 + mallocngStackBytes = 3248 + 1024 = 4272 ≤ extHookStack = 16384`). -/
abbrev aesEncFrameBytes : Nat := 0xcb0

/-- Own stack frame of `signal_crypto::aes_cbc::aes_256_cbc_decrypt` (`+0x00: stp x29, x30,
[sp, #-0x60]!` plus `+0x1c: sub sp, sp, #0x8f0`): `0x60 + 0x8f0 = 0x950 = 2384` bytes (`16`-byte
aligned; `2384 + mallocngStackBytes = 2384 + 1024 = 3408 ≤ extHookStack = 16384`). -/
abbrev aesDecFrameBytes : Nat := 0x950

/-- `signal_crypto::aes_cbc::aes_256_cbc_encrypt` (frame `0xcb0 = 3248` B) ghost replay over shared
`mallocng` at placement `mpl`:
1. Fails closed (`unmodelled`) if `key.len() ≠ 32` (`x3`) or `iv.len() ≠ 16` (`x5`).
2. Panics via `Rust.panicked` (`0` allocations) if `2 ^ 63 ≤ (ptLen / 16 + 1) * 16`.
3. Replays `calloc(ctLen, 1)` at `sp = s0.sp - 0xcb0#64`, writes `ct = aesEncOut E s1` at `p`,
   writes `Vec` header `{ctLen, p, ctLen}` at sret `x8`, and returns. -/
@[expose] noncomputable def aesEncHookMallocng (mpl : Obj.MultiPlacement)
    (E : AesKey → Block → Block) (s0 : State) : State :=
  if s0.readReg64 .x3 != 32#64 || s0.readReg64 .x5 != 16#64 then
    unmodelled "aes_256_cbc_encrypt: key.len != 32 or iv.len != 16" s0
  else
    let ptLen := (s0.readReg64 .x1).toNat
    let ctLen := (ptLen / 16 + 1) * 16
    if 2 ^ 63 ≤ ctLen then
      Rust.panicked s0
    else
      stepRustAlloc1 mpl true aesEncFrameBytes ctLen (fun s1 p =>
        let ct := aesEncOut E s1
        let n := BitVec.ofNat 64 ct.length
        retHook (fun s =>
          s.setMem (writeVecHeader (s.mem.writeBytes p ct) (s.readReg64 .x8) n p n)) s1) s0

/-- `signal_crypto::aes_cbc::aes_256_cbc_decrypt` (frame `0x950 = 2384` B) ghost replay over shared
`mallocng` at placement `mpl`:
1. Fails closed (`unmodelled`) if `key.len() ≠ 32` (`x3`) or `iv.len() ≠ 16` (`x5`).
2. Returns `Err(BadCiphertext)` (`errTag` at `x8`, `1` at `x8 + 8`, `0` allocations) when
   `ctLen = 0` or `ctLen % 16 ≠ 0`.
3. Replays `calloc(ctLen, 1)` at `sp = s0.sp - 0x950#64` and evaluates `aesDecOut D s1`:
   * `some pt`: writes `pt` at `p` and `Vec` header `{cap := ctLen, ptr := p, len := pt.length}`
     at `x8` (`Vec::truncate` leaves spare capacity `[p + pt.length .. p + ctLen)` unallocated);
   * `none` (invalid PKCS#7 padding): replays `free(p)` at `sp = s1.sp - 0x950#64` and returns
     `Err(BadCiphertext)` at `x8`. -/
@[expose] noncomputable def aesDecHookMallocng (mpl : Obj.MultiPlacement)
    (D : AesKey → Block → Block) (s0 : State) : State :=
  if s0.readReg64 .x3 != 32#64 || s0.readReg64 .x5 != 16#64 then
    unmodelled "aes_256_cbc_decrypt: key.len != 32 or iv.len != 16" s0
  else
    let ctLen := (s0.readReg64 .x1).toNat
    if ctLen == 0 || ctLen % 16 != 0 then
      retHook (fun s =>
        let r := s.readReg64 .x8
        s.setMem ((s.mem.write64 r errTag).write64 (r + 8#64) 1#64)) s0
    else
      stepRustAlloc1 mpl true aesDecFrameBytes ctLen (fun s1 p =>
        match aesDecOut D s1 with
        | some pt =>
          retHook (fun s =>
            let r := s.readReg64 .x8
            s.setMem (writeVecHeader (s.mem.writeBytes p pt) r
              (BitVec.ofNat 64 ctLen) p (BitVec.ofNat 64 pt.length))) s1
        | none =>
          stepRustDealloc1 mpl aesDecFrameBytes p (fun s2 =>
            retHook (fun s =>
              let r := s.readReg64 .x8
              s.setMem ((s.mem.write64 r errTag).write64 (r + 8#64) 1#64)) s2) s1) s0

end LibsignalBinary.Proofs.E2E.AesHooks0

-- AUTO-BRIDGE BEGIN
namespace CryptoVerification.E2E
export LibsignalBinary.Proofs.E2E.AesHooks0 (aesInput aesKey aesIv aesEncOut aesDecOut)
export LibsignalBinary.Proofs.E2E.AesHooks0 (aesEncHook0 aesDecHook0 aesEncFrameBytes aesDecFrameBytes)
export LibsignalBinary.Proofs.E2E.AesHooks0 (aesEncHookMallocng aesDecHookMallocng)
end CryptoVerification.E2E
-- AUTO-BRIDGE END
