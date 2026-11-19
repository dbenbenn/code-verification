/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Hoare.MultiCodeROHook
public import VerifiedLibraries.Mallocng.Spec
public import LibsignalBinary.Specifications.LibsignalE2E.HooksCommon
public import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr
public import LibsignalBinary.Specifications.SignalSession.CliRun

/-!
# Shared-Pool (`mallocng`) Replay Combinators for `libsignal-cli`

**Checked by Lean.** Shared-pool (`mallocng`) single-call replay combinators
(`restoreCallerRegs`, `stepRustAlloc1`, `stepRustDealloc1`; `0` definitions in any headline
closure) over `VerifiedLibraries.mallocngLib.codeROSubroutineHook`. Proof-side crypto hooks
live in `LibsignalBinary/Proofs/HookDischarge/CryptoMallocngBudgetBase.lean`
(`libcruxHmacHookMallocng`) and `LibsignalBinary/Proofs/E2E/AesHooks0.lean`
(`aesEncHookMallocng`, `aesDecHookMallocng`).
See `Computational/docs/TRUSTED_BASE.md` and `Computational/docs/DEVIATIONS.md` (DEV-E8, DEV-PQ1).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E

open Arm64 ProofLib CryptoGames CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr

/-! ## Single-call `mallocng` replay combinators -/

/-- Restore caller architectural CPU registers (`regs`, `vregs`, `sp`, `pc`, `pstate`, `fpsr`) from
`sCaller` while keeping `sCallee`'s memory, VM state (`brk`, `physMemAvail`), hardware nondeterminism
indices (`oracleIdx`, `exclFails`), and process state (`fs`, `trace`, `status`, `tpidrEl0`,
`brkStart`, `oracle`, `symtab`, `sigActions`, `sigAltStack`). -/
def restoreCallerRegs (sCaller sCallee : State) : State :=
  { sCallee with
    regs := sCaller.regs
    vregs := sCaller.vregs
    sp := sCaller.sp
    pc := sCaller.pc
    pstate := sCaller.pstate
    fpsr := sCaller.fpsr }

/-- Replay one alignment-1 Rust global allocation (`__rustc::__rust_alloc(size, 1)` when
`zeroed = false`, `__rustc::__rust_alloc_zeroed(size, 1)` when `zeroed = true`) at caller stack
depth `frameBytes` (`sp := s.sp - BitVec.ofNat 64 frameBytes`) through verified `mallocng`
(`"malloc"` or `"calloc"` at placement `mpl` under `Syscall.standard`):
* if `mallocng` stops in a non-`.Running` state, propagate `s1` unchanged;
* if `mallocng` returns `0#64` (`NULL`), panic via `Rust.panicked` while retaining `s1`'s
  memory/VM/oracle effects;
* otherwise restore caller architectural registers (`restoreCallerRegs s s1`) and pass the non-null
  block pointer `p = s1.readReg64 .x0` to `k`.

`__rdl_alloc` tail-branches directly to `malloc` (`0` shim frame); `__rdl_alloc_zeroed` pops its
transient `0x30`-byte frame before tail-branching to `calloc` (within `mallocngStackBytes = 1024`). -/
noncomputable def stepRustAlloc1 (mpl : Obj.MultiPlacement) (zeroed : Bool)
    (frameBytes size : Nat) (k : State → BitVec 64 → State) (s : State) : State :=
  let spCall := s.sp - BitVec.ofNat 64 frameBytes
  let sCall0 := (s.writeReg64 .sp spCall).writeReg64 .x0 (BitVec.ofNat 64 size)
  let sCall := if zeroed then sCall0.writeReg64 .x1 1#64 else sCall0
  let fnName := if zeroed then "calloc" else "malloc"
  let s1 := VerifiedLibraries.mallocngLib.codeROSubroutineHook mpl fnName
    (fun _ => none) (fun _ => none) Syscall.standard sCall
  if s1.status != .Running then
    s1
  else
    let p := s1.readReg64 .x0
    let sKeep := restoreCallerRegs s s1
    if p == 0#64 then
      Rust.panicked sKeep
    else
      k sKeep p

/-- Replay one alignment-1 Rust global deallocation (`__rustc::__rust_dealloc(ptr, _size, 1)` →
`free`, `0` shim frame) at caller stack depth `frameBytes` (`sp := s.sp - BitVec.ofNat 64 frameBytes`)
through verified `mallocng` (`"free"` at placement `mpl` under `Syscall.standard`). -/
noncomputable def stepRustDealloc1 (mpl : Obj.MultiPlacement) (frameBytes : Nat)
    (ptr : BitVec 64) (k : State → State) (s : State) : State :=
  let spCall := s.sp - BitVec.ofNat 64 frameBytes
  let sCall := (s.writeReg64 .sp spCall).writeReg64 .x0 ptr
  let s1 := VerifiedLibraries.mallocngLib.codeROSubroutineHook mpl "free"
    (fun _ => none) (fun _ => none) Syscall.standard sCall
  if s1.status != .Running then
    s1
  else
    k (restoreCallerRegs s s1)

end CryptoVerification.E2E
