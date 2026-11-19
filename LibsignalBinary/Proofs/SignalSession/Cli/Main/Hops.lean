/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.PublicApi.StoreKit.Fs
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs

/-!
# Continuation Hop Contracts M1–M6 for `signal-session` `main`

Layout-independent `SepWPp` continuation contracts for the six hops of `main` (`M+k` = entry + `k`):
- **M1** (`M+0 → M+0xc0`): collect `(1..argc).map(strlen)` into `AtM1End` (early exit `2` if `argc = 1`).
- **M2** (`M+0xc0 → M+0x560`): `parse(&args)` into `AtCall` (early exit `2` if `parseArgs = none`).
- **M3** (`M+0x560 → M+0x5d0`): `read_stdin` and `read_file("coins")` into `AtM4` (early exit `2` on `Err`).
- **M4** (`M+0x5d0 → M+0x720`): `coins::install`, `Stores::open`, and `run` into `AtM4End` (early exit `1` on `Err`).
- **M5** (`M+0x720 → M+0xf34`): `Stores::commit` into `AtM6` (`w21 = 1` on write failure).
- **M6** (`M+0xf34 → M+0xb24`): `write_stdout(&output)`, buffer drops, and shared exit (`free_args`, `main_ret`).
-/

public section

set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.LibsignalPublicApi.StoreKit

/-! ## Hop States and Shared Exit -/

/-- Unreachable `OutOfMemory` continuation (`⌜False⌝`) for `main` hops under panic-on-OOM hooks. -/
@[expose] def mainOom (_s0 : State) : State → SepProp := fun _ => ⌜False⌝

/-- Transitional `OutOfMemory` continuation (`⌜allocFailedIn s0 sf⌝ ∗ anyHeap`). -/
@[expose] def mainOomLegacy (s0 : State) : State → SepProp :=
  fun sf => ⌜allocFailedIn s0 sf⌝ ∗ anyHeap

theorem sepWPp_of_mainOom {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ProofLib.SepWPp prog ret s P Q Qp (mainOom s0)) :
    ProofLib.SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  obtain ⟨sf, hsteps, hout⟩ := h R hm hL
  rcases hout with hq | hpan | ⟨_, hmo⟩
  · exact ⟨sf, hsteps, Or.inl hq⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl hpan)⟩
  · exact (ProofLib.not_satisfies_false_sepConj hmo).elim

/-- Separation-logic state at `M+0xb24`: saved callee registers, 0x480-byte local frame, caller stack,
allocator pool, and `anyHeap`. -/
@[expose] def retMem (A : RustAlloc) (s0 : State) (stk : Nat) : SepProp :=
  mainSaved s0 ∗ memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗
    stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ A.pool ∗ anyHeap

abbrev callCells (fsp : BitVec 64) (w : CallW) : List (Nat × Nat × SepProp) :=
  [cell fsp 0x40 w.w6, cell fsp 0x48 w.w3, cell fsp 0x50 w.w4]

/-! ## M3: `read_stdin` (send / recv), `read_file("coins")` (`M+0x560 → M+0x5d0`) -/

/-- History invariant after `run`: loaded initial files and empty stdout, or prior `allocFailedIn`. -/
@[expose] def HistOk (i : Inputs) (s0 s : State) : Prop :=
  (s.fs.files = (initFsState (cliInputs i)).files ∧
    ProcessOutcome.traceStreamBytes .stdout s.trace = []) ∨ allocFailedIn s0 s

/-- Tightened post-`run` history invariant: exact initial files and empty stdout. -/
@[expose] def HistOkTight (i : Inputs) (s : State) : Prop :=
  s.fs.files = (initFsState (cliInputs i)).files ∧
    ProcessOutcome.traceStreamBytes .stdout s.trace = []

abbrev m4Cells (fsp : BitVec 64) (w : CallW) (inPtr : BitVec 64) (coinsLen : Nat) :
    List (Nat × Nat × SepProp) :=
  [cell fsp 0x40 w.w6, cell fsp 0x48 w.w3, cell fsp 0x50 w.w4, cell fsp 0x58 inPtr,
    cell fsp 0x1c8 (BitVec.ofNat 64 coinsLen)]

/-! ## M4: `coins::install`, `Stores::open`, `run` (`M+0x5d0 → M+0x720`) -/

/-- Owned stack slots at `M+0x720`: spilled input pointer and `run`'s `Ok` payload at `fsp + 0x1b8`. -/
abbrev m5Cells (A : RustAlloc) (fsp inPtr : BitVec 64) (g : StoresGhost) (out : List (BitVec 8)) :
    List (Nat × Nat × SepProp) :=
  [cell fsp 0x58 inPtr, (0x1b8, runResSize, runOkAt A (fsp + 0x1b8#64) g out)]

/-! ## M6: `write_stdout(&output)`, drops (`M+0xf34 → M+0xb24`) -/

/-- Spill slots at `M+0xf34`: output `Vec` (`[fsp+0x18]`, `[fsp+0x10]`, `[fsp+0x8]`) and input
capacity/pointer (`[fsp+0x20]`, `[fsp+0x58]`). -/
abbrev m6Cells (fsp outCap outPtr outLen inCap inPtr : BitVec 64) : List (Nat × Nat × SepProp) :=
  [cell fsp 0x8 outLen, cell fsp 0x10 outPtr, cell fsp 0x18 outCap, cell fsp 0x20 inCap,
    cell fsp 0x58 inPtr]

end CryptoVerification.SignalSession.Cli.MainHops
