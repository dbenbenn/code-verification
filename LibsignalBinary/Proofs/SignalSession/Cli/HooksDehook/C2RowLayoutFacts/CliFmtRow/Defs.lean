/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced -- proof-setup: allow-public-import
public import ProofLib.Placed.Split

/-!
# Contiguous `seg[1] ++ seg[2]` Real-ELF RX Program `c2FmtProg` & Caller-`lr` Trap (`CliFmtRow.Defs`)
-/

set_option autoImplicit false
set_option maxRecDepth 4000000

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.Defs

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification.SignalSession (isCliPanicSymbolPlaced libsignalSessionLib)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (f3PatchedElf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (f3TrialRxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced (cliElfMultiPlacement)

deriving instance Inhabited for Arm64.Snapshot.Region

/-- Default empty `Snapshot.Region` fallback for total extraction of `f3PatchedElf.segments[1]?`. -/
@[expose] def c2EmptySeg : Snapshot.Region := default

/-- Segment `1` (`:text_a`, `Perm.rx`) of `f3PatchedElf`, ending page-contiguously at `f3RxSegBase`. -/
@[expose] noncomputable def c2Seg1 : Snapshot.Region :=
  (ProofLib.Placed.Split.rGetD (f3PatchedElf.segments.map some) 1 none).getD c2EmptySeg

@[expose] noncomputable def c2Seg1Start : BitVec 64 := c2Seg1.start
@[expose] noncomputable def c2Seg1Bytes : List (BitVec 8) := c2Seg1.bytes

/-- Panic-only extern table matching `cliExternsPlaced mmpl W` on `libsignalSessionExterns`. -/
@[expose] def c2FmtExterns (name : String) : Option (State → State) :=
  if isCliPanicSymbolPlaced name then some Rust.panicked else none

/-- Extern stub table of Block `617` rebased to `c2Seg1Start`. -/
@[expose] noncomputable def c2FmtStubs : List (String × Nat) :=
  (libsignalSessionLib.blockLib 617).text.externs.map fun e =>
    (e, (cliElfMultiPlacement.ρ e - c2Seg1Start).toNat)

/-- Contiguous `seg[1] ++ seg[2]` RX program covering crate formatters and `lib2_0.o` std/alloc. -/
@[expose] noncomputable def c2FmtProg : Program where
  base := c2Seg1Start
  code := c2Seg1Bytes ++ f3TrialRxProg.code
  symbols := []
  stubs := c2FmtStubs
  externs := c2FmtExterns
  overrides := fun _ => none
  svc := Syscall.standard

/-- Sentinel halt hook installed at the caller's return address `lr` in `c2FmtProgTrap lr`. -/
@[expose] def c2LrTrapSym : String := "__c2_lr_trap"

@[expose] def c2HaltHook (s : State) : State :=
  { s with status := .Halted }

/-- Caller-`lr` trapped variant of `c2FmtProg`: halts immediately if internal execution ever jumps to
    `lr` with `sp ≠ s0.sp`, ensuring any `SubroutineOutcome` on `c2FmtProgTrap lr` never stepped
    from `pc = lr` and therefore stops at the first visit to `(lr, s0.sp)` on `c2FmtProg`. -/
@[expose] noncomputable def c2FmtProgTrap (lr : BitVec 64) : Program :=
  { c2FmtProg with
    stubs := (c2LrTrapSym, (lr - c2Seg1Start).toNat) :: c2FmtStubs
    externs := fun name =>
      if name == c2LrTrapSym then some c2HaltHook else c2FmtExterns name }

attribute [local irreducible] c2Seg1 c2Seg1Start c2Seg1Bytes c2FmtStubs f3TrialRxProg

theorem c2FmtProg_base : c2FmtProg.base = c2Seg1Start := rfl
theorem c2FmtProg_code : c2FmtProg.code = c2Seg1Bytes ++ f3TrialRxProg.code := rfl
theorem c2FmtProg_symbols : c2FmtProg.symbols = [] := rfl
theorem c2FmtProg_stubs : c2FmtProg.stubs = c2FmtStubs := rfl
theorem c2FmtProg_externs : c2FmtProg.externs = c2FmtExterns := rfl
theorem c2FmtProg_overrides : c2FmtProg.overrides = fun _ => none := rfl
theorem c2FmtProg_svc : c2FmtProg.svc = Syscall.standard := rfl

theorem c2FmtProgTrap_base (lr : BitVec 64) : (c2FmtProgTrap lr).base = c2Seg1Start := rfl
theorem c2FmtProgTrap_code (lr : BitVec 64) :
    (c2FmtProgTrap lr).code = c2Seg1Bytes ++ f3TrialRxProg.code := rfl
theorem c2FmtProgTrap_symbols (lr : BitVec 64) : (c2FmtProgTrap lr).symbols = [] := rfl
theorem c2FmtProgTrap_stubs (lr : BitVec 64) :
    (c2FmtProgTrap lr).stubs = (c2LrTrapSym, (lr - c2Seg1Start).toNat) :: c2FmtStubs := rfl
theorem c2FmtProgTrap_externs (lr : BitVec 64) :
    (c2FmtProgTrap lr).externs =
      fun name => if name == c2LrTrapSym then some c2HaltHook else c2FmtExterns name := rfl
theorem c2FmtProgTrap_overrides (lr : BitVec 64) :
    (c2FmtProgTrap lr).overrides = fun _ => none := rfl
theorem c2FmtProgTrap_svc (lr : BitVec 64) : (c2FmtProgTrap lr).svc = Syscall.standard := rfl

private theorem codeLoaded_with_stubs_externs (P : Program)
    (stubs' : List (String × Nat)) (externs' : String → Option (State → State)) (m : Memory) :
    ({ P with stubs := stubs', externs := externs' } : Program).CodeLoaded m ↔ P.CodeLoaded m :=
  ⟨fun h => Program.CodeLoaded.intro h.aligned h.no_wrap
      (fun i hi => ⟨h.byte_eq i hi, h.perm_eq i hi, h.isLazyFree_eq i hi⟩),
   fun h => Program.CodeLoaded.intro h.aligned h.no_wrap
      (fun i hi => ⟨h.byte_eq i hi, h.perm_eq i hi, h.isLazyFree_eq i hi⟩)⟩

theorem c2FmtProgTrap_codeLoaded_iff (lr : BitVec 64) (m : Memory) :
    (c2FmtProgTrap lr).CodeLoaded m ↔ c2FmtProg.CodeLoaded m :=
  codeLoaded_with_stubs_externs c2FmtProg _ _ m

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.Defs
