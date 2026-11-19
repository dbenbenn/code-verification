/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Defs
import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtLsPlacedSpecs -- proof-setup: allow-public-import

/-!
# Budget-Threaded Contracts for In-Image Whole-Crate Callees

`VmPreserved` and `RustCliAllocBudget` contracts for `Uuid::try_parse`,
`ServiceId::parse_from_service_id_string`, `PrivateKey::serialize`, and
`<ProtocolAddress as Display>::fmt`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost UuidParser protocolAddressAt)
open CryptoVerification.RustHeap (vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchet (
  addrDisplayStack extHookStack parseSidCodeSpec parseSidCodeStackSpec privSerializeStackX
  uuidTryParseCodeSpec uuidTryParseSpec uuidTryParseStackSpec
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget rustAllocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj (fmtWriteKnownEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs (CliFmtWriteVtableKind)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtLsPlacedSpecs (CliFmtWriteEnv)

/-! ## `VmPreserved`-strengthened `Uuid::try_parse` and `ServiceId::parse_from_service_id_string` -/

@[expose] def uuidTryParseBudgetSpec (parse : UuidParser) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) :=
  withVmPreserved (uuidTryParseSpec parse)

@[expose] def uuidTryParseCodeBudgetSpec (parse : UuidParser) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) :=
  withVmPreserved (uuidTryParseCodeSpec parse)

@[expose] def uuidTryParseStackBudgetSpec (hookStack : Nat := 0) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) :=
  withVmPreserved (uuidTryParseStackSpec hookStack)

@[expose] def parseSidCodeBudgetSpec (parse : UuidParser) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) :=
  withVmPreserved (parseSidCodeSpec parse)

@[expose] def parseSidCodeStackBudgetSpec (hookStack : Nat := 0) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) :=
  withVmPreserved (parseSidCodeStackSpec hookStack)

/-! ## `PrivateKey::serialize` -/

/-- Exact allocator event sequence of `<PrivateKey>::serialize`: a single 32-byte, 1-aligned
allocation (`self.key.to_vec()`). -/
@[expose] def privSerializeEvents : List AllocEvent :=
  rustAllocEvents 32 1

@[expose] def PrivSerializeEnv (evs : List AllocEvent) : Prop :=
  evs = privSerializeEvents

/-- Stack-parameterized budget contract for `<PrivateKey>::serialize` (Block `208`).
Ghost: `(k, bs, ret, st)`. Under `FitsEnv M lim st PrivSerializeEnv`, `__rust_alloc(32, 1)`
returns non-null and `onPanic = ⌜False⌝`. -/
@[expose] def privSerializeSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (totalStack : Nat) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × M.σ) where
  pre := fun (k, bs, ret, st) s =>
    ⌜s.readReg64 .x0 = k ∧ s.readReg64 .x8 = ret ∧ bs.length = 32 ∧
      FitsEnv M lim st PrivSerializeEnv⌝ ∗
      (k ↦ₛ bs) ∗ memRegion ret 24 ∗ A.pool lim st s ∗ stackAt s.sp totalStack
  post := fun (k, bs, ret, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (k ↦ₛ bs) ∗ vecU8 A.repAlloc ret bs ∗
      A.pool lim (M.stepEvents privSerializeEvents st) sf ∗ stackAt s0.sp totalStack

abbrev privSerializeSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × M.σ) :=
  privSerializeSpecWithStack M A lim extHookStack

abbrev privSerializeSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × M.σ) :=
  privSerializeSpecWithStack M A lim privSerializeStackX

/-! ## `<ProtocolAddress as Display>::fmt` -/

/-- Ghost state for `<ProtocolAddress as Display>::fmt` (Block `215`). -/
structure AddrDisplayGhost where
  addrPtr : BitVec 64
  rem : AddrGhost
  f : BitVec 64
  v : BitVec 64
  cap0 : BitVec 64
  ptr0 : BitVec 64
  vtKind : CliFmtWriteVtableKind
  bs : List (BitVec 8)

/-- Exact allocator event sequence emitted by `<ProtocolAddress as Display>::fmt` on `g`. -/
@[expose] def AddrDisplayGhost.exactEvs (g : AddrDisplayGhost) : List AllocEvent :=
  fmtWriteKnownEvents g.bs.length g.cap0
    [g.rem.name.bytes.length, 1, (formatDecimalNat g.rem.device.toNat).length]

/-- Envelope-parametric budget contract for `<ProtocolAddress as Display>::fmt` (Block `215`),
defaulting to `CliFmtWriteEnv`. Ghost: `(g, st)`. -/
@[expose] def addrDisplayEnvSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : List AllocEvent → Prop := CliFmtWriteEnv) :
    Spec (AddrDisplayGhost × M.σ) where
  pre := fun (g, st) s =>
    ⌜s.readReg64 .x0 = g.addrPtr ∧ s.readReg64 .x1 = g.f ∧
      g.rem.name.bytes.length < 2 ^ 60 ∧
      FitsEnv M lim st Env ∧ Env g.exactEvs⌝ ∗
      (g.f ↦₆₄ g.v) ∗ ((g.f + 8#64) ↦₆₄ g.vtKind.vtableAddr) ∗
      protocolAddressAt A.repAlloc g.rem g.addrPtr ∗
      vecU8At A.repAlloc g.v g.cap0 g.ptr0 g.bs ∗
      A.pool lim st s ∗ stackAt s.sp addrDisplayStack
  post := fun (g, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ sf.trace = s0.trace ∧ Env evs⌝ ∗
      (g.f ↦₆₄ g.v) ∗ ((g.f + 8#64) ↦₆₄ g.vtKind.vtableAddr) ∗
      protocolAddressAt A.repAlloc g.rem g.addrPtr ∗
      (∃∗ bs' : List (BitVec 8), vecU8 A.repAlloc g.v bs') ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp addrDisplayStack

abbrev addrDisplaySpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec (AddrDisplayGhost × M.σ) :=
  addrDisplayEnvSpec M A lim CliFmtWriteEnv

end LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget
