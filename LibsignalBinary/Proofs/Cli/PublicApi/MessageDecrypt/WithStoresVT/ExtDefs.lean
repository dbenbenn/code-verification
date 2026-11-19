/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Coins.Defs
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Defs
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegDispatchAux -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.RecordX.ScopeP -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Defs
import LibsignalBinary.Proofs.TripleRatchet.Record.Defs
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Defs
import LibsignalBinary.Proofs.TripleRatchet.TrapRng
import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Defs
import LibsignalBinary.Proofs.Cli.TripleRatchet.Getters.Defs
import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet
import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
import LibsignalBinary.Specifications.LibsignalSpqrV1.Statements
import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordCallees.Defs
import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordChainClone.Defs
import LibsignalBinary.Proofs.Common.StringCloneFlatX
import LibsignalBinary.Proofs.Common.StringCloneFlat
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# Ext-Generic `MessageDecrypt` Foundations (`ExtDefs`)

Defines ext-generic filesystem carriers, stacked allocator/callee contracts (`AllocContracts4K` and
`AllocContractsX`), and segment step relations over `tripleRatchetProgAtExt img.base ext` shared by
`_trap` and `WithStoresVT`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-- Stack budget for `<PublicKey as PartialEq>::eq` (`64 + extHookStack = 16448` bytes). -/
abbrev publicKeyEqStackX : Nat := Getters.publicKeyEqStackExt

theorem publicKeyEqStackX_eq : publicKeyEqStackX = 64 + extHookStack := rfl

theorem publicKeyEqStackX_val : publicKeyEqStackX = 16448 := rfl

/-- Specification for `<PublicKey as PartialEq>::eq` with `64 + extHookStack` stack bytes. -/
abbrev publicKeyEqSpecX : Spec (BitVec 64 × PublicKey × BitVec 64 × PublicKey × BitVec 64) :=
  Getters.publicKeyEqSpecExt

/-- `subroutine_ok` hypothesis for `<PublicKey as PartialEq>::eq` on `tripleRatchetProgAtExt b ext`. -/
abbrev PublicKeyEqOkExtX (b : BitVec 64) (ext : String → Option (State → State)) : Prop :=
  Getters.PublicKeyEqOkExt32 b ext

theorem allocHookStack_le_extHookStack : allocHookStack ≤ extHookStack := by decide

theorem decNeedAux_extHookStack_eq : 2 ^ 20 + extHookStack = 2 ^ 20 + 16384 := rfl

/-- Checks that `trustPollNeed` / `savePollNeed` at `extHookStack` covers the `192`-byte poll frame plus `64 + extHookStack`. -/
theorem idPollStack_covers_publicKeyEq_with_extHookStack :
    192 + (64 + extHookStack) ≤
      192 + max (max (640 + (320 + (2384 + extHookStack))) 96) (max 64 extHookStack) := by
  decide

/-- `memcpy` specification requiring `allocHookStack` (`4096` bytes) of stack slack. -/
@[expose] def msgDecryptMemcpySpec4K : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s0.sp allocHookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗
      stackAt s0.sp allocHookStack

end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT
