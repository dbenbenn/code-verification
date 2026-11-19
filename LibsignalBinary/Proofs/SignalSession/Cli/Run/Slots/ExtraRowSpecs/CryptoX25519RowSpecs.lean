/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Phase4GhostHooks -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookLs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoX25519RowSpecsBase -- proof-setup: allow-public-import

/-!
# X25519 Consumer `HookOk` Row Arms (`ExtraRowSpecs.CryptoX25519RowSpecs`)

Re-exports the cycle-free row contracts and pure fallbacks from `CryptoX25519RowSpecsBase` and
instantiates both row structures on the real linked-code ghosts
(`x25519PubFromSecretGhost x25519Mpl`, `x25519DiffieHellmanGhost x25519Mpl`).
-/

set_option autoImplicit false
set_option linter.dupNamespace false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoX25519RowSpecs

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (LibsignalPlacement)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Phase4GhostHooks
  (x25519DiffieHellmanGhost x25519DiffieHellmanGhost_at_ok
   x25519DiffieHellmanGhost_cliExt_keepsFs_ok x25519DiffieHellmanGhost_cliExt_ls_ok
   x25519DiffieHellmanGhost_cliExt_ok x25519DiffieHellmanGhost_cliExt_withAlloc_ls_ok
   x25519DiffieHellmanGhost_cliExt_withAlloc_ok x25519DiffieHellmanGhost_fs
   x25519DiffieHellmanGhost_keepsFs_ok x25519DiffieHellmanGhost_ls_ok
   x25519DiffieHellmanGhost_vmPreserved x25519DiffieHellmanGhost_withAlloc_ls_ok
   x25519DiffieHellmanGhost_withAlloc_ok x25519PubFromSecretGhost x25519PubFromSecretGhost_at_ok
   x25519PubFromSecretGhost_cliExt_keepsFs_ok x25519PubFromSecretGhost_cliExt_ls_ok
   x25519PubFromSecretGhost_cliExt_ok x25519PubFromSecretGhost_cliExt_withAlloc_ls_ok
   x25519PubFromSecretGhost_cliExt_withAlloc_ok
   x25519PubFromSecretGhost_derivePublicKeyBytesStackBudget_keepsFs_ok
   x25519PubFromSecretGhost_derivePublicKeyBytesStackBudget_ls_ok
   x25519PubFromSecretGhost_derivePublicKeyBytesStackBudget_ok
   x25519PubFromSecretGhost_derivePublicKeyBytesStackBudget_withAlloc_ls_ok
   x25519PubFromSecretGhost_derivePublicKeyBytesStackBudget_withAlloc_ok
   x25519PubFromSecretGhost_derivePublicKeyBytesStack_keepsFs_ok
   x25519PubFromSecretGhost_derivePublicKeyBytesStack_ls_ok
   x25519PubFromSecretGhost_derivePublicKeyBytesStack_ok
   x25519PubFromSecretGhost_derivePublicKeyBytesStack_withAlloc_ls_ok
   x25519PubFromSecretGhost_derivePublicKeyBytesStack_withAlloc_ok x25519PubFromSecretGhost_fs
   x25519PubFromSecretGhost_keepsFs_ok x25519PubFromSecretGhost_ls_ok
   x25519PubFromSecretGhost_pureByteFunction_keepsFs_ok
   x25519PubFromSecretGhost_pureByteFunction_ls_ok x25519PubFromSecretGhost_pureByteFunction_ok
   x25519PubFromSecretGhost_pureByteFunction_withAlloc_ls_ok
   x25519PubFromSecretGhost_pureByteFunction_withAlloc_ok x25519PubFromSecretGhost_vmPreserved
   x25519PubFromSecretGhost_withAlloc_ls_ok x25519PubFromSecretGhost_withAlloc_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoX25519RowSpecsBase
  (X25519DiffieHellmanRowSpec X25519PubFromSecretRowSpec diffieHellmanFallback_rowSpec
   pubFromSecretFallback_rowSpec)

export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoX25519RowSpecsBase
  (X25519DiffieHellmanRowSpec X25519PubFromSecretRowSpec diffieHellmanFallback_rowSpec
   pubFromSecretFallback_rowSpec)

/-- `x25519PubFromSecretGhost x25519Mpl` satisfies `X25519PubFromSecretRowSpec` unconditionally
    (`0` layout premises). -/
theorem x25519PubFromSecretGhost_rowSpec [LibsignalPlacement] (x25519Mpl : MultiPlacement) :
    X25519PubFromSecretRowSpec (x25519PubFromSecretGhost x25519Mpl) where
  vmPreserved := x25519PubFromSecretGhost_vmPreserved x25519Mpl
  fs_eq := x25519PubFromSecretGhost_fs x25519Mpl
  withStack_ls := fun stk hlo hhi => x25519PubFromSecretGhost_ls_ok x25519Mpl stk hlo hhi
  withStack_vm := fun stk hlo hhi => x25519PubFromSecretGhost_at_ok x25519Mpl stk hlo hhi
  withStack_keepsFs := fun stk hlo hhi => x25519PubFromSecretGhost_keepsFs_ok x25519Mpl stk hlo hhi
  withStack_alloc := fun A lim stk hlo hhi =>
    x25519PubFromSecretGhost_withAlloc_ok x25519Mpl A lim stk hlo hhi
  withStack_alloc_ls := fun A lim stk hlo hhi =>
    x25519PubFromSecretGhost_withAlloc_ls_ok x25519Mpl A lim stk hlo hhi
  cliExt_ls := x25519PubFromSecretGhost_cliExt_ls_ok x25519Mpl
  cliExt_vm := x25519PubFromSecretGhost_cliExt_ok x25519Mpl
  cliExt_keepsFs := x25519PubFromSecretGhost_cliExt_keepsFs_ok x25519Mpl
  cliExt_alloc := fun {_} A lim {_} hC =>
    x25519PubFromSecretGhost_cliExt_withAlloc_ok x25519Mpl A lim hC
  cliExt_alloc_ls := fun {_} A lim {_} hC =>
    x25519PubFromSecretGhost_cliExt_withAlloc_ls_ok x25519Mpl A lim hC
  pureByteFunction_ls := fun byVal =>
    x25519PubFromSecretGhost_pureByteFunction_ls_ok x25519Mpl byVal
  pureByteFunction_vm := fun byVal =>
    x25519PubFromSecretGhost_pureByteFunction_ok x25519Mpl byVal
  pureByteFunction_keepsFs := fun byVal =>
    x25519PubFromSecretGhost_pureByteFunction_keepsFs_ok x25519Mpl byVal
  pureByteFunction_alloc := fun A lim byVal =>
    x25519PubFromSecretGhost_pureByteFunction_withAlloc_ok x25519Mpl A lim byVal
  pureByteFunction_alloc_ls := fun A lim byVal =>
    x25519PubFromSecretGhost_pureByteFunction_withAlloc_ls_ok x25519Mpl A lim byVal
  derivePublicKeyBytesStack_ls := fun stk hlo hhi =>
    x25519PubFromSecretGhost_derivePublicKeyBytesStack_ls_ok x25519Mpl stk hlo hhi
  derivePublicKeyBytesStack_vm := fun stk hlo hhi =>
    x25519PubFromSecretGhost_derivePublicKeyBytesStack_ok x25519Mpl stk hlo hhi
  derivePublicKeyBytesStack_keepsFs := fun stk hlo hhi =>
    x25519PubFromSecretGhost_derivePublicKeyBytesStack_keepsFs_ok x25519Mpl stk hlo hhi
  derivePublicKeyBytesStack_alloc := fun A lim stk hlo hhi =>
    x25519PubFromSecretGhost_derivePublicKeyBytesStack_withAlloc_ok x25519Mpl A lim stk hlo hhi
  derivePublicKeyBytesStack_alloc_ls := fun A lim stk hlo hhi =>
    x25519PubFromSecretGhost_derivePublicKeyBytesStack_withAlloc_ls_ok x25519Mpl A lim stk hlo hhi
  derivePublicKeyBytesStackBudget_ls := fun stk hlo hhi =>
    x25519PubFromSecretGhost_derivePublicKeyBytesStackBudget_ls_ok x25519Mpl stk hlo hhi
  derivePublicKeyBytesStackBudget_vm := fun stk hlo hhi =>
    x25519PubFromSecretGhost_derivePublicKeyBytesStackBudget_ok x25519Mpl stk hlo hhi
  derivePublicKeyBytesStackBudget_keepsFs := fun stk hlo hhi =>
    x25519PubFromSecretGhost_derivePublicKeyBytesStackBudget_keepsFs_ok x25519Mpl stk hlo hhi
  derivePublicKeyBytesStackBudget_alloc := fun A lim stk hlo hhi =>
    x25519PubFromSecretGhost_derivePublicKeyBytesStackBudget_withAlloc_ok
      x25519Mpl A lim stk hlo hhi
  derivePublicKeyBytesStackBudget_alloc_ls := fun A lim stk hlo hhi =>
    x25519PubFromSecretGhost_derivePublicKeyBytesStackBudget_withAlloc_ls_ok
      x25519Mpl A lim stk hlo hhi

/-- `x25519DiffieHellmanGhost x25519Mpl` satisfies `X25519DiffieHellmanRowSpec` unconditionally
    (`0` layout premises). -/
theorem x25519DiffieHellmanGhost_rowSpec [LibsignalPlacement] (x25519Mpl : MultiPlacement) :
    X25519DiffieHellmanRowSpec (x25519DiffieHellmanGhost x25519Mpl) where
  vmPreserved := x25519DiffieHellmanGhost_vmPreserved x25519Mpl
  fs_eq := x25519DiffieHellmanGhost_fs x25519Mpl
  withStack_ls := fun stk hlo hhi => x25519DiffieHellmanGhost_ls_ok x25519Mpl stk hlo hhi
  withStack_vm := fun stk hlo hhi => x25519DiffieHellmanGhost_at_ok x25519Mpl stk hlo hhi
  withStack_keepsFs := fun stk hlo hhi => x25519DiffieHellmanGhost_keepsFs_ok x25519Mpl stk hlo hhi
  withStack_alloc := fun A lim stk hlo hhi =>
    x25519DiffieHellmanGhost_withAlloc_ok x25519Mpl A lim stk hlo hhi
  withStack_alloc_ls := fun A lim stk hlo hhi =>
    x25519DiffieHellmanGhost_withAlloc_ls_ok x25519Mpl A lim stk hlo hhi
  cliExt_ls := x25519DiffieHellmanGhost_cliExt_ls_ok x25519Mpl
  cliExt_vm := x25519DiffieHellmanGhost_cliExt_ok x25519Mpl
  cliExt_keepsFs := x25519DiffieHellmanGhost_cliExt_keepsFs_ok x25519Mpl
  cliExt_alloc := fun {_} A lim {_} hC =>
    x25519DiffieHellmanGhost_cliExt_withAlloc_ok x25519Mpl A lim hC
  cliExt_alloc_ls := fun {_} A lim {_} hC =>
    x25519DiffieHellmanGhost_cliExt_withAlloc_ls_ok x25519Mpl A lim hC

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoX25519RowSpecs
