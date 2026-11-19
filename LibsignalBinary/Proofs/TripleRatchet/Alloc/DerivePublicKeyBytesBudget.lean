/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytes
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout

/-!
# `VmPreserved` Contract for `PrivateKey::derive_public_key_bytes` (Block `200`)

Verifies `<libsignal_core::curve::curve25519::PrivateKey>::derive_public_key_bytes` against its
`VmPreserved`-strengthened specification on `tripleRatchetProgAt` and under `[LibsignalPlacement]`
(Block `200`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytesBudget

open CryptoVerification (
  LibsignalPlacement blkPC_200 blkPl_200 lsPubFromSecretSym ls_hook_ok_of_mem lsρ
)

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto PubKeyFn)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  derivePublicKeyBytesSpec derivePublicKeyBytesStackSpec derivePublicKeyBytesStack_of_spec
)

attribute [local irreducible] Program.fetch Program.externAt?

theorem derive_public_key_bytes_placed_ok_of_contract_stack [LibsignalPlacement]
    {pubKey : PubKeyFn} {H : String → Option (State → State)} (hookStack : Nat := 0)
    (hpub : subroutine_ok ((blkPC_200).rebase (blkPl_200).base H)
      (lsρ lsPubFromSecretSym)
      (derivePublicKeyBytesStackSpec pubKey hookStack)) :
    subroutine_ok ((blkPC_200).rebase (blkPl_200).base H) (blkPl_200).base
      (derivePublicKeyBytesStackSpec pubKey hookStack) := by
  have hfetch : ((blkPC_200).rebase (blkPl_200).base H).fetch
      ((blkPl_200).base + BitVec.ofNat 64 0) =
      some (.b ((blkPl_200).ρ lsPubFromSecretSym - (blkPl_200).base - BitVec.ofNat 64 0)) := by
    simp only [arm64_norm]
  rw [BitVec.add_zero] at hfetch
  exact subroutine_ok_of_b hfetch (by simp only [arm64_norm, wp_norm]) rfl
    (by intros; rfl) hpub

theorem derive_public_key_bytes_placed_ok_of_contract [LibsignalPlacement]
    {pubKey : PubKeyFn} {H : String → Option (State → State)}
    (hpub : subroutine_ok ((blkPC_200).rebase (blkPl_200).base H)
      (lsρ lsPubFromSecretSym)
      (derivePublicKeyBytesSpec pubKey)) :
    subroutine_ok ((blkPC_200).rebase (blkPl_200).base H) (blkPl_200).base
      (derivePublicKeyBytesSpec pubKey) := by
  have hfetch : ((blkPC_200).rebase (blkPl_200).base H).fetch
      ((blkPl_200).base + BitVec.ofNat 64 0) =
      some (.b ((blkPl_200).ρ lsPubFromSecretSym - (blkPl_200).base - BitVec.ofNat 64 0)) := by
    simp only [arm64_norm]
  rw [BitVec.add_zero] at hfetch
  exact subroutine_ok_of_b hfetch (by simp only [arm64_norm, wp_norm]) rfl
    (by intros; rfl) hpub

/-- Relocatable `<libsignal_core::curve::curve25519::PrivateKey>::derive_public_key_bytes`
(Block `200`) meets `derivePublicKeyBytesSpec pubKey` when `H` satisfies `HookSat` at
`lsPubFromSecretSym`. -/
theorem derive_public_key_bytes_placed_ok [LibsignalPlacement]
    {pubKey : PubKeyFn} {H : String → Option (State → State)}
    (hpub : HookSat H lsPubFromSecretSym (derivePublicKeyBytesSpec pubKey)) :
    subroutine_ok ((blkPC_200).rebase (blkPl_200).base H) (blkPl_200).base
      (derivePublicKeyBytesSpec pubKey) :=
  derive_public_key_bytes_placed_ok_of_contract (ls_hook_ok_of_mem hpub)

theorem derive_public_key_bytes_stack_placed_ok [LibsignalPlacement]
    {pubKey : PubKeyFn} {H : String → Option (State → State)} (hookStack : Nat := 0)
    (hpub : HookSat H lsPubFromSecretSym (derivePublicKeyBytesSpec pubKey)) :
    subroutine_ok ((blkPC_200).rebase (blkPl_200).base H) (blkPl_200).base
      (derivePublicKeyBytesStackSpec pubKey hookStack) :=
  derivePublicKeyBytesStack_of_spec hookStack (derive_public_key_bytes_placed_ok hpub)

end LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytesBudget
