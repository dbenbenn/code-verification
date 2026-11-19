/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.DropChain2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.SpecRestrict -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Mac.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.Defs

/-!
# Segment Specifications and Callee Hypotheses for `try_decrypt_with_state::<PqxdhRng>`

Intermediate segment contracts and callee `subroutine_ok` hypotheses for
`libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>`
(image offset `0x6eff8`, 822 instructions, `+0x000 .. +0xcd4`), supporting `tryDecryptSpec` and
`TryDecryptRunStmt` (`Root`).

Defines:
- Callee `subroutine_ok` hypotheses (`LocalIdentityKeyOk`, `IsSameAccountOk`, `ClearUpkOk`,
  `DropChainOk`, `ChainKeyToPbOk`, `DerivePublicKeyBytesOk`, `VerifyMacWithAddressesOk`, `CmkOk`,
  `GrowOneChainOk`) bundled with imported callee predicates into `TryDecryptCallees`.
- Checkpoint PCs (`segS1PC` .. `segS9PC`, `errTailPC`, `s3EvictLoopPC`, `errDropChainLoopPC`),
  stack frame layout predicates, and intermediate seam invariants.
- Segment contracts `S0Spec` .. `S9Spec` and `ErrTailSpec`, together with `TryDecryptOk`.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalSession

abbrev tryDecryptName : String :=
  "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_pqxdh_e2e::PqxdhRng>"

abbrev dropChainName : String := dropChain2Name

/-! ## 1. Callee Symbol Names and `subroutine_ok` Hypotheses -/

abbrev cmkName : String := "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"

/-- Symbol name (`0x15cac`) for `<RawVec<Chain>>::grow_one` (called at `try_decrypt+0xa98`; shared
monomorphization with `RawVec<MessageKey>::grow_one` at `size = 104`, `align = 8`). -/
abbrev growOneChainName : String :=
  "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one"

/-- Own stack frame size of `try_decrypt_with_state` (`+0x000: stp x29, x30, [sp, #-0x60]!` and
`+0x01c: sub sp, sp, #0x580`, total `0x5e0` = 1504 B, restored at `+0x394 .. +0x3ac`). -/
abbrev tryDecryptFrameSize : Nat := 1504

/-- Stack budget below `sp = s0.sp - 1504#64` available to callees of `try_decrypt_with_state`
(`rootStack - 1504 = 262144 - 1504 = 260640` B, which exceeds every callee stack budget including
`smallRootStack = 65536` B for `TR::from_session_state`, `spqrRecvStack = 16384` B, and
`cmkStack = 8192` B). -/
abbrev tryDecryptSubStack : Nat := rootStack - tryDecryptFrameSize

/-- Callee-saved register save area `[sp0 - 96#64 .. sp0]` (`[sp + 0x580 .. sp + 0x5e0]`, 96 bytes)
written by the prologue `+0x000 .. +0x014` and restored by `+0x394 .. +0x3ac`. -/
@[expose] def tryDecryptSavedRegs (sp0 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((sp0 - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp0 - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((sp0 - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((sp0 - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((sp0 - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19)

/-- Word 0 (`x26` at `errTailPC`) of `speAt` for `e`. -/
@[expose] def speTag : SignalProtocolError → BitVec 64
  | .invalidState => speWord 1
  | .ciphertextMessageTooShort _ => speWord 3
  | .legacyCiphertextVersion _ => speWord 4
  | .unrecognizedCiphertextVersion _ => speWord 5
  | .invalidProtobufEncoding => speWord 2
  | .noKeyTypeIdentifier => speWord 7
  | .badKeyType _ => speWord 8
  | .badKeyLength _ => speWord 9
  | .invalidKeyAgreement => speWord 10
  | .invalidSessionStructure _ => speWord 20
  | .duplicatedMessage _ _ => speWord 23
  | .invalidMessage _ _ => speWord 24
  | .panic => 0#64

/-- The 40-byte payload of `speAt A fnName a e` at `p = a + 8#64` (`sp + 0x168..0x190` at
`errTailPC`). -/
@[expose] def speBodyAt (A : RustAlloc) (fnName : List (BitVec 8)) (p : BitVec 64) :
    SignalProtocolError → SepProp
  | .invalidState =>
    (∃∗ bs : List (BitVec 8), vecU8 A p bs) ∗ strRefAt (p + 24#64) fnName
  | .ciphertextMessageTooShort n =>
    (p ↦₆₄ BitVec.ofNat 64 n) ∗ memRegion (p + 8#64) 32
  | .legacyCiphertextVersion v =>
    (p ↦₈ v) ∗ memRegion (p + 1#64) 39
  | .unrecognizedCiphertextVersion v =>
    (p ↦₈ v) ∗ memRegion (p + 1#64) 39
  | .invalidProtobufEncoding => memRegion p 40
  | .noKeyTypeIdentifier => memRegion p 40
  | .badKeyType t => (p ↦₈ t) ∗ memRegion (p + 1#64) 39
  | .badKeyLength n =>
    (p ↦₆₄ BitVec.ofNat 64 n) ∗ memRegion (p + 8#64) 32
  | .invalidKeyAgreement => memRegion p 40
  | .invalidSessionStructure r =>
    strRefAt p (invalidSessionStructureStr r) ∗ memRegion (p + 16#64) 24
  | .duplicatedMessage i c =>
    (p ↦₃₂ i) ∗ ((p + 4#64) ↦₃₂ c) ∗ memRegion (p + 8#64) 32
  | .invalidMessage t r =>
    invalidMessageStrAt A p r ∗ ((p + 24#64) ↦₈ msgTypeByte t) ∗ memRegion (p + 25#64) 15
  | .panic => ⌜False⌝

end CryptoVerification.LibsignalTripleRatchet.DecryptPq
