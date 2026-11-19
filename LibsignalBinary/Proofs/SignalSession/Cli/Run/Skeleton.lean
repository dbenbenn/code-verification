/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Pub.DropSpe.Proof -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Concat2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropPreKeyMsg -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSignalMessage -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropStores -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBase
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.WritePaths -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Specs
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyDecode
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommon
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressA1
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Reserve11
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StrlenUtf8A1
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.TryAllocateIn3
import LibsignalBinary.Proofs.SignalSession.Cli.PublicSpecs
import ProofLib.GenDecodes
import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHook
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTraced
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Defs

/-!
# `signal_session::run`: Callee Slots, Hook Bundles, and Stack Budgets

Defines the callee slot abstraction (`CalleeSlot`, `RunSlots`), extern hook bundles (`RunHooks` and
contract-backed `RunHooksExt`), callee contract bundle (`RunCallees`), stack frame budget
(`runFrame = 0x2a50`, `runCalleeNeed`, `runNeed`), and derived leaf and drop callee lemmas for
`signal_session::run`.
-/

public section

set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunSkeleton

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open Arm64.Process
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops

/-! ## 1. Re-exported drop and slice-concatenation specs -/

export CryptoVerification.SignalSession.Cli.DropSpeProof (dropSpeSpecStk)
export CryptoVerification.SignalSession.Cli.RunProofs (cliConcatName cliConcat2Spec)
export CryptoVerification.SignalSession.Cli.RunProofs
  (cliDropStoresName DropStoresGhost dropStoresSpec)
export CryptoVerification.SignalSession.Cli.RunProofs
  (cliDropSignalMessageName DropSignalMessageGhost dropSignalMessageSpec)
export CryptoVerification.SignalSession.Cli.RunProofs
  (cliDropPreKeyMsgName DropPreKeyMsgGhost dropPreKeyMsgSpec)

/-! ## 2. Wrapper callee slots -/

abbrev wrapEncryptName : String := "libsignal_cli_ratchet::encrypt"
abbrev wrapDecryptSignalName : String := "libsignal_cli_ratchet::decrypt_signal"
abbrev wrapInitiateName : String := "libsignal_cli_handshake::initiate"
abbrev wrapDecryptPrekeyName : String := "libsignal_cli_handshake::decrypt_prekey"
abbrev kemDeserializeName : String :=
  "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::deserialize"

/-- Abstract callee contract packaging a ghost parameter type, stack-indexed `Spec`, and minimum stack requirement `need`. -/
structure CalleeSlot where
  Ghost : Type
  spec : Nat → Spec Ghost
  need : Nat

/-- Callee slots of `signal_session::run`: `encrypt`, `decryptSignal`, `initiate`, `decryptPrekey`, and `kemDeserialize`. -/
structure RunSlots where
  encrypt : CalleeSlot
  decryptSignal : CalleeSlot
  initiate : CalleeSlot
  decryptPrekey : CalleeSlot
  kemDeserialize : CalleeSlot

/-! ## 3. Hook and callee hypotheses -/

/-- Configurable leaf stack budget for `signal_session_io::read_file`. -/
structure RunBudgets where
  readFile : Nat

abbrev pathNeed : Nat := 0x70 + max doReserveStackX extHookStack
abbrev splitIdNeed : Nat := 0x60 + dropSpeStackX
abbrev splitSignedNeed : Nat := 0x60 + max splitIdNeed dropSpeStackX
abbrev RunBudgets.dirGetNeed (B : RunBudgets) : Nat :=
  0x70 + max (max pathNeed B.readFile) extHookStack
abbrev RunBudgets.bundleReadNeed (B : RunBudgets) : Nat :=
  0x50 + max (max pathNeed B.readFile) extHookStack

/-- Stack frame size (`0x2a50` bytes, including saved registers) of `signal_session::run`. -/
abbrev runFrame : Nat := 0x2a50

/-- Maximum stack budget required among all direct callees and extern hooks of `signal_session::run`. -/
@[expose] def runCalleeNeed (B : RunBudgets) (σ : RunSlots) : Nat :=
  [ 0xB0 + extHookStack,             -- address
    finishGrowStackX,                 -- try_allocate_in [local#3]
    B.readFile,                       -- read_file
    pathNeed, B.dirGetNeed, B.bundleReadNeed, splitIdNeed, splitSignedNeed,
    0x60,                             -- IdentityKey::decode
    smallRootStack,                   -- SignalMessage::try_from
    CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromStack,
    32 + extHookStack,                -- drop_glue<SPE> [local#4], <SignalMessage>, <PKSM>
    96 + extHookStack,                -- drop_glue<Stores>, concat [local#3]
    extHookStack,                     -- direct hook calls
    σ.encrypt.need, σ.decryptSignal.need, σ.initiate.need, σ.decryptPrekey.need,
    σ.kemDeserialize.need ].foldr max 0

/-- Total stack requirement `runFrame + runCalleeNeed B σ` of `signal_session::run`. -/
@[expose] def runNeed (B : RunBudgets) (σ : RunSlots) : Nat := runFrame + runCalleeNeed B σ

/-! ## 6. Contract-backed `RunHooksExt` and callees -/

abbrev extRunBudgets : RunBudgets := { readFile := extHookStack }

private theorem stackAt_split_ge_skel {sp : BitVec 64} {inner stk : Nat}
    (hle : inner ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    stackAt sp stk =
      memRegion (sp - BitVec.ofNat 64 stk) (stk - inner) ∗ stackAt sp inner := by
  have h1 := stackAt_split_bottom sp inner (stk - inner) (by omega)
  rwa [Nat.add_sub_of_le hle] at h1

example : runFrame = 10832 := rfl

end CryptoVerification.SignalSession.Cli.RunSkeleton

