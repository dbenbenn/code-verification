/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.SetUnackEpoch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SmallCallees -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesLeavesExt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesChainExt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1CommonExtA -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage2
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.ModelBridge
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCallees
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.VerifySignature
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.VerifySignatureExt
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DropSessionStructureLocal5Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.KemPubSerializeLocal2
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatExt
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Proof
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytes

/-!
# Cryptographic, Session, and Local Callee Contracts for `initiate`

Transfers the PQXDH and SPQR callee contracts onto `initProg img W` (`InitLocalCallees`) and
`initProgExt img ext` (`InitLocalCalleesExt`), and proves the handshake-crate local instantiations
`<kem::Key<Public>>::serialize [local#2]` and `core::ptr::drop_glue::<SessionStructure> [local#5]`.
-/

public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs

/-! ## Symbol names -/

abbrev cliKemPublicKeySerializeName : String :=
  "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::serialize [local#1]"

abbrev cliDropSessionStructureName : String :=
  "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]"

abbrev cliVerifySignatureName : String :=
  "<libsignal_core::curve::PublicKey>::verify_signature"

abbrev cliIsSameAccountName : String :=
  "<libsignal_protocol::identity_key::IdentityKey>::is_same_account"

abbrev cliCalculateAgreementName : String :=
  "<libsignal_core::curve::PrivateKey>::calculate_agreement"

abbrev cliDerivePubKeyBytesName : String :=
  "<libsignal_core::curve::curve25519::PrivateKey>::derive_public_key_bytes"

abbrev cliHandshakeDeriveName : String :=
  "<libsignal_protocol::pqxdh::HandshakeKeys>::derive"

abbrev cliKemCtSerializeName : String :=
  "<libsignal_protocol::kem::Ciphertext>::serialize"

abbrev cliRootKeyCreateChainName : String :=
  "<libsignal_protocol::ratchet::keys::RootKey>::create_chain"

abbrev cliSpqrChainParamsName : String :=
  "libsignal_protocol::ratchet::spqr_chain_params"

abbrev cliSpqrInitialStateName : String :=
  "spqr::initial_state"

abbrev cliSessionStateNewName : String :=
  "<libsignal_protocol::state::session::SessionState>::new"

abbrev cliWithReceiverChainName : String :=
  "<libsignal_protocol::state::session::SessionState>::with_receiver_chain"

abbrev cliWithSenderChainName : String :=
  "<libsignal_protocol::state::session::SessionState>::with_sender_chain"

abbrev cliSetKyberCiphertextName : String :=
  "<libsignal_protocol::state::session::SessionState>::set_kyber_ciphertext"

abbrev cliSetUnackPreKeyMsgName : String :=
  "<libsignal_protocol::state::session::SessionState>::set_unacknowledged_pre_key_message"

abbrev cliSetUnackKyberIdName : String :=
  "<libsignal_protocol::state::session::SessionState>::set_unacknowledged_kyber_pre_key_id"

abbrev cliPromoteStateName : String :=
  "<libsignal_protocol::state::session::SessionRecord>::promote_state"

structure KemPubSerializeGhost where
  keyRef : BitVec 64
  kpkPtr : BitVec 64
  kpk : List (BitVec 8)

/-- Ghost arguments for `<PublicKey>::verify_signature`. -/
structure VerifySignatureGhost where
  pkPtr : BitVec 64
  pk : Pqxdh.Shared.Bytes
  msgPtr : BitVec 64
  m : Pqxdh.Shared.Bytes
  sigPtr : BitVec 64
  sig : Pqxdh.Shared.Bytes

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate
