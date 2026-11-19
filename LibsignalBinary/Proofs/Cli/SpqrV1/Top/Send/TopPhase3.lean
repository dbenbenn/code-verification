/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.States1a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.TopDecodes -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Defs
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Decodes -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.Decodes -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenPhase -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Contracts -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.TopRegions -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesBridge1
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesBridge2
import LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.AllocContracts4KExt
import LibsignalBinary.Proofs.SignalSession.Coins.Defs
import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampled
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesFinish1
import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendDispatch
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked2
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1Acknowledged
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1Received
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1Sampled
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2Sampled
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkReceivedCt1Sampled
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkSentCt1Received
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderReceived
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSent
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampled
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysUnsampled
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedNoHeaderReceived
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoder
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1Sent
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1Received
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateProof
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesBridge2
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Top
import LibsignalBinary.Proofs.SpqrV1.Top.Send.TopPhase3
import LibsignalBinary.Proofs.TripleRatchet.Bytes.Drops
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLen -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.OuterLoop
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOk

/-!
# Phase 3 & 4 Composition of `spqr::send::<signal_session_ratchet::Coins>` (`+3196 -> s0.x30`)

Composes `<Message>::serialize`, `<States>::into_pb`, `PqRatchetState` encoding, drop cleanup,
and the shared return epilogue (`+3196 -> s0.x30`) on the CLI image.
-/

public section

set_option autoImplicit false

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

set_option linter.unusedVariables false

set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames.LibsignalSession (Crypto ShaCompress)

open CryptoVerification

open CryptoVerification.CodeLayout

open CryptoVerification.RustHeap

open CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalSpqrV1

open CryptoVerification.SpqrV1.Alloc

open CryptoVerification.SpqrV1.Drop

open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

open CryptoVerification.SpqrV1.Prost.EncodeToVec

open CryptoVerification.SpqrV1.ChainProofs

open CryptoVerification.SpqrV1.Top.DecodeState

open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation

open CryptoVerification.SpqrV1.Top.ChainFrom

open CryptoVerification.SpqrV1.Top.MessageSerialize

open CryptoVerification.SpqrV1.Top.StateSize

open CryptoVerification.SpqrV1.States

open CryptoVerification.SpqrV1.States.FromPb

open CryptoVerification.SpqrV1.States.IntoPb

open CryptoVerification.SpqrV1.States.Leaves

open CryptoVerification.SpqrV1.Auth

open CryptoVerification.SpqrV1.Kdf

open CryptoVerification.SpqrV1.GF.UnacceleratedMul

open CryptoVerification.SpqrV1.GF.Mul2U16

open CryptoVerification.SpqrV1.Poly

open CryptoVerification.SpqrV1.Poly.EncodeBytes

open CryptoVerification.SpqrV1.Poly.NextChunk

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local simp, local arm64_norm, local wp_norm] ite_zero32_self ite_zero64_self

end CryptoVerification.SpqrV1.Top.Send

/-! ## Trap-at-rng (`trTrapExterns`) Hook Lifting and `decode_state_ok_x_trap` -/

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen hiding vecU8Buf vecU8At_eq_header_sep_buf
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge.ChunkedMerge
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.SpqrV1.Top.Send (spqrHooks_tripleRatchetExterns)

/-- `sessionExterns C.F abs` embeds into `trTrapExterns C abs` under `Rust.withPanics`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.sessionExterns_le_trTrap
    (C : Crypto) (abs : String → Option (State → State)) :
    ∀ n f, Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns C.F abs) n = some f →
      Rust.withPanics (trTrapExterns C abs) n = some f := by
  intro n f h
  have hr : n ≠ rngFillName := by
    rintro rfl
    simp [Rust.withPanics, CryptoVerification.LibsignalSession.sessionExterns,
      rngFillName, Rust.isPanicSymbol] at h
  rw [withPanics_trTrap_eq_kit C 0#64 abs hr]
  exact ConsumeMessageKeyTransfer.sessionExterns_le C 0#64 abs n f h

/-- Transfer a `HookSat` contract away from `rngFillName` from `tripleRatchetExterns` to `trTrapExterns`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.hookSat_trTrap_of_kit
    {α : Type} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {sym : String} {spec : Spec α}
    (hr : sym ≠ rngFillName)
    (h : HookSat (tripleRatchetExterns C ctl abs) sym spec) :
    HookSat (trTrapExterns C abs) sym spec := by
  rcases h with ⟨fn, hfn, hok⟩
  exact ⟨fn, (trTrapExterns_eq_tripleRatchetExterns C ctl abs hr).trans hfn, hok⟩

/-- Lift `SpqrHooks C A K abs` to `trTrapExterns C abs`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrHooks_trTrapExterns
    {C : Crypto} {A : RustAlloc} {K : MlKem} {abs : String → Option (State → State)}
    (hSH : SpqrHooks C A K abs) :
    SpqrHooks C A K (trTrapExterns C abs) :=
  let hk := spqrHooks_tripleRatchetExterns (C := C) (ctl := 0#64) hSH
  { hk with
    fromSeed := CryptoVerification.Cli.SpqrV1.Top.Send.hookSat_trTrap_of_kit (by decide) hk.fromSeed
    pk1 := CryptoVerification.Cli.SpqrV1.Top.Send.hookSat_trTrap_of_kit (by decide) hk.pk1
    pk2 := CryptoVerification.Cli.SpqrV1.Top.Send.hookSat_trTrap_of_kit (by decide) hk.pk2
    encaps1 := CryptoVerification.Cli.SpqrV1.Top.Send.hookSat_trTrap_of_kit (by decide) hk.encaps1
    encaps2 := CryptoVerification.Cli.SpqrV1.Top.Send.hookSat_trTrap_of_kit (by decide) hk.encaps2
    decaps := CryptoVerification.Cli.SpqrV1.Top.Send.hookSat_trTrap_of_kit (by decide) hk.decaps
    validatePk := CryptoVerification.Cli.SpqrV1.Top.Send.hookSat_trTrap_of_kit (by decide) hk.validatePk
    hmac := CryptoVerification.Cli.SpqrV1.Top.Send.hookSat_trTrap_of_kit (by decide) hk.hmac }

end CryptoVerification.SpqrV1.Top.DecodeState

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
open CryptoVerification.CodeLayout
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.NextChunk

end CryptoVerification.SpqrV1.Top.Send

