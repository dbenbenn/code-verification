/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Mac.Defs
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Hmac.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEq -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Bytes.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefs
import LibsignalBinary.Proofs.TripleRatchet.Alloc.ChainKeyToPb
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DoReserve
import LibsignalBinary.Proofs.TripleRatchet.Alloc.FinishGrow
import LibsignalBinary.Proofs.TripleRatchet.Alloc.IntoBoxedSlice
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerialize
import LibsignalBinary.Proofs.TripleRatchet.Alloc.TryCloneFromRef
import LibsignalBinary.Proofs.TripleRatchet.Bytes.Drops
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From
import LibsignalBinary.Proofs.TripleRatchet.ChainKey.FindReceiverChainKey
import LibsignalBinary.Proofs.TripleRatchet.ChainKey.MessageKeys
import LibsignalBinary.Proofs.TripleRatchet.ChainKey.NextChainKey
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.CtEqRO
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSlice
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.ProtoExt
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.ProtoX
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.VecExt
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.VecX
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Ext
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.X
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.Ext
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.X
import LibsignalBinary.Proofs.TripleRatchet.Getters.Identity
import LibsignalBinary.Proofs.TripleRatchet.Getters.SameAccount
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarint
import ProofLib.SepLogic.WP.Apply

/-!
# Callee Contract Glue for Triple Ratchet Proofs

Assembles unconditional and hook-scoped `subroutine_ok` corollaries across the triple-ratchet
submodules (`Alloc`, `Prost`, `Bytes`, `Getters`, `ChainKey`, and
`ConsumeMessageKeyTransfer`), discharging callee-hypothesis abbreviations on
`tripleRatchetProgAtExt`, `tripleRatchetProgAt`, and `AllocContractsX`.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.Glue

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet

/-! ## Callee Discharges Across Submodules -/

section Ext32Glue

open ProofLib.ProgramReflection

theorem hookSat_withPanics_blackBox {ext : String → Option (State → State)}
    {α : Type} {spec : Spec α}
    (h_bb : HookSat ext "subtle::black_box::<u8>" spec) :
    HookSat (Rust.withPanics ext) "subtle::black_box::<u8>" spec := by
  rcases h_bb with ⟨f, hf, hok⟩
  refine ⟨f, ?_, hok⟩
  simpa [Rust.withPanics, Rust.isPanicSymbol] using hf

end Ext32Glue

end CryptoVerification.LibsignalTripleRatchet.Glue
