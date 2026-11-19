/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.Defs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefs
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Wire.WireCodeSym -- proof-setup: allow-public-import

/-!
# Shared definitions and callee/hook wrappers for `SignalMessage::try_from`
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.Wire

open Arm64 ProofLib CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

/-! ## Relocatable `[LibsignalPlacement]` Definitions and Callee Contracts (Block `85`) -/

noncomputable abbrev tryFromPlacedProg [LibsignalPlacement] (H : LibsignalHooks) : Program :=
  (blkPC_85).rebase (blkPl_85).base H

/-- Unit witness for `logFilterAddr` / `logOff` (`lsLogFilterAddr`, `lsmpl.ρ "log::MAX_LOG_LEVEL_FILTER"`). -/
@[expose] def tryFromPlacedImg : Unit := ()

@[simp, arm64_norm, wp_norm]
theorem logFilterAddr_tryFromPlacedImg [LibsignalPlacement] :
    LibsignalSession.logFilterAddr tryFromPlacedImg = lsLogFilterAddr :=
  rfl

@[simp, arm64_norm, wp_norm]
theorem logOff_tryFromPlacedImg [LibsignalPlacement] :
    logOff tryFromPlacedImg = (lsLogFilterAddr ↦₆₄ 0#64) :=
  rfl

theorem panic_at_handle_alloc_error2_placed [LibsignalPlacement]
    {H : LibsignalHooks}
    (h_panic : H lsAllocHandleErrorSym = some Rust.panicked) :
    (tryFromPlacedProg H).externAt?
      ((blkPl_85).ρ lsAllocHandleErrorSym) =
      some Rust.panicked :=
  new_externAt?_handle_alloc_error h_panic

structure AllocHooksWPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop where
  dealloc : subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ lsRustDeallocSym)
    (withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack A extHookStack))
  panic_alloc : H lsAllocHandleErrorSym = some Rust.panicked

structure TripleRatchetHooksWPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop where
  alloc : AllocHooksWPlaced A H
  decodeErrorFrom : subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ decodeErrorFromName)
    (withLsCodeRoLoaded lsmpl (decodeErrorFromSpecWithStack A (2 * extHookStack)))
  decodeErrorPush : subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ decodeErrorPushName)
    (withLsCodeRoLoaded lsmpl (decodeErrorPushExternSpecWithStack A (2 * extHookStack)))
  decodeVarintSlow : subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ varintSlowName)
    (withLsCodeRoLoaded lsmpl (decodeVarintSlowSpecWithStack A (64 + 2 * extHookStack)))

@[expose] def IntoBoxedSliceOkPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ intoBoxedSliceName)
    (withLsCodeRoLoaded lsmpl (intoBoxedSliceSpecX A))

@[expose] def TryCloneFromRefOkPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ tryCloneFromRefName)
    (withLsCodeRoLoaded lsmpl (tryCloneFromRefSpecX A))

@[expose] def DecodeVarintSliceOkWPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ decodeVarintSliceName)
    (withLsCodeRoLoaded lsmpl (decodeVarintSliceSpecX A))

@[expose] def Int32MergeOkWPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ int32MergeName)
    (withLsCodeRoLoaded lsmpl (int32MergeSpecX A))

@[expose] def SkipFieldOkWPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ skipFieldName)
    (withLsCodeRoLoaded lsmpl (skipFieldSpecX A))

@[expose] def DropDecodeErrorOkWPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ dropDecodeErrorName)
    (withLsCodeRoLoaded lsmpl (dropDecodeErrorSpecX A))

@[expose] def BytesMergeOkWPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ bytesMergeName)
    (withLsCodeRoLoaded lsmpl (bytesMergeRawSpecX A))

@[expose] def DropSpeOkWPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ dropSpeName)
    (withLsCodeRoLoaded lsmpl (dropSpeSpecX A))

end CryptoVerification.LibsignalTripleRatchet.Wire
