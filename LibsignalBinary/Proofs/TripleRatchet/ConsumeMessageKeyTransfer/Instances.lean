/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.Hmac -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.Assembly
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndex
import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOne
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer

/-!
# Base-Program Subroutine Contracts on `tripleRatchetProgAt` and `[LibsignalPlacement]`

Transfers `LibsignalSession` subroutine contracts (`consume_message_key`,
`find_receiver_chain_index`, `hmac_sha256`, and `RawVec<Chain>::grow_one`) to
`tripleRatchetProgAt{,Ext}` via `session_subroutine_ok_mono`, proves hook-parametric contracts for
`PublicKey::deserialize`, `ct_eq`, and `PublicKey::eq`, and provides relocatable
`[LibsignalPlacement]` counterparts.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchetRepr

/-! ## Symbol names -/

/-- `RatchetState::consume_message_key` (image offset `0xded8`). -/
abbrev cmkName : String :=
  "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"

/-- `RatchetState::find_receiver_chain_index` (image offset `0xea88`). -/
abbrev findIndexName : String :=
  "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index"

/-- `crypto::hmac_sha256` (image offset `0x20b88`). -/
abbrev hmacName : String := "libsignal_protocol::crypto::hmac_sha256"

/-- `RawVec<Chain>::grow_one` (image offset `0x15cac`), sharing machine code with
`RawVec<MessageKey>::grow_one` (element size `104`, alignment `8`). -/
abbrev growOneChainName : String :=
  "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one"

/-- `PublicKey::deserialize` (image offset `0x3db50`). -/
abbrev deserializeName : String := "<libsignal_core::curve::PublicKey>::deserialize"

/-- `<PublicKey as PartialEq>::eq` (image offset `0x3ebf0`). -/
abbrev publicKeyEqName : String :=
  "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq"

/-- `<[u8] as ConstantTimeEq>::ct_eq` from `libsignal_core` (image offset `0x3ecc4`). -/
abbrev ctEqName : String := "<[u8] as subtle::ConstantTimeEq>::ct_eq"

/-! ## Transferred from the base program -/

section AnyHooks
open ProofLib.ProgramReflection

theorem tripleRatchetProgAt_blackBox_trap (C : Crypto)
    (abs : String → Option (State → State)) :
    Rust.withPanics (trTrapExterns C abs) "subtle::black_box::<u8>" =
      some CryptoVerification.LibsignalSession.blackBoxHook := by
  rw [withPanics_trTrap_ne C abs (by decide)]
  rfl_kernel

/-- `Rust.withPanics (tripleRatchetExterns C ctl abs)` maps `"subtle::black_box::<u8>"` to
`blackBoxHook`. -/
theorem tripleRatchetProgAt_blackBox (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    Rust.withPanics (tripleRatchetExterns C ctl abs) "subtle::black_box::<u8>" =
      some CryptoVerification.LibsignalSession.blackBoxHook := by
  rfl_kernel

/-- `"subtle::black_box::<u8>"` is not a Rust panic symbol, so `HookSat` lifts across `Rust.withPanics`. -/
theorem hookSat_withPanics_blackBox {α : Type} {ext : String → Option (State → State)}
    {spec : Spec α} (h : HookSat ext "subtle::black_box::<u8>" spec) :
    HookSat (Rust.withPanics ext) "subtle::black_box::<u8>" spec := by
  have hp : Rust.isPanicSymbol "subtle::black_box::<u8>" = false := by rfl_kernel
  obtain ⟨f, hf, hok⟩ := h
  exact ⟨f, by simp [Rust.withPanics, hp, hf], hok⟩

end AnyHooks

/-! ## Relocatable `[LibsignalPlacement]` Contracts -/

section Placed

variable [LibsignalPlacement]

/-- Relocatable `[LibsignalPlacement]` contract for `find_receiver_chain_index` (Block `26`). -/
theorem findIndex_placed_ok {H : String → Option (State → State)} (A : RustAlloc)
    (h_bb : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook) :
    subroutine_ok ((blkPC_26).rebase (blkPl_26).base H) (blkPl_26).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.LibsignalSession.FindReceiverChainIndex.findPlacedSpec A)) :=
  CryptoVerification.LibsignalSession.find_receiver_chain_index_placed_ok A h_bb

theorem findIndex_placed_ok_at_block {callerProg : Program} {i : Nat}
    {H : String → Option (State → State)} [IsLsBlockProg callerProg i H] (A : RustAlloc)
    (h_bb : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 26)
      (withLsCodeLoaded lsmpl
        (CryptoVerification.LibsignalSession.FindReceiverChainIndex.findPlacedSpec A)) :=
  ls_subroutine_ok_transfer (findIndex_placed_ok A h_bb) hi

/-- Relocatable `[LibsignalPlacement]` contract for `crypto::hmac_sha256` (Block `73`)
with `hmacPlacedSpec F`. -/
theorem hmac_placed_ok (F : ShaCompress)
    {H : String → Option (State → State)}
    (h_mc : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym = some hookMemcpy)
    (h_ms : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemsetSym = some hookMemset)
    (h_c256 : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym =
      some (CryptoVerification.LibsignalHmac.compress256Hook F)) :
    subroutine_ok ((blkPC_73).rebase (blkPl_73).base H) (blkPl_73).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.LibsignalSession.CryptoHmacSha256.hmacPlacedSpec F)) :=
  CryptoVerification.LibsignalSession.hmac_sha256_placed_ok F h_mc h_ms h_c256

/-- Relocatable `[LibsignalPlacement]` contract for `crypto::hmac_sha256` (Block `73`)
with `hmacSpec F` augmented with `LibsignalRoLoaded lsmpl`. -/
theorem hmac_placed_ro_ok (F : ShaCompress)
    {H : String → Option (State → State)}
    (h_mc : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym = some hookMemcpy)
    (h_ms : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemsetSym = some hookMemset)
    (h_c256 : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym =
      some (CryptoVerification.LibsignalHmac.compress256Hook F)) :
    subroutine_ok ((blkPC_73).rebase (blkPl_73).base H) (blkPl_73).base
      (withLsCodeLoaded lsmpl
        { CryptoVerification.LibsignalSession.hmacSpec F with
          pre := fun g s => (CryptoVerification.LibsignalSession.hmacSpec F).pre g s ∗
            ⌜LibsignalRoLoaded lsmpl s.mem⌝ }) :=
  CryptoVerification.LibsignalSession.hmac_sha256_placed_ro_ok F h_mc h_ms h_c256

theorem hmac_placed_ro_ok_at_block {callerProg : Program} {i : Nat}
    (F : ShaCompress) {H : String → Option (State → State)} [IsLsBlockProg callerProg i H]
    (h_mc : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemcpySym = some hookMemcpy)
    (h_ms : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsMemsetSym = some hookMemset)
    (h_c256 : H CryptoVerification.LibsignalSession.CryptoHmacSha256.lsCompress256Sym =
      some (CryptoVerification.LibsignalHmac.compress256Hook F))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 73)
      (withLsCodeLoaded lsmpl
        { CryptoVerification.LibsignalSession.hmacSpec F with
          pre := fun g s => (CryptoVerification.LibsignalSession.hmacSpec F).pre g s ∗
            ⌜LibsignalRoLoaded lsmpl s.mem⌝ }) :=
  ls_subroutine_ok_transfer (hmac_placed_ro_ok F h_mc h_ms h_c256) hi

/-- Relocatable `[LibsignalPlacement]` contract for `RawVec<Chain>::grow_one` (Block `43`). -/
theorem growOneChain_placed_ok {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_shim : H lsNoAllocShimSym = some hookNoop)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_realloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (h_panic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base
      (withLsCodeLoaded lsmpl (CryptoVerification.LibsignalSession.growOneSpec A)) :=
  CryptoVerification.LibsignalSession.grow_one_placed_ok h_shim h_alloc h_realloc h_panic

theorem growOneChain_placed_ok_at_block {callerProg : Program} {i : Nat} {A : RustAlloc}
    {H : String → Option (State → State)} [IsLsBlockProg callerProg i H]
    (h_shim : H lsNoAllocShimSym = some hookNoop)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_realloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 43)
      (withLsCodeLoaded lsmpl (CryptoVerification.LibsignalSession.growOneSpec A)) :=
  ls_subroutine_ok_transfer (growOneChain_placed_ok h_shim h_alloc h_realloc h_panic) hi

/-- Relocatable `[LibsignalPlacement]` contract for `PublicKey::deserialize` (Block `201`). -/
theorem deserialize_placed_ok (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_201).rebase (blkPl_201).base H) (blkPl_201).base
      CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserializePlacedSpec :=
  CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserialize_placed_ok H

theorem deserialize_placed_ok_withLsCodeLoaded (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_201).rebase (blkPl_201).base H) (blkPl_201).base
      (withLsCodeLoaded lsmpl
        CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserializePlacedSpec) :=
  subroutine_ok_withLsCodeLoaded_of_plain (deserialize_placed_ok H)

/-- Relocatable `[LibsignalPlacement]` contract for `<[u8] as ConstantTimeEq>::ct_eq` (Block `213`). -/
theorem ctEq_placed_ok {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base
      CryptoVerification.LibsignalSession.FindReceiverChainIndex.ctEqSliceSpec :=
  CryptoVerification.LibsignalSession.FindReceiverChainIndex.ct_eq_placed_ok h_bb

theorem ctEq_placed_ok_withLsCodeLoaded {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base
      (withLsCodeLoaded lsmpl
        CryptoVerification.LibsignalSession.FindReceiverChainIndex.ctEqSliceSpec) :=
  subroutine_ok_withLsCodeLoaded_of_plain (ctEq_placed_ok h_bb)

/-- Relocatable `[LibsignalPlacement]` contract for `<PublicKey as PartialEq>::eq` (Block `212`). -/
theorem publicKeyEq_placed_ok {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook) :
    subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (blkPl_212).base
      (withLsCodeLoaded lsmpl
        CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKeyEqSpec) :=
  CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKey_eq_placed_ok h_bb

end Placed

end CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer

