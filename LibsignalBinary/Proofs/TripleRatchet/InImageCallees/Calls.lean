/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ParseServiceId
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PrivateKeySerialize
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ProtocolAddressDisplay
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.All -- shake: keep

/-!
# Call-Site Lemmas for In-Image Whole-Crate Callees

Restates the contracts for `PublicKey::try_from`, `ServiceId::parse_from_service_id_string`,
`PrivateKey::serialize`, and `<ProtocolAddress as Display>::fmt` at call-site offset
`fnAddr name + k` (as well as relocatable cross-block `[LibsignalPlacement]` call sites).
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr

/-- Relocatable `PublicKey::try_from` (Block `211`) lifted to any caller block `prog`. -/
theorem pk_try_from_placed_ok_at [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : String → Option (State → State)} [IsLsBlockProg prog i H]
    (hi : i < 619 := by decide) (_hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsmpl.base 211) (withLsCodeLoaded lsmpl pkTryFromPlacedSpec) :=
  ls_subroutine_ok_of_block (callerProg := prog)
    (subroutine_ok_withLsCodeLoaded_of_plain (pkTryFrom_placed_ok H)) (_hi := hi)

/-- Relocatable `ServiceId::parse_from_service_id_string` (Block `206`) lifted to any caller block
`prog` from `huuid` on Block `252`. -/
theorem parse_sid_placed_ok_at_of_contract [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : String → Option (State → State)} [IsLsBlockProg prog i H]
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H)
      (blkPl_252).base (uuidTryParseSpec uuidTryParse))
    (hi : i < 619 := by decide) (_hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeSpec uuidTryParse)) :=
  ls_subroutine_ok_of_block (callerProg := prog)
    (parseSid_placed_ok_of_contract H huuid) (_hi := hi)

/-- Relocatable stack-framed `ServiceId::parse_from_service_id_string` (Block `206`) lifted to any
caller block `prog` from `huuid` on Block `252`. -/
theorem parse_sid_placed_ok_at_of_contract_stack [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : String → Option (State → State)} [IsLsBlockProg prog i H] (hookStack : Nat := 0)
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H)
      (blkPl_252).base (withLsCodeLoaded lsmpl (uuidTryParseStackSpec hookStack)))
    (hi : i < 619 := by decide) (_hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeStackSpec hookStack)) :=
  ls_subroutine_ok_of_block (callerProg := prog)
    (parseSid_placed_ok_of_contract_stack H hookStack huuid) (_hi := hi)

/-- Relocatable `ServiceId::parse_from_service_id_string` (Block `206`) lifted to any caller block
`prog` from `uuidTryParseCodeSpec uuidTryParse` on Block `252`. -/
theorem parse_sid_placed_ok_at_of_code [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : String → Option (State → State)} [IsLsBlockProg prog i H]
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H)
      (blkPl_252).base (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse)))
    (hi : i < 619 := by decide) (_hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeSpec uuidTryParse)) :=
  ls_subroutine_ok_of_block (callerProg := prog)
    (parseSid_placed_ok_of_code H huuid) (_hi := hi)

/-- Relocatable `PrivateKey::serialize` (Block `208`) lifted to any caller block `prog`. -/
theorem priv_serialize_placed_ok_at [LibsignalPlacement] {prog : Program} {i : Nat}
    {A : RustAlloc} {H : String → Option (State → State)} [IsLsBlockProg prog i H]
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hi : i < 619 := by decide) (_hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsmpl.base 208)
      (withLsCodeLoaded lsmpl (privSerializeSpec A)) :=
  ls_subroutine_ok_of_block (callerProg := prog)
    (subroutine_ok_withLsCodeLoaded_of_plain (privSerialize_placed_ok hshim halloc hpanic))
    (_hi := hi)

/-- Relocatable `PrivateKey::serialize` (`privSerializeSpecX A`, Block `208`) lifted to any caller
block `prog`. -/
theorem priv_serialize_placed_ok_at_x [LibsignalPlacement] {prog : Program} {i : Nat}
    {A : RustAlloc} {H : String → Option (State → State)} [IsLsBlockProg prog i H]
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hi : i < 619 := by decide) (_hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsmpl.base 208)
      (withLsCodeLoaded lsmpl (privSerializeSpecX A)) :=
  ls_subroutine_ok_of_block (callerProg := prog)
    (subroutine_ok_withLsCodeLoaded_of_plain (privSerialize_placed_ok_x hshim halloc hpanic))
    (_hi := hi)

/-- Relocatable `<ProtocolAddress as Display>::fmt` (Block `215`) lifted to any caller block `prog`. -/
theorem addr_display_placed_ok_at [LibsignalPlacement] {prog : Program} {i : Nat}
    {A : RustAlloc} {H : String → Option (State → State)} [IsLsBlockProg prog i H]
    (hW : HookSat H lsFmtWriteSym (fmtWriteSpec A))
    (hi : i < 619 := by decide) (_hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsmpl.base 215)
      (withLsCodeLoaded lsmpl (addrDisplaySpec A)) :=
  ls_subroutine_ok_of_block (callerProg := prog)
    (subroutine_ok_withLsCodeLoaded_of_plain (addrDisplay_placed_ok hW))
    (_hi := hi)

end CryptoVerification.LibsignalTripleRatchet
