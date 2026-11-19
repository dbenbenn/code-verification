/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.Defs
public meta import ProofLib.SepLogic.CodeLookup
public meta import ProofLib.VCGen
import LibsignalBinary.Proofs.CodeLayout

/-!
# Instruction Fetch and Callee Offsets for Seed `message::merge<Chain>`

Provides instruction-fetch automation and cross-block callee transfers (`bytes::merge`,
`int32::merge`) for `prost::encoding::message::merge::<Chain>` (`0x3974`, block `11`).
-/

public section

namespace CryptoVerification.E2E.Record.DeserializeSeed

section Fetch

open Lean Meta Elab Command Tactic Arm64 ProofLib ProofLib.ProgramReflection

end Fetch

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record

/-! ## Callee Offset Resolution -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

theorem bytesMerge_placed_ok_sub_seedChain [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H) (blkPl_7).base
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (bytesMergeRawSpec A))) :
    subroutine_ok (lsProg_11 H) (lsmpl.base 7)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (bytesMergeRawSpec A)) :=
  ls_call_ro_of_block (callerProg := lsProg_11 H) h

theorem int32Merge_placed_ok_sub_seedChain [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h : subroutine_ok ((blkPC_8).rebase (blkPl_8).base H) (blkPl_8).base
      (withLsCodeLoaded lsmpl (int32MergeSpec A))) :
    subroutine_ok (lsProg_11 H) (lsmpl.base 8)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (int32MergeSpec A)) :=
  ls_call_ro_of_cl (callerProg := lsProg_11 H) h

end Placed

end CryptoVerification.E2E.Record.DeserializeSeed
