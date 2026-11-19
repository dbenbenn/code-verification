/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Instances -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.Defs
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.CodeLayout

/-!
# Instruction Fetch, Jump Table, and Callee Transfers for Seed `merge_field` Tag `7`

Provides instruction-fetch automation, `.rodata` jump-table lemmas, and cross-block callee transfers
(`message::merge<Chain>` and `RawVec<Chain>::grow_one`) for `SessionStructure::merge_field`
(`0x581c`, block `15`) on tag `7`.
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
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer
open CryptoVerification.E2E.Record

open ProofLib.ProgramReflection in
/-- The 15-byte jump table of `SessionStructure::merge_field` at rodata `0x4901c` (tags 1..15). -/
def mfJumpTable_receiverChains : List (BitVec 8) :=
  [0x00#8, 0x82#8, 0x77#8, 0x5f#8, 0x19#8, 0x32#8, 0x8d#8, 0x6d#8,
   0xb5#8, 0xd6#8, 0xcb#8, 0x6d#8, 0x0b#8, 0x4c#8, 0x24#8]

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

theorem chainMerge_placed_ok_sub_receiverChains [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h : ChainMergeSeedPlacedOk H) :
    subroutine_ok (lsProg_15 H) (lsmpl.base 11) chainMergeSeedPlacedSpec :=
  ls_call_ro_of_block (callerProg := lsProg_15 H) h

theorem growOneChain_placed_ok_sub_receiverChains [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h : subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base
      (withLsCodeLoaded lsmpl (CryptoVerification.LibsignalSession.growOneSpec A0))) :
    subroutine_ok (lsProg_15 H) (lsmpl.base 43)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (CryptoVerification.LibsignalSession.growOneSpec A0)) :=
  ls_call_ro_of_cl (callerProg := lsProg_15 H) h

theorem rodata_mfJumpTable_placed_intro_receiverChains [LibsignalPlacement]
    {m : Memory} {P : SepProp} (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (lsmpl.ρ mergeFieldRodataSym ↦ᵣ mfJumpTable_receiverChains) ∗ P :=
  lsro_slice_intro hro (by lsro_addr) (by decide +kernel) hP

theorem rodata_mfJumpTable_tag7_placed_intro_receiverChains [LibsignalPlacement]
    {m : Memory} {P : SepProp} (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ ((lsmpl.ρ mergeFieldRodataSym + 6#64) ↦₈ᵣ 0x8d#8) ∗ P :=
  lsro8_intro hro (by lsro_addr) (by decide +kernel) hP

end Placed

end CryptoVerification.E2E.Record.DeserializeSeed
