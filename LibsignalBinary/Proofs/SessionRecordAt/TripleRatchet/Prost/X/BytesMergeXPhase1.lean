/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.BytesMergeXPhase2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DoReserveExt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Wire.X.CalleesW -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.BytesLeavesX
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.DecodeErrorFromX
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.DecodeVarintSlowX
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.VarintSliceX
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Wire.X.TryFromDefsX
import LibsignalBinary.Proofs.TripleRatchet.Bytes.Drops
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# Phase 1 and Top-Level Proof for `prost::encoding::bytes::merge`

Verifies `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]>` (`0x2788`, block `7`)
against `bytesMergeSpecW` on `contractProg img.base ext` and `bytesMergePlacedSpecW` under
`[LibsignalPlacement]`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet.Prost.X
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.X

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.WireX
open Proofs.libsignal.Hooks2
open Proofs.libsignal.Stage1X

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero


def L1_BytesMergeXPhase1 : Unit := ()

theorem bm_pointsToBytes_split_lastW (ptr : BitVec 64) (bs : List (BitVec 8))
    (hne : bs ≠ []) (hlen : bs.length < 2 ^ 63) :
    (ptr ↦ₛ bs) =
      (ptr ↦ₛ bs.dropLast) ∗
      ((ptr + BitVec.ofNat 64 bs.length + 0xffffffffffffffff#64) ↦₈ bs.getLast hne) :=
  bm_pointsToBytes_split_last ptr bs hne hlen

section Placed

open CryptoVerification

theorem SepWPp.to_subroutineOutcome_placed_x [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {x : BytesMergeGhost} {s0 : State} {P R : SepProp}
    (_hsp_align : s0.spAligned = true)
    (hm : s0.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s0.mem)
    (h : SepWPp prog (s0.readReg64 .lr) s0 P
      (MergePlacedPostW A x s0 R) (MergePlacedPanicW A x s0 R)) :
    ∃ sf, Steps prog s0 sf ∧
      SubroutineOutcome (bytesMergePlacedSpecW A) x R s0 sf := by
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hpost, hsp, hcs⟩ | ⟨hpan, P_f, hmf, hpanic⟩ | ⟨hoom, hmf⟩⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨⟨hpc, hsp, hrun⟩, ⟨hsp, hcs⟩, hpost hmf⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, hpanic hmf⟩)⟩
  · exact (not_satisfies_false_sepConj hmf).elim

/-- Relocatable `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]`
(Block `7`) meets `bytesMergePlacedSpecW A` from individual `withLsCl` callee/extern contracts. -/
theorem bytes_merge_placed_ok_of_contracts_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hdef : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromSpecX A)))
    (hmc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsρ "memcpy")
      (withLsCl lsmpl sessionMemcpySpecBMX))
    (hshim : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsρ CryptoVerification.lsRustNoAllocShimSym)
      (withLsCl lsmpl sessionShimSpecBMX))
    (halloc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsρ CryptoVerification.lsRustAllocSym)
      (withLsCl lsmpl (Proofs.libsignal.Stage1X.rustAllocSpecWithStack A
        CryptoVerification.LibsignalTripleRatchet.extHookStack)))
    (hpanic : ((blkPC_7).rebase (blkPl_7).base H).externAt?
      (lsρ CryptoVerification.lsHandleErrorSym) =
      some Rust.panicked)
    (hVarintSlow : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 293)
      (withLsCl lsmpl (WireX.decodeVarintSlowSpecX A)))
    (hVarintSlice : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 76)
      (withLsCl lsmpl (decodeVarintSliceSpecW A)))
    (hBytesFromVec : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A)))
    (hReserve : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 13)
      (withLsCl lsmpl (Proofs.libsignal.Hooks2.doReserveSpecX A)))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpecBMX A tmpPtr v v.length))) :
    BytesMergePlacedOkW A H := by
  have halloc' : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ CryptoVerification.lsRustAllocSym)
      (withLsCl lsmpl (CryptoVerification.LibsignalTripleRatchet.rustAllocSpecWithStack A
        CryptoVerification.LibsignalTripleRatchet.extHookStack)) := by
    refine subroutine_ok_withLsCl_map' halloc (fun ⟨sz, al⟩ R s0 hpre => ?_)
    refine ⟨(sz, al), R, hpre, fun sf hpost => ?_⟩
    dsimp only [CryptoVerification.LibsignalTripleRatchet.rustAllocSpecWithStack,
      Proofs.libsignal.Stage1X.rustAllocSpecWithStack] at hpost ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  exact bytes_merge_placed_ok_of_contracts_gen
    (hStack := CryptoVerification.LibsignalTripleRatchet.extHookStack)
    (errStack := decodeErrorHookStackW)
    (reqCap := false)
    (by decide) (by decide)
    hdef hmc hshim halloc' hpanic hVarintSlow hVarintSlice hBytesFromVec hReserve hVtableDrop

/-- Relocatable `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]`
(Block `7`) meets `bytesMergePlacedSpecW A` (`BytesMergePlacedOkW A H`) under
`Stage1X.AllocContractsPlaced A H` and `memcpy` at `extHookStack`. -/
theorem bytes_merge_placed_okW [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hA : Proofs.libsignal.Stage1X.AllocContractsPlaced A H)
    (hMemcpy : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H) (lsρ "memcpy")
      (withLsCl lsmpl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack))) :
    BytesMergePlacedOkW A H := by
  have hdef := decodeErrorFrom_placed_okW hA
  exact CryptoVerification.LibsignalTripleRatchet.Prost.X.bytes_merge_placed_ok_of_contracts_x
    (WireX.decodeErrorFrom_placed_ok_cl hdef)
    (bm_memcpy_placed_ok_cl hMemcpy)
    (bm_shim_placed_ok_cl hA)
    (hA.alloc (callerProg := (blkPC_7).rebase (blkPl_7).base H))
    (hA.externAt_handle_error (callerProg := (blkPC_7).rebase (blkPl_7).base H))
    (WireX.decodeVarintSlow_placed_ok_cl (decodeVarintSlow_placed_okW hdef))
    (WireX.decodeVarintSlice_placed_ok_cl (decodeVarintSlice_placed_okW hdef))
    bytesFromVec_placed_ok_cl
    (Proofs.libsignal.Hooks2.do_reserve_placed_ok_cl hA)
    (fun tmpPtr v => bytesVtableDrop_placed_ok_cl hA tmpPtr v v.length)

/-- Assemble `BytesMergePlacedOkW HooksE.A0 H` directly from `Stage2ContractsA0Placed H`. -/
theorem bytes_merge_placed_okW_of_stage2 [LibsignalPlacement]
    {H : LibsignalHooks}
    (hC : Proofs.libsignal.Hooks2.Stage2ContractsA0Placed H) :
    BytesMergePlacedOkW CryptoVerification.E2E.HooksE.A0 H :=
  bytes_merge_placed_okW (Proofs.libsignal.Hooks2.allocContractsPlaced_of_stage2ContractsA0Placed hC) hC.memcpy

end Placed

end CryptoVerification.LibsignalTripleRatchet.Prost.X
