/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.KeyDefs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Code
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.KeyInner
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.KeySeg3a
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.KeySeg3c
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainKeyFieldG
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# `message::merge<Chain> [local#5]`: ChainKey Slice

Proves the inner-loop exit `step_chain3_seg3d` (`+0x368 → +0x3f0 → +0x0a8`) and assembles segments
3a (`KeySeg3a`), 3b (`KeyInner`), 3c (`KeySeg3c`), and 3d into the unconditional tag-3 `ChainKey`
slice `chain3ChainKey_ok_ext` (`Chain3ChainKeyStmtExt`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAt sliceCursorAfter)
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainKeyFieldG
open Proofs.libsignal.Hooks2

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg
attribute [local arm64_norm ↓, local wp_norm ↓]
  ChainMergeStateSimp.sp_setPC_pre_seedChain
  ChainMergeStateSimp.sp_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg64_setPC_pre_seedChain
  ChainMergeStateSimp.readReg64_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg32_setPC_pre_seedChain
  ChainMergeStateSimp.readReg32_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg_setPC_pre_seedChain
  ChainMergeStateSimp.readReg_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.calleeSavedVRegs_setPC_pre_seedChain
  ChainMergeStateSimp.calleeSavedVRegs_setMem_setPC_pre_seedChain

attribute [local simp, local arm64_norm] ChainMergeStateSimp.getLsbD_63_eq_seedChain

/-! ## 1. Segment 3d: Inner loop exit (`+0x368 → +0x3f0 → +0x0a8`) -/

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
