/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay.Step2Comparse

/-!
# Symbolic Term-to-DAG Walk (`dagN_0`..`dagN_157`) for Clean Alice & Bob Runs
-/

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent CliEvent RunEvent)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.Composed.Refinement.Cli
open DY.Libsignal.PQXDH.Refinement (PreKeyFields)
open Symbolic.Swarm.CREF
open Symbolic.BugInjection
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0 compTag4 compSha256Rows)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
  (cliSetupMatchesPinned_satisfiable_of_plausible compHooks0 compRecordsI0)
open Symbolic.BugInjection.Proofs.Common443.CompI0Laws (compI0_kyberCorrectOn)
open ByteSpecs
open Symbolic.BugInjection.Proofs.Common443.CompRTag
open Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
open Symbolic.BugInjection.Proofs.Common443.CompRI0ShaInj
open Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey
open Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
open Symbolic.Swarm.COMPOSED

@[expose] public section

attribute [local irreducible] Symbolic.BugInjection.hexBytes

section Step2DagWalk

open DY.Libsignal.TripleRatchet (TRSignalMsg messageVersion trHonestWireMsg trMsgKeys computeMac)
open DY.Libsignal.Composed.Refinement (TrialCtx trialTerms)

def cleanAddrBs : HwBytes := serializeAddresses ⟨aliceUuid, 1⟩ ⟨bobUuid, 1⟩

theorem dagOp_lit_eq {id : Nat} {bs₀ bs₁ : HwBytes}
    (hop : dagOp id = .lit bs₀) (hbs : bs₀ = bs₁) : dagOp id = .lit bs₁ :=
  hbs ▸ hop

structure OpaqueAt (S : OpaqueSymbolSemantics) (g : Ghost) (pts : List DY.Bytes)
    (b : DY.Bytes) (id : Nat) : Prop where
  bytes_eq : (gamma' compI0 S g b).bytes = dagBytes id
  shape_eq : (gamma' compI0 S g b).shape = litOf (dagBytes id)
  safe : DagSafeMemo S g pts b

theorem termAt_of_opaqueAt {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {b : DY.Bytes} {id : Nat} (hid : id < dagSize) (hop : dagOp id = .lit (dagBytes id))
    (ho : OpaqueAt S g pts b id) : DagTermAt S g pts b id :=
  termAt_of_opaque dag_nodes_ok hid hop ho.bytes_eq ho.shape_eq ho.safe

structure CleanDagHyp (S : OpaqueSymbolSemantics) (g : Ghost) (pts : List DY.Bytes)
    (pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes) : Prop where
  hσ_0_32 : g.σ 0 32 = dagBytes 26
  hσ_5_32 : g.σ 5 32 = dagBytes 29
  hσ_10_32 : g.σ 10 32 = dagBytes 32
  hσ_11_64 : g.σ 11 64 = dagBytes 34
  hσ_16_64 : g.σ 16 64 = dagBytes 35
  hσ_17_64 : g.σ 17 64 = dagBytes 36
  hσ_22_32 : g.σ 22 32 = dagBytes 67
  hσ_23_32 : g.σ 23 32 = dagBytes 69
  hσ_24_32 : g.σ 24 32 = dagBytes 72
  hσ_32_32 : g.σ 32 32 = dagBytes 93
  hσ_32_64 : g.σ 32 64 = dagBytes 94
  hσ_39_32 : g.σ 39 32 = dagBytes 95
  hσ_39_64 : g.σ 39 64 = dagBytes 96
  hσ_45_32 : g.σ 45 32 = dagBytes 127
  hσ_pt1 : g.σ 31 32 = ev1.input
  hpt1_mem : randTerm 31 32 ∈ pts
  hσ_pt2 : g.σ 38 32 = ev2.input
  hpt2_mem : randTerm 38 32 ∈ pts
  haddr : ∀ w : DY.Bytes, g.addr w = cleanAddrBs
  hzero : OpaqueAt S g pts DY.Spqr.zeroKey 7
  hpqpk : OpaqueAt S g pts pqpkT 25
  hsalt1 : OpaqueAt S g pts salt1T 21
  hpqm1 : OpaqueAt S g pts pqm1T 22
  hsalt2 : OpaqueAt S g pts salt2T 23
  hpqm2 : OpaqueAt S g pts pqm2T 24

-- Node 0 (id_empty): .lit []
abbrev dagT_0 : DY.Bytes := DY.Literal.literalToBytes ByteArray.empty
theorem dagN_0 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (_hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_0 0 :=
  termAt_lit (ba := ByteArray.empty) dag_nodes_ok (by decide) (dagOp_lit_eq rfl (by decide +kernel))
-- Node 1 (id_b0): .lit [0x0#8]
abbrev dagT_1 : DY.Bytes := DY.Libsignal.TripleRatchet.litByte 0
theorem dagN_1 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (_hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_1 1 :=
  termAt_lit (ba := ⟨#[0]⟩) dag_nodes_ok (by decide) (dagOp_lit_eq rfl (by decide +kernel))
-- Node 2 (id_b1): .lit [0x1#8]
abbrev dagT_2 : DY.Bytes := DY.Libsignal.TripleRatchet.litByte 1
theorem dagN_2 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (_hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_2 2 :=
  termAt_lit (ba := ⟨#[1]⟩) dag_nodes_ok (by decide) (dagOp_lit_eq rfl (by decide +kernel))
-- Node 3 (id_b2): .lit [0x2#8]
abbrev dagT_3 : DY.Bytes := DY.Libsignal.TripleRatchet.litByte 2
theorem dagN_3 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (_hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_3 3 :=
  termAt_lit (ba := ⟨#[2]⟩) dag_nodes_ok (by decide) (dagOp_lit_eq rfl (by decide +kernel))
-- Node 4 (id_b3): .lit [0x3#8]
abbrev dagT_4 : DY.Bytes := DY.Libsignal.TripleRatchet.litByte 3
theorem dagN_4 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (_hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_4 4 :=
  termAt_lit (ba := ⟨#[3]⟩) dag_nodes_ok (by decide) (dagOp_lit_eq rfl (by decide +kernel))
-- Node 5 (id_b5): .lit [0x5#8]
abbrev dagT_5 : DY.Bytes := DY.Libsignal.TripleRatchet.litByte 5
theorem dagN_5 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (_hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_5 5 :=
  termAt_lit (ba := ⟨#[5]⟩) dag_nodes_ok (by decide) (dagOp_lit_eq rfl (by decide +kernel))
-- Node 6 (id_disc): .lit [0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8]
abbrev dagT_6 : DY.Bytes := DY.Literal.literalToBytes ⟨Array.replicate 32 0xff⟩
theorem dagN_6 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (_hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_6 6 :=
  termAt_lit (ba := ⟨Array.replicate 32 0xff⟩) dag_nodes_ok (by decide) (dagOp_lit_eq rfl (by decide +kernel))
-- Node 7 (id_zero): .lit [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]
abbrev dagT_7 : DY.Bytes := DY.Literal.literalToBytes ⟨Array.replicate 32 0⟩
theorem dagN_7 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (_hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_7 7 :=
  termAt_lit (ba := ⟨Array.replicate 32 0⟩) dag_nodes_ok (by decide) (dagOp_lit_eq rfl (by decide +kernel))
theorem termAt_strLit_loc {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {s : String} {id : Nat} {v : DY.Libsignal.HwBytes}
    (hid : id < dagSize) (hop : dagOp id = .lit v)
    (heq : v = DY.Libsignal.Composed.Refinement.ofByteArray s.toList.utf8Encode) :
    DagTermAt S g pts (DY.Literal.literalToBytes s.toUTF8) id :=
  termAt_lit (ba := s.toUTF8) dag_nodes_ok hid (by rw [toUTF8_eq_utf8Encode]; exact dagOp_lit_eq hop heq)

-- Node 8 (id_pqxdh_lbl): .lit [0x57#8, 0x68#8, 0x69#8, 0x73#8, 0x70#8, 0x65#8, 0x72#8, 0x54#8, 0x65#8, 0x78#8, 0x74#8, 0x5f#8, 0x58#8, 0x32#8, 0x35#8, 0x35#8, 0x31#8, 0x39#8, 0x5f#8, 0x53#8, 0x48#8, 0x41#8, 0x2d#8, 0x32#8, 0x35#8, 0x36#8, 0x5f#8, 0x43#8, 0x52#8, 0x59#8, 0x53#8, 0x54#8, 0x41#8, 0x4c#8, 0x53#8, 0x2d#8, 0x4b#8, 0x59#8, 0x42#8, 0x45#8, 0x52#8, 0x2d#8, 0x31#8, 0x30#8, 0x32#8, 0x34#8]
abbrev dagT_8 : DY.Bytes := DY.Literal.literalToBytes "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024".toUTF8
theorem dagN_8 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (_hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_8 8 :=
  termAt_strLit_loc (s := "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") (by decide) rfl (by decide +kernel)
-- Node 9 (id_wr_lbl): .lit [0x57#8, 0x68#8, 0x69#8, 0x73#8, 0x70#8, 0x65#8, 0x72#8, 0x52#8, 0x61#8, 0x74#8, 0x63#8, 0x68#8, 0x65#8, 0x74#8]
abbrev dagT_9 : DY.Bytes := DY.Libsignal.TripleRatchet.lit "WhisperRatchet"
theorem dagN_9 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (_hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_9 9 :=
  termAt_strLit_loc (s := "WhisperRatchet") (by decide) rfl (by decide +kernel)
-- Node 10 (id_wmk_lbl): .lit [0x57#8, 0x68#8, 0x69#8, 0x73#8, 0x70#8, 0x65#8, 0x72#8, 0x4d#8, 0x65#8, 0x73#8, 0x73#8, 0x61#8, 0x67#8, 0x65#8, 0x4b#8, 0x65#8, 0x79#8, 0x73#8]
abbrev dagT_10 : DY.Bytes := DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys"
theorem dagN_10 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (_hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_10 10 :=
  termAt_strLit_loc (s := "WhisperMessageKeys") (by decide) rfl (by decide +kernel)
-- Node 11 (id_alice_str): .lit [0x61#8, 0x6c#8, 0x69#8, 0x63#8, 0x65#8]
abbrev dagT_11 : DY.Bytes := DY.Literal.literalToBytes "alice".toUTF8
theorem dagN_11 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (_hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_11 11 :=
  termAt_strLit_loc (s := "alice") (by decide) rfl (by decide +kernel)
-- Node 12 (id_bob_str): .lit [0x62#8, 0x6f#8, 0x62#8]
abbrev dagT_12 : DY.Bytes := DY.Literal.literalToBytes "bob".toUTF8
theorem dagN_12 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (_hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_12 12 :=
  termAt_strLit_loc (s := "bob") (by decide) rfl (by decide +kernel)
-- Node 13 (id_wr1): .concat 9 2
abbrev dagT_13 : DY.Bytes := DY.Concat.concat dagT_9 dagT_2
theorem dagN_13 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_13 13 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_9 hw) (dagN_2 hw)
-- Node 14 (id_wr2): .concat 9 3
abbrev dagT_14 : DY.Bytes := DY.Concat.concat dagT_9 dagT_3
theorem dagN_14 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_14 14 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_9 hw) (dagN_3 hw)
-- Node 15 (id_wmk1): .concat 10 2
abbrev dagT_15 : DY.Bytes := DY.Concat.concat dagT_10 dagT_2
theorem dagN_15 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_15 15 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_10 hw) (dagN_2 hw)
-- Node 16 (id_wmk2): .concat 10 3
abbrev dagT_16 : DY.Bytes := DY.Concat.concat dagT_10 dagT_3
theorem dagN_16 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_16 16 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_10 hw) (dagN_3 hw)
-- Node 17 (id_wmk3): .concat 10 4
abbrev dagT_17 : DY.Bytes := DY.Concat.concat dagT_10 dagT_4
theorem dagN_17 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_17 17 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_10 hw) (dagN_4 hw)
-- Node 18 (id_pq1): .concat 8 2
abbrev dagT_18 : DY.Bytes := DY.Concat.concat dagT_8 dagT_2
theorem dagN_18 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_18 18 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_8 hw) (dagN_2 hw)
-- Node 19 (id_pq2): .concat 8 3
abbrev dagT_19 : DY.Bytes := DY.Concat.concat dagT_8 dagT_3
theorem dagN_19 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_19 19 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_8 hw) (dagN_3 hw)
-- Node 20 (id_pq3): .concat 8 4
abbrev dagT_20 : DY.Bytes := DY.Concat.concat dagT_8 dagT_4
theorem dagN_20 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_20 20 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_8 hw) (dagN_4 hw)
-- Node 21 (id_salt1): .lit [0x75#8, 0x65#8, 0xcf#8, 0xed#8, 0xac#8, 0x58#8, 0x7#8, 0x14#8, 0x5e#8, 0x7e#8, 0xf3#8, 0xb6#8, 0x54#8, 0xfe#8, 0x14#8, 0x42#8, 0xac#8, 0x60#8, 0x61#8, 0x9c#8, 0xb3#8, 0xc6#8, 0x2e#8, 0x1e#8, 0xf7#8, 0xf6#8, 0xf7#8, 0xc6#8, 0x44#8, 0x3a#8, 0xb#8, 0x8a#8]
abbrev dagT_21 (salt1T : DY.Bytes) : DY.Bytes := salt1T
theorem dagN_21 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_21 salt1T) 21 :=
  termAt_of_opaqueAt (by decide) (dagOp_lit_eq rfl (by decide +kernel)) hw.hsalt1
-- Node 22 (id_pqm1): .lit [0x1#8, 0x1#8, 0x1#8, 0x1#8, 0x0#8, 0x71#8, 0xd6#8, 0xb8#8, 0x72#8, 0x73#8, 0x54#8, 0x13#8, 0xd1#8, 0xbc#8, 0xb9#8, 0xaa#8, 0x63#8, 0x69#8, 0x38#8, 0xb2#8, 0x4b#8, 0x48#8, 0x12#8, 0xa7#8, 0xe8#8, 0x0#8, 0x62#8, 0x87#8, 0x26#8, 0x44#8, 0xbb#8, 0x49#8, 0x4a#8, 0x91#8, 0x46#8, 0x38#8, 0xb0#8]
abbrev dagT_22 (pqm1T : DY.Bytes) : DY.Bytes := pqm1T
theorem dagN_22 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_22 pqm1T) 22 :=
  termAt_of_opaqueAt (by decide) (dagOp_lit_eq rfl (by decide +kernel)) hw.hpqm1
-- Node 23 (id_salt2): .lit [0x3#8, 0x87#8, 0x4f#8, 0xd6#8, 0x41#8, 0xef#8, 0xd7#8, 0x49#8, 0x17#8, 0x2b#8, 0x5d#8, 0xe4#8, 0x9#8, 0xf1#8, 0x61#8, 0x4c#8, 0x16#8, 0xee#8, 0x73#8, 0x10#8, 0x2e#8, 0x61#8, 0x6e#8, 0xfe#8, 0xb7#8, 0xa6#8, 0xf7#8, 0x23#8, 0x57#8, 0x14#8, 0x4c#8, 0x7a#8]
abbrev dagT_23 (salt2T : DY.Bytes) : DY.Bytes := salt2T
theorem dagN_23 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_23 salt2T) 23 :=
  termAt_of_opaqueAt (by decide) (dagOp_lit_eq rfl (by decide +kernel)) hw.hsalt2
-- Node 24 (id_pqm2): .lit [0x1#8, 0x1#8, 0x2#8, 0x1#8, 0x1#8, 0x86#8, 0x2#8, 0xe5#8, 0xc4#8, 0xb4#8, 0x8#8, 0x55#8, 0x4b#8, 0x7#8, 0xc7#8, 0xd3#8, 0x58#8, 0xfb#8, 0xd#8, 0x6#8, 0x22#8, 0x57#8, 0x8d#8, 0xfb#8, 0x95#8, 0xd6#8, 0xaf#8, 0xc2#8, 0xa9#8, 0xdf#8, 0x5a#8, 0xac#8, 0x8#8, 0x37#8, 0xa5#8, 0xdf#8, 0xc5#8]
abbrev dagT_24 (pqm2T : DY.Bytes) : DY.Bytes := pqm2T
theorem dagN_24 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_24 pqm2T) 24 :=
  termAt_of_opaqueAt (by decide) (dagOp_lit_eq rfl (by decide +kernel)) hw.hpqm2
-- Node 25 (id_kyberPk): .lit [0xa8#8, 0x73#8, 0xe#8, 0x93#8, 0x64#8, 0x58#8, 0x1#8, 0xc#8, 0xbc#8, 0x88#8, 0xc9#8, 0x60#8, 0xd7#8, 0xa8#8, 0x81#8, 0xb9#8, 0x50#8, 0xbc#8, 0x17#8, 0xa6#8, 0x72#8, 0xb3#8, 0xfa#8, 0xc3#8, 0x2a#8, 0x10#8, 0x1b#8, 0x1f#8, 0x71#8, 0x99#8, 0x93#8, 0x37#8, 0xb6#8, 0xe9#8, 0xe6#8, 0xa5#8, 0xe9#8, 0xe0#8, 0xcd#8, 0x84#8, 0xf1#8, 0x7c#8, 0x3b#8, 0xf2#8, 0x67#8, 0x62#8, 0xc4#8, 0x9d#8, 0x96#8, 0x38#8, 0x82#8, 0x9d#8, 0xe6#8, 0xa1#8, 0xa1#8, 0xf7#8, 0x74#8, 0x53#8, 0x74#8, 0x42#8, 0x34#8, 0xa8#8, 0xb4#8, 0xaf#8, 0x72#8, 0x6b#8, 0x64#8, 0x90#8, 0x7#8, 0xd4#8, 0x2a#8, 0x68#8, 0xed#8, 0xc9#8, 0x76#8, 0x34#8, 0x5c#8, 0x23#8, 0xa4#8, 0x59#8, 0xc2#8, 0x32#8, 0x64#8, 0xaa#8, 0x15#8, 0x97#8, 0x91#8, 0x3#8, 0x83#8, 0x45#8, 0xa7#8, 0xc2#8, 0x7a#8, 0x5c#8, 0x50#8, 0x9f#8, 0xa9#8, 0xfb#8, 0x3b#8, 0xa1#8, 0x71#8, 0xb3#8, 0x4e#8, 0x6a#8, 0x78#8, 0x15#8, 0xf9#8, 0x3b#8, 0xa5#8, 0xf6#8, 0x7d#8, 0xfe#8, 0xca#8, 0x5a#8, 0xd7#8, 0xdc#8, 0x4d#8, 0x17#8, 0x6c#8, 0x43#8, 0x2d#8, 0x7#8, 0x78#8, 0x6f#8, 0x11#8, 0x6e#8, 0x20#8, 0x31#8, 0x74#8, 0xfb#8, 0x78#8, 0x20#8, 0x52#8, 0x93#8, 0x14#8, 0xbc#8, 0xc0#8, 0xa6#8, 0x8d#8, 0x11#8, 0xa2#8, 0x5e#8, 0x7a#8, 0x5d#8, 0x9a#8, 0xdc#8, 0xa5#8, 0x60#8, 0x89#8, 0x66#8, 0xb6#8, 0x4c#8, 0xb8#8, 0xac#8, 0x36#8, 0x72#8, 0xef#8, 0x6a#8, 0x85#8, 0xe7#8, 0x94#8, 0x21#8, 0xcb#8, 0x25#8, 0x17#8, 0x5a#8, 0x47#8, 0x27#8, 0xfe#8, 0x18#8, 0x55#8, 0x98#8, 0x67#8, 0x7c#8, 0x5d#8, 0x66#8, 0x66#8, 0xd6#8, 0x2#8, 0x1e#8, 0x1f#8, 0x17#8, 0x11#8, 0x47#8, 0xf0#8, 0xb5#8, 0x43#8, 0xd7#8, 0xb4#8, 0xae#8, 0x22#8, 0x46#8, 0x74#8, 0xe7#8, 0x37#8, 0x7d#8, 0x59#8, 0x14#8, 0xe6#8, 0x65#8, 0x64#8, 0x47#8, 0x43#8, 0xa1#8, 0x78#8, 0xfc#8, 0x6e#8, 0x5c#8, 0xea#8, 0xd#8, 0x71#8, 0x5c#8, 0xbb#8, 0x5c#8, 0x21#8, 0x9d#8, 0x87#8, 0xc1#8, 0x70#8, 0x16#8, 0xe0#8, 0x3d#8, 0x8c#8, 0x76#8, 0xa8#8, 0xed#8, 0xc0#8, 0x84#8, 0xed#8, 0xb2#8, 0x8d#8, 0x74#8, 0x8a#8, 0x6d#8, 0xd9#8, 0x7b#8, 0x11#8, 0xe5#8, 0x96#8, 0xbf#8, 0x67#8, 0x93#8, 0x7c#8, 0xa8#8, 0x28#8, 0x9f#8, 0x9b#8, 0x7c#8, 0x1a#8, 0xb3#8, 0xc7#8, 0x9#8, 0xac#8, 0x25#8, 0xca#8, 0x9#8, 0xac#8, 0x33#8, 0x28#8, 0x9b#8, 0x4f#8, 0x86#8, 0x24#8, 0x12#8, 0x6#8, 0xb2#8, 0x2b#8, 0xdc#8, 0xd8#8, 0x2e#8, 0x35#8, 0xf0#8, 0x23#8, 0x52#8, 0x78#8, 0x40#8, 0x9e#8, 0x81#8, 0x74#8, 0x8d#8, 0x19#8, 0x35#8, 0x8c#8, 0xf5#8, 0x2b#8, 0x4b#8, 0xe4#8, 0x56#8, 0x5f#8, 0x84#8, 0xb4#8, 0xdc#8, 0x36#8, 0x87#8, 0x71#8, 0xe4#8, 0xb1#8, 0x22#8, 0x59#8, 0xbc#8, 0xa#8, 0x3b#8, 0x11#8, 0x27#8, 0xb#8, 0x26#8, 0xf1#8, 0x2#8, 0x7d#8, 0x32#8, 0xf5#8, 0x58#8, 0x73#8, 0x16#8, 0xa4#8, 0xc2#8, 0x55#8, 0x5e#8, 0xf#8, 0x45#8, 0x37#8, 0xaf#8, 0x8#8, 0x15#8, 0xa6#8, 0xfc#8, 0x6c#8, 0x58#8, 0xe5#8, 0x90#8, 0xd2#8, 0xa4#8, 0x20#8, 0x6d#8, 0x5c#8, 0x29#8, 0x72#8, 0x21#8, 0x7#8, 0x6c#8, 0x57#8, 0xb8#8, 0xd8#8, 0x31#8, 0x2f#8, 0xec#8, 0x25#8, 0xc0#8, 0xf0#8, 0x91#8, 0x79#8, 0x8c#8, 0x61#8, 0xb5#8, 0x4#8, 0x9#8, 0x62#8, 0xd0#8, 0x61#8, 0x0#8, 0xc3#8, 0x16#8, 0x87#8, 0xa5#8, 0xa#8, 0xa3#8, 0xac#8, 0x81#8, 0xb9#8, 0x9b#8, 0xf0#8, 0x49#8, 0xe7#8, 0x7a#8, 0x22#8, 0x7e#8, 0x5c#8, 0x1e#8, 0xb2#8, 0x52#8, 0x3a#8, 0x6a#8, 0x11#8, 0xb3#8, 0x4d#8, 0x86#8, 0xc7#8, 0x62#8, 0x49#8, 0x97#8, 0x6e#8, 0x41#8, 0x48#8, 0x71#8, 0x85#8, 0x84#8, 0x1b#8, 0xe4#8, 0x14#8, 0x24#8, 0x3b#8, 0x7e#8, 0x52#8, 0xc8#8, 0x4f#8, 0xbe#8, 0x66#8, 0x75#8, 0x83#8, 0x7#8, 0x3b#8, 0x2d#8, 0x58#8, 0x52#8, 0xcf#8, 0xe9#8, 0x74#8, 0x7a#8, 0xe7#8, 0x5#8, 0xad#8, 0x23#8, 0x94#8, 0xef#8, 0x52#8, 0x9#8, 0x46#8, 0xab#8, 0x53#8, 0x8a#8, 0xb6#8, 0xa0#8, 0x9c#8, 0x53#8, 0x59#8, 0x61#8, 0x74#8, 0x9e#8, 0x96#8, 0x12#8, 0x6e#8, 0x98#8, 0x30#8, 0x74#8, 0x1e#8, 0x64#8, 0x81#8, 0xa2#8, 0x28#8, 0x8#8, 0xb8#8, 0x89#8, 0xb7#8, 0x72#8, 0x67#8, 0x85#8, 0x3e#8, 0xc5#8, 0x6a#8, 0x2#8, 0xda#8, 0x16#8, 0x98#8, 0x7c#8, 0x1b#8, 0x61#8, 0xc8#8, 0x50#8, 0xd5#8, 0xdb#8, 0xc8#8, 0x4e#8, 0xe3#8, 0x11#8, 0x31#8, 0xb3#8, 0x32#8, 0x5#8, 0x55#8, 0x49#8, 0x56#8, 0x60#8, 0x33#8, 0x61#8, 0x9c#8, 0x7a#8, 0x8e#8, 0xec#8, 0x2c#8, 0xa2#8, 0xe1#8, 0x30#8, 0xc1#8, 0x98#8, 0x81#8, 0xb1#8, 0x30#8, 0xb4#8, 0x82#8, 0x42#8, 0x64#8, 0x3e#8, 0x5c#8, 0x62#8, 0xc5#8, 0xf3#8, 0x72#8, 0x88#8, 0xb4#8, 0x1#8, 0xe5#8, 0x37#8, 0xb6#8, 0x48#8, 0xa4#8, 0x45#8, 0x70#8, 0x21#8, 0x35#8, 0xd2#8, 0x81#8, 0x43#8, 0xf1#8, 0x9#8, 0xba#8, 0xc#8, 0x6a#8, 0xcd#8, 0xbe#8, 0x19#8, 0x3b#8, 0x52#8, 0x86#8, 0x2b#8, 0x5#8, 0x46#8, 0x33#8, 0xc0#8, 0x60#8, 0xce#8, 0x18#8, 0x90#8, 0x57#8, 0x83#8, 0xd7#8, 0x32#8, 0xbc#8, 0xe0#8, 0x7b#8, 0x70#8, 0x68#8, 0x74#8, 0x6c#8, 0xf0#8, 0x33#8, 0xe3#8, 0x94#8, 0xab#8, 0x0#8, 0x1#8, 0x52#8, 0x88#8, 0x76#8, 0x38#8, 0xe3#8, 0xf1#8, 0x34#8, 0x65#8, 0x34#8, 0x1f#8, 0xe9#8, 0xc3#8, 0x29#8, 0x7e#8, 0x5c#8, 0x2c#8, 0xdc#8, 0xa7#8, 0xb6#8, 0x3b#8, 0x26#8, 0x52#8, 0x6b#8, 0x25#8, 0x5#8, 0x80#8, 0xb6#8, 0x74#8, 0x51#8, 0x55#8, 0xc#8, 0xa0#8, 0x55#8, 0x31#8, 0xbc#8, 0xb5#8, 0xad#8, 0x27#8, 0x3#8, 0x26#8, 0x5e#8, 0x64#8, 0x4a#8, 0xf5#8, 0xe5#8, 0xca#8, 0x67#8, 0xb3#8, 0x74#8, 0x77#8, 0x8b#8, 0x7d#8, 0x91#8, 0x3b#8, 0xb3#8, 0x37#8, 0x16#8, 0x5c#8, 0xe5#8, 0xc7#8, 0x8c#8, 0xb9#8, 0x1c#8, 0x5d#8, 0x8a#8, 0x7a#8, 0xcf#8, 0xf2#8, 0x57#8, 0x11#8, 0x8d#8, 0xa5#8, 0x8f#8, 0xa5#8, 0xa5#8, 0x26#8, 0x63#8, 0x12#8, 0xc6#8, 0x69#8, 0x7a#8, 0x25#8, 0xfe#8, 0xb2#8, 0xae#8, 0x42#8, 0x6#8, 0xc8#8, 0x41#8, 0x29#8, 0x9e#8, 0xb7#8, 0x4c#8, 0x53#8, 0xae#8, 0x60#8, 0x7c#8, 0x85#8, 0xf7#8, 0x21#8, 0x60#8, 0x2c#8, 0x98#8, 0x25#8, 0x21#8, 0x89#8, 0x61#8, 0x65#8, 0x4f#8, 0x47#8, 0x16#8, 0x0#8, 0x3a#8, 0xf2#8, 0x90#8, 0x5f#8, 0x69#8, 0xad#8, 0xd5#8, 0xca#8, 0x5e#8, 0xe8#8, 0xf4#8, 0x44#8, 0x77#8, 0x26#8, 0x42#8, 0x55#8, 0xe1#8, 0x4a#8, 0x83#8, 0x69#8, 0x3a#8, 0x28#8, 0x26#8, 0x16#8, 0x93#8, 0xb#8, 0xac#8, 0x9#8, 0x40#8, 0x95#8, 0xca#8, 0x61#8, 0xc1#8, 0xe#8, 0xc1#8, 0xa4#8, 0xc2#8, 0x43#8, 0xa4#8, 0xbe#8, 0xf6#8, 0xd#8, 0x41#8, 0xd7#8, 0x96#8, 0xb9#8, 0x26#8, 0x59#8, 0xdd#8, 0x4b#8, 0x67#8, 0xa6#8, 0xb8#8, 0x78#8, 0x15#8, 0x94#8, 0x94#8, 0x62#8, 0x66#8, 0x4b#8, 0xc1#8, 0x86#8, 0x8f#8, 0xf0#8, 0x49#8, 0x41#8, 0xf6#8, 0xe1#8, 0xaa#8, 0x69#8, 0xe4#8, 0x40#8, 0x5#8, 0x17#8, 0x19#8, 0x71#8, 0xb2#8, 0xcd#8, 0x5f#8, 0x7a#8, 0x10#8, 0xa9#8, 0x69#8, 0xbb#8, 0xcc#8, 0x88#8, 0x8c#8, 0xa6#8, 0x79#8, 0x28#8, 0x92#8, 0xd7#8, 0x15#8, 0xad#8, 0x29#8, 0xa6#8, 0xbd#8, 0x21#8, 0x9e#8, 0x32#8, 0x28#8, 0x28#8, 0x7a#8, 0x28#8, 0xad#8, 0x87#8, 0x57#8, 0x26#8, 0xde#8, 0x89#8, 0x22#8, 0x58#8, 0x15#8, 0x79#8, 0x7e#8, 0x80#8, 0x97#8, 0xd6#8, 0x70#8, 0x70#8, 0xc1#8, 0x3a#8, 0xbf#8, 0xb3#8, 0x97#8, 0x98#8, 0x92#8, 0x59#8, 0x64#8, 0x48#8, 0x9#8, 0x5f#8, 0xc0#8, 0xbb#8, 0x77#8, 0x5d#8, 0x86#8, 0xa8#8, 0xa5#8, 0xbc#8, 0x16#8, 0x22#8, 0x92#8, 0x42#8, 0x4c#8, 0xb2#8, 0x6f#8, 0xec#8, 0x92#8, 0x92#8, 0x9b#8, 0xac#8, 0x2#8, 0xdb#8, 0x3b#8, 0xcb#8, 0xa5#8, 0xfc#8, 0x9f#8, 0xe5#8, 0x14#8, 0x2a#8, 0xf9#8, 0x96#8, 0x7a#8, 0xb2#8, 0x2#8, 0x70#8, 0x8f#8, 0x35#8, 0x6a#8, 0x35#8, 0x42#8, 0x49#8, 0x86#8, 0x92#8, 0xaf#8, 0x1b#8, 0x14#8, 0x61#8, 0xfc#8, 0xe4#8, 0x8f#8, 0x6f#8, 0xc4#8, 0x2a#8, 0x4c#8, 0x13#8, 0x16#8, 0x13#8, 0x19#8, 0x64#8, 0x2f#8, 0x63#8, 0x10#8, 0xb5#8, 0x80#8, 0x6a#8, 0xd8#8, 0x99#8, 0x28#8, 0xb3#8, 0x2a#8, 0x1b#8, 0xea#8, 0x50#8, 0x7c#8, 0x99#8, 0x51#8, 0xb4#8, 0x58#8, 0xbb#8, 0x60#8, 0x9a#8, 0x41#8, 0xa1#8, 0xa3#8, 0x5b#8, 0xc6#8, 0x3a#8, 0xc0#8, 0x1c#8, 0x56#8, 0x8c#8, 0x31#8, 0x88#8, 0xb6#8, 0x10#8, 0x41#8, 0x62#8, 0x50#8, 0x16#8, 0x84#8, 0xf#8, 0x7#8, 0x78#8, 0x2e#8, 0x9b#8, 0xc9#8, 0x86#8, 0xc6#8, 0x15#8, 0x16#8, 0xa4#8, 0x3#8, 0x7c#8, 0xf7#8, 0x27#8, 0x3d#8, 0x5c#8, 0x9c#8, 0x6b#8, 0x1a#8, 0xa#8, 0x66#8, 0x44#8, 0x43#8, 0xb7#8, 0xb2#8, 0x88#8, 0x35#8, 0x3c#8, 0x81#8, 0x79#8, 0x8b#8, 0x37#8, 0xce#8, 0xa2#8, 0x3c#8, 0x3a#8, 0xb5#8, 0x3b#8, 0x18#8, 0x93#8, 0x26#8, 0x4b#8, 0xc8#8, 0x3b#8, 0x72#8, 0x6d#8, 0x31#8, 0x50#8, 0x42#8, 0xb#8, 0xd#8, 0x86#8, 0xec#8, 0xbf#8, 0xfa#8, 0xf3#8, 0xc#8, 0x48#8, 0xab#8, 0xb5#8, 0x8d#8, 0x46#8, 0x2#8, 0xb#8, 0x2c#8, 0x63#8, 0xf9#8, 0x61#8, 0x45#8, 0x99#8, 0x25#8, 0xa5#8, 0x4d#8, 0x1b#8, 0x5a#8, 0xed#8, 0x59#8, 0x1e#8, 0x5#8, 0x80#8, 0xae#8, 0xd6#8, 0x2b#8, 0x28#8, 0x88#8, 0x6#8, 0xac#8, 0x5f#8, 0x66#8, 0x8c#8, 0x53#8, 0x51#8, 0x7#8, 0xde#8, 0x56#8, 0x9d#8, 0x88#8, 0xc#8, 0xca#8, 0xff#8, 0x8b#8, 0x11#8, 0x50#8, 0xf8#8, 0x24#8, 0xdd#8, 0x68#8, 0xb8#8, 0xf8#8, 0xba#8, 0xb7#8, 0x8f#8, 0x99#8, 0x22#8, 0xd9#8, 0x46#8, 0x86#8, 0xa8#8, 0x93#8, 0xa2#8, 0x5b#8, 0x26#8, 0x52#8, 0x79#8, 0xf1#8, 0x6f#8, 0x32#8, 0x9a#8, 0x5a#8, 0xe#8, 0x99#8, 0x60#8, 0xed#8, 0xc4#8, 0x15#8, 0x4a#8, 0x34#8, 0x55#8, 0xd1#8, 0x73#8, 0x47#8, 0x9d#8, 0xda#8, 0xca#8, 0x87#8, 0x92#8, 0x92#8, 0xb3#8, 0x8c#8, 0xb5#8, 0xfb#8, 0xb1#8, 0xbb#8, 0x31#8, 0x66#8, 0x62#8, 0xdb#8, 0xe3#8, 0x12#8, 0x17#8, 0x51#8, 0x86#8, 0x36#8, 0x17#8, 0x1e#8, 0xff#8, 0x50#8, 0x3f#8, 0x5a#8, 0x32#8, 0x58#8, 0x2f#8, 0xfc#8, 0xc1#8, 0xac#8, 0x2#8, 0x34#8, 0xac#8, 0xea#8, 0x7e#8, 0x38#8, 0x54#8, 0x42#8, 0x84#8, 0x40#8, 0x51#8, 0xa4#8, 0xd4#8, 0x4b#8, 0x8e#8, 0xa2#8, 0x57#8, 0x69#8, 0x76#8, 0x74#8, 0x3e#8, 0x30#8, 0x92#8, 0xb2#8, 0xe5#8, 0xc#8, 0x10#8, 0x64#8, 0xa7#8, 0x41#8, 0x15#8, 0xaf#8, 0xe0#8, 0xdc#8, 0x31#8, 0xf#8, 0xb3#8, 0x8d#8, 0x47#8, 0x87#8, 0x5f#8, 0x10#8, 0x43#8, 0xe#8, 0x3d#8, 0x93#8, 0x86#8, 0xa8#8, 0xf6#8, 0xc3#8, 0xf#8, 0x87#8, 0x25#8, 0x37#8, 0x62#8, 0xbf#8, 0xd1#8, 0x3b#8, 0x5b#8, 0x48#8, 0x69#8, 0x47#8, 0xa1#8, 0x2b#8, 0x3e#8, 0xb9#8, 0x96#8, 0xa3#8, 0x36#8, 0xe2#8, 0x59#8, 0xd9#8, 0x82#8, 0x27#8, 0x2c#8, 0xaa#8, 0xcd#8, 0xb#8, 0x2c#8, 0x4a#8, 0x73#8, 0xe8#8, 0xa6#8, 0xeb#8, 0xc8#8, 0x6#8, 0x2a#8, 0x25#8, 0xcb#8, 0xa4#8, 0xd4#8, 0x77#8, 0xaa#8, 0xdb#8, 0xbd#8, 0xb1#8, 0x3#8, 0xaf#8, 0xc7#8, 0x66#8, 0xc9#8, 0xdf#8, 0x6a#8, 0x62#8, 0x51#8, 0x44#8, 0xa6#8, 0xf3#8, 0x78#8, 0x3f#8, 0xa8#8, 0xfb#8, 0x41#8, 0x91#8, 0xbc#8, 0x5e#8, 0xc1#8, 0x8#8, 0x3b#8, 0x8a#8, 0x73#8, 0x38#8, 0x8c#8, 0x86#8, 0xab#8, 0x13#8, 0xe9#8, 0x3e#8, 0xd4#8, 0x87#8, 0x12#8, 0xe6#8, 0xf1#8, 0x3#8, 0x73#8, 0x90#8, 0x42#8, 0x1c#8, 0x14#8, 0x20#8, 0xf1#8, 0xa#8, 0x41#8, 0xf1#8, 0x20#8, 0x42#8, 0x46#8, 0x13#8, 0x59#8, 0x4e#8, 0xd6#8, 0x6b#8, 0x20#8, 0xb9#8, 0xc3#8, 0x33#8, 0x51#8, 0xc9#8, 0x86#8, 0x53#8, 0x8f#8, 0xa1#8, 0xd8#8, 0x8e#8, 0x2a#8, 0xac#8, 0x22#8, 0x86#8, 0x7c#8, 0x63#8, 0xcb#8, 0xe9#8, 0x3b#8, 0x6f#8, 0xb7#8, 0x90#8, 0xf3#8, 0xa8#8, 0xbc#8, 0x2c#8, 0xe3#8, 0x58#8, 0x60#8, 0xf6#8, 0x9f#8, 0x33#8, 0x6a#8, 0x79#8, 0x4e#8, 0x87#8, 0x80#8, 0xb9#8, 0xe6#8, 0x5d#8, 0x47#8, 0x92#8, 0x6c#8, 0xcb#8, 0x49#8, 0x13#8, 0x16#8, 0xd4#8, 0x14#8, 0xe8#8, 0xe2#8, 0x35#8, 0xb8#8, 0x8b#8, 0xcd#8, 0x2f#8, 0x7#8, 0x55#8, 0x39#8, 0x33#8, 0xc9#8, 0x2#8, 0x5a#8, 0x95#8, 0x72#8, 0x3c#8, 0x11#8, 0x5d#8, 0xfa#8, 0xad#8, 0x68#8, 0x29#8, 0x89#8, 0x51#8, 0x75#8, 0xa5#8, 0xd2#8, 0x65#8, 0x27#8, 0xb9#8, 0x58#8, 0x17#8, 0x3#8, 0xe2#8, 0xc4#8, 0x7c#8, 0x52#8, 0x82#8, 0xa0#8, 0xaa#8, 0x62#8, 0x70#8, 0x40#8, 0xc6#8, 0xf7#8, 0x90#8, 0x8d#8, 0xbf#8, 0x26#8, 0xcf#8, 0xc5#8, 0x62#8, 0x34#8, 0xf1#8, 0xf9#8, 0x36#8, 0x72#8, 0x39#8, 0x99#8, 0x4f#8, 0xab#8, 0x55#8, 0x5e#8, 0x92#8, 0x3#8, 0x8d#8, 0x6c#8, 0x50#8, 0x96#8, 0x6a#8, 0xbf#8, 0xf#8, 0xc9#8, 0x24#8, 0xdf#8, 0x4#8, 0x8b#8, 0x2#8, 0x34#8, 0x9a#8, 0x4b#8, 0xc5#8, 0x9c#8, 0x8#8, 0x29#8, 0xb8#8, 0xd8#8, 0x2c#8, 0x42#8, 0xcf#8, 0xa1#8, 0x7b#8, 0xbf#8, 0x21#8, 0xcf#8, 0x82#8, 0xeb#8, 0x1b#8, 0xcb#8, 0x83#8, 0x1d#8, 0x86#8, 0x1a#8, 0x48#8, 0xdc#8, 0x39#8, 0x23#8, 0xed#8, 0x84#8, 0xcc#8, 0xe4#8, 0xa6#8, 0x15#8, 0xc2#8, 0x6b#8, 0x70#8, 0xb7#8, 0x89#8, 0xb9#8, 0x1d#8, 0xb0#8, 0x6a#8, 0x9c#8, 0xc7#8, 0x32#8, 0x4c#8, 0x8b#8, 0xaa#8, 0xf#8, 0xd8#8, 0x6a#8, 0x52#8, 0xd4#8, 0xb2#8, 0x90#8, 0x3b#8, 0x1#8, 0x5d#8, 0x8b#8, 0xb4#8, 0xb6#8, 0x9#8, 0x85#8, 0x1c#8, 0x83#8, 0x82#8, 0x7f#8, 0x61#8, 0xca#8, 0xea#8, 0x67#8, 0x58#8, 0x9d#8, 0x12#8, 0x76#8, 0x87#8, 0x5b#8, 0x1a#8, 0xe8#8, 0x35#8, 0x7c#8, 0xe6#8, 0x42#8, 0xa5#8, 0x18#8, 0xa6#8, 0xe#8, 0xed#8, 0x25#8, 0xa2#8, 0xfc#8, 0x38#8, 0xac#8, 0xa9#8, 0xb#8, 0x6f#8, 0x13#8, 0x59#8, 0x87#8, 0x7b#8, 0x4a#8, 0x45#8, 0xb9#8, 0x2b#8, 0x72#8, 0x5e#8, 0x75#8, 0x87#8, 0x9b#8, 0xa2#8, 0xaf#8, 0xfc#8, 0x5#8, 0x9#8, 0xe4#8, 0x89#8, 0x6a#8, 0x4c#8, 0x5c#8, 0x7b#8, 0x28#8, 0xd6#8, 0x37#8, 0x91#8, 0x36#8, 0x59#8, 0x6c#8, 0xa#8, 0xc#8, 0x8e#8, 0x68#8, 0x52#8, 0xe0#8, 0xbc#8, 0xa#8, 0xe8#8, 0xda#8, 0x3b#8, 0x39#8, 0xa#8, 0x9d#8, 0x55#8, 0x35#8, 0xc4#8, 0xbf#8, 0xf1#8, 0xad#8, 0x30#8, 0x18#8, 0x49#8, 0x2d#8, 0x1a#8, 0xa7#8, 0x99#8, 0x6#8, 0x46#8, 0xe2#8, 0x2a#8, 0x7e#8, 0x79#8, 0x95#8, 0x37#8, 0xaa#8, 0x50#8, 0xc6#8, 0xbf#8, 0x42#8, 0x64#8, 0xbf#8, 0x61#8, 0x98#8, 0x9f#8, 0x89#8, 0x70#8, 0x0#8, 0x91#8, 0x32#8, 0x54#8, 0x1c#8, 0x7a#8, 0x43#8, 0xc1#8, 0x2b#8, 0x78#8, 0x70#8, 0xf8#8, 0x69#8, 0x6f#8, 0x78#8, 0x97#8, 0xbd#8, 0xbf#8, 0xd2#8, 0x1a#8, 0x75#8, 0x19#8, 0x26#8, 0x19#8, 0xa4#8, 0x44#8, 0x6a#8, 0x9f#8, 0x8#8]
abbrev dagT_25 (pqpkT : DY.Bytes) : DY.Bytes := pqpkT
theorem dagN_25 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_25 pqpkT) 25 :=
  termAt_of_opaqueAt (by decide) (dagOp_lit_eq rfl (by decide +kernel)) hw.hpqpk
-- Node 26 (id_ikA): .rand 0 32
abbrev dagT_26 : DY.Bytes := randTerm 0 32
theorem dagN_26 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_26 26 :=
  termAt_rand dag_nodes_ok (by decide) rfl hw.hσ_0_32
theorem dagSh_26 : randTerm 0 32 = dagShape dagOp dagSize 26 :=
  randTerm_eq_dagShape dag_nodes_ok (by decide) rfl
-- Node 27 (id_ikA_pk): .dhPk 26
abbrev dagT_27 : DY.Bytes := DY.DiffieHellman.dhPk dagT_26
theorem dagN_27 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_27 27 :=
  termAt_dhPk dag_nodes_ok (by decide) rfl (dagN_26 hw)
-- Node 28 (id_serIkA): .concat 5 27
abbrev dagT_28 : DY.Bytes := DY.Concat.concat dagT_5 dagT_27
theorem dagN_28 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_28 28 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_5 hw) (dagN_27 hw)
-- Node 29 (id_ikB): .rand 5 32
abbrev dagT_29 : DY.Bytes := randTerm 5 32
theorem dagN_29 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_29 29 :=
  termAt_rand dag_nodes_ok (by decide) rfl hw.hσ_5_32
theorem dagSh_29 : randTerm 5 32 = dagShape dagOp dagSize 29 :=
  randTerm_eq_dagShape dag_nodes_ok (by decide) rfl
-- Node 30 (id_ikB_pk): .dhPk 29
abbrev dagT_30 : DY.Bytes := DY.DiffieHellman.dhPk dagT_29
theorem dagN_30 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_30 30 :=
  termAt_dhPk dag_nodes_ok (by decide) rfl (dagN_29 hw)
-- Node 31 (id_serIkB): .concat 5 30
abbrev dagT_31 : DY.Bytes := DY.Concat.concat dagT_5 dagT_30
theorem dagN_31 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_31 31 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_5 hw) (dagN_30 hw)
-- Node 32 (id_spkB): .rand 10 32
abbrev dagT_32 : DY.Bytes := randTerm 10 32
theorem dagN_32 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_32 32 :=
  termAt_rand dag_nodes_ok (by decide) rfl hw.hσ_10_32
theorem dagSh_32 : randTerm 10 32 = dagShape dagOp dagSize 32 :=
  randTerm_eq_dagShape dag_nodes_ok (by decide) rfl
-- Node 33 (id_spkB_pk): .dhPk 32
abbrev dagT_33 : DY.Bytes := DY.DiffieHellman.dhPk dagT_32
theorem dagN_33 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_33 33 :=
  termAt_dhPk dag_nodes_ok (by decide) rfl (dagN_32 hw)
-- Node 34 (id_spkNonce): .rand 11 64
abbrev dagT_34 : DY.Bytes := randTerm 11 64
theorem dagN_34 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_34 34 :=
  termAt_rand dag_nodes_ok (by decide) rfl hw.hσ_11_64
theorem dagSh_34 : randTerm 11 64 = dagShape dagOp dagSize 34 :=
  randTerm_eq_dagShape dag_nodes_ok (by decide) rfl
-- Node 35 (id_pqskB): .rand 16 64
abbrev dagT_35 : DY.Bytes := randTerm 16 64
theorem dagN_35 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_35 35 :=
  termAt_rand dag_nodes_ok (by decide) rfl hw.hσ_16_64
theorem dagSh_35 : randTerm 16 64 = dagShape dagOp dagSize 35 :=
  randTerm_eq_dagShape dag_nodes_ok (by decide) rfl
-- Node 36 (id_pqNonce): .rand 17 64
abbrev dagT_36 : DY.Bytes := randTerm 17 64
theorem dagN_36 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_36 36 :=
  termAt_rand dag_nodes_ok (by decide) rfl hw.hσ_17_64
theorem dagSh_36 : randTerm 17 64 = dagShape dagOp dagSize 36 :=
  randTerm_eq_dagShape dag_nodes_ok (by decide) rfl
-- Node 37 (id_sec_ikA_0): .concat 1 26
abbrev dagT_37 : DY.Bytes := DY.Concat.concat dagT_1 dagT_26
theorem dagN_37 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_37 37 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_1 hw) (dagN_26 hw)
-- Node 38 (id_sec_ikA_1): .concat 1 37
abbrev dagT_38 : DY.Bytes := DY.Concat.concat dagT_1 dagT_37
theorem dagN_38 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_38 38 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_1 hw) (dagN_37 hw)
-- Node 39 (id_sec_ikA_2): .concat 11 38
abbrev dagT_39 : DY.Bytes := DY.Concat.concat dagT_11 dagT_38
theorem dagN_39 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_39 39 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_11 hw) (dagN_38 hw)
-- Node 40 (id_sec_ikA_3): .concat 1 39
abbrev dagT_40 : DY.Bytes := DY.Concat.concat dagT_1 dagT_39
theorem dagN_40 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_40 40 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_1 hw) (dagN_39 hw)
-- Node 41 (id_sec_ikA_4): .concat 2 40
abbrev dagT_41 : DY.Bytes := DY.Concat.concat dagT_2 dagT_40
theorem dagN_41 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_41 41 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_2 hw) (dagN_40 hw)
-- Node 42 (id_sec_ikA_5): .concat 2 41
abbrev dagT_42 : DY.Bytes := DY.Concat.concat dagT_2 dagT_41
theorem dagN_42 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_42 42 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_2 hw) (dagN_41 hw)
-- Node 43 (id_sec_ikA_6): .concat 2 42
abbrev dagT_43 : DY.Bytes := DY.Concat.concat dagT_2 dagT_42
theorem dagN_43 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_43 43 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_2 hw) (dagN_42 hw)
-- Node 44 (id_sec_ikA_7): .concat 2 43
abbrev dagT_44 : DY.Bytes := DY.Concat.concat dagT_2 dagT_43
theorem dagN_44 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_44 44 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_2 hw) (dagN_43 hw)
-- Node 45 (id_sec_ikA_8): .concat 2 44
abbrev dagT_45 : DY.Bytes := DY.Concat.concat dagT_2 dagT_44
theorem dagN_45 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_45 45 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_2 hw) (dagN_44 hw)
-- Node 46 (id_sec_ikB_0): .concat 1 29
abbrev dagT_46 : DY.Bytes := DY.Concat.concat dagT_1 dagT_29
theorem dagN_46 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_46 46 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_1 hw) (dagN_29 hw)
-- Node 47 (id_sec_ikB_1): .concat 1 46
abbrev dagT_47 : DY.Bytes := DY.Concat.concat dagT_1 dagT_46
theorem dagN_47 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_47 47 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_1 hw) (dagN_46 hw)
-- Node 48 (id_sec_ikB_2): .concat 12 47
abbrev dagT_48 : DY.Bytes := DY.Concat.concat dagT_12 dagT_47
theorem dagN_48 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_48 48 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_12 hw) (dagN_47 hw)
-- Node 49 (id_sec_ikB_3): .concat 1 48
abbrev dagT_49 : DY.Bytes := DY.Concat.concat dagT_1 dagT_48
theorem dagN_49 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_49 49 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_1 hw) (dagN_48 hw)
-- Node 50 (id_sec_ikB_4): .concat 2 49
abbrev dagT_50 : DY.Bytes := DY.Concat.concat dagT_2 dagT_49
theorem dagN_50 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_50 50 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_2 hw) (dagN_49 hw)
-- Node 51 (id_sec_ikB_5): .concat 2 50
abbrev dagT_51 : DY.Bytes := DY.Concat.concat dagT_2 dagT_50
theorem dagN_51 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_51 51 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_2 hw) (dagN_50 hw)
-- Node 52 (id_sec_ikB_6): .concat 2 51
abbrev dagT_52 : DY.Bytes := DY.Concat.concat dagT_2 dagT_51
theorem dagN_52 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_52 52 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_2 hw) (dagN_51 hw)
-- Node 53 (id_sec_spkB_0): .concat 2 32
abbrev dagT_53 : DY.Bytes := DY.Concat.concat dagT_2 dagT_32
theorem dagN_53 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_53 53 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_2 hw) (dagN_32 hw)
-- Node 54 (id_sec_spkB_1): .concat 1 53
abbrev dagT_54 : DY.Bytes := DY.Concat.concat dagT_1 dagT_53
theorem dagN_54 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_54 54 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_1 hw) (dagN_53 hw)
-- Node 55 (id_sec_spkB_2): .concat 12 54
abbrev dagT_55 : DY.Bytes := DY.Concat.concat dagT_12 dagT_54
theorem dagN_55 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_55 55 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_12 hw) (dagN_54 hw)
-- Node 56 (id_sec_spkB_3): .concat 1 55
abbrev dagT_56 : DY.Bytes := DY.Concat.concat dagT_1 dagT_55
theorem dagN_56 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_56 56 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_1 hw) (dagN_55 hw)
-- Node 57 (id_sec_spkB_4): .concat 2 56
abbrev dagT_57 : DY.Bytes := DY.Concat.concat dagT_2 dagT_56
theorem dagN_57 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_57 57 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_2 hw) (dagN_56 hw)
-- Node 58 (id_sec_spkB_5): .concat 2 57
abbrev dagT_58 : DY.Bytes := DY.Concat.concat dagT_2 dagT_57
theorem dagN_58 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_58 58 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_2 hw) (dagN_57 hw)
-- Node 59 (id_sec_spkB_6): .concat 2 58
abbrev dagT_59 : DY.Bytes := DY.Concat.concat dagT_2 dagT_58
theorem dagN_59 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_59 59 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_2 hw) (dagN_58 hw)
-- Node 60 (id_sec_pqskB_0): .concat 1 35
abbrev dagT_60 : DY.Bytes := DY.Concat.concat dagT_1 dagT_35
theorem dagN_60 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_60 60 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_1 hw) (dagN_35 hw)
-- Node 61 (id_sec_pqskB_1): .concat 2 60
abbrev dagT_61 : DY.Bytes := DY.Concat.concat dagT_2 dagT_60
theorem dagN_61 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_61 61 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_2 hw) (dagN_60 hw)
-- Node 62 (id_sec_pqskB_2): .concat 12 61
abbrev dagT_62 : DY.Bytes := DY.Concat.concat dagT_12 dagT_61
theorem dagN_62 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_62 62 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_12 hw) (dagN_61 hw)
-- Node 63 (id_sec_pqskB_3): .concat 1 62
abbrev dagT_63 : DY.Bytes := DY.Concat.concat dagT_1 dagT_62
theorem dagN_63 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_63 63 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_1 hw) (dagN_62 hw)
-- Node 64 (id_sec_pqskB_4): .concat 2 63
abbrev dagT_64 : DY.Bytes := DY.Concat.concat dagT_2 dagT_63
theorem dagN_64 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_64 64 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_2 hw) (dagN_63 hw)
-- Node 65 (id_sec_pqskB_5): .concat 2 64
abbrev dagT_65 : DY.Bytes := DY.Concat.concat dagT_2 dagT_64
theorem dagN_65 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_65 65 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_2 hw) (dagN_64 hw)
-- Node 66 (id_sec_pqskB_6): .concat 2 65
abbrev dagT_66 : DY.Bytes := DY.Concat.concat dagT_2 dagT_65
theorem dagN_66 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_66 66 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_2 hw) (dagN_65 hw)
-- Node 67 (id_ek_sk): .rand 22 32
abbrev dagT_67 : DY.Bytes := randTerm 22 32
theorem dagN_67 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_67 67 :=
  termAt_rand dag_nodes_ok (by decide) rfl hw.hσ_22_32
theorem dagSh_67 : randTerm 22 32 = dagShape dagOp dagSize 67 :=
  randTerm_eq_dagShape dag_nodes_ok (by decide) rfl
-- Node 68 (id_ek_pk): .dhPk 67
abbrev dagT_68 : DY.Bytes := DY.DiffieHellman.dhPk dagT_67
theorem dagN_68 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_68 68 :=
  termAt_dhPk dag_nodes_ok (by decide) rfl (dagN_67 hw)
-- Node 69 (id_ent): .rand 23 32
abbrev dagT_69 : DY.Bytes := randTerm 23 32
theorem dagN_69 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_69 69 :=
  termAt_rand dag_nodes_ok (by decide) rfl hw.hσ_23_32
theorem dagSh_69 : randTerm 23 32 = dagShape dagOp dagSize 69 :=
  randTerm_eq_dagShape dag_nodes_ok (by decide) rfl
-- Node 70 (id_ct): .kemEncap 25 69
abbrev dagT_70 (pqpkT : DY.Bytes) : DY.Bytes := (DY.PQKem.kemEncap (dagT_25 pqpkT) dagT_69).1
theorem dagN_70 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_70 pqpkT) 70 :=
  (termAt_kemEncap (id1 := 70) (id2 := 71) dag_nodes_ok (by decide) rfl (by decide) rfl (dagN_25 hw) (dagN_69 hw)).1
-- Node 71 (id_ss): .kemSS 25 69
abbrev dagT_71 (pqpkT : DY.Bytes) : DY.Bytes := (DY.PQKem.kemEncap (dagT_25 pqpkT) dagT_69).2
theorem dagN_71 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_71 pqpkT) 71 :=
  (termAt_kemEncap (id1 := 70) (id2 := 71) dag_nodes_ok (by decide) rfl (by decide) rfl (dagN_25 hw) (dagN_69 hw)).2
-- Node 72 (id_dhsA): .rand 24 32
abbrev dagT_72 : DY.Bytes := randTerm 24 32
theorem dagN_72 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_72 72 :=
  termAt_rand dag_nodes_ok (by decide) rfl hw.hσ_24_32
theorem dagSh_72 : randTerm 24 32 = dagShape dagOp dagSize 72 :=
  randTerm_eq_dagShape dag_nodes_ok (by decide) rfl
-- Node 73 (id_dhsA_pk): .dhPk 72
abbrev dagT_73 : DY.Bytes := DY.DiffieHellman.dhPk dagT_72
theorem dagN_73 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_73 73 :=
  termAt_dhPk dag_nodes_ok (by decide) rfl (dagN_72 hw)
-- Node 74 (id_dh1): .dh 33 26
abbrev dagT_74 : DY.Bytes := DY.DiffieHellman.dh dagT_33 dagT_26
theorem dagN_74 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_74 74 :=
  termAt_dh dag_nodes_ok (by decide) rfl rfl rfl dagSh_32 dagSh_26 (dagN_32 hw) (dagN_33 hw) (dagN_26 hw) (dagN_27 hw)
theorem dagN_74_symm {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (DY.DiffieHellman.dh dagT_27 dagT_32) 74 :=
  termAt_dh_symm dag_nodes_ok (by decide) rfl rfl rfl dagSh_32 dagSh_26 (dagN_32 hw) (dagN_33 hw) (dagN_26 hw) (dagN_27 hw)
-- Node 75 (id_dh2): .dh 68 29
abbrev dagT_75 : DY.Bytes := DY.DiffieHellman.dh dagT_68 dagT_29
theorem dagN_75 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_75 75 :=
  termAt_dh dag_nodes_ok (by decide) rfl rfl rfl dagSh_67 dagSh_29 (dagN_67 hw) (dagN_68 hw) (dagN_29 hw) (dagN_30 hw)
theorem dagN_75_symm {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (DY.DiffieHellman.dh dagT_30 dagT_67) 75 :=
  termAt_dh_symm dag_nodes_ok (by decide) rfl rfl rfl dagSh_67 dagSh_29 (dagN_67 hw) (dagN_68 hw) (dagN_29 hw) (dagN_30 hw)
-- Node 76 (id_dh3): .dh 68 32
abbrev dagT_76 : DY.Bytes := DY.DiffieHellman.dh dagT_68 dagT_32
theorem dagN_76 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_76 76 :=
  termAt_dh dag_nodes_ok (by decide) rfl rfl rfl dagSh_67 dagSh_32 (dagN_67 hw) (dagN_68 hw) (dagN_32 hw) (dagN_33 hw)
theorem dagN_76_symm {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (DY.DiffieHellman.dh dagT_33 dagT_67) 76 :=
  termAt_dh_symm dag_nodes_ok (by decide) rfl rfl rfl dagSh_67 dagSh_32 (dagN_67 hw) (dagN_68 hw) (dagN_32 hw) (dagN_33 hw)
-- Node 77 (id_ikm_c3): .concat 76 71
abbrev dagT_77 (pqpkT : DY.Bytes) : DY.Bytes := DY.Concat.concat dagT_76 (dagT_71 pqpkT)
theorem dagN_77 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_77 pqpkT) 77 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_76 hw) (dagN_71 hw)
-- Node 78 (id_ikm_c2): .concat 75 77
abbrev dagT_78 (pqpkT : DY.Bytes) : DY.Bytes := DY.Concat.concat dagT_75 (dagT_77 pqpkT)
theorem dagN_78 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_78 pqpkT) 78 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_75 hw) (dagN_77 hw)
-- Node 79 (id_ikm_c1): .concat 74 78
abbrev dagT_79 (pqpkT : DY.Bytes) : DY.Bytes := DY.Concat.concat dagT_74 (dagT_78 pqpkT)
theorem dagN_79 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_79 pqpkT) 79 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_74 hw) (dagN_78 hw)
-- Node 80 (id_ikm): .concat 6 79
abbrev dagT_80 (pqpkT : DY.Bytes) : DY.Bytes := DY.Concat.concat dagT_6 (dagT_79 pqpkT)
theorem dagN_80 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_80 pqpkT) 80 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_6 hw) (dagN_79 hw)
-- Node 81 (id_keys_prk): .kdf 7 80
abbrev dagT_81 (pqpkT : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract dagT_7 (dagT_80 pqpkT)
theorem dagN_81 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_81 pqpkT) 81 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_7 hw) (dagN_80 hw)
-- Node 82 (id_keys_b1): .kdf 81 18
abbrev dagT_82 (pqpkT : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_81 pqpkT) dagT_18
theorem dagN_82 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_82 pqpkT) 82 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_81 hw) (dagN_18 hw)
-- Node 83 (id_keys_c2): .concat 82 19
abbrev dagT_83 (pqpkT : DY.Bytes) : DY.Bytes := DY.Concat.concat (dagT_82 pqpkT) dagT_19
theorem dagN_83 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_83 pqpkT) 83 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_82 hw) (dagN_19 hw)
-- Node 84 (id_keys_b2): .kdf 81 83
abbrev dagT_84 (pqpkT : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_81 pqpkT) (dagT_83 pqpkT)
theorem dagN_84 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_84 pqpkT) 84 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_81 hw) (dagN_83 hw)
-- Node 85 (id_keys_c3): .concat 84 20
abbrev dagT_85 (pqpkT : DY.Bytes) : DY.Bytes := DY.Concat.concat (dagT_84 pqpkT) dagT_20
theorem dagN_85 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_85 pqpkT) 85 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_84 hw) (dagN_20 hw)
-- Node 86 (id_keys_b3): .kdf 81 85
abbrev dagT_86 (pqpkT : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_81 pqpkT) (dagT_85 pqpkT)
theorem dagN_86 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_86 pqpkT) 86 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_81 hw) (dagN_85 hw)
-- Node 87 (id_dh_init): .dh 73 32
abbrev dagT_87 : DY.Bytes := DY.DiffieHellman.dh dagT_73 dagT_32
theorem dagN_87 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_87 87 :=
  termAt_dh dag_nodes_ok (by decide) rfl rfl rfl dagSh_72 dagSh_32 (dagN_72 hw) (dagN_73 hw) (dagN_32 hw) (dagN_33 hw)
theorem dagN_87_symm {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (DY.DiffieHellman.dh dagT_33 dagT_72) 87 :=
  termAt_dh_symm dag_nodes_ok (by decide) rfl rfl rfl dagSh_72 dagSh_32 (dagN_72 hw) (dagN_73 hw) (dagN_32 hw) (dagN_33 hw)
-- Node 88 (id_stA0_prk): .kdf 82 87
abbrev dagT_88 (pqpkT : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_82 pqpkT) dagT_87
theorem dagN_88 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_88 pqpkT) 88 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_82 hw) (dagN_87 hw)
-- Node 89 (id_stA0_b1): .kdf 88 13
abbrev dagT_89 (pqpkT : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_88 pqpkT) dagT_13
theorem dagN_89 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_89 pqpkT) 89 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_88 hw) (dagN_13 hw)
-- Node 90 (id_stA0_c2): .concat 89 14
abbrev dagT_90 (pqpkT : DY.Bytes) : DY.Bytes := DY.Concat.concat (dagT_89 pqpkT) dagT_14
theorem dagN_90 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_90 pqpkT) 90 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_89 hw) (dagN_14 hw)
-- Node 91 (id_stA0_b2): .kdf 88 90
abbrev dagT_91 (pqpkT : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_88 pqpkT) (dagT_90 pqpkT)
theorem dagN_91 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_91 pqpkT) 91 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_88 hw) (dagN_90 hw)
-- Node 92 (id_stA0_sid): .concat 73 82
abbrev dagT_92 (pqpkT : DY.Bytes) : DY.Bytes := DY.Concat.concat dagT_73 (dagT_82 pqpkT)
theorem dagN_92 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_92 pqpkT) 92 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_73 hw) (dagN_82 hw)
-- Node 93 (id_coins1_32): .rand 32 32
abbrev dagT_93 : DY.Bytes := randTerm 32 32
theorem dagN_93 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_93 93 :=
  termAt_rand dag_nodes_ok (by decide) rfl hw.hσ_32_32
theorem dagSh_93 : randTerm 32 32 = dagShape dagOp dagSize 93 :=
  randTerm_eq_dagShape dag_nodes_ok (by decide) rfl
-- Node 94 (id_coins1_64): .rand 32 64
abbrev dagT_94 : DY.Bytes := randTerm 32 64
theorem dagN_94 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_94 94 :=
  termAt_rand dag_nodes_ok (by decide) rfl hw.hσ_32_64
theorem dagSh_94 : randTerm 32 64 = dagShape dagOp dagSize 94 :=
  randTerm_eq_dagShape dag_nodes_ok (by decide) rfl
-- Node 95 (id_coins2_32): .rand 39 32
abbrev dagT_95 : DY.Bytes := randTerm 39 32
theorem dagN_95 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_95 95 :=
  termAt_rand dag_nodes_ok (by decide) rfl hw.hσ_39_32
theorem dagSh_95 : randTerm 39 32 = dagShape dagOp dagSize 95 :=
  randTerm_eq_dagShape dag_nodes_ok (by decide) rfl
-- Node 96 (id_coins2_64): .rand 39 64
abbrev dagT_96 : DY.Bytes := randTerm 39 64
theorem dagN_96 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_96 96 :=
  termAt_rand dag_nodes_ok (by decide) rfl hw.hσ_39_64
theorem dagSh_96 : randTerm 39 64 = dagShape dagOp dagSize 96 :=
  randTerm_eq_dagShape dag_nodes_ok (by decide) rfl
-- Node 97 (id_seed1): .kdf 91 2
abbrev dagT_97 (pqpkT : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_91 pqpkT) dagT_2
theorem dagN_97 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_97 pqpkT) 97 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_91 hw) (dagN_2 hw)
-- Node 98 (id_cks1): .kdf 91 3
abbrev dagT_98 (pqpkT : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_91 pqpkT) dagT_3
theorem dagN_98 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_98 pqpkT) 98 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_91 hw) (dagN_3 hw)
-- Node 99 (id_m1_prk): .kdf 21 97
abbrev dagT_99 (pqpkT salt1T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_21 salt1T) (dagT_97 pqpkT)
theorem dagN_99 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_99 pqpkT salt1T) 99 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_21 hw) (dagN_97 hw)
-- Node 100 (id_m1_b1): .kdf 99 15
abbrev dagT_100 (pqpkT salt1T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_99 pqpkT salt1T) dagT_15
theorem dagN_100 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_100 pqpkT salt1T) 100 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_99 hw) (dagN_15 hw)
-- Node 101 (id_m1_c2): .concat 100 16
abbrev dagT_101 (pqpkT salt1T : DY.Bytes) : DY.Bytes := DY.Concat.concat (dagT_100 pqpkT salt1T) dagT_16
theorem dagN_101 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_101 pqpkT salt1T) 101 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_100 hw) (dagN_16 hw)
-- Node 102 (id_m1_b2): .kdf 99 101
abbrev dagT_102 (pqpkT salt1T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_99 pqpkT salt1T) (dagT_101 pqpkT salt1T)
theorem dagN_102 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_102 pqpkT salt1T) 102 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_99 hw) (dagN_101 hw)
-- Node 103 (id_m1_c3): .concat 102 17
abbrev dagT_103 (pqpkT salt1T : DY.Bytes) : DY.Bytes := DY.Concat.concat (dagT_102 pqpkT salt1T) dagT_17
theorem dagN_103 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_103 pqpkT salt1T) 103 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_102 hw) (dagN_17 hw)
-- Node 104 (id_m1_b3): .kdf 99 103
abbrev dagT_104 (pqpkT salt1T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_99 pqpkT salt1T) (dagT_103 pqpkT salt1T)
theorem dagN_104 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_104 pqpkT salt1T) 104 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_99 hw) (dagN_103 hw)
-- Node 105 (id_ct1): .symEncPt 100 104 31 [0x66#8, 0x69#8, 0x72#8, 0x73#8, 0x74#8]
abbrev dagT_105 (pqpkT salt1T : DY.Bytes) : DY.Bytes := DY.SymEnc.symEnc (dagT_100 pqpkT salt1T) (dagT_104 pqpkT salt1T) (randTerm 31 32)
theorem dagN_105 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_105 pqpkT salt1T) 105 :=
  termAt_symEncPt dag_nodes_ok (by decide) (congrArg (DagOp.symEncPt 100 104 31) (by decide +kernel) : dagOp 105 = .symEncPt 100 104 31 ev1.input) (dagN_100 hw) (dagN_104 hw) hw.hpt1_mem hw.hσ_pt1 (by decide +kernel)
-- Node 106 (id_wire1): .trWire 4 73 0 0 105 22 [0x0#8, 0x8a#8, 0x6f#8, 0x1c#8, 0x2e#8, 0x3b#8, 0x4d#8, 0x4e#8, 0x5f#8, 0x9a#8, 0xb#8, 0x1c#8, 0x2d#8, 0x3e#8, 0x4f#8, 0x5a#8, 0x6b#8, 0x1#8, 0x0#8, 0x5d#8, 0x3e#8, 0x2f#8, 0x10#8, 0x7a#8, 0x8b#8, 0x4c#8, 0x9d#8, 0x8e#8, 0xf#8, 0xa1#8, 0xb2#8, 0xc3#8, 0xd4#8, 0xe5#8, 0xf6#8, 0x1#8]
abbrev dagT_106 (pqpkT salt1T pqm1T : DY.Bytes) : DY.Bytes := trHonestWireMsg dagT_73 0 0 (dagT_105 pqpkT salt1T) (dagT_22 pqm1T)
theorem dagN_106 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_106 pqpkT salt1T pqm1T) 106 :=
  termAt_trWire dag_nodes_ok (by decide) (congrArg (DagOp.trWire messageVersion 73 0 0 105 22) (by decide +kernel) : dagOp 106 = .trWire messageVersion 73 0 0 105 22 cleanAddrBs) (dagN_73 hw) (dagN_105 hw) (dagN_22 hw) (hw.haddr _)
-- Node 107 (id_mac1_c1): .concat 31 106
abbrev dagT_107 (pqpkT salt1T pqm1T : DY.Bytes) : DY.Bytes := DY.Concat.concat dagT_31 (dagT_106 pqpkT salt1T pqm1T)
theorem dagN_107 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_107 pqpkT salt1T pqm1T) 107 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_31 hw) (dagN_106 hw)
-- Node 108 (id_mac1_c2): .concat 28 107
abbrev dagT_108 (pqpkT salt1T pqm1T : DY.Bytes) : DY.Bytes := DY.Concat.concat dagT_28 (dagT_107 pqpkT salt1T pqm1T)
theorem dagN_108 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_108 pqpkT salt1T pqm1T) 108 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_28 hw) (dagN_107 hw)
-- Node 109 (id_mac1_h): .kdf 102 108
abbrev dagT_109 (pqpkT salt1T pqm1T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_102 pqpkT salt1T) (dagT_108 pqpkT salt1T pqm1T)
theorem dagN_109 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_109 pqpkT salt1T pqm1T) 109 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_102 hw) (dagN_108 hw)
-- Node 110 (id_mac1): .trunc8 109
abbrev dagT_110 (pqpkT salt1T pqm1T : DY.Bytes) : DY.Bytes := DY.Trunc.trunc8 (dagT_109 pqpkT salt1T pqm1T)
theorem dagN_110 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_110 pqpkT salt1T pqm1T) 110 :=
  termAt_trunc8 dag_nodes_ok (by decide) rfl (dagN_109 hw)
-- Node 111 (id_m1): .concat 106 110
abbrev dagT_111 (pqpkT salt1T pqm1T : DY.Bytes) : DY.Bytes := DY.Concat.concat (dagT_106 pqpkT salt1T pqm1T) (dagT_110 pqpkT salt1T pqm1T)
theorem dagN_111 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_111 pqpkT salt1T pqm1T) 111 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_106 hw) (dagN_110 hw)
-- Node 112 (id_seed2): .kdf 98 2
abbrev dagT_112 (pqpkT : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_98 pqpkT) dagT_2
theorem dagN_112 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_112 pqpkT) 112 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_98 hw) (dagN_2 hw)
-- Node 113 (id_cks2): .kdf 98 3
abbrev dagT_113 (pqpkT : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_98 pqpkT) dagT_3
theorem dagN_113 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_113 pqpkT) 113 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_98 hw) (dagN_3 hw)
-- Node 114 (id_m2_prk): .kdf 23 112
abbrev dagT_114 (pqpkT salt2T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_23 salt2T) (dagT_112 pqpkT)
theorem dagN_114 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_114 pqpkT salt2T) 114 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_23 hw) (dagN_112 hw)
-- Node 115 (id_m2_b1): .kdf 114 15
abbrev dagT_115 (pqpkT salt2T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_114 pqpkT salt2T) dagT_15
theorem dagN_115 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_115 pqpkT salt2T) 115 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_114 hw) (dagN_15 hw)
-- Node 116 (id_m2_c2): .concat 115 16
abbrev dagT_116 (pqpkT salt2T : DY.Bytes) : DY.Bytes := DY.Concat.concat (dagT_115 pqpkT salt2T) dagT_16
theorem dagN_116 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_116 pqpkT salt2T) 116 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_115 hw) (dagN_16 hw)
-- Node 117 (id_m2_b2): .kdf 114 116
abbrev dagT_117 (pqpkT salt2T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_114 pqpkT salt2T) (dagT_116 pqpkT salt2T)
theorem dagN_117 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_117 pqpkT salt2T) 117 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_114 hw) (dagN_116 hw)
-- Node 118 (id_m2_c3): .concat 117 17
abbrev dagT_118 (pqpkT salt2T : DY.Bytes) : DY.Bytes := DY.Concat.concat (dagT_117 pqpkT salt2T) dagT_17
theorem dagN_118 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_118 pqpkT salt2T) 118 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_117 hw) (dagN_17 hw)
-- Node 119 (id_m2_b3): .kdf 114 118
abbrev dagT_119 (pqpkT salt2T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_114 pqpkT salt2T) (dagT_118 pqpkT salt2T)
theorem dagN_119 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_119 pqpkT salt2T) 119 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_114 hw) (dagN_118 hw)
-- Node 120 (id_ct2): .symEncPt 115 119 38 [0x73#8, 0x65#8, 0x63#8, 0x6f#8, 0x6e#8, 0x64#8]
abbrev dagT_120 (pqpkT salt2T : DY.Bytes) : DY.Bytes := DY.SymEnc.symEnc (dagT_115 pqpkT salt2T) (dagT_119 pqpkT salt2T) (randTerm 38 32)
theorem dagN_120 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_120 pqpkT salt2T) 120 :=
  termAt_symEncPt dag_nodes_ok (by decide) (congrArg (DagOp.symEncPt 115 119 38) (by decide +kernel) : dagOp 120 = .symEncPt 115 119 38 ev2.input) (dagN_115 hw) (dagN_119 hw) hw.hpt2_mem hw.hσ_pt2 (by decide +kernel)
-- Node 121 (id_wire2): .trWire 4 73 1 0 120 24 [0x0#8, 0x8a#8, 0x6f#8, 0x1c#8, 0x2e#8, 0x3b#8, 0x4d#8, 0x4e#8, 0x5f#8, 0x9a#8, 0xb#8, 0x1c#8, 0x2d#8, 0x3e#8, 0x4f#8, 0x5a#8, 0x6b#8, 0x1#8, 0x0#8, 0x5d#8, 0x3e#8, 0x2f#8, 0x10#8, 0x7a#8, 0x8b#8, 0x4c#8, 0x9d#8, 0x8e#8, 0xf#8, 0xa1#8, 0xb2#8, 0xc3#8, 0xd4#8, 0xe5#8, 0xf6#8, 0x1#8]
abbrev dagT_121 (pqpkT salt2T pqm2T : DY.Bytes) : DY.Bytes := trHonestWireMsg dagT_73 1 0 (dagT_120 pqpkT salt2T) (dagT_24 pqm2T)
theorem dagN_121 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_121 pqpkT salt2T pqm2T) 121 :=
  termAt_trWire dag_nodes_ok (by decide) (congrArg (DagOp.trWire messageVersion 73 1 0 120 24) (by decide +kernel) : dagOp 121 = .trWire messageVersion 73 1 0 120 24 cleanAddrBs) (dagN_73 hw) (dagN_120 hw) (dagN_24 hw) (hw.haddr _)
-- Node 122 (id_mac2_c1): .concat 31 121
abbrev dagT_122 (pqpkT salt2T pqm2T : DY.Bytes) : DY.Bytes := DY.Concat.concat dagT_31 (dagT_121 pqpkT salt2T pqm2T)
theorem dagN_122 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_122 pqpkT salt2T pqm2T) 122 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_31 hw) (dagN_121 hw)
-- Node 123 (id_mac2_c2): .concat 28 122
abbrev dagT_123 (pqpkT salt2T pqm2T : DY.Bytes) : DY.Bytes := DY.Concat.concat dagT_28 (dagT_122 pqpkT salt2T pqm2T)
theorem dagN_123 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_123 pqpkT salt2T pqm2T) 123 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_28 hw) (dagN_122 hw)
-- Node 124 (id_mac2_h): .kdf 117 123
abbrev dagT_124 (pqpkT salt2T pqm2T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_117 pqpkT salt2T) (dagT_123 pqpkT salt2T pqm2T)
theorem dagN_124 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_124 pqpkT salt2T pqm2T) 124 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_117 hw) (dagN_123 hw)
-- Node 125 (id_mac2): .trunc8 124
abbrev dagT_125 (pqpkT salt2T pqm2T : DY.Bytes) : DY.Bytes := DY.Trunc.trunc8 (dagT_124 pqpkT salt2T pqm2T)
theorem dagN_125 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_125 pqpkT salt2T pqm2T) 125 :=
  termAt_trunc8 dag_nodes_ok (by decide) rfl (dagN_124 hw)
-- Node 126 (id_m2): .concat 121 125
abbrev dagT_126 (pqpkT salt2T pqm2T : DY.Bytes) : DY.Bytes := DY.Concat.concat (dagT_121 pqpkT salt2T pqm2T) (dagT_125 pqpkT salt2T pqm2T)
theorem dagN_126 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_126 pqpkT salt2T pqm2T) 126 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_121 hw) (dagN_125 hw)
-- Node 127 (id_dhsB): .rand 45 32
abbrev dagT_127 : DY.Bytes := randTerm 45 32
theorem dagN_127 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_127 127 :=
  termAt_rand dag_nodes_ok (by decide) rfl hw.hσ_45_32
theorem dagSh_127 : randTerm 45 32 = dagShape dagOp dagSize 127 :=
  randTerm_eq_dagShape dag_nodes_ok (by decide) rfl
-- Node 128 (id_dhsB_pk): .dhPk 127
abbrev dagT_128 : DY.Bytes := DY.DiffieHellman.dhPk dagT_127
theorem dagN_128 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_128 128 :=
  termAt_dhPk dag_nodes_ok (by decide) rfl (dagN_127 hw)
-- Node 129 (id_dh_bob): .dh 128 72
abbrev dagT_129 : DY.Bytes := DY.DiffieHellman.dh dagT_128 dagT_72
theorem dagN_129 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_129 129 :=
  termAt_dh dag_nodes_ok (by decide) rfl rfl rfl dagSh_127 dagSh_72 (dagN_127 hw) (dagN_128 hw) (dagN_72 hw) (dagN_73 hw)
theorem dagN_129_symm {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (DY.DiffieHellman.dh dagT_73 dagT_127) 129 :=
  termAt_dh_symm dag_nodes_ok (by decide) rfl rfl rfl dagSh_127 dagSh_72 (dagN_127 hw) (dagN_128 hw) (dagN_72 hw) (dagN_73 hw)
-- Node 130 (id_stB_prk): .kdf 89 129
abbrev dagT_130 (pqpkT : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_89 pqpkT) dagT_129
theorem dagN_130 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_130 pqpkT) 130 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_89 hw) (dagN_129 hw)
-- Node 131 (id_stB_b1): .kdf 130 13
abbrev dagT_131 (pqpkT : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_130 pqpkT) dagT_13
theorem dagN_131 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_131 pqpkT) 131 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_130 hw) (dagN_13 hw)
-- Node 132 (id_stB_c2): .concat 131 14
abbrev dagT_132 (pqpkT : DY.Bytes) : DY.Bytes := DY.Concat.concat (dagT_131 pqpkT) dagT_14
theorem dagN_132 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_132 pqpkT) 132 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_131 hw) (dagN_14 hw)
-- Node 133 (id_stB_b2): .kdf 130 132
abbrev dagT_133 (pqpkT : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_130 pqpkT) (dagT_132 pqpkT)
theorem dagN_133 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_133 pqpkT) 133 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_130 hw) (dagN_132 hw)
-- Node 134 (id_dh_selfA): .dh 73 72
abbrev dagT_134 : DY.Bytes := DY.DiffieHellman.dh dagT_73 dagT_72
theorem dagN_134 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts dagT_134 134 :=
  termAt_dh dag_nodes_ok (by decide) rfl rfl rfl dagSh_72 dagSh_72 (dagN_72 hw) (dagN_73 hw) (dagN_72 hw) (dagN_73 hw)
theorem dagN_134_symm {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (DY.DiffieHellman.dh dagT_73 dagT_72) 134 :=
  termAt_dh_symm dag_nodes_ok (by decide) rfl rfl rfl dagSh_72 dagSh_72 (dagN_72 hw) (dagN_73 hw) (dagN_72 hw) (dagN_73 hw)
-- Node 135 (id_selfA_prk): .kdf 89 134
abbrev dagT_135 (pqpkT : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_89 pqpkT) dagT_134
theorem dagN_135 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_135 pqpkT) 135 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_89 hw) (dagN_134 hw)
-- Node 136 (id_selfA_b1): .kdf 135 13
abbrev dagT_136 (pqpkT : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_135 pqpkT) dagT_13
theorem dagN_136 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_136 pqpkT) 136 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_135 hw) (dagN_13 hw)
-- Node 137 (id_selfA_c2): .concat 136 14
abbrev dagT_137 (pqpkT : DY.Bytes) : DY.Bytes := DY.Concat.concat (dagT_136 pqpkT) dagT_14
theorem dagN_137 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_137 pqpkT) 137 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_136 hw) (dagN_14 hw)
-- Node 138 (id_selfA_b2): .kdf 135 137
abbrev dagT_138 (pqpkT : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_135 pqpkT) (dagT_137 pqpkT)
theorem dagN_138 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_138 pqpkT) 138 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_135 hw) (dagN_137 hw)
-- Node 139 (id_seed_self0): .kdf 138 2
abbrev dagT_139 (pqpkT : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_138 pqpkT) dagT_2
theorem dagN_139 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_139 pqpkT) 139 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_138 hw) (dagN_2 hw)
-- Node 140 (id_cks_self1): .kdf 138 3
abbrev dagT_140 (pqpkT : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_138 pqpkT) dagT_3
theorem dagN_140 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_140 pqpkT) 140 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_138 hw) (dagN_3 hw)
-- Node 141 (tr_bob3_s0_prk): .kdf 7 112
abbrev dagT_141 (pqpkT : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract dagT_7 (dagT_112 pqpkT)
theorem dagN_141 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_141 pqpkT) 141 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_7 hw) (dagN_112 hw)
-- Node 142 (tr_bob3_s0_b1): .kdf 141 15
abbrev dagT_142 (pqpkT : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_141 pqpkT) dagT_15
theorem dagN_142 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_142 pqpkT) 142 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_141 hw) (dagN_15 hw)
-- Node 143 (tr_bob3_s0_c2): .concat 142 16
abbrev dagT_143 (pqpkT : DY.Bytes) : DY.Bytes := DY.Concat.concat (dagT_142 pqpkT) dagT_16
theorem dagN_143 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_143 pqpkT) 143 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_142 hw) (dagN_16 hw)
-- Node 144 (tr_bob3_s0_b2): .kdf 141 143
abbrev dagT_144 (pqpkT : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_141 pqpkT) (dagT_143 pqpkT)
theorem dagN_144 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_144 pqpkT) 144 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_141 hw) (dagN_143 hw)
-- Node 145 (tr_bob3_s0_c3): .concat 144 17
abbrev dagT_145 (pqpkT : DY.Bytes) : DY.Bytes := DY.Concat.concat (dagT_144 pqpkT) dagT_17
theorem dagN_145 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_145 pqpkT) 145 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_144 hw) (dagN_17 hw)
-- Node 146 (tr_bob3_s0_b3): .kdf 141 145
abbrev dagT_146 (pqpkT : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_141 pqpkT) (dagT_145 pqpkT)
theorem dagN_146 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_146 pqpkT) 146 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_141 hw) (dagN_145 hw)
-- Node 147 (tr_bob3_s0_fmac): .kdf 144 123
abbrev dagT_147 (pqpkT salt2T pqm2T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_144 pqpkT) (dagT_123 pqpkT salt2T pqm2T)
theorem dagN_147 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_147 pqpkT salt2T pqm2T) 147 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_144 hw) (dagN_123 hw)
-- Node 148 (tr_bob3_s0_mac): .trunc8 147
abbrev dagT_148 (pqpkT salt2T pqm2T : DY.Bytes) : DY.Bytes := DY.Trunc.trunc8 (dagT_147 pqpkT salt2T pqm2T)
theorem dagN_148 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_148 pqpkT salt2T pqm2T) 148 :=
  termAt_trunc8 dag_nodes_ok (by decide) rfl (dagN_147 hw)
-- Node 149 (tr_bob3_s1_prk): .kdf 21 112
abbrev dagT_149 (pqpkT salt1T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_21 salt1T) (dagT_112 pqpkT)
theorem dagN_149 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_149 pqpkT salt1T) 149 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_21 hw) (dagN_112 hw)
-- Node 150 (tr_bob3_s1_b1): .kdf 149 15
abbrev dagT_150 (pqpkT salt1T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_149 pqpkT salt1T) dagT_15
theorem dagN_150 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_150 pqpkT salt1T) 150 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_149 hw) (dagN_15 hw)
-- Node 151 (tr_bob3_s1_c2): .concat 150 16
abbrev dagT_151 (pqpkT salt1T : DY.Bytes) : DY.Bytes := DY.Concat.concat (dagT_150 pqpkT salt1T) dagT_16
theorem dagN_151 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_151 pqpkT salt1T) 151 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_150 hw) (dagN_16 hw)
-- Node 152 (tr_bob3_s1_b2): .kdf 149 151
abbrev dagT_152 (pqpkT salt1T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_149 pqpkT salt1T) (dagT_151 pqpkT salt1T)
theorem dagN_152 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_152 pqpkT salt1T) 152 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_149 hw) (dagN_151 hw)
-- Node 153 (tr_bob3_s1_c3): .concat 152 17
abbrev dagT_153 (pqpkT salt1T : DY.Bytes) : DY.Bytes := DY.Concat.concat (dagT_152 pqpkT salt1T) dagT_17
theorem dagN_153 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_153 pqpkT salt1T) 153 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_152 hw) (dagN_17 hw)
-- Node 154 (tr_bob3_s1_b3): .kdf 149 153
abbrev dagT_154 (pqpkT salt1T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_149 pqpkT salt1T) (dagT_153 pqpkT salt1T)
theorem dagN_154 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_154 pqpkT salt1T) 154 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_149 hw) (dagN_153 hw)
-- Node 155 (tr_bob3_s1_fmac): .kdf 152 123
abbrev dagT_155 (pqpkT salt1T salt2T pqm2T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_152 pqpkT salt1T) (dagT_123 pqpkT salt2T pqm2T)
theorem dagN_155 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_155 pqpkT salt1T salt2T pqm2T) 155 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_152 hw) (dagN_123 hw)
-- Node 156 (tr_bob3_s1_mac): .trunc8 155
abbrev dagT_156 (pqpkT salt1T salt2T pqm2T : DY.Bytes) : DY.Bytes := DY.Trunc.trunc8 (dagT_155 pqpkT salt1T salt2T pqm2T)
theorem dagN_156 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_156 pqpkT salt1T salt2T pqm2T) 156 :=
  termAt_trunc8 dag_nodes_ok (by decide) rfl (dagN_155 hw)
-- Node 157 (tr_selfA_miR): .concat 28 106
abbrev dagT_157 (pqpkT salt1T pqm1T : DY.Bytes) : DY.Bytes := DY.Concat.concat dagT_28 (dagT_106 pqpkT salt1T pqm1T)
theorem dagN_157 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_157 pqpkT salt1T pqm1T) 157 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_28 hw) (dagN_106 hw)
-- Node 158 (tr_selfA_mi): .concat 31 157
abbrev dagT_158 (pqpkT salt1T pqm1T : DY.Bytes) : DY.Bytes := DY.Concat.concat dagT_31 (dagT_157 pqpkT salt1T pqm1T)
theorem dagN_158 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_158 pqpkT salt1T pqm1T) 158 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_31 hw) (dagN_157 hw)
-- Node 159 (tr_selfA_s0_prk): .kdf 7 139
abbrev dagT_159 (pqpkT : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract dagT_7 (dagT_139 pqpkT)
theorem dagN_159 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_159 pqpkT) 159 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_7 hw) (dagN_139 hw)
-- Node 160 (tr_selfA_s0_b1): .kdf 159 15
abbrev dagT_160 (pqpkT : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_159 pqpkT) dagT_15
theorem dagN_160 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_160 pqpkT) 160 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_159 hw) (dagN_15 hw)
-- Node 161 (tr_selfA_s0_c2): .concat 160 16
abbrev dagT_161 (pqpkT : DY.Bytes) : DY.Bytes := DY.Concat.concat (dagT_160 pqpkT) dagT_16
theorem dagN_161 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_161 pqpkT) 161 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_160 hw) (dagN_16 hw)
-- Node 162 (tr_selfA_s0_b2): .kdf 159 161
abbrev dagT_162 (pqpkT : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_159 pqpkT) (dagT_161 pqpkT)
theorem dagN_162 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_162 pqpkT) 162 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_159 hw) (dagN_161 hw)
-- Node 163 (tr_selfA_s0_c3): .concat 162 17
abbrev dagT_163 (pqpkT : DY.Bytes) : DY.Bytes := DY.Concat.concat (dagT_162 pqpkT) dagT_17
theorem dagN_163 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_163 pqpkT) 163 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_162 hw) (dagN_17 hw)
-- Node 164 (tr_selfA_s0_b3): .kdf 159 163
abbrev dagT_164 (pqpkT : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_159 pqpkT) (dagT_163 pqpkT)
theorem dagN_164 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_164 pqpkT) 164 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_159 hw) (dagN_163 hw)
-- Node 165 (tr_selfA_s0_fmac): .kdf 162 158
abbrev dagT_165 (pqpkT salt1T pqm1T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_162 pqpkT) (dagT_158 pqpkT salt1T pqm1T)
theorem dagN_165 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_165 pqpkT salt1T pqm1T) 165 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_162 hw) (dagN_158 hw)
-- Node 166 (tr_selfA_s0_mac): .trunc8 165
abbrev dagT_166 (pqpkT salt1T pqm1T : DY.Bytes) : DY.Bytes := DY.Trunc.trunc8 (dagT_165 pqpkT salt1T pqm1T)
theorem dagN_166 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_166 pqpkT salt1T pqm1T) 166 :=
  termAt_trunc8 dag_nodes_ok (by decide) rfl (dagN_165 hw)
-- Node 167 (tr_selfA_s1_prk): .kdf 21 139
abbrev dagT_167 (pqpkT salt1T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_21 salt1T) (dagT_139 pqpkT)
theorem dagN_167 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_167 pqpkT salt1T) 167 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_21 hw) (dagN_139 hw)
-- Node 168 (tr_selfA_s1_b1): .kdf 167 15
abbrev dagT_168 (pqpkT salt1T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_167 pqpkT salt1T) dagT_15
theorem dagN_168 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_168 pqpkT salt1T) 168 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_167 hw) (dagN_15 hw)
-- Node 169 (tr_selfA_s1_c2): .concat 168 16
abbrev dagT_169 (pqpkT salt1T : DY.Bytes) : DY.Bytes := DY.Concat.concat (dagT_168 pqpkT salt1T) dagT_16
theorem dagN_169 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_169 pqpkT salt1T) 169 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_168 hw) (dagN_16 hw)
-- Node 170 (tr_selfA_s1_b2): .kdf 167 169
abbrev dagT_170 (pqpkT salt1T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_167 pqpkT salt1T) (dagT_169 pqpkT salt1T)
theorem dagN_170 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_170 pqpkT salt1T) 170 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_167 hw) (dagN_169 hw)
-- Node 171 (tr_selfA_s1_c3): .concat 170 17
abbrev dagT_171 (pqpkT salt1T : DY.Bytes) : DY.Bytes := DY.Concat.concat (dagT_170 pqpkT salt1T) dagT_17
theorem dagN_171 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_171 pqpkT salt1T) 171 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_170 hw) (dagN_17 hw)
-- Node 172 (tr_selfA_s1_b3): .kdf 167 171
abbrev dagT_172 (pqpkT salt1T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_167 pqpkT salt1T) (dagT_171 pqpkT salt1T)
theorem dagN_172 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_172 pqpkT salt1T) 172 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_167 hw) (dagN_171 hw)
-- Node 173 (tr_selfA_s1_fmac): .kdf 170 158
abbrev dagT_173 (pqpkT salt1T pqm1T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_170 pqpkT salt1T) (dagT_158 pqpkT salt1T pqm1T)
theorem dagN_173 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_173 pqpkT salt1T pqm1T) 173 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_170 hw) (dagN_158 hw)
-- Node 174 (tr_selfA_s1_mac): .trunc8 173
abbrev dagT_174 (pqpkT salt1T pqm1T : DY.Bytes) : DY.Bytes := DY.Trunc.trunc8 (dagT_173 pqpkT salt1T pqm1T)
theorem dagN_174 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_174 pqpkT salt1T pqm1T) 174 :=
  termAt_trunc8 dag_nodes_ok (by decide) rfl (dagN_173 hw)
-- Node 175 (tr_selfA_s2_prk): .kdf 23 139
abbrev dagT_175 (pqpkT salt2T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_23 salt2T) (dagT_139 pqpkT)
theorem dagN_175 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_175 pqpkT salt2T) 175 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_23 hw) (dagN_139 hw)
-- Node 176 (tr_selfA_s2_b1): .kdf 175 15
abbrev dagT_176 (pqpkT salt2T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_175 pqpkT salt2T) dagT_15
theorem dagN_176 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_176 pqpkT salt2T) 176 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_175 hw) (dagN_15 hw)
-- Node 177 (tr_selfA_s2_c2): .concat 176 16
abbrev dagT_177 (pqpkT salt2T : DY.Bytes) : DY.Bytes := DY.Concat.concat (dagT_176 pqpkT salt2T) dagT_16
theorem dagN_177 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_177 pqpkT salt2T) 177 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_176 hw) (dagN_16 hw)
-- Node 178 (tr_selfA_s2_b2): .kdf 175 177
abbrev dagT_178 (pqpkT salt2T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_175 pqpkT salt2T) (dagT_177 pqpkT salt2T)
theorem dagN_178 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_178 pqpkT salt2T) 178 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_175 hw) (dagN_177 hw)
-- Node 179 (tr_selfA_s2_c3): .concat 178 17
abbrev dagT_179 (pqpkT salt2T : DY.Bytes) : DY.Bytes := DY.Concat.concat (dagT_178 pqpkT salt2T) dagT_17
theorem dagN_179 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_179 pqpkT salt2T) 179 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_178 hw) (dagN_17 hw)
-- Node 180 (tr_selfA_s2_b3): .kdf 175 179
abbrev dagT_180 (pqpkT salt2T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_175 pqpkT salt2T) (dagT_179 pqpkT salt2T)
theorem dagN_180 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_180 pqpkT salt2T) 180 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_175 hw) (dagN_179 hw)
-- Node 181 (tr_selfA_s2_fmac): .kdf 178 158
abbrev dagT_181 (pqpkT salt1T pqm1T salt2T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_178 pqpkT salt2T) (dagT_158 pqpkT salt1T pqm1T)
theorem dagN_181 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_181 pqpkT salt1T pqm1T salt2T) 181 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_178 hw) (dagN_158 hw)
-- Node 182 (tr_selfA_s2_mac): .trunc8 181
abbrev dagT_182 (pqpkT salt1T pqm1T salt2T : DY.Bytes) : DY.Bytes := DY.Trunc.trunc8 (dagT_181 pqpkT salt1T pqm1T salt2T)
theorem dagN_182 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_182 pqpkT salt1T pqm1T salt2T) 182 :=
  termAt_trunc8 dag_nodes_ok (by decide) rfl (dagN_181 hw)
-- Node 183 (tr_skipB_s0_prk): .kdf 7 97
abbrev dagT_183 (pqpkT : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract dagT_7 (dagT_97 pqpkT)
theorem dagN_183 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_183 pqpkT) 183 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_7 hw) (dagN_97 hw)
-- Node 184 (tr_skipB_s0_b1): .kdf 183 15
abbrev dagT_184 (pqpkT : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_183 pqpkT) dagT_15
theorem dagN_184 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_184 pqpkT) 184 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_183 hw) (dagN_15 hw)
-- Node 185 (tr_skipB_s0_c2): .concat 184 16
abbrev dagT_185 (pqpkT : DY.Bytes) : DY.Bytes := DY.Concat.concat (dagT_184 pqpkT) dagT_16
theorem dagN_185 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_185 pqpkT) 185 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_184 hw) (dagN_16 hw)
-- Node 186 (tr_skipB_s0_b2): .kdf 183 185
abbrev dagT_186 (pqpkT : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_183 pqpkT) (dagT_185 pqpkT)
theorem dagN_186 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_186 pqpkT) 186 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_183 hw) (dagN_185 hw)
-- Node 187 (tr_skipB_s0_c3): .concat 186 17
abbrev dagT_187 (pqpkT : DY.Bytes) : DY.Bytes := DY.Concat.concat (dagT_186 pqpkT) dagT_17
theorem dagN_187 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_187 pqpkT) 187 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_186 hw) (dagN_17 hw)
-- Node 188 (tr_skipB_s0_b3): .kdf 183 187
abbrev dagT_188 (pqpkT : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_183 pqpkT) (dagT_187 pqpkT)
theorem dagN_188 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_188 pqpkT) 188 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_183 hw) (dagN_187 hw)
-- Node 189 (tr_skipB_s0_fmac): .kdf 186 108
abbrev dagT_189 (pqpkT salt1T pqm1T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_186 pqpkT) (dagT_108 pqpkT salt1T pqm1T)
theorem dagN_189 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_189 pqpkT salt1T pqm1T) 189 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_186 hw) (dagN_108 hw)
-- Node 190 (tr_skipB_s0_mac): .trunc8 189
abbrev dagT_190 (pqpkT salt1T pqm1T : DY.Bytes) : DY.Bytes := DY.Trunc.trunc8 (dagT_189 pqpkT salt1T pqm1T)
theorem dagN_190 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_190 pqpkT salt1T pqm1T) 190 :=
  termAt_trunc8 dag_nodes_ok (by decide) rfl (dagN_189 hw)
-- Node 191 (tr_skipB_s2_prk): .kdf 23 97
abbrev dagT_191 (pqpkT salt2T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_23 salt2T) (dagT_97 pqpkT)
theorem dagN_191 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_191 pqpkT salt2T) 191 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_23 hw) (dagN_97 hw)
-- Node 192 (tr_skipB_s2_b1): .kdf 191 15
abbrev dagT_192 (pqpkT salt2T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_191 pqpkT salt2T) dagT_15
theorem dagN_192 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_192 pqpkT salt2T) 192 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_191 hw) (dagN_15 hw)
-- Node 193 (tr_skipB_s2_c2): .concat 192 16
abbrev dagT_193 (pqpkT salt2T : DY.Bytes) : DY.Bytes := DY.Concat.concat (dagT_192 pqpkT salt2T) dagT_16
theorem dagN_193 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_193 pqpkT salt2T) 193 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_192 hw) (dagN_16 hw)
-- Node 194 (tr_skipB_s2_b2): .kdf 191 193
abbrev dagT_194 (pqpkT salt2T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_191 pqpkT salt2T) (dagT_193 pqpkT salt2T)
theorem dagN_194 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_194 pqpkT salt2T) 194 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_191 hw) (dagN_193 hw)
-- Node 195 (tr_skipB_s2_c3): .concat 194 17
abbrev dagT_195 (pqpkT salt2T : DY.Bytes) : DY.Bytes := DY.Concat.concat (dagT_194 pqpkT salt2T) dagT_17
theorem dagN_195 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_195 pqpkT salt2T) 195 :=
  termAt_concat dag_nodes_ok (by decide) rfl (dagN_194 hw) (dagN_17 hw)
-- Node 196 (tr_skipB_s2_b3): .kdf 191 195
abbrev dagT_196 (pqpkT salt2T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_191 pqpkT salt2T) (dagT_195 pqpkT salt2T)
theorem dagN_196 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_196 pqpkT salt2T) 196 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_191 hw) (dagN_195 hw)
-- Node 197 (tr_skipB_s2_fmac): .kdf 194 108
abbrev dagT_197 (pqpkT salt1T pqm1T salt2T : DY.Bytes) : DY.Bytes := DY.KdfExtract.kdfExtract (dagT_194 pqpkT salt2T) (dagT_108 pqpkT salt1T pqm1T)
theorem dagN_197 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_197 pqpkT salt1T pqm1T salt2T) 197 :=
  termAt_kdf dag_nodes_ok (by decide) rfl (dagN_194 hw) (dagN_108 hw)
-- Node 198 (tr_skipB_s2_mac): .trunc8 197
abbrev dagT_198 (pqpkT salt1T pqm1T salt2T : DY.Bytes) : DY.Bytes := DY.Trunc.trunc8 (dagT_197 pqpkT salt1T pqm1T salt2T)
theorem dagN_198 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes} {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes} (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) : DagTermAt S g pts (dagT_198 pqpkT salt1T pqm1T salt2T) 198 :=
  termAt_trunc8 dag_nodes_ok (by decide) rfl (dagN_197 hw)

theorem dagN_zeroKey {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes}
    (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) :
    DagTermAt S g pts DY.Spqr.zeroKey 7 :=
  termAt_of_opaqueAt (by decide) (dagOp_lit_eq rfl (by decide +kernel)) hw.hzero

theorem dagTrialRow_0 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes}
    (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) :
    DagSafeMemo S g pts (trMsgKeys DY.Spqr.zeroKey (dagT_112 pqpkT)).cipherKey ∧
    DagSafeMemo S g pts (trMsgKeys DY.Spqr.zeroKey (dagT_112 pqpkT)).macKey ∧
    DagSafeMemo S g pts (trMsgKeys DY.Spqr.zeroKey (dagT_112 pqpkT)).iv ∧
    DagSafeMemo S g pts (computeMac (trMsgKeys DY.Spqr.zeroKey (dagT_112 pqpkT)).macKey
      dagT_28 dagT_31 (dagT_121 pqpkT salt2T pqm2T)) := by
  obtain ⟨tck, tmk, tiv⟩ := termAt_trMsgKeys
    (prk_id := 141) (ck_id := 142) (c2_id := 143) (mk_id := 144) (c3_id := 145) (iv_id := 146)
    dag_nodes_ok
    (dagN_15 hw) (dagN_16 hw) (dagN_17 hw)
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    (dagN_zeroKey hw) (dagN_112 hw)
  have tmac := termAt_computeMac
    (c1_id := 122) (c2_id := 123) (h_id := 147) (t_id := 148)
    dag_nodes_ok
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    tmk (dagN_28 hw) (dagN_31 hw) (dagN_121 hw)
  exact ⟨tck.safeMemo, tmk.safeMemo, tiv.safeMemo, tmac.safeMemo⟩

theorem dagTrialRow_1 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes}
    (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) :
    DagSafeMemo S g pts (trMsgKeys salt1T (dagT_112 pqpkT)).cipherKey ∧
    DagSafeMemo S g pts (trMsgKeys salt1T (dagT_112 pqpkT)).macKey ∧
    DagSafeMemo S g pts (trMsgKeys salt1T (dagT_112 pqpkT)).iv ∧
    DagSafeMemo S g pts (computeMac (trMsgKeys salt1T (dagT_112 pqpkT)).macKey
      dagT_28 dagT_31 (dagT_121 pqpkT salt2T pqm2T)) := by
  obtain ⟨tck, tmk, tiv⟩ := termAt_trMsgKeys
    (prk_id := 149) (ck_id := 150) (c2_id := 151) (mk_id := 152) (c3_id := 153) (iv_id := 154)
    dag_nodes_ok
    (dagN_15 hw) (dagN_16 hw) (dagN_17 hw)
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    (dagN_21 hw) (dagN_112 hw)
  have tmac := termAt_computeMac
    (c1_id := 122) (c2_id := 123) (h_id := 155) (t_id := 156)
    dag_nodes_ok
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    tmk (dagN_28 hw) (dagN_31 hw) (dagN_121 hw)
  exact ⟨tck.safeMemo, tmk.safeMemo, tiv.safeMemo, tmac.safeMemo⟩

theorem dagTrialRow_2 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes}
    (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) :
    DagSafeMemo S g pts (trMsgKeys salt2T (dagT_112 pqpkT)).cipherKey ∧
    DagSafeMemo S g pts (trMsgKeys salt2T (dagT_112 pqpkT)).macKey ∧
    DagSafeMemo S g pts (trMsgKeys salt2T (dagT_112 pqpkT)).iv ∧
    DagSafeMemo S g pts (computeMac (trMsgKeys salt2T (dagT_112 pqpkT)).macKey
      dagT_28 dagT_31 (dagT_121 pqpkT salt2T pqm2T)) := by
  obtain ⟨tck, tmk, tiv⟩ := termAt_trMsgKeys
    (prk_id := 114) (ck_id := 115) (c2_id := 116) (mk_id := 117) (c3_id := 118) (iv_id := 119)
    dag_nodes_ok
    (dagN_15 hw) (dagN_16 hw) (dagN_17 hw)
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    (dagN_23 hw) (dagN_112 hw)
  have tmac := termAt_computeMac
    (c1_id := 122) (c2_id := 123) (h_id := 124) (t_id := 125)
    dag_nodes_ok
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    tmk (dagN_28 hw) (dagN_31 hw) (dagN_121 hw)
  exact ⟨tck.safeMemo, tmk.safeMemo, tiv.safeMemo, tmac.safeMemo⟩

theorem dagTrialRow_3 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes}
    (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) :
    DagSafeMemo S g pts (trMsgKeys DY.Spqr.zeroKey (dagT_139 pqpkT)).cipherKey ∧
    DagSafeMemo S g pts (trMsgKeys DY.Spqr.zeroKey (dagT_139 pqpkT)).macKey ∧
    DagSafeMemo S g pts (trMsgKeys DY.Spqr.zeroKey (dagT_139 pqpkT)).iv ∧
    DagSafeMemo S g pts (computeMac (trMsgKeys DY.Spqr.zeroKey (dagT_139 pqpkT)).macKey
      dagT_31 dagT_28 (dagT_106 pqpkT salt1T pqm1T)) := by
  obtain ⟨tck, tmk, tiv⟩ := termAt_trMsgKeys
    (prk_id := 159) (ck_id := 160) (c2_id := 161) (mk_id := 162) (c3_id := 163) (iv_id := 164)
    dag_nodes_ok
    (dagN_15 hw) (dagN_16 hw) (dagN_17 hw)
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    (dagN_zeroKey hw) (dagN_139 hw)
  have tmac := termAt_computeMac
    (c1_id := 157) (c2_id := 158) (h_id := 165) (t_id := 166)
    dag_nodes_ok
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    tmk (dagN_31 hw) (dagN_28 hw) (dagN_106 hw)
  exact ⟨tck.safeMemo, tmk.safeMemo, tiv.safeMemo, tmac.safeMemo⟩

theorem dagTrialRow_4 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes}
    (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) :
    DagSafeMemo S g pts (trMsgKeys salt1T (dagT_139 pqpkT)).cipherKey ∧
    DagSafeMemo S g pts (trMsgKeys salt1T (dagT_139 pqpkT)).macKey ∧
    DagSafeMemo S g pts (trMsgKeys salt1T (dagT_139 pqpkT)).iv ∧
    DagSafeMemo S g pts (computeMac (trMsgKeys salt1T (dagT_139 pqpkT)).macKey
      dagT_31 dagT_28 (dagT_106 pqpkT salt1T pqm1T)) := by
  obtain ⟨tck, tmk, tiv⟩ := termAt_trMsgKeys
    (prk_id := 167) (ck_id := 168) (c2_id := 169) (mk_id := 170) (c3_id := 171) (iv_id := 172)
    dag_nodes_ok
    (dagN_15 hw) (dagN_16 hw) (dagN_17 hw)
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    (dagN_21 hw) (dagN_139 hw)
  have tmac := termAt_computeMac
    (c1_id := 157) (c2_id := 158) (h_id := 173) (t_id := 174)
    dag_nodes_ok
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    tmk (dagN_31 hw) (dagN_28 hw) (dagN_106 hw)
  exact ⟨tck.safeMemo, tmk.safeMemo, tiv.safeMemo, tmac.safeMemo⟩

theorem dagTrialRow_5 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes}
    (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) :
    DagSafeMemo S g pts (trMsgKeys salt2T (dagT_139 pqpkT)).cipherKey ∧
    DagSafeMemo S g pts (trMsgKeys salt2T (dagT_139 pqpkT)).macKey ∧
    DagSafeMemo S g pts (trMsgKeys salt2T (dagT_139 pqpkT)).iv ∧
    DagSafeMemo S g pts (computeMac (trMsgKeys salt2T (dagT_139 pqpkT)).macKey
      dagT_31 dagT_28 (dagT_106 pqpkT salt1T pqm1T)) := by
  obtain ⟨tck, tmk, tiv⟩ := termAt_trMsgKeys
    (prk_id := 175) (ck_id := 176) (c2_id := 177) (mk_id := 178) (c3_id := 179) (iv_id := 180)
    dag_nodes_ok
    (dagN_15 hw) (dagN_16 hw) (dagN_17 hw)
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    (dagN_23 hw) (dagN_139 hw)
  have tmac := termAt_computeMac
    (c1_id := 157) (c2_id := 158) (h_id := 181) (t_id := 182)
    dag_nodes_ok
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    tmk (dagN_31 hw) (dagN_28 hw) (dagN_106 hw)
  exact ⟨tck.safeMemo, tmk.safeMemo, tiv.safeMemo, tmac.safeMemo⟩

theorem dagTrialRow_6 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes}
    (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) :
    DagSafeMemo S g pts (trMsgKeys DY.Spqr.zeroKey (dagT_97 pqpkT)).cipherKey ∧
    DagSafeMemo S g pts (trMsgKeys DY.Spqr.zeroKey (dagT_97 pqpkT)).macKey ∧
    DagSafeMemo S g pts (trMsgKeys DY.Spqr.zeroKey (dagT_97 pqpkT)).iv ∧
    DagSafeMemo S g pts (computeMac (trMsgKeys DY.Spqr.zeroKey (dagT_97 pqpkT)).macKey
      dagT_28 dagT_31 (dagT_106 pqpkT salt1T pqm1T)) := by
  obtain ⟨tck, tmk, tiv⟩ := termAt_trMsgKeys
    (prk_id := 183) (ck_id := 184) (c2_id := 185) (mk_id := 186) (c3_id := 187) (iv_id := 188)
    dag_nodes_ok
    (dagN_15 hw) (dagN_16 hw) (dagN_17 hw)
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    (dagN_zeroKey hw) (dagN_97 hw)
  have tmac := termAt_computeMac
    (c1_id := 107) (c2_id := 108) (h_id := 189) (t_id := 190)
    dag_nodes_ok
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    tmk (dagN_28 hw) (dagN_31 hw) (dagN_106 hw)
  exact ⟨tck.safeMemo, tmk.safeMemo, tiv.safeMemo, tmac.safeMemo⟩

theorem dagTrialRow_7 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes}
    (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) :
    DagSafeMemo S g pts (trMsgKeys salt1T (dagT_97 pqpkT)).cipherKey ∧
    DagSafeMemo S g pts (trMsgKeys salt1T (dagT_97 pqpkT)).macKey ∧
    DagSafeMemo S g pts (trMsgKeys salt1T (dagT_97 pqpkT)).iv ∧
    DagSafeMemo S g pts (computeMac (trMsgKeys salt1T (dagT_97 pqpkT)).macKey
      dagT_28 dagT_31 (dagT_106 pqpkT salt1T pqm1T)) := by
  obtain ⟨tck, tmk, tiv⟩ := termAt_trMsgKeys
    (prk_id := 99) (ck_id := 100) (c2_id := 101) (mk_id := 102) (c3_id := 103) (iv_id := 104)
    dag_nodes_ok
    (dagN_15 hw) (dagN_16 hw) (dagN_17 hw)
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    (dagN_21 hw) (dagN_97 hw)
  have tmac := termAt_computeMac
    (c1_id := 107) (c2_id := 108) (h_id := 109) (t_id := 110)
    dag_nodes_ok
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    tmk (dagN_28 hw) (dagN_31 hw) (dagN_106 hw)
  exact ⟨tck.safeMemo, tmk.safeMemo, tiv.safeMemo, tmac.safeMemo⟩

theorem dagTrialRow_8 {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {pqpkT salt1T pqm1T salt2T pqm2T : DY.Bytes}
    (hw : CleanDagHyp S g pts pqpkT salt1T pqm1T salt2T pqm2T) :
    DagSafeMemo S g pts (trMsgKeys salt2T (dagT_97 pqpkT)).cipherKey ∧
    DagSafeMemo S g pts (trMsgKeys salt2T (dagT_97 pqpkT)).macKey ∧
    DagSafeMemo S g pts (trMsgKeys salt2T (dagT_97 pqpkT)).iv ∧
    DagSafeMemo S g pts (computeMac (trMsgKeys salt2T (dagT_97 pqpkT)).macKey
      dagT_28 dagT_31 (dagT_106 pqpkT salt1T pqm1T)) := by
  obtain ⟨tck, tmk, tiv⟩ := termAt_trMsgKeys
    (prk_id := 191) (ck_id := 192) (c2_id := 193) (mk_id := 194) (c3_id := 195) (iv_id := 196)
    dag_nodes_ok
    (dagN_15 hw) (dagN_16 hw) (dagN_17 hw)
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    (dagN_23 hw) (dagN_97 hw)
  have tmac := termAt_computeMac
    (c1_id := 107) (c2_id := 108) (h_id := 197) (t_id := 198)
    dag_nodes_ok
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    tmk (dagN_28 hw) (dagN_31 hw) (dagN_106 hw)
  exact ⟨tck.safeMemo, tmk.safeMemo, tiv.safeMemo, tmac.safeMemo⟩

end Step2DagWalk

end
end Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay
