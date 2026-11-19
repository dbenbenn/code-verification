/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3a2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropSessionStructure3
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderStore.SessionRecordCallees
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSpe2Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenBlocks
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenVerNeBlocks
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpe
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep

/-!
# Stage P3 Version-Mismatch Path

Proves `stageP3_ver_ne_ext_ok` (`+0x1e04 → s0.readReg64 .x30` when `st.version ≠ msgVer`) on
`tripleRatchetProgAtExt b ext`, logging the version mismatch, recording the decryption-failed
`SignalProtocolError`, dropping both `SessionStructure` slots, and returning to
`s0.readReg64 .x30`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

/-! ## 1. Spatial Fold Helpers for `stageP3_ver_ne_ext_ok` -/

theorem sp3e0_48_ver_fold (sp w0 w2 w3 w4 w5 : BitVec 64) (lo1 hi1 : BitVec 32) :
    ((sp + 0x3e0#64) ↦₆₄ w0) ∗
    ((sp + 0x3e8#64) ↦₃₂ lo1) ∗
    ((sp + 0x3ec#64) ↦₃₂ hi1) ∗
    ((sp + 0x3f0#64) ↦₆₄ w2) ∗
    ((sp + 0x3f8#64) ↦₆₄ w3) ∗
    ((sp + 0x400#64) ↦₆₄ w4) ∗
    ((sp + 0x408#64) ↦₆₄ w5) ⊢
    memRegion (sp + 0x3e0#64) 48 := by
  have hp : ((sp + 0x3e8#64) ↦₃₂ lo1) ∗ ((sp + 0x3ec#64) ↦₃₂ hi1) =
      ((sp + 0x3e8#64) ↦₆₄ (hi1 ++ lo1)) := pointsTo32_pair_sp3e8 sp lo1 hi1
  refine Entails.trans (entails_replace_sub (Entails.of_eq hp) (by sep_focus) rfl) ?_
  have hw := words6_entails_memRegion48 (sp + 0x3e0#64) w0 (hi1 ++ lo1) w2 w3 w4 w5
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hw
  exact Entails.trans (Entails.of_eq (by ac_rfl)) hw

theorem memRegion344_3e0_split_eq (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 344 =
      memRegion (sp + 0x3e0#64) 48 ∗ memRegion (sp + 0x410#64) 296 :=
  ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 48) (k := 296)
    (b' := sp + 0x410#64) rfl (by bv_omega) (by decide)
theorem pointsTo64_split_sp3e8 (sp w : BitVec 64) :
    ((sp + 0x3e8#64) ↦₆₄ w) =
      ((sp + 0x3e8#64) ↦₃₂ w.extractLsb' 0 32) ∗
      ((sp + 0x3ec#64) ↦₃₂ w.extractLsb' 32 32) := by
  have h : sp + 0x3ec#64 = (sp + 0x3e8#64) + 4#64 := by bv_omega
  rw [h, pointsTo64_split32]

/-! ## 2. Version-Mismatch Tail (`stageP3_err_ver_tail_ext_ok`, `+0x33b0 → s0.readReg64 .x30`) -/

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
