/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.PrevBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3a2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropSessionStructure3
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderStore.SessionRecordCallees
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSpe2Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenVerNeBlocks
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Consts
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.ErrK2
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers

/-!
# Version-Mismatch Error Tail (`+0x2cfc → s0.readReg64 .x30`)

Proves `over_ver_ne_tail_2cfc_cli_4k_ok` and `over_ver_ne_tail_2cfc_cli_ok` on
`tripleRatchetProgAtExt` when `errs` holds two `UnrecognizedMessageVersion` entries
(`errs.len = 2#64`, `errs.cap = 4#64`) and `previous_sessions` holds one archived session: allocates
the 17-byte `"decryption failed"` message, drops both error entries and `current_session`, and runs
the K2 `previous_sessions` epilogue to return.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

private theorem cond_eq_adds64_of_ne_neg1_tail {w : BitVec 64} (h : w ≠ 0xffffffffffffffff#64) :
    ConditionHolds CondCode.EQ (addsPState64 w 1#64) = false := by
  rw [conditionHolds_eq_addsPState64, beq_eq_false_iff_ne]; revert h; bv_omega

private theorem errs48_48_96_join_tail (errsPtr : BitVec 64) :
    memRegion errsPtr 48 ∗ memRegion (errsPtr + 0x30#64) 48 ∗ memRegion (errsPtr + 0x60#64) 96 =
      memRegion errsPtr 192 := by
  have h1 :
      memRegion (errsPtr + 0x30#64) 48 ∗ memRegion (errsPtr + 0x60#64) 96 =
        memRegion (errsPtr + 0x30#64) 144 := by
    rw [ProofLib.memRegion_split' (b := errsPtr + 0x30#64) (n := 48) (k := 96)
          (b' := errsPtr + 0x60#64) rfl (by bv_omega) (by decide)]
  rw [h1, ProofLib.memRegion_split' (b := errsPtr) (n := 48) (k := 144)
        (b' := errsPtr + 0x30#64) rfl (by bv_omega) (by decide)]

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe
