/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Defs
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropSessionStructure3
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Qpan
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderStore.SessionRecordCallees
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP2a
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsC
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsE
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2Tail
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrA
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub1V4
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V3Steps
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1Common -- shake: keep

/-!
# Stage P2 Over-Path Substage P2.1 and Outer `v3` Reject Path

Re-exports `stageP2_over_sub1_v4_kits` and proves the outer `v3` (`msgVer = 3#8`) reject path
(`+0x0868 → s0.readReg64 .x30`), which runs `promote_matching_session` returning `Ok(false)`,
allocates `"X3DH no longer supported"`, drops the `process_prekey_impl` state and `SessionRecord`,
and writes `.error (.protocol (.invalidMessage .preKey .badCiphertext))` to `outPtr`.
-/

public section

set_option autoImplicit false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (prevSessionsEmptyAt)

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  decryptPrekeySavedRegsAt

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

private theorem p2_strToOwnedStack_le_overPure :
    Matched.strToOwnedLocal2Stack ≤ stageP2OverPureAndErrStack := by
  decide

private theorem p2_cells48_le_overPure : 48 ≤ stageP2OverPureAndErrStack := by
  decide

private theorem p2_stackAt_48_cells6 (sp : BitVec 64) :
    stackAt sp 48 = cells (sp - 48#64) 6 := by
  change memRegion (sp - 48#64) 48 = _
  rw [show (48 : Nat) = 8 * 6 by decide, ProofLib.memRegion_cells (sp - 48#64) 6 (by decide)]

private theorem p2_sessionAt_entails_state (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8))) :
    sessionStateReprAt A ss G sess ⊢ sessionStateAt A ss G sess.state := by
  unfold sessionStateReprAt
  exact Entails.pure_left fun _ => Entails.refl _

/-! ## Outer `v3` Reject Path (`+0x0868 → s0.readReg64 .x30`) -/

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
