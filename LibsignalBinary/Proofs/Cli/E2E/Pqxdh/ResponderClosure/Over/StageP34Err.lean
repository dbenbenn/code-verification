/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4Defs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.HeapDefs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4ErrUnwind
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4StoreSession
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP34ErrStepsA
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP34Defs
import LibsignalBinary.Proofs.CodeLayout

/-!
# Stage P4 `store_session` `Ok` Epilogue on 1-Element `previous_sessions`

Proves `stageP4_storeSession_ok_tail_prev1_vregs_p4` and `stageP4_storeSession_ok_tail_prev1_vregs`
(`+0x444 → s0.readReg64 .x30`), dropping `SessionStructure` and the 1-element `previous_sessions`
vector into `memRegion (coroPtr + 0xe0#64) 368`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

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
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.OverP34

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Stage P4 `store_session` `Ok` Epilogue (`+0x444 → s0.readReg64 .x30`) -/

private theorem p4_fold_sret_ok_prev1 {A : RustAlloc} (outPtr ptCap ptPtr w_24 : BitVec 64)
    (u_384 w_2c : BitVec 32) (pt : List (BitVec 8))
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64) :
    (outPtr ↦₆₄ 0xfffffffffffffffe#64) ∗
    ((outPtr + 0x8#64) ↦₃₂ ptCap.extractLsb' 0 32) ∗
    ((outPtr + 0xc#64) ↦₆₄ (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)) ∗
    ((outPtr + 0x14#64) ↦₆₄
      ((BitVec.ofNat 64 pt.length).extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)) ∗
    ((outPtr + 0x1c#64) ↦₆₄ (u_384 ++ (BitVec.ofNat 64 pt.length).extractLsb' 32 32)) ∗
    ((outPtr + 0x24#64) ↦₆₄ w_24) ∗
    ((outPtr + 0x2c#64) ↦₃₂ w_2c) ∗
    (ptPtr ↦ₛ pt) ∗
    (if ptCap = 0#64 then emp
     else A.live ptPtr ptCap.toNat 1 ∗
       memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ⊢
    vecResultAt A outPtr (.ok pt) := by
  rw [pointsTo32_pair_out1c']
  have hreplace :
      ∀ {A B R P Q : SepProp},
        (A ⊢ B) → P = A ∗ R → B ∗ R = Q → (P ⊢ Q) := by
    intro A B R P Q hab hp hq
    rw [hp, ← hq]
    exact sepConj_mono_left hab
  exact Entails.trans
    (hreplace (memRegion16_out20_fold' outPtr w_24 u_384 w_2c) (by sep_focus) (by ac_rfl))
    (p4_fold_decResultAt_ok A outPtr ptCap ptPtr pt hpt_le hcap_lt hptr_nz)

private theorem sp370_words_entails_memRegion36_prev1 (sp v0 v1 v2 v3 : BitVec 64) (v4 : BitVec 32) :
    ((sp + 0x370#64) ↦₆₄ v0) ∗
    ((sp + 0x378#64) ↦₆₄ v1) ∗
    ((sp + 0x380#64) ↦₆₄ v2) ∗
    ((sp + 0x388#64) ↦₆₄ v3) ∗
    ((sp + 0x390#64) ↦₃₂ v4) ⊢
    memRegion (sp + 0x370#64) 36 := by
  have h := stagingCellsAt_entails_memRegion36 (sp + 0x370#64) v0 v1 v2 v3 v4
  unfold stagingCellsAt at h
  simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using h

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
