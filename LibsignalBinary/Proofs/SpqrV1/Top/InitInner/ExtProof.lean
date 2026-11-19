/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.ExtHelpers
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbOuter
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SpqrV1.Auth.New -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.Defs
import LibsignalBinary.Proofs.CodeLayout

/-!
# Extended-Stack (`*Ext`) Verification of `spqr::init_inner`

Proves `InitInnerBaseOkExt` and `InitInnerOkXExt` (`initInnerStackExt = 18912`B) from
`AllocContracts` or 4K extern hooks together with `AuthNewOkExt`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Top.InitInner

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.DecoderPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit' sessionMemcpySpec libcMemcpySpec

private theorem cells_1032_3_expose_ext (sp : BitVec 64) (Rest : SepProp) :
    cells (sp - 1032#64) 3 ∗ Rest ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        ((sp - 1032#64) ↦₆₄ w0) ∗ ((sp - 1024#64) ↦₆₄ w1) ∗ ((sp - 1016#64) ↦₆₄ w2) ∗ Rest := by
  cells_unfold; simp only [sepExists_sepConj_left, arm64_norm]
  apply Entails.sepExists_elim; intro w0; apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w2
  refine Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2 ?_))
  exact Entails.of_eq (by ac_rfl)

private theorem calleeSaved_chain_hi_ext {s0 s sf : State}
    (hcs_hi : s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcs : CalleeSavedPreserved s sf) :
    sf.readReg64 .x22 = s0.readReg64 .x22 ∧ sf.readReg64 .x23 = s0.readReg64 .x23 ∧
    sf.readReg64 .x24 = s0.readReg64 .x24 ∧ sf.readReg64 .x25 = s0.readReg64 .x25 ∧
    sf.readReg64 .x26 = s0.readReg64 .x26 ∧ sf.readReg64 .x27 = s0.readReg64 .x27 ∧
    calleeSavedVRegs sf = calleeSavedVRegs s0 := by
  dsimp only [CalleeSavedPreserved] at hcs
  rcases hcs_hi with ⟨h22, h23, h24, h25, h26, h27, hvregs⟩
  exact ⟨by simp only [hcs, h22], by simp only [hcs, h23], by simp only [hcs, h24],
         by simp only [hcs, h25], by simp only [hcs, h26], by simp only [hcs, h27],
         by simp only [hcs, hvregs]⟩

private theorem calleeSaved_x29_ext {s sf : State} {v : BitVec 64}
    (h : s.readReg64 .x29 = v) (hcs : CalleeSavedPreserved s sf) : sf.readReg64 .x29 = v := by
  dsimp only [CalleeSavedPreserved] at hcs; simp only [hcs, h]

private theorem calleeSaved_x19_ext {s sf : State} {v : BitVec 64}
    (h : s.readReg64 .x19 = v) (hcs : CalleeSavedPreserved s sf) : sf.readReg64 .x19 = v := by
  dsimp only [CalleeSavedPreserved] at hcs; simp only [hcs, h]

end CryptoVerification.SpqrV1.Top.InitInner
