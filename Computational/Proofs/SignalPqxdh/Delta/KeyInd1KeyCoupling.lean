/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyDefs
import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyHopG0G3
import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyCorrAt
import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyStop
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyAtomic -- proof-setup: allow-public-import
import Computational.Proofs.SpecLemmas.Pqxdh.Security.HeadlineDelta
import Computational.Proofs.SignalPqxdh.Headline

/-!
# Costed `ReductionDsl` Assembly for One-Key PQXDH δ Key Indistinguishability

**Checked by Lean.** Packages the atomic `sig` and `shcr` costed reductions with a parameterized
`GapDhWithSign` reduction into `pqxdhKeyInd1KeyCostedFamily` and assembles `PqxdhKeyIndSecureδ`
from syntactic, semantic, `G0 -> G3`, and `G3` reduction obligations.
-/

public section

set_option autoImplicit false

open _root_.ReductionDsl
open SignalPqxdh
open SignalPqxdh.Costed (pqSigAndDdhIface)
open SignalPqxdh.Security
open Proofs.SignalPqxdh.Security
open Computational.Proofs.SignalPqxdh.AtomicLift

namespace Proofs.SignalPqxdh.Security.PqxdhDelta

/-- One-key `KeyIndCostedReductionFamily S` combining `sigKeyInd1KeyAtomicProg S` and
    `shcrKeyInd1KeyAtomicProg S` with a `CostedReduction` `GapDhWithSign` program `gdhProg`. -/
def pqxdhKeyInd1KeyCostedFamily (S : Setup)
    (gdhProg : QueryBudget → CostedReduction pqAtomicOps pqSigAndDdhIface (keyIndSpec S)
      (pqKeyIndCodec S) (.prod (PB 32) (PB 32)) .unit .bool (PB 32)) :
    KeyIndCostedReductionFamily S where
  sig  := sigKeyInd1KeyAtomicProg S
  shcr := shcrKeyInd1KeyAtomicProg S
  gdh  := gdhProg

/-- `PqxdhKeyIndReductionBoundStaticδ` for `(pqxdhKeyInd1KeyCostedFamily S gdhProg).eval` from a
    static `G3` bound on `(pqxdhKeyInd1KeyCostedFamily S gdhProg).eval.gdh`. -/
theorem pqxdhKeyInd1KeySecurityStaticδ_of_gdh (S : Setup)
    (gdhProg : QueryBudget → CostedReduction pqAtomicOps pqSigAndDdhIface (keyIndSpec S)
      (pqKeyIndCodec S) (.prod (PB 32) (PB 32)) .unit .bool (PB 32))
    (hG3 : KI1KeyG3BoundStmt S (pqxdhKeyInd1KeyCostedFamily S gdhProg).eval.gdh) :
    PqxdhKeyIndReductionBoundStaticδ S (pqxdhKeyInd1KeyCostedFamily S gdhProg).eval := by
  intro P hP δ hδ b A
  have h := pqxdh_1key_key_ind_withδ_of_hops S
    (pqxdhKeyInd1KeyCostedFamily S gdhProg).eval.gdh
    (ki1KeyHopG0G3 S) hG3 P hP δ hδ b A
  have hSig :
      GapSigEufCma P P.isValidDhTriple ((pqxdhKeyInd1KeyCostedFamily S gdhProg).eval.sig b A) =
        GapSigEufCma P P.isValidDhTriple (sigReductionKeyInd1Key S b A) :=
    GapSigEufCma_sigKeyInd1KeyAtomicAdv P P.isValidDhTriple S b A
  have hShcr :
      KemShCr P ((pqxdhKeyInd1KeyCostedFamily S gdhProg).eval.shcr b A) =
        KemShCr P (shcrReductionKeyInd1Key S b A) :=
    KemShCr_shcrKeyInd1KeyAtomicAdv P S b A
  rw [← hSig, ← hShcr] at h
  exact h

/-- Assembles `PqxdhKeyIndSecureδ S` from an activity-bounded costed reduction family and its
    syntactic, semantic, `G0 -> G3`, and `G3` obligations. -/
theorem pqxdhKeyIndSecureδ_of_activeFamily (S : Setup)
    (R : KeyIndCostedReductionFamily S)
    (hCost : KeyIndCostedReductionBounds S R)
    (hQuery : KeyIndReductionQueryBounds S R.eval)
    (hHop : KI1KeyActiveHopG0G3Stmt S R.eval.sig R.eval.shcr)
    (hG3 : KI1KeyActiveG3BoundStmt S R.eval.gdh) :
    PqxdhKeyIndSecureδ S :=
  ⟨R, hCost, hQuery, pqxdh_1key_key_ind_active_withδ_of_hops S R.eval.sig R.eval.shcr R.eval.gdh hHop hG3⟩

end Proofs.SignalPqxdh.Security.PqxdhDelta
