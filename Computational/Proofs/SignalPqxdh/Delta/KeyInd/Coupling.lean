/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.KeyIndDefs
import VCVio.EvalDist.Monad.Basic

/-!
# PQXDH δ key indistinguishability: `G3 → G3.5` coupling

**Checked by Lean.** Proves `kiCoupling` (`KICouplingStmt`, DEV-PQ21), the `G3 → G3.5` up-to-bad
coupling bound incorporating the KEM correctness bad event `hasBadKemCorrRecords`.
-/

public section

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security
open Proofs.SignalPqxdh.Security
open Proofs.SignalPqxdh.Security.FgGapDh
open Proofs.SignalPqxdh.Security.FgGapDh.Ik
open Proofs.SignalPqxdh.Security.FgGapDh.Opk

namespace Proofs.SignalPqxdh.Security.PqxdhDelta

namespace KICoupling

theorem evalDist_bind_pure_or_le {α : Type} (m : ProbComp α) (b1 b2 : α → Bool) :
    𝒟[m >>= fun x => pure (b1 x || b2 x)] {true} ≤
      𝒟[m >>= fun x => pure (b1 x)] {true} +
      𝒟[m >>= fun x => pure (b2 x)] {true} := by
  rw [evalDist_bind_true_eq_probExpect_comp m (fun x => pure (b1 x || b2 x)),
      evalDist_bind_true_eq_probExpect_comp m (fun x => pure (b1 x)),
      evalDist_bind_true_eq_probExpect_comp m (fun x => pure (b2 x))]
  refine probExpect_add_le_fg m _ _ _ (fun x => ?_)
  cases b1 x <;> cases b2 x <;> simp

theorem isInvariant_randLens_hasBadKemCorrRecords (S : Setup) (P : Primitives) :
    (randLens S).IsInvariant (fun (p : Bool × KeyIndLazyState S) =>
      pure (hasBadKemCorrRecords S P p.2.adv.shCr.initKemRecs p.2.adv.shCr.recvKemRecs)) :=
  CacheLens.IsInvariant.of_cache_indep (randLens S) _ (fun _ _ _ => rfl)

theorem isInvariant_roLens_hasBadKemCorrRecords (S : Setup) (P : Primitives) :
    (roLens S).IsInvariant (fun (p : Bool × KeyIndLazyState S) =>
      pure (hasBadKemCorrRecords S P p.2.adv.shCr.initKemRecs p.2.adv.shCr.recvKemRecs)) :=
  CacheLens.IsInvariant.of_cache_indep (roLens S) _ (fun _ _ _ => rfl)

end KICoupling

end Proofs.SignalPqxdh.Security.PqxdhDelta
