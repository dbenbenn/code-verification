/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticKeepOpk.DefsI0
import Symbolic.BugInjection.Proofs.SyntheticKeepOpk.NoFullExplains.Trace

/-!
# Full-Trace Explanation Disproof for `KeepOpkCli` (`NoFullExplains.lean`)

Proves `not_explains_full`: no symbolic execution `(ss, vis)` under `(S, g)` can explain all 6
CLI calls of `KeepOpkCli.trace` under `keepOpkCompFitsPinned`.

In Calls `0..2`, Bob's session start on `ev 2` consumes his unique one-time prekey (`opkId = 3`)
and logs `PQXDHEvent.OPKUsed`, setting `PQXDH.opkUsedB = true`. In Calls `3..5`, Alice initiates a
second session with a distinct ephemeral base key (`p₂.baseKey.take 33 ≠ p₅.baseKey.take 33`)
reusing the same OPK; `PathFaithfulAt` forces `Step.bobStart` on `ev 5`, which is blocked by
single-use OPK enforcement (`!PQXDH.opkUsedB`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticKeepOpk.NoFullExplains

open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry Explains)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.DefsI0
  (keepOpkI0 keepOpkHooks0 keepOpkCompFitsPinned)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.NoFullExplains.Trace
  (not_explains_keepOpk_generic)

theorem not_explains_full
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ss : List Step) (vis : List VisEntry)
    (hfit : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r) :
    ¬ Explains keepOpkI0 r S g ss vis
        Symbolic.BugInjection.Synthetic.Witnesses.KeepOpkCli.trace := by
  let _ := hfit
  exact not_explains_keepOpk_generic r S g ss vis

end Symbolic.BugInjection.Proofs.SyntheticKeepOpk.NoFullExplains
