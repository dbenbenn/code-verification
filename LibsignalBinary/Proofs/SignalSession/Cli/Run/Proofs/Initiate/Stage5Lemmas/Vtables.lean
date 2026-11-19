/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityVtables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.Session -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentitySpec
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionSpec
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Stage 5 Vtable and File-System Frame Helpers

Layout-independent `.data.rel.ro` vtable dispatch and size/alignment lemmas for
`get_local_registration_id`, `save_identity`, and `store_session`, together with
`subroutine_ok_keepsFiles`.
-/

public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas

open Arm64 ProofLib ProofLib.ProgramReflection open CryptoVerification.RustHeap
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

set_option maxRecDepth 200000

/-- Spec wrapper extending `spec.post` with `sf.fs.files = s0.fs.files`. -/
@[expose] def keepsFiles {α : Type} (spec : Spec α) : Spec α :=
  { spec with post := fun x s0 sf => ⌜sf.fs.files = s0.fs.files⌝ ∗ spec.post x s0 sf }

/-- Under `TraceFsSound prog`, any `subroutine_ok` contract that guarantees `sf.trace = s0.trace`
on normal return automatically preserves `s.fs.files`. -/
theorem subroutine_ok_keepsFiles {α : Type} {prog : Program} {fn : BitVec 64} {spec : Spec α}
    (hFs : TraceFsSound prog) (hok : subroutine_ok prog fn spec)
    (htr : ∀ x s0 sf R, (sf.mem ⊨ spec.post x s0 sf ∗ R) → sf.trace = s0.trace) :
    subroutine_ok prog fn (keepsFiles spec) := by
  have hw := subroutine_ok_withStepsPost hok
  refine subroutine_ok_mono hw (fun _ _ _ h => h) ?_ (fun _ _ _ _ h => h)
    (fun _ _ _ _ _ h => h) (fun _ _ _ _ h => h)
  intro x R s0 sf hpost
  change sf.mem ⊨ (⌜Steps prog s0 sf⌝ ∗ spec.post x s0 sf) ∗ R at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  obtain ⟨hst, hpost'⟩ := hpost
  have heq : sf.trace = s0.trace := htr x s0 sf R hpost'
  have hfiles : sf.fs.files = s0.fs.files :=
    hFs.files_eq hst (evs := []) (by rw [heq, List.append_nil]) NoFsEv.nil
  change sf.mem ⊨ (⌜sf.fs.files = s0.fs.files⌝ ∗ spec.post x s0 sf) ∗ R
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hfiles, hpost'⟩

/-! ## Raw `.data.rel.ro` Size & Alignment Words -/

private def dummyPeer : AddrGhost :=
  { name := { cap := 0, ptr := 0, bytes := [] }
    device := 1 }

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas
