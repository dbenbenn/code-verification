/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepBase
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementWeak.Defs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.RecvCoins
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliver
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliverInject
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementWeak.Honest

/-!
# Weak refinement: the inject step

Adapts the `inject` step coupling lemmas of `Refinement/StepDeliverInject.lean` to `SimInvW`
and `SpqrWLocal`, culminating in `closeByState_inject_stepW`.
-/

public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC] {ℓ : ℕ}

namespace WP2A.I3

theorem accept_epoch_eq_of_le {St Msg C : Type} (s : SM.GameState St Msg C)
    (Q : Party) (st' : St) (pos : SM.Pos) (hle : pos.epoch ≤ s.epoch Q) :
    (s.accept Q st' pos).epoch = s.epoch := by
  funext R
  unfold SM.GameState.accept SM.GameState.delete
  dsimp only
  by_cases hR : R = Q
  · subst hR; simp [Function.update_self, Nat.max_eq_left hle]
  · simp [Function.update_of_ne hR]

end WP2A.I3

namespace WP2A.I8

theorem chainSync_with_key {g : GhostChain} {v : RatchetReceiverState (BitVec 256) (BitVec 256)}
    (k : Option PublicKey) (h : ChainSync g v) :
    ChainSync { g with key := k } v := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end WP2A.I8

end CryptoGames.LibsignalSM.Proofs.Refinement
