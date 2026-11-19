/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticUnackPrekeyOmitted.Defs

/-!
# Refutation of Prefix Collisions for `synthetic-unack-prekey-omitted-cli`

Proves `not_collisionAfterExplainedPrefix_uo` (`0 sorry`) for parameterized `uoEvents out1`
(`[.run evInit, .run (evSend out1)]`) as well as direct corollaries for the recorded witness trace
(`UnackPrekeyOmittedCli.trace`) and the `(compI0, compHooks0)` carrier trace (`uoCarrierTrace`):
- Call 0 (`init` Alice): refuted via `not_nextEventCollidesClassical_init rfl`.
- Call 1 (`send` Alice `"hello bob"`): `[.run evInit]` and `(evSend out1).input = CompRX0SS38.ptB = ptMsg35`
  match `Cheval26SmallSubgroupHighBitComp443`, so `not_nextEventCollidesClassical_send`,
  `not_readCollisionCliClassical_of_no_recv`, `CliCoinSplit.init_exit0_cut_eq`, and `ptDead35_self`
  refute any send plaintext memo collision independently of `out1`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticUnackPrekeyOmitted.NoSendCollision

open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent RunEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.Composed.Refinement.Cli
open Symbolic.BugInjection
open Symbolic.BugInjection.Proofs.Common443
open Symbolic.BugInjection.Proofs.Common443.CliCoinSplitClose
open Symbolic.BugInjection.Proofs.Common443.CliEventBridge
open Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443
open Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.CliBridge (ptB_eq_ptMsg35)
open Symbolic.BugInjection.Proofs.SyntheticUnackPrekeyOmitted.Defs

attribute [local irreducible] Symbolic.BugInjection.hexBytes

/-- Call 1 with arbitrary `exit` (supporting any stdout or exit status). -/
def evSendWithExit (exit1 : Option (Nat × HwBytes)) : RunEvent :=
  { party := "alice"
    cmd := .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩
    input := CompRX0SS38.ptB
    coins := CompRX0SS38.cB
    exit := exit1 }

theorem not_collisionAfterExplainedPrefix_uo_of_exit
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    (exit1 : Option (Nat × HwBytes))
    (hwf : ProtocolSetupWF r) :
    ¬ CollisionAfterExplainedPrefix compI0 r S [.run evInit, .run (evSendWithExit exit1)] := by
  have hbf : Symbolic.Proofs.Swarm.UA.ClassicalBridge.BreakFree
      [.run evInit, .run (evSendWithExit exit1)] :=
    breakFree_cons_run _ (breakFree_cons_run _ Symbolic.Proofs.Swarm.UA.ClassicalBridge.breakFree_nil)
  refine not_collisionAfterExplainedPrefix_of_splits hbf ?_
  intro evs₁ ev evs₂ g ss vis hevs hex
  rcases list_eq_two_splits hevs with ⟨rfl, hev, _⟩ | ⟨rfl, hev, _⟩
  · injection hev with hev'; subst hev'
    exact not_nextEventCollidesClassical_init rfl
  · injection hev with hev'; subst hev'
    have hnrc₁ : ¬ ReadCollisionCliClassical compI0 r S g ss [.run evInit] := by
      refine not_readCollisionCliClassical_of_no_recv ?_
      intro ev' out' hev' ⟨p', hcmd'⟩ _
      simp only [List.mem_singleton] at hev'
      injection hev' with hev''; subst hev''; cases hcmd'
    refine not_nextEventCollidesClassical_send hwf schedFits_evInit hex hnrc₁ rfl ?_
    intro τ ms hex_cli _ hnb hbme hmcol
    obtain ⟨hτ, hex_hw⟩ := CliCoinSplit.init_exit0_cut_eq (by decide) cliCoins0_length hex_cli
    subst hτ
    dsimp only [evInit, evSendWithExit] at hex_hw hbme
    rw [init_draws_cliCoins0_eq_hb, trace_take_35_eq] at hex_hw
    have hem : EventMatchesEntry compI0 r S g (.pt ptMsg35) (ptEntryOfNextEncrypt r ms) :=
      ⟨rfl, by simpa [EventMatchesEntry, BytesMatchEntry, ptEntryAt, ptEntryOfNextEncrypt,
        ptB_eq_ptMsg35, eventBytes] using hbme⟩
    have hmcol' : MemoCollisionOn compI0 r S g (fun u => u.AttackerKnows (runTraceMoves r ms))
        (runTraceMoves r ms) (runVis r ms)
        (ptEntryOfNextEncrypt r ms).terms (ptEntryOfNextEncrypt r ms).terms := by
      simpa [MemoCollisionOn, ptEntryAt, ptEntryOfNextEncrypt] using hmcol
    exact ptDead35_self hwf hnb hex_hw hem hmcol'

theorem not_collisionAfterExplainedPrefix_uo
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    (out1 : HwBytes)
    (hwf : ProtocolSetupWF r) :
    ¬ CollisionAfterExplainedPrefix compI0 r S (uoEvents out1) :=
  not_collisionAfterExplainedPrefix_uo_of_exit (some (0, out1)) hwf

theorem not_collisionAfterExplainedPrefix_uo_trace
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    (hwf : ProtocolSetupWF r) :
    ¬ CollisionAfterExplainedPrefix compI0 r S
        Symbolic.BugInjection.Synthetic.Witnesses.UnackPrekeyOmittedCli.trace :=
  uoEvents_eq ▸ not_collisionAfterExplainedPrefix_uo uoSendOut hwf

theorem not_collisionAfterExplainedPrefix_uo_carrier
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    (hwf : ProtocolSetupWF r) :
    ¬ CollisionAfterExplainedPrefix compI0 r S uoCarrierTrace :=
  uoEvents_carrier_eq ▸ not_collisionAfterExplainedPrefix_uo uoCarrierSendOut hwf

end Symbolic.BugInjection.Proofs.SyntheticUnackPrekeyOmitted.NoSendCollision
