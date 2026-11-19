/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticKeepOpk.DefsI0
import Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.WitnessParse
import Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanTrace
import Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanGhost
import Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanPrefix
import Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.MemoCheck
import Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollision
import Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollisionAux

/-!
# Receive Collision Absence on All `.recv` Events of `KeepOpkCli`

Proves `not_nextEventCollides_recv` across every `.recv` split of `KeepOpkCli.trace` (`ev 2` and
`ev 5`) by combining:
- `WitnessParse.recv_split_cases` to split `(evs₁, ev)` into `(trace0.take 2, ev 2)` and
  `(trace0.take 5, ev 5)`,
- `not_knownBaseKeyOn_of_no_recv` at `m = 2` and `CleanPrefix.not_knownBaseKeyOn_5` at `m = 5`,
- `CleanPrefix.extract_clean_2` / `CleanPrefix.extract_clean_5` to produce a clean prefix witness
  `(gClean r cls, ssClean cls m, visClean r cls m)` with `cleanPreKeyRep cls m`, and
- `MemoCheck.not_bobStartCollides_2` / `MemoCheck.not_bobStartCollides_5` to rule out
  `BobSessionStartCollidesOrImplicitRejectsOn`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision

open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.PQXDH.Refinement (wirePrekeyTag)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry Explains parsePreKeyWire)
open DY.Libsignal.Composed.Refinement.Cli (NextEventCollides)
open Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollision
  (not_nextEventCollides_accepted_prekey not_preKeyStartCollidesOrRejects_of_clean)
open Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollisionAux (not_knownBaseKeyOn_of_no_recv)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.DefsI0
  (keepOpkI0 keepOpkHooks0 keepOpkCompFitsPinned)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.WitnessParse
  (trace0 ev2InF ev5InF ev2In_eq ev5In_eq ev2_facts ev5_facts p2 p5 parse_ev2 parse_ev5
   noRecvEvent_take2 recv_split_cases)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanTrace
  (not_readCollisionCli_ssClean)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanGhost
  (gClean not_kyberMismatch_keepOpkI0)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanPrefix
  (not_knownBaseKeyOn_5 extract_clean_2 extract_clean_5)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.MemoCheck
  (not_bobStartCollides_2 not_bobStartCollides_5)

attribute [local irreducible] WitnessParse.ev

theorem not_nextEventCollides_recv
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ss : List Step) (vis : List VisEntry)
    (evs₁ : List CliEvent) (ev : RunEvent) (evs₂ : List CliEvent)
    (hfit : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r)
    (_hnfe : ∀ g' ss' vis',
      ¬ Explains keepOpkI0 r S g' ss' vis'
          Symbolic.BugInjection.Synthetic.Witnesses.KeepOpkCli.trace)
    (hsplit : Symbolic.BugInjection.Synthetic.Witnesses.KeepOpkCli.trace = evs₁ ++ .run ev :: evs₂)
    (hex : Explains keepOpkI0 r S g ss vis evs₁)
    (hrecv : ∃ peer, ev.cmd = .recv peer) :
    ¬ NextEventCollides keepOpkI0 r S g ss vis evs₁ ev := by
  rcases recv_split_cases hsplit hrecv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hin2 : (WitnessParse.ev 2).input = wirePrekeyTag :: ev2InF.tail := by
      rw [ev2In_eq]; decide +kernel
    have hp2 : parsePreKeyWire (wirePrekeyTag :: ev2InF.tail) = some p2 := by
      rw [← hin2]; exact parse_ev2
    obtain ⟨cls, hv, hex_c, hmem_c, _⟩ := extract_clean_2 hfit hex
    rw [hin2] at hmem_c
    exact not_nextEventCollides_accepted_prekey ev2_facts.2.1 hin2 hp2
      (not_knownBaseKeyOn_of_no_recv hfit.1.1.1 hex noRecvEvent_take2)
      (not_preKeyStartCollidesOrRejects_of_clean
        (not_kyberMismatch_keepOpkI0 r p2) hex_c
        (not_readCollisionCli_ssClean keepOpkI0 r S (gClean r cls) cls 2 (trace0.take 2))
        hmem_c (not_bobStartCollides_2 hfit hv hex_c))
  · have hin5 : (WitnessParse.ev 5).input = wirePrekeyTag :: ev5InF.tail := by
      rw [ev5In_eq]; decide +kernel
    have hp5 : parsePreKeyWire (wirePrekeyTag :: ev5InF.tail) = some p5 := by
      rw [← hin5]; exact parse_ev5
    obtain ⟨cls, hv, hex_c, hmem_c, _, _⟩ := extract_clean_5 hfit hex
    rw [hin5] at hmem_c
    exact not_nextEventCollides_accepted_prekey ev5_facts.2.1 hin5 hp5
      (not_knownBaseKeyOn_5 hfit hex)
      (not_preKeyStartCollidesOrRejects_of_clean
        (not_kyberMismatch_keepOpkI0 r p5) hex_c
        (not_readCollisionCli_ssClean keepOpkI0 r S (gClean r cls) cls 5 (trace0.take 5))
        hmem_c (not_bobStartCollides_5 hfit hv hex_c))

end Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision
