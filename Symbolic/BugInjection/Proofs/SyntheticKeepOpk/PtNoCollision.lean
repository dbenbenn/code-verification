/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticKeepOpk.DefsI0
import Symbolic.BugInjection.Proofs.SyntheticKeepOpk.NoFullExplains.PtSend
import Symbolic.Proofs.Tests.CliNonvacuity.WitnessBase

/-!
# Plaintext Collision Absence on All `.send` Events of `KeepOpkCli`

Proves `not_nextEventCollides_send`: no `.send` run event in `KeepOpkCli.trace`
can satisfy `NextEventCollides` after an explained prefix under `keepOpkCompFitsPinned`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticKeepOpk.PtNoCollision

open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry Explains)
open DY.Libsignal.Composed.Refinement.Cli (NextEventCollides)
open Symbolic.Proofs.Tests.CliNonvacuity.WitnessBase (le_length_aesCbcEncrypt)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.DefsI0
  (keepOpkI0 keepOpkHooks0 keepOpkCompFitsPinned
   keepOpkAesBlock keepOpkKyberEncaps keepOpkKyberEncaps_length)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.NoFullExplains.PtSend
  (not_nextEventCollides_send_generic)

theorem not_nextEventCollides_send
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ss : List Step) (vis : List VisEntry)
    (evs₁ : List CliEvent) (ev : RunEvent) (evs₂ : List CliEvent)
    (hfit : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r)
    (hsplit : Symbolic.BugInjection.Synthetic.Witnesses.KeepOpkCli.trace = evs₁ ++ .run ev :: evs₂)
    (hex : Explains keepOpkI0 r S g ss vis evs₁)
    (hsend : ∃ peer, ev.cmd = .send peer) :
    ¬ NextEventCollides keepOpkI0 r S g ss vis evs₁ ev := by
  refine not_nextEventCollides_send_generic keepOpkI0 r S g ss vis evs₁ ev evs₂
    hfit.1.1.1 hfit.2.1.1 ?_ ?_ hsplit hex hsend
  · intro text k iv
    change 16 ≤ (CryptoGames.LibsignalSession.aesCbcEncrypt keepOpkAesBlock
      (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) text).length
    exact le_length_aesCbcEncrypt keepOpkAesBlock
      (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) text
  · intro _ rand
    change (keepOpkKyberEncaps rand).length = 1600
    exact keepOpkKyberEncaps_length rand

end Symbolic.BugInjection.Proofs.SyntheticKeepOpk.PtNoCollision
