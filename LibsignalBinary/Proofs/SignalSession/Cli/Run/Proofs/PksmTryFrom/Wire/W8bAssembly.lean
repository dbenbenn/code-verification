/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.PrologueB -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTail
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCleanup
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.OkBridge
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ParseLemmas
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DropDecodeError -- proof-setup: allow-public-import

/-!
# `PreKeySignalMessage::try_from`: Top-Level Entry-to-Return Assembly (`preKeyTryFrom_ok_of_postLoop`)

Defines `pksmTryFromSpec` and `PreKeyPostLoopOkW`, and composes the early-error path
(`+0x000 → +0x504 → ret`), the protobuf decode loop (`+0x000 → +0x460`), the loop-error
cleanup (`+0x460 → +0x504 → ret`), and `PreKeyPostLoopOkW` (`+0x460 → ret`) into
`preKeyTryFrom_ok_of_postLoop`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

private abbrev SepWPp := @Wire.SepWPp
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre
private abbrev SepWPp.bind_frame_tryFrom := @Wire.SepWPp.bind_frame_tryFrom

/-! ## 1. All-Inputs Spec (`pksmTryFromSpec`) and `SepWPp` Post Combinators -/

theorem SepWPp.mono_post {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Q' Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp)
    (hQ : ∀ sf Pf, sf.pc = ret → sf.status = .Running → Q sf Pf → Q' sf Pf) :
    SepWPp prog ret s P Q' Qp := by
  intro R hm hL
  obtain ⟨sf, hst, ⟨hpc, hrun, Pf, hmf, hq, hv⟩ | hpan⟩ := h R hm hL
  · exact ⟨sf, hst, Or.inl ⟨hpc, hrun, Pf, hmf, hQ sf Pf hpc hrun hq, hv⟩⟩
  · exact ⟨sf, hst, Or.inr hpan⟩

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
