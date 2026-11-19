/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.Common -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsSites
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3Helpers
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanup
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.SliceHelpers
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Defs
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton

/-!
# Callee `SepWPp` Wrappers for Arm `R1b`

Typed `SepWPp` call wrappers isolating allocator, `memcpy`, `Dir::path`, `read_file`, and
`bundleRead` invocations in Arm `R1b`.
-/

theorem r1b_allocFailedIn_sub {s0 s1 s2 : State}
    (hp : s0.trace <+: s1.trace) (ha : allocFailedIn s1 s2) :
    allocFailedIn s0 s2 := by
  rcases hp with ⟨k, hk⟩
  dsimp only [allocFailedIn] at ha ⊢
  rw [← hk, List.length_append, ← List.drop_drop] at ha
  exact List.mem_of_mem_drop ha

end CryptoVerification.SignalSession.Cli.RunCompose
