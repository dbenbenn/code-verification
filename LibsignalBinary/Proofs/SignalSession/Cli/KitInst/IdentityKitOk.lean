/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentitySpec
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Skeleton -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
import LibsignalBinary.Proofs.SignalSession.Cli.Specs
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommon
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityFutDropExt
import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.Identity
import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsBinary
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.E2E.Bin.Record
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# CLI `IdentityStoreKitOkIE` Assembly

Assembles `StoreKit.Identity.IdentityStoreKitOkIE` for `cliIdentityStoreSpec` from the
`IdentityFiles` shim, poll, and `futDrop` contracts over an arbitrary allocator, `ReadRule`,
initial file table, and external-hook map.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.KitInst.IdKit

open Arm64 ProofLib
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli.MainHops

/-! ## Stack bounds -/

abbrev trustShimNeed : Nat := 0x30 + extHookStack

abbrev saveShimNeed : Nat := 0x30 + extHookStack

abbrev growOneDirNeed : Nat := 0x40 + CryptoVerification.LibsignalTripleRatchet.finishGrowStackX

abbrev dirPutStrNeed : Nat := 0x50 + max growOneDirNeed extHookStack

abbrev trustPollNeed (readStk : Nat) : Nat :=
  0xc0 + max (max (RunSkeleton.RunBudgets.dirGetNeed ⟨readStk⟩) 0x60) (max 64 extHookStack)

abbrev savePollNeed (readStk : Nat) : Nat :=
  0xd0 + max (max (max (RunSkeleton.RunBudgets.dirGetNeed ⟨readStk⟩) dirPutStrNeed) (max 0x60 64))
    (max publicKeySerializeStackX extHookStack)

private theorem panic_absorb_own {φ : Prop} {own R : SepProp} {m : Memory}
    (h : m ⊨ (⌜φ⌝ ∗ anyHeap) ∗ (own ∗ R)) :
    m ⊨ (⌜φ⌝ ∗ anyHeap) ∗ R := by
  have h1 : m ⊨ ⌜φ⌝ ∗ ((anyHeap ∗ own) ∗ R) :=
    Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) h
  rw [satisfies_pure_sepConj] at h1
  have h2 : m ⊨ ⌜φ⌝ ∗ (anyHeap ∗ R) := by
    rw [satisfies_pure_sepConj]
    exact ⟨h1.1, Satisfies.mono (sepConj_mono_left (entails_anyHeap (anyHeap ∗ own))) h1.2⟩
  exact Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) h2

/-! ## Kit assembly -/

private theorem trustPoll_hstk_ext32 {readStk s2 : Nat} (hs2 : trustPollNeed readStk ≤ s2) :
    0xc0 + max (max (RunSkeleton.RunBudgets.dirGetNeed ⟨readStk⟩) 0x60)
      Getters.publicKeyEqStackExt ≤ s2 := by
  dsimp only [trustPollNeed, extHookStack, Getters.publicKeyEqStackExt,
    RunSkeleton.RunBudgets.dirGetNeed] at hs2 ⊢
  omega

private theorem savePoll_hstk_ext32 {readStk s4 : Nat} (hs4 : savePollNeed readStk ≤ s4) :
    0xd0 + max (max (max (RunSkeleton.RunBudgets.dirGetNeed ⟨readStk⟩) dirPutStrNeed) 0x60)
      (max publicKeySerializeStackX Getters.publicKeyEqStackExt) ≤ s4 := by
  dsimp only [savePollNeed, extHookStack, Getters.publicKeyEqStackExt,
    RunSkeleton.RunBudgets.dirGetNeed] at hs4 ⊢
  omega

end CryptoVerification.SignalSession.Cli.KitInst.IdKit
