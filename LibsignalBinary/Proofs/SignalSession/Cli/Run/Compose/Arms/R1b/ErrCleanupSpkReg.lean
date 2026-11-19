/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanup -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

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

private theorem r1b_rejoin_188 (fsp regCap regPtr : BitVec 64) :
    memRegion (fsp + 0x188#64) 16 ∗ ((fsp + 0x198#64) ↦₆₄ regCap) ∗
      ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ memRegion (fsp + 0x1a8#64) 16 ⊢
      memRegion (fsp + 0x188#64) 48 := by
  have h1a0 : ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ memRegion (fsp + 0x1a8#64) 16 ⊢
      memRegion (fsp + 0x1a0#64) 24 := by
    have ha : fsp + 0x1a8#64 = (fsp + 0x1a0#64) + 8#64 := by bv_omega
    rw [ha]; exact r1b_cell64_cons regPtr (by decide)
  have h198 : ((fsp + 0x198#64) ↦₆₄ regCap) ∗ memRegion (fsp + 0x1a0#64) 24 ⊢
      memRegion (fsp + 0x198#64) 32 := by
    have ha : fsp + 0x1a0#64 = (fsp + 0x198#64) + 8#64 := by bv_omega
    rw [ha]; exact r1b_cell64_cons regCap (by decide)
  have h188 : memRegion (fsp + 0x188#64) 16 ∗ memRegion (fsp + 0x198#64) 32 ⊢
      memRegion (fsp + 0x188#64) 48 := by
    have ha : fsp + 0x198#64 = (fsp + 0x188#64) + 16#64 := by bv_omega
    rw [ha, show (48 : Nat) = 16 + 32 from rfl,
      ProofLib.memRegion_split (fsp + 0x188#64) 16 32 (by decide)]
    exact Entails.refl _
  exact Entails.trans (sepConj_mono_right (Entails.trans (sepConj_mono_right h1a0) h198)) h188

private theorem r1b_rejoin_168 (fsp spkPtr spkCap : BitVec 64) :
    ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
      memRegion (fsp + 0x178#64) 8 ⊢ memRegion (fsp + 0x168#64) 24 := by
  have ha8 : fsp + 0x170#64 = (fsp + 0x168#64) + 8#64 := by bv_omega
  have ha16 : fsp + 0x178#64 = (fsp + 0x168#64) + 16#64 := by bv_omega
  rw [ha8, ha16]
  exact r1b_cells2_region8_to_24 (fsp + 0x168#64) spkPtr spkCap

@[expose] def r1b_errLow4 (fsp : BitVec 64) : SepProp :=
  memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
  memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16

theorem r1b_fold_low4 (fsp : BitVec 64) (R : SepProp) :
    memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
      memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗ R =
      r1b_errLow4 fsp ∗ R := by
  dsimp only [r1b_errLow4]; simp only [sepConj_assoc]

end CryptoVerification.SignalSession.Cli.RunCompose
