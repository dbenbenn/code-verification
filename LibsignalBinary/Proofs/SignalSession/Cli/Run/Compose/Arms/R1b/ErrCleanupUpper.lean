/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanup -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupSpkReg
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

private def r1b_owned3 (A : RustAlloc)
    (kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64)
    (kpkBs spkBs regBs : List (BitVec 8)) : SepProp :=
  ownedBytes A kpkCap kpkPtr kpkLen kpkBs ∗
  ownedBytes A spkCap spkPtr spkLen spkBs ∗
  ownedBytes A regCap regPtr regLen regBs

private theorem r1b_fold_owned3 (A : RustAlloc)
    (kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64)
    (kpkBs spkBs regBs : List (BitVec 8)) (R : SepProp) :
    ownedBytes A kpkCap kpkPtr kpkLen kpkBs ∗
      ownedBytes A spkCap spkPtr spkLen spkBs ∗
      ownedBytes A regCap regPtr regLen regBs ∗ R =
      r1b_owned3 A kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen
        kpkBs spkBs regBs ∗ R := by
  dsimp only [r1b_owned3]; simp only [sepConj_assoc]

private def r1b_mid9 (fsp spkPtr spkCap v188 v190 regCap regPtr v1a8 v1b0 : BitVec 64) : SepProp :=
  ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
  memRegion (fsp + 0x178#64) 8 ∗
  ((fsp + 0x188#64) ↦₆₄ v188) ∗ ((fsp + 0x190#64) ↦₆₄ v190) ∗
  ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
  ((fsp + 0x1a8#64) ↦₆₄ v1a8) ∗ ((fsp + 0x1b0#64) ↦₆₄ v1b0)

private theorem r1b_fold_mid9
    (fsp spkPtr spkCap v188 v190 regCap regPtr v1a8 v1b0 : BitVec 64) (R : SepProp) :
    ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
      memRegion (fsp + 0x178#64) 8 ∗
      ((fsp + 0x188#64) ↦₆₄ v188) ∗ ((fsp + 0x190#64) ↦₆₄ v190) ∗
      ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
      ((fsp + 0x1a8#64) ↦₆₄ v1a8) ∗ ((fsp + 0x1b0#64) ↦₆₄ v1b0) ∗ R =
      r1b_mid9 fsp spkPtr spkCap v188 v190 regCap regPtr v1a8 v1b0 ∗ R := by
  dsimp only [r1b_mid9]; simp only [sepConj_assoc]

private def r1b_mid7 (fsp spkPtr spkCap regCap regPtr : BitVec 64) : SepProp :=
  ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
  memRegion (fsp + 0x178#64) 8 ∗
  memRegion (fsp + 0x188#64) 16 ∗
  ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
  memRegion (fsp + 0x1a8#64) 16

private theorem r1b_fold_mid7
    (fsp spkPtr spkCap regCap regPtr : BitVec 64) (R : SepProp) :
    ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
      memRegion (fsp + 0x178#64) 8 ∗
      memRegion (fsp + 0x188#64) 16 ∗
      ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
      memRegion (fsp + 0x1a8#64) 16 ∗ R =
      r1b_mid7 fsp spkPtr spkCap regCap regPtr ∗ R := by
  dsimp only [r1b_mid7]; simp only [sepConj_assoc]

end CryptoVerification.SignalSession.Cli.RunCompose
