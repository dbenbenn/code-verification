/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.SignalSession.Cli.Kits -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Pure -- shake: keep
public import ProofLib
public import ProofLib.GenDecodes
public import ProofLib.ProgramReflection.Variant.TrapTransfer
public import ProofLib.SepLogic.WPp
public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession.Cli

theorem write_15_overlap_mid (buf w0 : BitVec 64) :
    (buf ↦₆₄ w0) ∗ memRegion (buf + 8#64) 7 ⊢
      (buf ↦ₛ (unpack64 w0).take 7) ∗ memRegion (buf + 7#64) 8 := by
  have h1 : (unpack64 w0).length = 8 := unpack64_length w0
  have h7 : ((unpack64 w0).take 7).length = 7 := by simp [h1]
  have hrem : ((unpack64 w0).drop 7).length = 1 := by simp [h1]
  rw [pointsTo64_eq_pointsToBytes, ← List.take_append_drop 7 (unpack64 w0),
      pointsToBytes_append, h7]
  simp only [sepConj_assoc]
  refine sepConj_mono_right ?_
  rw [memRegion_split (buf + 7#64) 1 7 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_left (hrem ▸ pointsToBytes_entails_memRegion _ _)

theorem write_15_overlap_done (buf w0 w7 : BitVec 64) :
    (buf ↦ₛ (unpack64 w0).take 7) ∗ ((buf + 7#64) ↦₆₄ w7) ⊢
      buf ↦ₛ ((unpack64 w0).take 7 ++ unpack64 w7) := by
  have h7 : ((unpack64 w0).take 7).length = 7 := by simp [unpack64_length]
  rw [pointsTo64_eq_pointsToBytes, pointsToBytes_append, h7]
  exact Entails.refl _

theorem write_14_overlap_mid (buf w0 : BitVec 64) :
    (buf ↦₆₄ w0) ∗ memRegion (buf + 8#64) 6 ⊢
      (buf ↦ₛ (unpack64 w0).take 6) ∗ memRegion (buf + 6#64) 8 := by
  have h1 : (unpack64 w0).length = 8 := unpack64_length w0
  have h6 : ((unpack64 w0).take 6).length = 6 := by simp [h1]
  have hrem : ((unpack64 w0).drop 6).length = 2 := by simp [h1]
  rw [pointsTo64_eq_pointsToBytes, ← List.take_append_drop 6 (unpack64 w0),
      pointsToBytes_append, h6]
  simp only [sepConj_assoc]
  refine sepConj_mono_right ?_
  rw [memRegion_split (buf + 6#64) 2 6 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_left (hrem ▸ pointsToBytes_entails_memRegion _ _)

theorem write_14_overlap_done (buf w0 w6 : BitVec 64) :
    (buf ↦ₛ (unpack64 w0).take 6) ∗ ((buf + 6#64) ↦₆₄ w6) ⊢
      buf ↦ₛ ((unpack64 w0).take 6 ++ unpack64 w6) := by
  have h6 : ((unpack64 w0).take 6).length = 6 := by simp [unpack64_length]
  rw [pointsTo64_eq_pointsToBytes, pointsToBytes_append, h6]
  exact Entails.refl _

end CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers
