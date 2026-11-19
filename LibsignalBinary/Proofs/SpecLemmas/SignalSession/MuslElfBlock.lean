/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.MuslStart -- proof-setup: allow-public-import
import ProofLib.SepLogic.WPp

public section

set_option autoImplicit false

/-!
# musl Startup Block from `_start` to `main`

Packages `MuslStart.musl_start_ofImage` (hops 1–7 from `_start` at `B` to `main = B - 89668`)
as a single `Steps` transition `musl_start_block` on `Program.ofImage img E` over the
initial stack table, program headers, 60 zero stack words below `sp0 - 48`, and musl's
writable statics (`muslRwWords`) at `B + 0x2000`.
-/

namespace CryptoVerification.SignalSession.MuslElf

open Arm64 ProofLib CryptoVerification.SignalSession.MuslExit
  CryptoVerification.SignalSession.MuslStart

/-- `k` consecutive 8-byte cells starting at `a`. -/
@[expose] def cellsW (a : BitVec 64) : Nat → SepProp
  | 0 => emp
  | k + 1 => (∃∗ v : BitVec 64, a ↦₆₄ v) ∗ cellsW (a + 8#64) k

theorem memRegion_cellsW (a : BitVec 64) (k : Nat) (h : 8 * k ≤ 2 ^ 64) :
    memRegion a (8 * k) = cellsW a k := by
  induction k generalizing a with
  | zero => exact memRegion_zero a
  | succ k ih =>
    rw [show 8 * (k + 1) = 8 + 8 * k by omega, memRegion_split a 8 (8 * k) (by omega),
      memRegion_eight, ih _ (by omega), cellsW]

theorem sat_of_entails_frame {m : Memory} {P Q F : SepProp} (hm : m ⊨ P) (h : P ⊢ Q ∗ F) :
    m ⊨ Q := by
  have h1 := Satisfies.mono h hm
  rw [sepConj_comm] at h1
  exact Satisfies.drop_left h1

theorem pointsTo64_eq_8 (a v : BitVec 64) :
    (a ↦₆₄ v) = ((a ↦₈ v.extractLsb' 0 8) ∗
      (pointsTo8 (a + 1#64) (v.extractLsb' 8 8) ∗ pointsTo8 (a + 2#64) (v.extractLsb' 16 8) ∗
       pointsTo8 (a + 3#64) (v.extractLsb' 24 8) ∗ pointsTo8 (a + 4#64) (v.extractLsb' 32 8) ∗
       pointsTo8 (a + 5#64) (v.extractLsb' 40 8) ∗ pointsTo8 (a + 6#64) (v.extractLsb' 48 8) ∗
       pointsTo8 (a + 7#64) (v.extractLsb' 56 8))) := by
  unfold pointsTo64; rw [BitVec.add_zero]

/-- Initial contents of musl's writable statics at `B + 0x2000 .. B + 0x2258` (600 bytes). -/
@[expose] def muslRwWords (h0 g3 g4 ia F : BitVec 64) : List (BitVec 64) :=
  [h0, 0#64, g3, g4, ia, ia, F, F] ++ List.replicate 67 0#64

end CryptoVerification.SignalSession.MuslElf
