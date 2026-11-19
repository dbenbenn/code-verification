/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.PrevBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrB -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep

/-!
# Version-Mismatch Closure Heap and Statement Definitions

Stack scratch layout (`overScratch`), optional vector-register preservation (`optVRegsEq`), and
`+0x1e04 → ret` specification statements (`OverVerNe1e04CliStmtGenExt`, `OverVerNe1e04CliA0StmtGen`)
for the CLI PQXDH responder closure version-mismatch (`msgVer ≠ 4`) path with one archived
`previous_sessions` entry.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (growOneSpeStack)
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure


/-- Optional `calleeSavedVRegs` preservation (`true` = full ARM64 PCS `d8..d15`, `false` = GPR-only). -/
@[expose] def optVRegsEq (trackVRegs : Bool) (sf s : State) : Prop :=
  if trackVRegs then calleeSavedVRegs sf = calleeSavedVRegs s else True

theorem optVRegsEq_refl (trackVRegs : Bool) (s : State) : optVRegsEq trackVRegs s s := by
  cases trackVRegs <;> simp [optVRegsEq]

theorem optVRegsEq_trans {trackVRegs : Bool} {s1 s2 s3 : State}
    (h12 : optVRegsEq trackVRegs s2 s1) (h23 : optVRegsEq trackVRegs s3 s2) :
    optVRegsEq trackVRegs s3 s1 := by
  cases trackVRegs
  · trivial
  · simp only [optVRegsEq, ↓reduceIte] at h12 h23 ⊢
    exact h23.trans h12

theorem optVRegsEq_of_vregs_eq (trackVRegs : Bool) {sf s : State}
    (h : calleeSavedVRegs sf = calleeSavedVRegs s) :
    optVRegsEq trackVRegs sf s := by
  cases trackVRegs <;> simp [optVRegsEq, h]

@[simp]
theorem optVRegsEq_true (sf s : State) :
    optVRegsEq true sf s ↔ calleeSavedVRegs sf = calleeSavedVRegs s :=
  Iff.rfl

@[simp]
theorem optVRegsEq_false (sf s : State) :
    optVRegsEq false sf s ↔ True :=
  Iff.rfl

/-- Closure stack scratch slots untouched outside the 1-element `previous_sessions` loop
(`sp + 0x538..0x930` = 1016 B, `sp + 0x990..0xa90` = 256 B, `sp + 0xbe8..0xc70` = 136 B). -/
@[expose] def overScratch (q : BitVec 64) : SepProp :=
  memRegion (q + 0x538#64) 1016 ∗
  memRegion (q + 0x990#64) 256 ∗
  memRegion (q + 0xbe8#64) 136

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe
