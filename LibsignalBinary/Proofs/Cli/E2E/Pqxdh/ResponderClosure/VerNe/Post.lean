/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.DecDefs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.S1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Tail
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep

/-!
# Version-Mismatch `+0x1e04` Composition

Composes the initial version-mismatch entry (`+0x1e04 → +0x1e78`, `errs.len = 1`), the 1-element
`previous_sessions` loop (`+0x1e78 → +0x2cfc`, `errs.len = 2`), and the error-cleanup tail
(`+0x2cfc → s0.readReg64 .x30`) into `OverVerNe1e04CliStmtGenExt` and `OverVerNe1e04CliA0StmtGen`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (growOneSpeStack)
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure


attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## Stack and spatial fold helpers -/

private theorem stackAt_sub_eq_post (sp : BitVec 64) (big small : Nat)
    (h1 : small ≤ big := by decide) (h2 : big ≤ 2 ^ 64 := by decide) :
    stackAt sp big = memRegion (sp - BitVec.ofNat 64 big) (big - small) ∗ stackAt sp small := by
  have h := ProofLib.stackAt_split_bottom sp small (big - small) (by omega)
  rwa [Nat.add_sub_of_le h1] at h

private theorem slot3e0_344_fold_post (sp w : BitVec 64) :
    ((sp + 0x3e0#64) ↦₆₄ w) ∗ memRegion (sp + 0x3e8#64) 336 ⊢ memRegion (sp + 0x3e0#64) 344 := by
  rw [ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 8) (k := 336) (b' := sp + 0x3e8#64)
        rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)

private theorem stack_bottom_join_post (sp : BitVec 64) :
    memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - overDecStackX) ∗
    memRegion (sp - BitVec.ofNat 64 overDecStackX) (overDecStackX - growOneSpeStack) =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) :=
  (ProofLib.memRegion_split'
    (b := sp - BitVec.ofNat 64 rootStack)
    (n := rootStack - overDecStackX)
    (k := overDecStackX - growOneSpeStack)
    (b' := sp - BitVec.ofNat 64 overDecStackX)
    (by decide) (by dsimp only [rootStack, overDecStackX]; bv_omega) (by decide)).symm

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe
