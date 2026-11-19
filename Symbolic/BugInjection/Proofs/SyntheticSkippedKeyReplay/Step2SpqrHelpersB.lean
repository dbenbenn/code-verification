/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay.Step2SpqrHelpersA

/-!
# Wire Equality Lemma for Alice SPQR Extraction (`c1`)
-/

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay

open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement

@[expose] public section

attribute [local irreducible] Symbolic.BugInjection.hexBytes

noncomputable section Step2Part2D

theorem p_c1_wire_eq_dag22 :
    p_c1.message.take (p_c1.message.length - 8) =
      DY.Libsignal.Refinement.trWireBytes cleanAddrBs DY.Libsignal.Refinement.canonicalVariation
        { version := DY.Libsignal.TripleRatchet.messageVersion.toNat,
          ratchetKey := dagBytes 73, counter := 0, previousCounter := 0,
          ciphertext := dagBytes 105 } (dagBytes 22) := by
  decide +kernel

end Step2Part2D

end
end Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay
