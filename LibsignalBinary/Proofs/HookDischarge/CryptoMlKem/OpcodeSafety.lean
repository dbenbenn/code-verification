/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Placed.OpcodeExclusion
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs

/-!
# Static opcode-exclusion and self-containment checks

Isolates the whole-bundle kernel checks (`!isSvc`, `!isMsrTpidrEl0`, `externs = []`) over all
32 blocks (`58,690` words) of `mlkemMultiLib` so `PlacedCodeBase.lean` compiles in `< 5s`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.OpcodeSafety

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)

theorem mlkemMultiLib_blocks_all_externs_empty :
    ∀ b ∈ mlkemMultiLib.blocks, b.externs = [] := by
  decide +kernel

theorem mlkemMultiLib_blocks_all_svc0_and_msr :
    mlkemMultiLib.blocks.all (fun b => b.patchSafe svc0Pat && b.patchSafe msrTpidrEl0Pat) = true := by
  decide +kernel

theorem mlkemMultiLib_blocks_all_svc0 :
    mlkemMultiLib.blocks.all (fun b => b.patchSafe svc0Pat) = true := by
  have h := mlkemMultiLib_blocks_all_svc0_and_msr
  rw [List.all_eq_true] at h ⊢
  intro b hb
  exact (Bool.and_eq_true_iff.mp (h b hb)).1

theorem mlkemMultiLib_blocks_all_msr :
    mlkemMultiLib.blocks.all (fun b => b.patchSafe msrTpidrEl0Pat) = true := by
  have h := mlkemMultiLib_blocks_all_svc0_and_msr
  rw [List.all_eq_true] at h ⊢
  intro b hb
  exact (Bool.and_eq_true_iff.mp (h b hb)).2

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.OpcodeSafety
