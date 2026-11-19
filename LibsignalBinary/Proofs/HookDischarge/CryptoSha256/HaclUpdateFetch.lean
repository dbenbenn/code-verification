/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclCode -- proof-setup: allow-public-import
meta import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclCode

/-!
# Placed fetch lemmas for `libcrux_sha2::hacl::sha256_update`

Instruction-fetch lemmas for `libcrux_sha2::hacl::sha256_update` (block `1`, `2,074` words).
-/

set_option autoImplicit false
set_option maxRecDepth 4000000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclUpdateFetch

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclCode
  (libcruxHmacLib HaclPlacement haclMpl)

private theorem rebase_self_prog (p : Program) :
    p.rebase p.base p.externs p.overrides = p := by
  cases p; rfl

@[expose] def haclLib1 : Obj.PlacedLib := libcruxHmacLib.blockLib 1
@[expose] def haclPl1 [HaclPlacement] : Obj.Placement := libcruxHmacLib.blockPlacement haclMpl 1
theorem haclPlaceable1 [HaclPlacement] : haclLib1.Placeable haclPl1 :=
  libcruxHmacLib.placeable_blockLib (by decide) HaclPlacement.placeable
@[expose] def haclPC1 [HaclPlacement] : Program := haclLib1.program haclPl1
@[expose] def haclProg1 : Program := { code := haclLib1.text.code, symbols := haclLib1.text.symbols }
@[expose] def haclTree1 : WordTree := word_tree_of% haclProg1
theorem hacl1_code_eq : haclLib1.text.code = haclTree1.toBytes := by rfl_kernel
theorem hacl1_tree_size : haclTree1.checkSize? = some 2074 := by rfl_kernel

theorem haclPC1_rebase [HaclPlacement] :
    (libcruxHmacLib.blockProgram haclMpl 1).rebase (haclMpl.base 1) (fun _ => none) =
      haclPC1.rebase haclPl1.base (fun _ => none) := rfl
theorem haclPC1_eq_blockProgram [HaclPlacement] :
    haclPC1.rebase haclPl1.base (fun _ => none) = libcruxHmacLib.blockProgram haclMpl 1 :=
  rebase_self_prog (libcruxHmacLib.blockProgram haclMpl 1)
theorem haclPl1_base [HaclPlacement] : haclPl1.base = haclMpl.base 1 := rfl
theorem haclPl1_rho [HaclPlacement] (sym : String) :
    libcruxHmacLib.resolve haclMpl sym = haclPl1.ρ sym := rfl

section
set_option linter.literalFetch false
gen_placed_fetches haclPC1 haclLib1 haclTree1 hacl1_code_eq hacl1_tree_size
  via_placement haclPl1 haclPlaceable1 [0x0 → 0x2064]
end

end LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclUpdateFetch
