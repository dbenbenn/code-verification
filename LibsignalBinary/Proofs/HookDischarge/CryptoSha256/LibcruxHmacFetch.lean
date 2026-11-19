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
# Placed fetch lemmas for `libcrux_hmac::hmac`

Instruction-fetch lemmas for `libcrux_hmac::hmac` (block `6`, `712` words).
-/

set_option autoImplicit false
set_option maxRecDepth 4000000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoSha256.LibcruxHmacFetch

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclCode
  (libcruxHmacLib HaclPlacement haclMpl)

private theorem rebase_self_prog (p : Program) :
    p.rebase p.base p.externs p.overrides = p := by
  cases p; rfl

@[expose] def haclLib6 : Obj.PlacedLib := libcruxHmacLib.blockLib 6
@[expose] def haclPl6 [HaclPlacement] : Obj.Placement := libcruxHmacLib.blockPlacement haclMpl 6
theorem haclPlaceable6 [HaclPlacement] : haclLib6.Placeable haclPl6 :=
  libcruxHmacLib.placeable_blockLib (by decide) HaclPlacement.placeable
@[expose] def haclPC6 [HaclPlacement] : Program := haclLib6.program haclPl6
@[expose] def haclProg6 : Program := { code := haclLib6.text.code, symbols := haclLib6.text.symbols }
@[expose] def haclTree6 : WordTree := word_tree_of% haclProg6
theorem hacl6_code_eq : haclLib6.text.code = haclTree6.toBytes := by rfl_kernel
theorem hacl6_tree_size : haclTree6.checkSize? = some 712 := by rfl_kernel

theorem haclPC6_rebase [HaclPlacement] :
    (libcruxHmacLib.blockProgram haclMpl 6).rebase (haclMpl.base 6) (fun _ => none) =
      haclPC6.rebase haclPl6.base (fun _ => none) := rfl
theorem haclPC6_eq_blockProgram [HaclPlacement] :
    haclPC6.rebase haclPl6.base (fun _ => none) = libcruxHmacLib.blockProgram haclMpl 6 :=
  rebase_self_prog (libcruxHmacLib.blockProgram haclMpl 6)
theorem haclPl6_base [HaclPlacement] : haclPl6.base = haclMpl.base 6 := rfl
theorem haclPl6_rho [HaclPlacement] (sym : String) :
    libcruxHmacLib.resolve haclMpl sym = haclPl6.ρ sym := rfl

section
set_option linter.literalFetch false
gen_placed_fetches haclPC6 haclLib6 haclTree6 hacl6_code_eq hacl6_tree_size
  via_placement haclPl6 haclPlaceable6 [0x0 → 0xb1c]
end

end LibsignalBinary.Proofs.HookDischarge.CryptoSha256.LibcruxHmacFetch
