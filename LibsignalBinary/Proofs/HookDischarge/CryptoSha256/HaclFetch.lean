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
# Placed fetch lemmas for `libcrux_sha2::hacl`

Instruction-fetch lemmas for the short `libcrux_sha2::hacl` functions (blocks `0`, `2`, `3`, `4`,
and `5`): `sha256_init`, `sha256_update_nblocks`, `sha256_update_last`, `sha256_finish`, and
`hash_256`.
-/

set_option autoImplicit false
set_option maxRecDepth 4000000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclFetch

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclCode
  (libcruxHmacLib HaclPlacement haclMpl)

private theorem rebase_self_prog (p : Program) :
    p.rebase p.base p.externs p.overrides = p := by
  cases p; rfl

/-! ## Block 0: `sha256_init` (`78` words, `[0x0 → 0x134]`) -/

@[expose] def haclLib0 : Obj.PlacedLib := libcruxHmacLib.blockLib 0
@[expose] def haclPl0 [HaclPlacement] : Obj.Placement := libcruxHmacLib.blockPlacement haclMpl 0
theorem haclPlaceable0 [HaclPlacement] : haclLib0.Placeable haclPl0 :=
  libcruxHmacLib.placeable_blockLib (by decide) HaclPlacement.placeable
@[expose] def haclPC0 [HaclPlacement] : Program := haclLib0.program haclPl0
@[expose] def haclProg0 : Program := { code := haclLib0.text.code, symbols := haclLib0.text.symbols }
@[expose] def haclTree0 : WordTree := word_tree_of% haclProg0
theorem hacl0_code_eq : haclLib0.text.code = haclTree0.toBytes := by rfl_kernel
theorem hacl0_tree_size : haclTree0.checkSize? = some 78 := by rfl_kernel
theorem haclPC0_rebase [HaclPlacement] :
    (libcruxHmacLib.blockProgram haclMpl 0).rebase (haclMpl.base 0) (fun _ => none) =
      haclPC0.rebase haclPl0.base (fun _ => none) := rfl
theorem haclPC0_eq_blockProgram [HaclPlacement] :
    haclPC0.rebase haclPl0.base (fun _ => none) = libcruxHmacLib.blockProgram haclMpl 0 :=
  rebase_self_prog (libcruxHmacLib.blockProgram haclMpl 0)
theorem haclPl0_base [HaclPlacement] : haclPl0.base = haclMpl.base 0 := rfl

section
set_option linter.literalFetch false
gen_placed_fetches haclPC0 haclLib0 haclTree0 hacl0_code_eq hacl0_tree_size
  via_placement haclPl0 haclPlaceable0 [0x0 → 0x134]
end

/-! ## Block 2: `sha256_update_nblocks` (`35` words, `[0x0 → 0x88]`) -/

@[expose] def haclLib2 : Obj.PlacedLib := libcruxHmacLib.blockLib 2
@[expose] def haclPl2 [HaclPlacement] : Obj.Placement := libcruxHmacLib.blockPlacement haclMpl 2
theorem haclPlaceable2 [HaclPlacement] : haclLib2.Placeable haclPl2 :=
  libcruxHmacLib.placeable_blockLib (by decide) HaclPlacement.placeable
@[expose] def haclPC2 [HaclPlacement] : Program := haclLib2.program haclPl2
@[expose] def haclProg2 : Program := { code := haclLib2.text.code, symbols := haclLib2.text.symbols }
@[expose] def haclTree2 : WordTree := word_tree_of% haclProg2
theorem hacl2_code_eq : haclLib2.text.code = haclTree2.toBytes := by rfl_kernel
theorem hacl2_tree_size : haclTree2.checkSize? = some 35 := by rfl_kernel
theorem haclPC2_rebase [HaclPlacement] :
    (libcruxHmacLib.blockProgram haclMpl 2).rebase (haclMpl.base 2) (fun _ => none) =
      haclPC2.rebase haclPl2.base (fun _ => none) := rfl
theorem haclPC2_eq_blockProgram [HaclPlacement] :
    haclPC2.rebase haclPl2.base (fun _ => none) = libcruxHmacLib.blockProgram haclMpl 2 :=
  rebase_self_prog (libcruxHmacLib.blockProgram haclMpl 2)
theorem haclPl2_base [HaclPlacement] : haclPl2.base = haclMpl.base 2 := rfl
theorem haclPl2_rho [HaclPlacement] (sym : String) :
    libcruxHmacLib.resolve haclMpl sym = haclPl2.ρ sym := rfl

section
set_option linter.literalFetch false
gen_placed_fetches haclPC2 haclLib2 haclTree2 hacl2_code_eq hacl2_tree_size
  via_placement haclPl2 haclPlaceable2 [0x0 → 0x88]
end

/-! ## Block 3: `sha256_update_last` (`74` words, `[0x0 → 0x124]`) -/

@[expose] def haclLib3 : Obj.PlacedLib := libcruxHmacLib.blockLib 3
@[expose] def haclPl3 [HaclPlacement] : Obj.Placement := libcruxHmacLib.blockPlacement haclMpl 3
theorem haclPlaceable3 [HaclPlacement] : haclLib3.Placeable haclPl3 :=
  libcruxHmacLib.placeable_blockLib (by decide) HaclPlacement.placeable
@[expose] def haclPC3 [HaclPlacement] : Program := haclLib3.program haclPl3
@[expose] def haclProg3 : Program := { code := haclLib3.text.code, symbols := haclLib3.text.symbols }
@[expose] def haclTree3 : WordTree := word_tree_of% haclProg3
theorem hacl3_code_eq : haclLib3.text.code = haclTree3.toBytes := by rfl_kernel
theorem hacl3_tree_size : haclTree3.checkSize? = some 74 := by rfl_kernel
theorem haclPC3_rebase [HaclPlacement] :
    (libcruxHmacLib.blockProgram haclMpl 3).rebase (haclMpl.base 3) (fun _ => none) =
      haclPC3.rebase haclPl3.base (fun _ => none) := rfl
theorem haclPC3_eq_blockProgram [HaclPlacement] :
    haclPC3.rebase haclPl3.base (fun _ => none) = libcruxHmacLib.blockProgram haclMpl 3 :=
  rebase_self_prog (libcruxHmacLib.blockProgram haclMpl 3)
theorem haclPl3_base [HaclPlacement] : haclPl3.base = haclMpl.base 3 := rfl
theorem haclPl3_rho [HaclPlacement] (sym : String) :
    libcruxHmacLib.resolve haclMpl sym = haclPl3.ρ sym := rfl

section
set_option linter.literalFetch false
gen_placed_fetches haclPC3 haclLib3 haclTree3 hacl3_code_eq hacl3_tree_size
  via_placement haclPl3 haclPlaceable3 [0x0 → 0x124]
end

/-! ## Block 4: `sha256_finish` (`79` words, `[0x0 → 0x138]`) -/

@[expose] def haclLib4 : Obj.PlacedLib := libcruxHmacLib.blockLib 4
@[expose] def haclPl4 [HaclPlacement] : Obj.Placement := libcruxHmacLib.blockPlacement haclMpl 4
theorem haclPlaceable4 [HaclPlacement] : haclLib4.Placeable haclPl4 :=
  libcruxHmacLib.placeable_blockLib (by decide) HaclPlacement.placeable
@[expose] def haclPC4 [HaclPlacement] : Program := haclLib4.program haclPl4
@[expose] def haclProg4 : Program := { code := haclLib4.text.code, symbols := haclLib4.text.symbols }
@[expose] def haclTree4 : WordTree := word_tree_of% haclProg4
theorem hacl4_code_eq : haclLib4.text.code = haclTree4.toBytes := by rfl_kernel
theorem hacl4_tree_size : haclTree4.checkSize? = some 79 := by rfl_kernel
theorem haclPC4_rebase [HaclPlacement] :
    (libcruxHmacLib.blockProgram haclMpl 4).rebase (haclMpl.base 4) (fun _ => none) =
      haclPC4.rebase haclPl4.base (fun _ => none) := rfl
theorem haclPC4_eq_blockProgram [HaclPlacement] :
    haclPC4.rebase haclPl4.base (fun _ => none) = libcruxHmacLib.blockProgram haclMpl 4 :=
  rebase_self_prog (libcruxHmacLib.blockProgram haclMpl 4)
theorem haclPl4_base [HaclPlacement] : haclPl4.base = haclMpl.base 4 := rfl

section
set_option linter.literalFetch false
gen_placed_fetches haclPC4 haclLib4 haclTree4 hacl4_code_eq hacl4_tree_size
  via_placement haclPl4 haclPlaceable4 [0x0 → 0x138]
end

/-! ## Block 5: `hash_256` (`101` words, `[0x0 → 0x190]`) -/

@[expose] def haclLib5 : Obj.PlacedLib := libcruxHmacLib.blockLib 5
@[expose] def haclPl5 [HaclPlacement] : Obj.Placement := libcruxHmacLib.blockPlacement haclMpl 5
theorem haclPlaceable5 [HaclPlacement] : haclLib5.Placeable haclPl5 :=
  libcruxHmacLib.placeable_blockLib (by decide) HaclPlacement.placeable
@[expose] def haclPC5 [HaclPlacement] : Program := haclLib5.program haclPl5
@[expose] def haclProg5 : Program := { code := haclLib5.text.code, symbols := haclLib5.text.symbols }
@[expose] def haclTree5 : WordTree := word_tree_of% haclProg5
theorem hacl5_code_eq : haclLib5.text.code = haclTree5.toBytes := by rfl_kernel
theorem hacl5_tree_size : haclTree5.checkSize? = some 101 := by rfl_kernel
theorem haclPC5_rebase [HaclPlacement] :
    (libcruxHmacLib.blockProgram haclMpl 5).rebase (haclMpl.base 5) (fun _ => none) =
      haclPC5.rebase haclPl5.base (fun _ => none) := rfl
theorem haclPC5_eq_blockProgram [HaclPlacement] :
    haclPC5.rebase haclPl5.base (fun _ => none) = libcruxHmacLib.blockProgram haclMpl 5 :=
  rebase_self_prog (libcruxHmacLib.blockProgram haclMpl 5)
theorem haclPl5_base [HaclPlacement] : haclPl5.base = haclMpl.base 5 := rfl
theorem haclPl5_rho [HaclPlacement] (sym : String) :
    libcruxHmacLib.resolve haclMpl sym = haclPl5.ρ sym := rfl

section
set_option linter.literalFetch false
gen_placed_fetches haclPC5 haclLib5 haclTree5 hacl5_code_eq hacl5_tree_size
  via_placement haclPl5 haclPlaceable5 [0x0 → 0x190]
end

end LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclFetch
