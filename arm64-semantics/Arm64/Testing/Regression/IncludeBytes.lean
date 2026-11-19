/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Surface.IncludeBytes

/-!
# Unit Tests for `include_bytes%`

Tests that `include_bytes% "path" off len` splices exact byte slices (including empty slices,
4 KiB chunk-boundary transitions, non-16-aligned multi-chunk tails, and public/private/`noncomputable`
declarations) and rejects out-of-bounds slices.
-/

@[expose] public section

namespace Testing.IncludeBytes

example : include_bytes% "IncludeBytes.fixture" 0 3 = [0x30#8, 0x31#8, 0x32#8] := rfl
example : include_bytes% "IncludeBytes.fixture" 8 3 = [0x38#8, 0x39#8, 0x0a#8] := rfl
example : include_bytes% "IncludeBytes.fixture" 11 0 = [] := rfl

/-- error: include_bytes%: -/
#guard_msgs (substring := true) in
example : include_bytes% "IncludeBytes.fixture" 9 3 = [] := rfl

/-! ## 4 KiB Chunk-Boundary and Multi-Chunk Equivalence Tests -/

set_option maxRecDepth 40000 in
/-- Exact 4096-to-4097 byte threshold transition: an inline 4096-byte `toListExpr` slice plus 1 byte
    is definitionally equal to the chunked 4097-byte `elabBytes` slice. -/
example :
    (include_bytes% "../ProcessE2E/bin/exit_codes.elf" 0 4096) ++
      (include_bytes% "../ProcessE2E/bin/exit_codes.elf" 4096 1) =
    include_bytes% "../ProcessE2E/bin/exit_codes.elf" 0 4097 := rfl

/-- Multi-chunk computable slice of length `8213 = 2 * 4096 + 16 + 5` (two full 4 KiB chunks plus
    one `IncludeBytes.cons16` group and a 5-byte `List.cons` remainder). -/
def chunked8213 : List (BitVec 8) :=
  include_bytes% "../ProcessE2E/bin/exit_codes.elf" 0 8213

#guard chunked8213.length == 8213

set_option maxRecDepth 40000 in
/-- Kernel definitional equality between three unchunked `toListExpr` slices (`≤ 4096` bytes each)
    and the 3-chunk `chunked8213` definition. -/
example :
    (include_bytes% "../ProcessE2E/bin/exit_codes.elf" 0 4096) ++
      (include_bytes% "../ProcessE2E/bin/exit_codes.elf" 4096 4096) ++
      (include_bytes% "../ProcessE2E/bin/exit_codes.elf" 8192 21) =
    chunked8213 := rfl

noncomputable def noncomputableChunked5000 : List (BitVec 8) :=
  include_bytes% "../ProcessE2E/bin/exit_codes.elf" 200 5000

set_option maxRecDepth 40000 in
example : noncomputableChunked5000.length = 5000 := rfl

end Testing.IncludeBytes
end

public section

namespace Testing.IncludeBytes

/-- Non-exposed `public def` (`isExporting = false` in body) with a multi-chunk `include_bytes%`. -/
def unexposedChunked5000 : List (BitVec 8) :=
  include_bytes% "../ProcessE2E/bin/exit_codes.elf" 0 5000

#guard unexposedChunked5000.length == 5000

private def privateChunked5000 : List (BitVec 8) :=
  include_bytes% "../ProcessE2E/bin/exit_codes.elf" 100 5000

#guard privateChunked5000.length == 5000

end Testing.IncludeBytes
end
