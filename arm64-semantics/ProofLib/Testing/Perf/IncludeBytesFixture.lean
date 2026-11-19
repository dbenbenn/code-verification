/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import Arm64.Trusted.Surface.IncludeBytes

/-!
# 320 KiB Computable `include_bytes%` Fixture

Exports a 320 KiB (`327,680`-byte, 80-chunk) computable `List (BitVec 8)` constant and companion
5,000-byte slice under default `maxHeartbeats` (`200,000`) so `IncludeBytesScale.lean` can verify
cross-module `.olean` compilation, `#guard` evaluation, `word_tree_of%`, `rfl_kernel`,
`gen_labels_from_objects`, and `seg_lens%`.
-/

set_option autoImplicit false

@[expose] public section

namespace Examples.Testing.ProofLib.Perf.IncludeBytesFixture

/-- 320 KiB (`80 × 4096` bytes = `81,920` ARM64 words) computable binary slice compiled under the
    default `maxHeartbeats` budget (`200,000`). -/
def alphaCode320k : List (BitVec 8) :=
  include_bytes% "../../../Arm64/Testing/ProcessE2E/bin/exit_codes.elf" 0 327680

/-- Concrete `Arm64.Program` wrapping `alphaCode320k` across an `.olean` boundary. -/
def alphaProg320k : Arm64.Program :=
  { code := alphaCode320k }

/-- 5,000-byte multi-chunk slice (`4096 + 904` bytes) for `ExtractedObj` and `ElfImage` tests. -/
def alphaCode5000 : List (BitVec 8) :=
  include_bytes% "../../../Arm64/Testing/ProcessE2E/bin/exit_codes.elf" 0 5000

end Examples.Testing.ProofLib.Perf.IncludeBytesFixture
end
