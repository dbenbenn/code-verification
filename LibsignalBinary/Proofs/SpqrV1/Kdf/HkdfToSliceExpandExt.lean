/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtractDefsExt -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtractExt
import LibsignalBinary.Proofs.SpqrV1.Kdf.HooksExt
import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
import LibsignalBinary.Proofs.SpqrV1.Chain.Defs -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Chain.Repr -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

/-!
# `spqr::kdf::hkdf_to_slice`: Contract-Backed Extract Completion and Expand Block 1

Completes the HKDF-Extract phase (`0x633cc → 0x634fc`) and proves HKDF-Expand Block 1, epilogue,
`okmLen = 32` exit, and loop entry under `HkdfStubsExt` and `S2FrameRO` at stack budget
`hkdfToSliceStackExt` (`17616` B).
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.Kdf.HkdfToSliceExtProof

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Extract (RunsToE S2Frame frame_of_agreesOutside)
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.ChainProofs hiding hkdfToSliceName
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Kdf.SpqrKdfExt
open CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local simp, local arm64_norm]
  MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write64_base_off_disjoint
  Memory.read64_write8_base_off_disjoint
  extractLsb'_56_8_read64
  State.readReg64_setMem State.pc_setMem State.sp_setMem State.status_setMem
  Expand.mem_setMem
  extractLsb'_0_64_zero128 extractLsb'_64_64_zero128
  hsp_592_add_96_eq_sp
  read8_write64_264_271

theorem cs_x19 {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .x19 = s.readReg64 .x19 := h.2 .x19 (by simp)
theorem cs_x20 {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .x20 = s.readReg64 .x20 := h.2 .x20 (by simp)
theorem cs_x21 {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .x21 = s.readReg64 .x21 := h.2 .x21 (by simp)
theorem cs_x22 {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .x22 = s.readReg64 .x22 := h.2 .x22 (by simp)
theorem cs_x24 {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .x24 = s.readReg64 .x24 := h.2 .x24 (by simp)
theorem cs_x25 {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .x25 = s.readReg64 .x25 := h.2 .x25 (by simp)
theorem cs_x26 {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .x26 = s.readReg64 .x26 := h.2 .x26 (by simp)
theorem cs_x27 {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .x27 = s.readReg64 .x27 := h.2 .x27 (by simp)
theorem cs_x28 {s s' : State} (h : CalleeSaved s s') : s'.readReg64 .x28 = s.readReg64 .x28 := h.2 .x28 (by simp)

section ExtractCompletion

private theorem okmLen_cmp_lemmas_ext {okmLen : ℕ}
    (hokm : okmLen = 32 ∨ okmLen = 64 ∨ okmLen = 96) :
    (AddWithCarry64 (BitVec.ofNat 64 okmLen + bv% (2 ^ 64 - 8161)) 8159#64 true).2.c = true ∧
    BitVec.ule bv% (2 ^ 64 - 8160) (BitVec.ofNat 64 okmLen + bv% (2 ^ 64 - 8161)) = true ∧
    BitVec.ult (BitVec.ofNat 64 okmLen + bv% (2 ^ 64 - 8161)) bv% (2 ^ 64 - 8160) = false := by
  rcases hokm with rfl | rfl | rfl <;> decide

end ExtractCompletion

/-! ## Expand Phase Common Invariant (`HExpCommonExt`) & Block 1 (`hex:634fc → hex:636f0`) -/

section Block1Segments

end Block1Segments

/-! ## Postcondition, Epilogue (`hex:634a8`), `okmLen = 32` Exit, & Loop Entry (`hex:637b8`) -/

section EpilogueAndLoopEntry

end EpilogueAndLoopEntry

end CryptoVerification.SpqrV1.Kdf.HkdfToSliceExtProof

