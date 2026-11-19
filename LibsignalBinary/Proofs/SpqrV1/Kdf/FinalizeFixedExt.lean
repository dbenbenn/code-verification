/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixedInnerExt -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import LibsignalBinary.Proofs.SpqrV1.Kdf.HooksExt
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import LibsignalBinary.Proofs.CodeLayout

/-!
# Outer Hash, Epilogue, and `Fin3GenRunsToEExt` for `finalize_fixed` (`0x6ce50`)

Completes `finalize_fixed3_gen_runsToE_ext : Fin3GenRunsToEExt img F ext` from
`SpqrKdfHooksExt img F ext` at `finalizeFixed3StackExt` (`16528` B).
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.Kdf

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Extract
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.CodeLayout
open ProofLib.ProgramReflection
open SpqrKdfExt

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

namespace FinalizeFixed3ExtProof

/-! ### Shared Outer Hash & Epilogue (`hex:6cf04 → lr`) -/

private theorem read32_seg4a_mid (m : Memory) (hm fsp off : BitVec 64) (w : BitVec 32)
    (hoff : off = 128#64 ∨ off = 132#64)
    (hd : DisjointRegions fsp 64 hm 0x90)
    (hw : m.read32 (hm + off) = w) :
    (((((((((m.write8 (hm + 63#64) 0#8).write64
      fsp 0#64).write64 (fsp + 8#64) 0#64).write64
      (fsp + 16#64) 0#64).write64 (fsp + 24#64) 0#64).write64
      (fsp + 32#64) 0#64).write64 (fsp + 40#64) 0#64).write64
      (fsp + 48#64) 0#64).write64 (fsp + 56#64) 0#64).read32
      (hm + off) = w := by
  have hag_fsp : AgreesOutside (m.write8 (hm + 63#64) 0#8)
      (((((((((m.write8 (hm + 63#64) 0#8).write64
        fsp 0#64).write64 (fsp + 8#64) 0#64).write64
        (fsp + 16#64) 0#64).write64 (fsp + 24#64) 0#64).write64
        (fsp + 32#64) 0#64).write64 (fsp + 40#64) 0#64).write64
        (fsp + 48#64) 0#64).write64 (fsp + 56#64) 0#64)
      fsp 64 := by agrees_outside_writes
  have hag_63 : AgreesOutside m (m.write8 (hm + 63#64) 0#8) (hm + 63#64) 1 := by
    agrees_outside_writes
  rcases hoff with rfl | rfl <;>
    rw [hag_fsp.read32_eq (hd.sub_right _ ⟨by decide, by bv_omega⟩),
        hag_63.read32_eq (by unfold DisjointRegions; bv_omega), hw]

private def FinPostGenExt (out_bytes : List (BitVec 8)) (s0 s' : State) : Prop :=
  s'.pc = s0.readReg64 .lr ∧
  s'.status = .Running ∧
  CalleeSaved s0 s' ∧
  s'.mem.readBytes (s0.readReg64 .x0) 32 = out_bytes ∧
  S2Frame s0.mem s'.mem (FinRegsExt s0)

end FinalizeFixed3ExtProof

end CryptoVerification.SpqrV1.Kdf
