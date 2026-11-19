/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandHelpersExt -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ContractsExt
import LibsignalBinary.Proofs.CodeLayout

/-!
# Extended-Stack Cut Predicates and Segments for `expand_multi_info`

Defines `extHookStack` cut-point predicates `StateX0pX`–`ExpandPostX` and proves the
Block 1 and loop-entry segments of `GenericHkdf<Hmac<Sha256>>::expand_multi_info` on
`tripleRatchetProgAtExt`.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.LibsignalTripleRatchet.HkdfExt.ExpandExt

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.HkdfExt
open CryptoVerification.LibsignalTripleRatchet.Extract (frame_of_agreesOutside RunsToE S2Frame)
open CryptoVerification.LibsignalTripleRatchet.Expand
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)

attribute [scoped simp, local arm64_norm]
  MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write64_base_off_disjoint
  Memory.read64_write8_base_off_disjoint
  sp_sub_496_eq_esp sp_add_neg496_eq_esp esp_add_496_sub_496
  read8_write64_120_127 CryptoVerification.LibsignalTripleRatchet.Expand.truncate8_ofNat64
  bv32_zero_add bv8_zero_add
  t1_length t2_length t3_length

private theorem runsTo_toE_local {prog : Program} {s₀ : State} {P : State → Prop}
    (h : RunsTo prog s₀ P) : RunsToE prog s₀ P :=
  fun hL => by
    obtain ⟨sf, hst, htr, hP, hLf⟩ := h hL
    exact ⟨sf, hst, htr, hP, hLf⟩

theorem CallingConventionPreserved.x23 {s s' : State} (h : CallingConventionPreserved s s') :
    s'.readReg64 .x23 = s.readReg64 .x23 := h.2.2.2.2.2.1
theorem CallingConventionPreserved.x24 {s s' : State} (h : CallingConventionPreserved s s') :
    s'.readReg64 .x24 = s.readReg64 .x24 := h.2.2.2.2.2.2.1
theorem CallingConventionPreserved.x25 {s s' : State} (h : CallingConventionPreserved s s') :
    s'.readReg64 .x25 = s.readReg64 .x25 := h.2.2.2.2.2.2.2.1
theorem CallingConventionPreserved.x26 {s s' : State} (h : CallingConventionPreserved s s') :
    s'.readReg64 .x26 = s.readReg64 .x26 := h.2.2.2.2.2.2.2.2.1
theorem CallingConventionPreserved.x28 {s s' : State} (h : CallingConventionPreserved s s') :
    s'.readReg64 .x28 = s.readReg64 .x28 := h.2.2.2.2.2.2.2.2.2.2.1

theorem canWrite_esp_64_add {m : Memory} {s₀ : State} {k : ℕ}
    (hrw : m.RW (esp s₀) 496) (hk : k < 64) :
    m.canWrite (esp s₀ + (64#64 + BitVec.ofNat 64 k)) 1 = true ∧
    m.canWrite (esp s₀ + 64#64 + BitVec.ofNat 64 k) 1 = true := by
  have h1 : m.canWrite (esp s₀ + (64#64 + BitVec.ofNat 64 k)) 1 = true :=
    hrw.canWrite_sub (by bv_omega) (by decide)
  refine ⟨h1, ?_⟩
  rw [BitVec.add_assoc]; exact h1

theorem agreesOutside_counter_writes {m₁ : Memory} {s₀ : State} {k : ℕ}
    {b1 c b2 : BitVec 8} (hk : k < 63) :
    AgreesOutside m₁
      ((((m₁.write8 (esp s₀ + 127#64) b1).write8
        (esp s₀ + 240#64) c).write8
        (esp s₀ + 64#64 + BitVec.ofNat 64 k) c).write8
        (esp s₀ + 127#64) b2)
      (esp s₀ + 64#64) 177 := by
  refine agreesOutside_esp_write8 ?_ (by decide)
  refine AgreesOutside.write8 ?_ (by simp only [InRegion]; bv_omega)
  refine agreesOutside_esp_write8 ?_ (by decide)
  exact agreesOutside_esp_write8 (AgreesOutside.rfl' _ _ _) (by decide)

section SegmentsX

end SegmentsX

end CryptoVerification.LibsignalTripleRatchet.HkdfExt.ExpandExt
