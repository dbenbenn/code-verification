/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceSecondHalf -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceFirstHalf
import LibsignalBinary.Proofs.CodeLayout

/-!
# Straight-Line Segments of `Hmac<Sha256>::new_from_slice`

Proves the straight-line `RunsTo` segments of
`<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice` on
`tripleRatchetProgAtExt` for keys of length `≤ 64`.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace CryptoVerification.LibsignalTripleRatchet.HkdfExt.NfsSteps

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.CBC
open CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalAesCbc
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalSession.CryptoHmacSha256
open ProofLib.ProgramReflection

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local arm64_norm]
  MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write8_base_off_disjoint
  Memory.read8_write8_base_zero_off
  Memory.read8_write8_base_off_zero
  Memory.read8_write64_base_off_disjoint
  Memory.read8_write64_base_zero_off
  Memory.read8_write64_base_off_zero
  Memory.read8_write64_base_off_inbounds
  Memory.read64_write64_base_off_disjoint
  Memory.read64_write64_base_zero_off
  Memory.read64_write64_base_off_zero
  Memory.read64_write8_base_off_disjoint
  Memory.read64_write8_base_zero_off
  Memory.read64_write8_base_off_zero
  truncate8_zeroExtend_xor_32
  truncate8_zeroExtend_xor_64

@[scoped simp, local arm64_norm]
theorem nfsSp_setMem (s₀ : State) (m : Memory) : nfsSp (s₀.setMem m) = nfsSp s₀ := rfl

theorem NfsSavedStack_setMem_iff {s₀ : State} {m₁ m : Memory} :
    NfsSavedStack (s₀.setMem m₁) m ↔ NfsSavedStack s₀ m := by
  constructor <;> intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ <;>
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem NfsRegInv_setMem_iff {b : BitVec 64} {s₀ s : State} {m₁ : Memory} :
    NfsRegInv b (s₀.setMem m₁) s ↔ NfsRegInv b s₀ s := by
  constructor <;> intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ <;>
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem nfsRegInv_of_cc {b : BitVec 64} {s₀ s s' : State}
    (hR : NfsRegInv b s₀ s) (hcc : CallingConventionPreserved s s') :
    NfsRegInv b s₀ s' :=
  ⟨hcc.1.trans hR.sp_eq,
   hR.sp_align,
   hcc.2.readReg64_x29.trans hR.x29_eq,
   hcc.2.1.trans hR.x19_eq,
   hcc.2.2.1.trans hR.x20_eq,
   hcc.2.2.2.2.1.trans hR.x22_eq,
   hcc.2.2.2.2.2.2.2.1.trans hR.x25_eq,
   hcc.2.2.2.2.2.2.2.2.1.trans hR.x26_eq,
   hcc.2.2.2.2.2.2.2.2.2.1.trans hR.x27_eq⟩

theorem Frame_of_agreesOutside_stack_only {sp : BitVec 64} {m₀ m m' : Memory}
    {off : BitVec 64} {sz : ℕ}
    (hf : Frame m₀ m [(sp, 544)])
    (hA : AgreesOutside m m' (sp + off) sz)
    (hoff : off.toNat + sz ≤ 544) :
    Frame m₀ m' [(sp, 544)] :=
  hf.trans_agreesOutside_sub (b := sp) (n := 544) (by simp) (by clear * - hoff; bv_omega) hA

end CryptoVerification.LibsignalTripleRatchet.HkdfExt.NfsSteps
