/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExpandExt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Chain.Defs
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Kdf.HooksExt
import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
import LibsignalBinary.Proofs.CodeLayout

/-!
# `spqr::kdf::hkdf_to_slice`: Contract-Backed Expand Loop and Top-Level `RunsToE`

Proves the `okmLen ∈ {64, 96}` HKDF-Expand loop (`0x636f0 → 0x639e4`) and top-level
`hkdf_to_slice_runsToE_ext` under `HkdfStubsExt` and `S2FrameRO` at stack budget
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

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Extract (RunsToE S2Frame frame_of_agreesOutside)
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.ChainProofs hiding hkdfToSliceName
open CryptoVerification.SpqrV1.Kdf CryptoVerification.SpqrV1.Kdf.SpqrKdfExt CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local simp, local arm64_norm]
  MemWidth.bytes SimdMemSize.bytes Memory.read8_write64_base_off_disjoint Memory.read64_write8_base_off_disjoint
  extractLsb'_56_8_read64 State.readReg64_setMem State.pc_setMem State.sp_setMem State.status_setMem Expand.mem_setMem
  extractLsb'_0_64_zero128 extractLsb'_64_64_zero128 hsp_592_add_96_eq_sp read8_write64_264_271

private theorem s2FrameRO_stk_read64 {roRegs : List (BitVec 64 × ℕ)} {s₀ : State} {m₁ m₂ : Memory}
    {dstOff off : BitVec 64} {dstLen : ℕ}
    (hrw : m₁.RW (hsp s₀) 688)
    (hfr : S2FrameRO roRegs m₁ m₂ [(hsp s₀ + dstOff, dstLen), (hsp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)])
    (h : (off.toNat + 8 ≤ dstOff.toNat ∨ dstOff.toNat + dstLen ≤ off.toNat) ∧ off.toNat + 8 ≤ 688)
    (hdst : dstOff.toNat + dstLen ≤ 688 ∧ dstOff.toNat ≠ off.toNat := by bv_omega) :
    m₂.read64 (hsp s₀ + off) = m₁.read64 (hsp s₀ + off) := by
  rcases h with ⟨_, _⟩; rcases hdst with ⟨_, _⟩
  refine hfr.read64_eq_of_readable (hrw.sub (by bv_omega)).readable fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> (dsimp [extHookStack]; unfold DisjointRegions; bv_omega)

private theorem s2FrameRO_stk_readBytes {roRegs : List (BitVec 64 × ℕ)} {s₀ : State} {m₁ m₂ : Memory}
    {dstOff off : BitVec 64} {dstLen sz : ℕ}
    (hrw : m₁.RW (hsp s₀) 688)
    (hfr : S2FrameRO roRegs m₁ m₂ [(hsp s₀ + dstOff, dstLen), (hsp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)])
    (h : 0 < sz ∧ (off.toNat + sz ≤ dstOff.toNat ∨ dstOff.toNat + dstLen ≤ off.toNat) ∧ off.toNat + sz ≤ 688)
    (hdst : dstOff.toNat + dstLen ≤ 688 ∧ dstOff.toNat ≠ off.toNat := by bv_omega) :
    m₂.readBytes (hsp s₀ + off) sz = m₁.readBytes (hsp s₀ + off) sz := by
  rcases h with ⟨_, _, _⟩; rcases hdst with ⟨_, _⟩
  refine hfr.readBytes_eq (hrw.sub (by bv_omega)).readable (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> (dsimp [extHookStack]; unfold DisjointRegions; bv_omega)

theorem stackAt_hkdfToSlice_ext (s₀ : State) :
    stackAt s₀.sp hkdfToSliceStackExt = memRegion (hsp s₀ - 16928#64) 17616 := by
  unfold stackAt hkdfToSliceStackExt extHookStack hsp; congr 1; bv_omega

end CryptoVerification.SpqrV1.Kdf.HkdfToSliceExtProof
