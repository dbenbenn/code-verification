/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceGt64SegsExt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceLe64HalfExt -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
import LibsignalBinary.Proofs.SpqrV1.Kdf.HooksExt
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceGen
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceLe64Ext
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSlice -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

/-!
# Contract-Backed Generalized `Hmac<Sha256>::new_from_slice [local#3]`

Contract-backed (`RunsToE` / `S2FrameRO`) finalization of `SHA-256(key)` on the `key.length > 64`
path (`0x6707c → 0x6717c`) and assembly of `new_from_slice3_gen_runsToE_ext`.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.Kdf.Nfs3Ext

open CryptoVerification.LibsignalTripleRatchet (extHookStack)

open Arm64 ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.CBC
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalSession.CryptoHmacSha256
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Extract (RunsToE S2Frame)
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Kdf.SpqrKdfExt
open CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof hiding
  NfsMemInv3 NfsRegInv3
  read64_write8_stack_iv write64_quad_400_iv write64_quad_0_ivsw
  Nfs3OpadPostHook Nfs3OpadMidState Nfs3OpadEndState
  Nfs3PreCompress2 Nfs3PostCompress2 rodata_sha256IV_0x837d8
open CryptoVerification.SpqrV1.Kdf.NewFromSlice3GenProof hiding
  write64_quad_240_iv NfsGt64Common StateG0 StateG1 StateG2a StateG2 StateG3 StateG2b StateG2c StateG4
open ProofLib.ProgramReflection
open CryptoVerification.CodeLayout

@[local simp, local arm64_norm] private theorem extractLsb'_0_64_zero128 : BitVec.extractLsb' 0 64 0#128 = 0#64 := rfl
@[local simp, local arm64_norm] private theorem extractLsb'_64_64_zero128 : BitVec.extractLsb' 64 64 0#128 = 0#64 := rfl
@[local simp, local arm64_norm] private theorem zero8_append_8 :
    (0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 : BitVec 64) = 0#64 := rfl
@[local simp, local arm64_norm] private theorem zero64_append_2 : (0#64 ++ 0#64 : BitVec 128) = 0#128 := rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm]
  MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write8_base_off_disjoint Memory.read8_write8_base_zero_off Memory.read8_write8_base_off_zero
  Memory.read8_write64_base_off_disjoint Memory.read8_write64_base_zero_off Memory.read8_write64_base_off_zero
  Memory.read8_write64_base_off_inbounds
  Memory.read32_write8_base_off_disjoint Memory.read32_write8_base_zero_off Memory.read32_write8_base_off_zero
  Memory.read32_write64_base_off_disjoint Memory.read32_write64_base_zero_off Memory.read32_write64_base_off_zero
  Memory.read64_write8_base_off_disjoint Memory.read64_write8_base_zero_off Memory.read64_write8_base_off_zero
  Memory.read64_write32_base_off_disjoint Memory.read64_write32_base_zero_off Memory.read64_write32_base_off_zero
  Memory.read64_write64_base_off_disjoint Memory.read64_write64_base_zero_off Memory.read64_write64_base_off_zero

theorem s2Frame_pro_112_of_agreesOutside {s₀ : State} {m₁ m₂ : Memory} {off : BitVec 64} {sz : ℕ}
    (h1 : S2Frame (nfsPrologueMem s₀) m₁
      [(nfsSp s₀ + 112#64, 352), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)])
    (h2 : AgreesOutside m₁ m₂ (nfsSp s₀ + off) sz)
    (hoff : 112 ≤ off.toNat ∧ off.toNat + sz ≤ 464) :
    S2Frame (nfsPrologueMem s₀) m₂
      [(nfsSp s₀ + 112#64, 352), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] := by
  refine h1.trans ((S2Frame.of_frame (agreesOutside_toFrame h2)).mono fun a ha r hr => ?_)
  have ha1 := ha (nfsSp s₀ + 112#64, 352) (by simp)
  simp only [List.mem_singleton] at hr
  subst hr
  rcases hoff with ⟨hlo, hhi⟩
  clear * - ha1 hlo hhi
  simp only [OutsideRegion] at ha1 ⊢
  bv_omega

theorem nfsSavedStack_prologue_352_s2 (s₀ : State) (m : Memory)
    (hf : S2Frame (nfsPrologueMem s₀) m
      [(nfsSp s₀ + 112#64, 352), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hrw_stk : s₀.mem.RW (nfsSp s₀) 544)
    (hd_stk_ext : DisjointRegions (nfsSp s₀) 544 (nfsSp s₀ - 16384#64) 16384) :
    NfsSavedStack s₀ (m.write64 (nfsSp s₀ + 432#64) 1#64) := by
  have hrw_pro : (nfsPrologueMem s₀).RW (nfsSp s₀) 544 :=
    (Frame.rw_iff (agreesOutside_toFrame (agreesOutside_nfsPrologueMem s₀)) _ _).mpr hrw_stk
  have hread (k : BitVec 64) (hk : 464 ≤ k.toNat ∧ k.toNat + 8 ≤ 544) :
      m.read64 (nfsSp s₀ + k) = (nfsPrologueMem s₀).read64 (nfsSp s₀ + k) := by
    rcases hk with ⟨hk1, hk2⟩
    refine hf.read64_eq
      (hrw_pro.sub (by clear * - hk1 hk2; bv_omega))
      (fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · clear * - hk1 hk2
      simp only [DisjointRegions]; bv_omega
    · exact (hd_stk_ext.sub_left (nfsSp s₀ + k)
        ⟨by decide, by clear * - hk1 hk2; bv_omega⟩).symm
  refine {
    m432 := by simp (config := { decide := true }) only [arm64_norm]
    m464 := by simp (config := { decide := true }) only [arm64_norm, hread 464#64 (by decide), nfsPrologueMem]
    m472 := by simp (config := { decide := true }) only [arm64_norm, hread 472#64 (by decide), nfsPrologueMem]
    m480 := by simp (config := { decide := true }) only [arm64_norm, hread 480#64 (by decide), nfsPrologueMem]
    m496 := by simp (config := { decide := true }) only [arm64_norm, hread 496#64 (by decide), nfsPrologueMem]
    m504 := by simp (config := { decide := true }) only [arm64_norm, hread 504#64 (by decide), nfsPrologueMem]
    m512 := by simp (config := { decide := true }) only [arm64_norm, hread 512#64 (by decide), nfsPrologueMem]
    m520 := by simp (config := { decide := true }) only [arm64_norm, hread 520#64 (by decide), nfsPrologueMem]
    m528 := by simp (config := { decide := true }) only [arm64_norm, hread 528#64 (by decide), nfsPrologueMem]
    m536 := by simp (config := { decide := true }) only [arm64_norm, hread 536#64 (by decide), nfsPrologueMem]
  }

end CryptoVerification.SpqrV1.Kdf.Nfs3Ext

namespace CryptoVerification.SpqrV1.Kdf

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.LibsignalAesCbc
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Extract (RunsToE S2Frame)
open CryptoVerification.SpqrV1.Kdf.SpqrKdfExt

end CryptoVerification.SpqrV1.Kdf
