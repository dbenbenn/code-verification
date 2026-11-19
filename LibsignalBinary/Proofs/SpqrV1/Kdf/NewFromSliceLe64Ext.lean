/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceLe64HalfExt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceSecondHalf -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.SpqrV1.Kdf.HooksExt
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceFirstHalf
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlock -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSlice -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

/-!
# Contract-Backed Second Half and Short-Key Path of `Hmac<Sha256>::new_from_slice`

Proves the shared second half (`0x6748c → lr`) and the full `key.length ≤ 64` `RunsToE` contract
(for both read-only and read-write keys) of `new_from_slice [local#3]`.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.Kdf.Nfs3Ext

open CryptoVerification.LibsignalTripleRatchet (extHookStack)

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.CBC
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalSession.CryptoHmacSha256
open CryptoVerification.LibsignalSessionRepr
open Obj
open CryptoVerification.LibsignalTripleRatchet.Extract (RunsToE S2Frame)
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Kdf.SpqrKdfExt
open CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof hiding
  NfsMemInv3 NfsRegInv3
  read64_write8_stack_iv write64_quad_400_iv write64_quad_0_ivsw
  Nfs3OpadPostHook Nfs3OpadMidState Nfs3OpadEndState
  Nfs3PreCompress2 Nfs3PostCompress2 rodata_sha256IV_0x837d8
open ProofLib.ProgramReflection
open CryptoVerification.CodeLayout

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
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

theorem nfsSavedStack_write64_432_of_s2FrameRO {roRegs : List (BitVec 64 × ℕ)}
    {s₀ : State} {m m' : Memory} {sz : ℕ}
    (hs : NfsSavedStack s₀ (m.write64 (nfsSp s₀ + 432#64) 1#64))
    (hrw_stk : m.RW (nfsSp s₀) 544)
    (hd_stk_ext : DisjointRegions (nfsSp s₀) 544 (nfsSp s₀ - 16384#64) 16384)
    (hf : S2FrameRO roRegs m m'
      [(nfsSp s₀ + 112#64, sz), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hsz : sz ≤ 64) :
    NfsSavedStack s₀ (m'.write64 (nfsSp s₀ + 432#64) 1#64) := by
  have hread (k : BitVec 64) (hk : 464 ≤ k.toNat ∧ k.toNat + 8 ≤ 544) :
      (m'.write64 (nfsSp s₀ + 432#64) 1#64).read64 (nfsSp s₀ + k) =
      (m.write64 (nfsSp s₀ + 432#64) 1#64).read64 (nfsSp s₀ + k) := by
    have h1 : (m'.write64 (nfsSp s₀ + 432#64) 1#64).read64 (nfsSp s₀ + k) = m'.read64 (nfsSp s₀ + k) := by
      refine Frame.read64_eq (agreesOutside_toFrame (AgreesOutside.write64_self m' (nfsSp s₀ + 432#64) 1#64)) ?_
      rcases hk with ⟨hk1, hk2⟩
      clear * - hk1 hk2; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega
    have h2 : (m.write64 (nfsSp s₀ + 432#64) 1#64).read64 (nfsSp s₀ + k) = m.read64 (nfsSp s₀ + k) := by
      refine Frame.read64_eq (agreesOutside_toFrame (AgreesOutside.write64_self m (nfsSp s₀ + 432#64) 1#64)) ?_
      rcases hk with ⟨hk1, hk2⟩
      clear * - hk1 hk2; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega
    rw [h1, h2]
    exact s2FrameRO_hook_read64_stack_eq hf hrw_stk hd_stk_ext hk.2
      (by
        by_cases h0 : sz = 0
        · exact Or.inl h0
        · refine Or.inr ?_
          rcases hk with ⟨hk1, hk2⟩
          clear * - h0 hsz hk1 hk2
          constructor <;> bv_omega)
  exact {
    m432 := Memory.read64_write64_same m' (nfsSp s₀ + 432#64) 1#64
    m464 := (hread 464#64 (by decide)).trans hs.m464
    m472 := (hread 472#64 (by decide)).trans hs.m472
    m480 := (hread 480#64 (by decide)).trans hs.m480
    m496 := (hread 496#64 (by decide)).trans hs.m496
    m504 := (hread 504#64 (by decide)).trans hs.m504
    m512 := (hread 512#64 (by decide)).trans hs.m512
    m520 := (hread 520#64 (by decide)).trans hs.m520
    m528 := (hread 528#64 (by decide)).trans hs.m528
    m536 := (hread 536#64 (by decide)).trans hs.m536
  }

theorem readBytes_64_eq_keyBlock_of_s2FrameRO {roRegs : List (BitVec 64 × ℕ)}
    {sp : BitVec 64} {m1 m2 : Memory} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64)
    (hrw_stk1 : m1.RW sp 544)
    (hd_stk_ext : DisjointRegions sp 544 (sp - 16384#64) 16384)
    (hzero1 : m1.readBytes (sp + 112#64) 64 = List.replicate 64 0#8)
    (hkey2 : m2.readBytes (sp + 112#64) key.length = key)
    (hf12 : S2FrameRO roRegs m1 m2
      [(sp + 112#64, key.length), (sp - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    m2.readBytes (sp + 112#64) 64 = keyBlock key := by
  have h64 : 64 = key.length + (64 - key.length) := (Nat.add_sub_of_le hlen).symm
  have hsplit2 : m2.readBytes (sp + 112#64) 64 =
      m2.readBytes (sp + 112#64) key.length ++
        m2.readBytes ((sp + 112#64) + BitVec.ofNat 64 key.length) (64 - key.length) :=
    (congrArg (m2.readBytes (sp + 112#64)) h64).trans
      (Memory.readBytes_add m2 (sp + 112#64) key.length (64 - key.length))
  have hsplit1 : m1.readBytes (sp + 112#64) 64 =
      m1.readBytes (sp + 112#64) key.length ++
        m1.readBytes ((sp + 112#64) + BitVec.ofNat 64 key.length) (64 - key.length) :=
    (congrArg (m1.readBytes (sp + 112#64)) h64).trans
      (Memory.readBytes_add m1 (sp + 112#64) key.length (64 - key.length))
  have htail1 : m1.readBytes ((sp + 112#64) + BitVec.ofNat 64 key.length) (64 - key.length) =
      List.replicate (64 - key.length) 0#8 := by
    have hd := congrArg (List.drop key.length) (hsplit1.symm.trans hzero1)
    rwa [List.drop_left' (Memory.readBytes_length _ _ _), List.drop_replicate] at hd
  have htail2 : m2.readBytes ((sp + 112#64) + BitVec.ofNat 64 key.length) (64 - key.length) =
      m1.readBytes ((sp + 112#64) + BitVec.ofNat 64 key.length) (64 - key.length) := by
    have hrw_tail : RW m1 ((sp + 112#64) + BitVec.ofNat 64 key.length) (64 - key.length) :=
      hrw_stk1.sub (by clear * - hlen; bv_omega)
    refine Memory.readBytes_congr_region (by omega) fun b hb => ?_
    obtain ⟨hperm_b, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hrw_tail b hb)
    have hr : (m1.perm b).r = true := by rw [hperm_b]; rfl
    refine hf12.1 b hr hlf fun r hr_mem => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
    rcases hr_mem with rfl | rfl
    · clear * - hlen hb
      simp only [InRegion, OutsideRegion] at hb ⊢
      bv_omega
    · have hb_stk : InRegion sp 544 b := by
        clear * - hlen hb
        simp only [InRegion] at hb ⊢
        bv_omega
      exact hd_stk_ext.symm.outside hb_stk (by decide)
  rw [hsplit2, hkey2, htail2, htail1]
  rfl

end CryptoVerification.SpqrV1.Kdf.Nfs3Ext
