/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Kdf.FrameROExt -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlock
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceFirstHalf
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceFirstHalf
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSlice -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

/-!
# Contract-Backed First Half of `Hmac<Sha256>::new_from_slice [local#3]`

Contract-backed straight-line segments (`0x66fa0 → 0x6748c`) for the `key.length ≤ 64` prologue,
`memcpy`, and ipad XOR chunks of `new_from_slice [local#3]`.
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

/-! ## `RunsToE` / `S2Frame` / `S2FrameRO` Stack-Frame Bridge Lemmas (`extHookStack = 16384`) -/

theorem RunsToE.of_hmacRunsTo {prog : Program} {s₀ : State} {P : State → Prop}
    (h : RunsTo prog s₀ P) : RunsToE prog s₀ P := by
  intro hL
  obtain ⟨sf, hst, htr, hvregs, hP, hLf⟩ := h hL
  exact ⟨sf, hst, ⟨htr, hvregs⟩, hP, hLf⟩

theorem S2Frame.readBytes_eq_of_readable {m₁ m₂ : Memory} {regs : List (BitVec 64 × ℕ)}
    (h : S2Frame m₁ m₂ regs) {a : BitVec 64} {n : ℕ} (hread : m₁.Readable a n)
    (hd : ∀ r ∈ regs, DisjointRegions r.1 r.2 a n) (hn : n ≤ 2 ^ 64 := by decide) :
    m₂.readBytes a n = m₁.readBytes a n := by
  refine Memory.readBytes_congr_region hn fun b hb => ?_
  exact h.1 b (hread b hb).1 (hread b hb).2 fun r hr_mem => (hd r hr_mem).outside hb hn

theorem s2Frame_of_r7b_frame_16928 {out sp : BitVec 64} {m₁ m₂ : Memory}
    (hf : Frame m₁ m₂ [(out, 0x98), (sp - 544#64, 544)]) :
    S2Frame m₁ m₂ [(out, 0x98), (sp - 16928#64, 16928)] := by
  refine (S2Frame.of_frame hf).mono fun a ha r hr => ?_
  have hout := ha (out, 0x98) (by simp)
  have hstk := ha (sp - 16928#64, 16928) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hout
  · clear * - hstk
    simp only [OutsideRegion] at hstk ⊢
    bv_omega

theorem s2Frame_of_r7b_stack_frame_16928 {out sp : BitVec 64} {m₁ m₂ : Memory}
    (hf : Frame m₁ m₂ [(sp - 544#64, 544)]) :
    S2Frame m₁ m₂ [(out, 0x98), (sp - 16928#64, 16928)] := by
  refine (S2Frame.of_frame hf).mono fun a ha r hr => ?_
  have hstk := ha (sp - 16928#64, 16928) (by simp)
  simp only [List.mem_singleton] at hr
  subst hr
  clear * - hstk
  simp only [OutsideRegion] at hstk ⊢
  bv_omega

theorem s2Frame_of_hook_frame_16928 {out sp nfsSp_sp off : BitVec 64} {sz : ℕ} {m₁ m₂ : Memory}
    (hf : S2Frame m₁ m₂ [(nfsSp_sp + off, sz), (nfsSp_sp - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hsp : nfsSp_sp = sp - 544#64)
    (hoff : off.toNat + sz ≤ 544) :
    S2Frame m₁ m₂ [(out, 0x98), (sp - 16928#64, 16928)] := by
  subst hsp
  refine hf.mono fun a ha r hr => ?_
  have hstk := ha (sp - 16928#64, 16928) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · clear * - hstk hoff
    simp only [OutsideRegion] at hstk ⊢
    bv_omega
  · clear * - hstk
    simp only [OutsideRegion, extHookStack] at hstk ⊢
    bv_omega

theorem s2FrameRO_of_hook_frame_16928 {roRegs : List (BitVec 64 × ℕ)}
    {out sp nfsSp_sp off : BitVec 64} {sz : ℕ} {m₁ m₂ : Memory}
    (hf : S2FrameRO roRegs m₁ m₂ [(nfsSp_sp + off, sz), (nfsSp_sp - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hsp : nfsSp_sp = sp - 544#64)
    (hoff : off.toNat + sz ≤ 544) :
    S2FrameRO roRegs m₁ m₂ [(out, 0x98), (sp - 16928#64, 16928)] := by
  subst hsp
  refine hf.mono fun a ha r hr => ?_
  have hstk := ha (sp - 16928#64, 16928) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · clear * - hstk hoff
    simp only [OutsideRegion] at hstk ⊢
    bv_omega
  · clear * - hstk
    simp only [OutsideRegion, extHookStack] at hstk ⊢
    bv_omega

theorem s2Frame_hook_readBytes_stack_eq {sp off k : BitVec 64} {sz n : ℕ} {m m' : Memory}
    (hf : S2Frame m m' [(sp + off, sz), (sp - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hrw_stk : m.RW sp 544)
    (hd_stk_ext : DisjointRegions sp 544 (sp - 16384#64) 16384)
    (hk : 0 < n ∧ k.toNat + n ≤ 544)
    (hd_off_k : sz ≤ (k - off).toNat ∧ n ≤ (off - k).toNat) :
    m'.readBytes (sp + k) n = m.readBytes (sp + k) n := by
  have hrw_k : RW m (sp + k) n := hrw_stk.sub (by have := hk.2; clear * - this; bv_omega)
  refine hf.readBytes_eq hrw_k (fun r hr => ?_) (by have := hk.2; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rcases hd_off_k with ⟨h1, h2⟩
    clear * - h1 h2
    simp only [DisjointRegions]
    bv_omega
  · exact (hd_stk_ext.sub_left (sp + k) ⟨hk.1, by have := hk.2; clear * - this; bv_omega⟩).symm

theorem s2FrameRO_hook_read64_stack_eq {roRegs : List (BitVec 64 × ℕ)}
    {sp off k : BitVec 64} {sz : ℕ} {m m' : Memory}
    (hf : S2FrameRO roRegs m m' [(sp + off, sz), (sp - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hrw_stk : m.RW sp 544)
    (hd_stk_ext : DisjointRegions sp 544 (sp - 16384#64) 16384)
    (hk : k.toNat + 8 ≤ 544)
    (hd_off_k : sz = 0 ∨ (sz ≤ (k - off).toNat ∧ 8 ≤ (off - k).toNat)) :
    m'.read64 (sp + k) = m.read64 (sp + k) := by
  have hrw_k : RW m (sp + k) 8 := hrw_stk.sub (by clear * - hk; bv_omega)
  refine Memory.read64_congr fun b hb => ?_
  obtain ⟨hperm_b, hlf_b⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hrw_k b hb)
  have hr : (m.perm b).r = true := by rw [hperm_b]; rfl
  refine hf.1 b hr hlf_b fun r hr_mem => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
  rcases hr_mem with rfl | rfl
  · rcases hd_off_k with rfl | ⟨h1, h2⟩
    · simp [OutsideRegion]
    · have hd : DisjointRegions (sp + off) sz (sp + k) 8 := by
        clear * - h1 h2; simp only [DisjointRegions]; bv_omega
      exact hd.outside hb (by decide)
  · exact (hd_stk_ext.sub_left (sp + k) ⟨by decide, by clear * - hk; bv_omega⟩).symm.outside hb (by decide)

theorem s2Frame_hook_read64_stack_eq {sp off k : BitVec 64} {sz : ℕ} {m m' : Memory}
    (hf : S2Frame m m' [(sp + off, sz), (sp - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hrw_stk : m.RW sp 544)
    (hd_stk_ext : DisjointRegions sp 544 (sp - 16384#64) 16384)
    (hk : k.toNat + 8 ≤ 544)
    (hd_off_k : sz = 0 ∨ (sz ≤ (k - off).toNat ∧ 8 ≤ (off - k).toNat)) :
    m'.read64 (sp + k) = m.read64 (sp + k) :=
  s2FrameRO_hook_read64_stack_eq (S2FrameRO.of_s2frame (roRegs := []) hf) hrw_stk hd_stk_ext hk hd_off_k

theorem nfsSavedStack_setMem_iff {s₀ : State} {m₁ m : Memory} :
    NfsSavedStack (s₀.setMem m₁) m ↔ NfsSavedStack s₀ m := by
  constructor <;> intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ <;>
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem frame_of_agreesOutside_stack_only {sp : BitVec 64} {m₀ m m' : Memory}
    {off : BitVec 64} {sz : ℕ}
    (hf : Frame m₀ m [(sp, 544)])
    (hA : AgreesOutside m m' (sp + off) sz)
    (hoff : off.toNat + sz ≤ 544) :
    Frame m₀ m' [(sp, 544)] :=
  hf.trans_agreesOutside_sub (b := sp) (n := 544) (by simp) (by clear * - hoff; bv_omega) hA

end CryptoVerification.SpqrV1.Kdf.Nfs3Ext
