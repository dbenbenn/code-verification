/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.FrameROExt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceGt64 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.SpqrV1.Kdf.HooksExt
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlock -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSlice -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceGen -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

/-!
# Contract-Backed Long-Key Prefix Segments of `Hmac<Sha256>::new_from_slice`

Contract-backed (`RunsToE` / `S2Frame`) symbolic execution of the `key.length > 64` branch from
entry (`0x66fa0`) through tail padding (`0x6707c`).
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
  write64_quad_240_iv NfsGt64Common StateG0 StateG1 StateG2a StateG2 StateG3 StateG2b StateG2c
open ProofLib.ProgramReflection
open CryptoVerification.CodeLayout

attribute [-arm64_norm, -simp] CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof.read64_write8_stack_iv

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

private theorem nfs_ule_65_true {x : BitVec 64} (h : 64 < x.toNat) :
    BitVec.ule 0x41#64 x = true := by
  simp [BitVec.ule]; omega

private theorem hmacRunsTo_to_runsToE {prog : Program} {s₀ : State} {P : State → Prop}
    (h : RunsTo prog s₀ P) : RunsToE prog s₀ P := by
  intro hL
  obtain ⟨sf, hst, htr, hvregs, hP, hLf⟩ := h hL
  exact ⟨sf, hst, ⟨htr, hvregs⟩, hP, hLf⟩

private theorem s2Frame_readBytes_eq_of_readable {m₁ m₂ : Memory} {regs : List (BitVec 64 × ℕ)}
    (h : S2Frame m₁ m₂ regs) {a : BitVec 64} {n : ℕ} (hread : m₁.Readable a n)
    (hd : ∀ r ∈ regs, DisjointRegions r.1 r.2 a n) (hn : n ≤ 2 ^ 64 := by decide) :
    m₂.readBytes a n = m₁.readBytes a n := by
  refine Memory.readBytes_congr_region hn fun b hb => ?_
  exact h.1 b (hread b hb).1 (hread b hb).2 fun r hr_mem => (hd r hr_mem).outside hb hn

private theorem s2Frame_hook_readBytes_stack_eq' {sp off k : BitVec 64} {sz n : ℕ} {m m' : Memory}
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

private theorem s2Frame_hook_read64_stack_eq' {sp off k : BitVec 64} {sz : ℕ} {m m' : Memory}
    (hf : S2Frame m m' [(sp + off, sz), (sp - BitVec.ofNat 64 extHookStack, extHookStack)])
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

/-! ## `S2Frame` Helpers and `NfsGt64CommonExt` (`hex:66fe8 .. hex:670e4`) -/

theorem s2Frame_zero_of_agreesOutside {s₀ : State} {m₁ m₂ : Memory} {off : BitVec 64} {sz : ℕ}
    (h1 : S2Frame (nfsZeroMem s₀) m₁
      [(nfsSp s₀ + 176#64, 288), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)])
    (h2 : AgreesOutside m₁ m₂ (nfsSp s₀ + off) sz)
    (hoff : 176 ≤ off.toNat ∧ off.toNat + sz ≤ 464) :
    S2Frame (nfsZeroMem s₀) m₂
      [(nfsSp s₀ + 176#64, 288), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] := by
  refine h1.trans ((S2Frame.of_frame (agreesOutside_toFrame h2)).mono fun a ha r hr => ?_)
  have ha1 := ha (nfsSp s₀ + 176#64, 288) (by simp)
  simp only [List.mem_singleton] at hr
  subst hr
  rcases hoff with ⟨hlo, hhi⟩
  clear * - ha1 hlo hhi
  simp only [OutsideRegion] at ha1 ⊢
  bv_omega

theorem s2Frame_zero_of_hook {s₀ : State} {m₁ m₂ : Memory} {off : BitVec 64} {sz : ℕ}
    (h1 : S2Frame (nfsZeroMem s₀) m₁
      [(nfsSp s₀ + 176#64, 288), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)])
    (h2 : S2Frame m₁ m₂
      [(nfsSp s₀ + off, sz), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hoff : 176 ≤ off.toNat ∧ off.toNat + sz ≤ 464) :
    S2Frame (nfsZeroMem s₀) m₂
      [(nfsSp s₀ + 176#64, 288), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] := by
  refine h1.trans (h2.mono fun a ha r hr => ?_)
  have ha1 := ha (nfsSp s₀ + 176#64, 288) (by simp)
  have ha2 := ha (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rcases hoff with ⟨hlo, hhi⟩
    clear * - ha1 hlo hhi
    simp only [OutsideRegion] at ha1 ⊢
    bv_omega
  · exact ha2

theorem s2Frame_pro_112_of_zero {s₀ : State} {m : Memory}
    (h : S2Frame (nfsZeroMem s₀) m
      [(nfsSp s₀ + 176#64, 288), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    S2Frame (nfsPrologueMem s₀) m
      [(nfsSp s₀ + 112#64, 352), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] := by
  have h0 : S2Frame (nfsPrologueMem s₀) (nfsZeroMem s₀)
      [(nfsSp s₀ + 112#64, 352), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] := by
    refine (S2Frame.of_frame (agreesOutside_toFrame (agreesOutside_nfsZeroMem s₀))).mono fun a ha r hr => ?_
    have ha1 := ha (nfsSp s₀ + 112#64, 352) (by simp)
    simp only [List.mem_singleton] at hr
    subst hr
    clear * - ha1
    simp only [OutsideRegion] at ha1 ⊢
    bv_omega
  refine h0.trans (h.mono fun a ha r hr => ?_)
  have ha1 := ha (nfsSp s₀ + 112#64, 352) (by simp)
  have ha2 := ha (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · clear * - ha1
    simp only [OutsideRegion] at ha1 ⊢
    bv_omega
  · exact ha2

theorem s2Frame_16928_of_pro_112 {s₀ : State} {m : Memory}
    (h : S2Frame (nfsPrologueMem s₀) m
      [(nfsSp s₀ + 112#64, 352), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    S2Frame s₀.mem m [(s₀.sp - 16928#64, 16928)] := by
  have hpro : S2Frame s₀.mem (nfsPrologueMem s₀) [(s₀.sp - 16928#64, 16928)] := by
    refine (S2Frame.of_frame (agreesOutside_toFrame (agreesOutside_nfsPrologueMem s₀))).mono fun a ha r hr => ?_
    have ha1 := ha (s₀.sp - 16928#64, 16928) (by simp)
    simp only [List.mem_singleton] at hr
    subst hr
    clear * - ha1
    simp only [OutsideRegion, nfsSp] at ha1 ⊢
    bv_omega
  refine hpro.trans (h.mono fun a ha r hr => ?_)
  have ha1 := ha (s₀.sp - 16928#64, 16928) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · clear * - ha1
    simp only [OutsideRegion, nfsSp] at ha1 ⊢
    bv_omega
  · clear * - ha1
    simp only [OutsideRegion, nfsSp, extHookStack] at ha1 ⊢
    bv_omega

theorem s2Frame_16928_of_zero {s₀ : State} {m : Memory}
    (h : S2Frame (nfsZeroMem s₀) m
      [(nfsSp s₀ + 176#64, 288), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    S2Frame s₀.mem m [(s₀.sp - 16928#64, 16928)] :=
  s2Frame_16928_of_pro_112 (s2Frame_pro_112_of_zero h)

theorem s2Frame_out_16928_of_16928 {s₀ : State} {m₁ m₂ : Memory}
    (h : S2Frame m₁ m₂ [(s₀.sp - 16928#64, 16928)]) :
    S2Frame m₁ m₂ [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)] := by
  refine h.mono fun a ha r hr => ?_
  simp only [List.mem_singleton] at hr
  subst hr
  exact ha (s₀.sp - 16928#64, 16928) (by simp)

theorem disj_stk_extstk_of_disj_16928 {s₀ : State} {a : BitVec 64} {n : ℕ}
    (hd : DisjointRegions a n (s₀.sp - 16928#64) 16928) :
    DisjointRegions (nfsSp s₀) 544 (nfsSp s₀ - 16384#64) 16384 := by
  clear * - hd
  simp only [DisjointRegions, nfsSp] at hd ⊢
  bv_omega

/-! ## Cut `G0Ext` (`hex:66fe8`) and Prologue (`hex:66fa0 → hex:66fe8`) -/

theorem readBytes_64_after_pad_memset_s2 {m_copy m' : Memory} {sp : BitVec 64}
    {tail : List (BitVec 8)}
    (htail_copy : m_copy.readBytes (sp + 288#64) tail.length = tail)
    (htail_lt : tail.length < 64)
    (hrw_stk : (m_copy.write8 (sp + 288#64 + BitVec.ofNat 64 tail.length) 128#8).RW (sp) 544)
    (hd_stk_ext : DisjointRegions sp 544 (sp - 16384#64) 16384)
    (hdst : m'.readBytes (sp + 288#64 + BitVec.ofNat 64 tail.length + 1#64) (63 - tail.length) =
      List.replicate (63 - tail.length) 0#8)
    (hfr : S2Frame (m_copy.write8 (sp + 288#64 + BitVec.ofNat 64 tail.length) 128#8) m'
      [(sp + 288#64 + BitVec.ofNat 64 tail.length + 1#64, 63 - tail.length),
       (sp - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    m'.readBytes (sp + 288#64) 64 = innerPadBlock1 tail := by
  set m_pre := m_copy.write8 (sp + 288#64 + BitVec.ofNat 64 tail.length) 128#8
  set m_hook := m_pre.writeBytes (sp + 288#64 + BitVec.ofNat 64 tail.length + 1#64)
    (List.replicate (63 - tail.length) 0#8)
  have hsplit : 64 = (tail.length + 1) + (63 - tail.length) := by omega
  have hadd1 := CryptoVerification.LibsignalAesCbc.Run.Bytes.readBytes_add m' (sp + 288#64) (tail.length + 1) (63 - tail.length)
  have hadd2 := CryptoVerification.LibsignalAesCbc.Run.Bytes.readBytes_add m_hook (sp + 288#64) (tail.length + 1) (63 - tail.length)
  rw [← hsplit] at hadd1 hadd2
  have h_addr : sp + 288#64 + BitVec.ofNat 64 (tail.length + 1) =
      sp + 288#64 + BitVec.ofNat 64 tail.length + 1#64 := by
    clear * - htail_lt; bv_omega
  rw [h_addr] at hadd1 hadd2
  have h_hi_hook : m_hook.readBytes (sp + 288#64 + BitVec.ofNat 64 tail.length + 1#64) (63 - tail.length) =
      List.replicate (63 - tail.length) 0#8 :=
    CryptoVerification.LibsignalAesCbc.Run.Layout.readBytes_writeBytes_eq m_pre
      (sp + 288#64 + BitVec.ofNat 64 tail.length + 1#64)
      (List.replicate (63 - tail.length) 0#8) (63 - tail.length) List.length_replicate (by omega)
  have hag_ms : AgreesOutside m_pre m_hook
      (sp + 288#64 + BitVec.ofNat 64 tail.length + 1#64) (63 - tail.length) := by
    have hlen : (List.replicate (63 - tail.length) 0#8).length = 63 - tail.length := List.length_replicate
    rw [← hlen]
    exact ProofLib.agreesOutside_writeBytes m_pre _ _
  have hd_lo : DisjointRegions (sp + 288#64 + BitVec.ofNat 64 tail.length + 1#64) (63 - tail.length)
      (sp + 288#64) (tail.length + 1) := by
    clear * - htail_lt; simp only [DisjointRegions]; bv_omega
  have hd_lo_ext : DisjointRegions (sp - BitVec.ofNat 64 extHookStack) extHookStack
      (sp + 288#64) (tail.length + 1) :=
    (hd_stk_ext.sub_left (sp + 288#64) ⟨by omega, by clear * - htail_lt; bv_omega⟩).symm
  have h_lo_m' : m'.readBytes (sp + 288#64) (tail.length + 1) =
      m_pre.readBytes (sp + 288#64) (tail.length + 1) :=
    s2Frame_readBytes_eq_of_readable hfr
      (hrw_stk.sub (by clear * - htail_lt; bv_omega)).readable
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hd_lo
        · exact hd_lo_ext)
      (by omega)
  have h_lo_hook : m_hook.readBytes (sp + 288#64) (tail.length + 1) =
      m_pre.readBytes (sp + 288#64) (tail.length + 1) :=
    (agreesOutside_toFrame hag_ms).readBytes_eq (by simp [hd_lo]) (by omega)
  have h_eq : m'.readBytes (sp + 288#64) 64 = m_hook.readBytes (sp + 288#64) 64 := by
    rw [hadd1, hadd2, h_lo_m', h_lo_hook, hdst, h_hi_hook]
  rw [h_eq]
  exact readBytes_64_after_pad_memset_lt64 m_copy (sp + 288#64) tail htail_copy htail_lt

end CryptoVerification.SpqrV1.Kdf.Nfs3Ext
