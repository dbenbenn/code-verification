/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ContractsExt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceSecondHalf -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.NewFromSliceStepsExt
import ProofLib.SepLogic.HeapIntro
import LibsignalBinary.Proofs.CodeLayout

/-!
# Extended-Stack Verification of `Hmac<Sha256>::new_from_slice`

Proves `NewFromSliceOkExt'` for `<Hmac<Sha256> as KeyInit>::new_from_slice` on
`tripleRatchetProgAtExt` from `memcpy` and `compress256` contracts, along with `RunsToE`
call bridges for HKDF `extract`.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.LibsignalTripleRatchet.HkdfExt.NfsExt

section BlSteps

open Arm64 ProofLib CryptoVerification.LibsignalTripleRatchet

end BlSteps

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.CBC
open CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Extract
open CryptoVerification.LibsignalTripleRatchet.HkdfExt
open CryptoVerification.LibsignalAesCbc
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalSession.CryptoHmacSha256
open CryptoVerification.LibsignalTripleRatchet.HkdfExt.NfsSteps
open ProofLib.ProgramReflection

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr

theorem RunsToE.of_runsTo {prog : Program} {s₀ : State} {P : State → Prop}
    (h : CryptoHmacSha256.RunsTo prog s₀ P) : RunsToE prog s₀ P := by
  intro hL
  obtain ⟨sf, hst, htr, hvregs, hP, hLf⟩ := h hL
  exact ⟨sf, hst, ⟨htr, hvregs⟩, hP, hLf⟩

theorem RunsToE.mono_traceEq {prog : Program} {s₀ : State} {P Q : State → Prop}
    (h : RunsToE prog s₀ P)
    (hPQ : ∀ sf, LibsignalTripleRatchet.TraceEq s₀ sf → P sf → Q sf) :
    RunsToE prog s₀ Q := by
  intro hL
  obtain ⟨sf, hst, htr, hP, hLf⟩ := h hL
  exact ⟨sf, hst, htr, hPQ sf htr hP, hLf⟩

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

theorem s2Frame_hook_read64_stack_eq {sp off k : BitVec 64} {sz : ℕ} {m m' : Memory}
    (hf : S2Frame m m' [(sp + off, sz), (sp - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hrw_stk : m.RW sp 544)
    (hd_stk_ext : DisjointRegions sp 544 (sp - 16384#64) 16384)
    (hk : k.toNat + 8 ≤ 544)
    (hd_off_k : sz = 0 ∨ (sz ≤ (k - off).toNat ∧ 8 ≤ (off - k).toNat)) :
    m'.read64 (sp + k) = m.read64 (sp + k) := by
  have hrw_k : RW m (sp + k) 8 := hrw_stk.sub (by clear * - hk; bv_omega)
  refine Memory.read64_congr fun b hb => ?_
  obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hrw_k b hb)
  have hr : (m.perm b).r = true := by rw [hp]; rfl
  refine hf.1 b hr hlf fun r hr_mem => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
  rcases hr_mem with rfl | rfl
  · rcases hd_off_k with rfl | ⟨h1, h2⟩
    · simp [OutsideRegion]
    · have hd : DisjointRegions (sp + off) sz (sp + k) 8 := by
        clear * - h1 h2; simp only [DisjointRegions]; bv_omega
      exact hd.outside hb (by decide)
  · exact (hd_stk_ext.sub_left (sp + k) ⟨by decide, by clear * - hk; bv_omega⟩).symm.outside hb (by decide)

theorem nfsSavedStack_write64_432_of_s2Frame {s₀ : State} {m m' : Memory} {sz : ℕ}
    (hs : NfsSavedStack s₀ (m.write64 (nfsSp s₀ + 432#64) 1#64))
    (hrw_stk : m.RW (nfsSp s₀) 544)
    (hd_stk_ext : DisjointRegions (nfsSp s₀) 544 (nfsSp s₀ - 16384#64) 16384)
    (hf : S2Frame m m' [(nfsSp s₀ + 112#64, sz), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)])
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
    exact s2Frame_hook_read64_stack_eq hf hrw_stk hd_stk_ext hk.2
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

theorem readBytes_64_eq_keyBlock_of_s2Frame {sp : BitVec 64} {m1 m2 : Memory} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64)
    (hrw_stk1 : m1.RW sp 544)
    (hd_stk_ext : DisjointRegions sp 544 (sp - 16384#64) 16384)
    (hzero1 : m1.readBytes (sp + 112#64) 64 = List.replicate 64 0#8)
    (hkey2 : m2.readBytes (sp + 112#64) key.length = key)
    (hf12 : S2Frame m1 m2 [(sp + 112#64, key.length), (sp - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    m2.readBytes (sp + 112#64) 64 = keyBlock key := by
  have h64 : 64 = key.length + (64 - key.length) := (Nat.add_sub_of_le hlen).symm
  have hsplit2 : m2.readBytes (sp + 112#64) 64 =
      m2.readBytes (sp + 112#64) key.length ++
        m2.readBytes ((sp + 112#64) + BitVec.ofNat 64 key.length) (64 - key.length) :=
    (congrArg (m2.readBytes (sp + 112#64)) h64).trans
      (LibsignalAesCbc.Run.Bytes.readBytes_add m2 (sp + 112#64) key.length (64 - key.length))
  have hsplit1 : m1.readBytes (sp + 112#64) 64 =
      m1.readBytes (sp + 112#64) key.length ++
        m1.readBytes ((sp + 112#64) + BitVec.ofNat 64 key.length) (64 - key.length) :=
    (congrArg (m1.readBytes (sp + 112#64)) h64).trans
      (LibsignalAesCbc.Run.Bytes.readBytes_add m1 (sp + 112#64) key.length (64 - key.length))
  have htail1 : m1.readBytes ((sp + 112#64) + BitVec.ofNat 64 key.length) (64 - key.length) =
      List.replicate (64 - key.length) 0#8 := by
    have hd := congrArg (List.drop key.length) (hsplit1.symm.trans hzero1)
    rwa [List.drop_left' (Memory.readBytes_length _ _ _), List.drop_replicate] at hd
  have htail2 : m2.readBytes ((sp + 112#64) + BitVec.ofNat 64 key.length) (64 - key.length) =
      m1.readBytes ((sp + 112#64) + BitVec.ofNat 64 key.length) (64 - key.length) := by
    have hrw_tail : RW m1 ((sp + 112#64) + BitVec.ofNat 64 key.length) (64 - key.length) :=
      hrw_stk1.sub (by clear * - hlen; bv_omega)
    refine Memory.readBytes_congr_region (by omega) fun b hb => ?_
    obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hrw_tail b hb)
    have hr : (m1.perm b).r = true := by rw [hp]; rfl
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

end CryptoVerification.LibsignalTripleRatchet.HkdfExt.NfsExt

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalAesCbc
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSession.CryptoHmacSha256 (RW nfsSp HmacSt)
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Extract

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr

private theorem hmacInnerInit_eq_innerState_nfs (F : ShaCompress) (key : List (BitVec 8)) :
    hmacInnerInit F key = CryptoHmacSha256.innerState F key := rfl

private theorem hmacOuterInit_eq_outerState_nfs (F : ShaCompress) (key : List (BitVec 8)) :
    hmacOuterInit F key = CryptoHmacSha256.outerState F key := rfl

private theorem isBlock_hmacCoreAt_nil_nfs (F : ShaCompress) (a : BitVec 64) (key : List (BitVec 8)) :
    IsBlock (hmacCoreAt F a key []) a 0x90
      (fun m => HmacSt m a F key []) := by
  have hlen := HkdfExt.shaStateBytes_length
  have b88 := IsBlock.pointsTo64 (a + 0x88#64) 1#64
  have b68 := (IsBlock.pointsToBytes_len (a := a + 0x68#64)
    (hlen (hmacOuterInit F key))).sepConj b88 (by bv_arith) (by decide)
  have b60 := (IsBlock.pointsTo64 (a + 0x60#64) (BitVec.ofNat 64 1)).sepConj b68
    (by bv_arith) (by decide)
  have b40 := (IsBlock.pointsToBytes_len (a := a + 0x40#64)
    (hlen (hmacInnerInit F key))).sepConj b60 (by bv_arith) (by decide)
  have b3f := (IsBlock.pointsTo8 (a + 0x3f#64) (BitVec.ofNat 8 0)).sepConj b40
    (by bv_arith) (by decide)
  have bpad := (IsBlock.memRegion (a + BitVec.ofNat 64 0) 63).sepConj b3f
    (by bv_arith) (by decide)
  have bnil := (IsBlock.pointsToBytes a []).sepConj bpad (by simp) (by decide)
  have b := IsBlock.pure_sepConj (φ := ([] : List (BitVec 8)).length < 64) fun _ => bnil
  refine b.cast rfl fun m => ?_
  simp [HmacSt, hlen, hmacInnerInit_eq_innerState_nfs, hmacOuterInit_eq_outerState_nfs]

private theorem isBlock_nfsResult (F : ShaCompress) (ret : BitVec 64) (key : List (BitVec 8)) :
    IsBlock ((ret ↦₆₄ 0#64) ∗ hmacCoreAt F (ret + 8#64) key []) ret 0x98
      (fun m => m.read64 ret = 0#64 ∧ HmacSt m (ret + 8#64) F key []) :=
  (IsBlock.pointsTo64 ret 0#64).sepConj (isBlock_hmacCoreAt_nil_nfs F (ret + 8#64) key) rfl
    (by decide)

private theorem satisfies_three_blocks_nfs {P1 P2 P3 : SepProp} {b1 b2 b3 : BitVec 64} {n1 n2 n3 : ℕ}
    {Φ1 Φ2 Φ3 : Memory → Prop} {m : Memory}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlock P2 b2 n2 Φ2) (hb3 : IsBlock P3 b3 n3 Φ3)
    (hΦ1 : Φ1 m) (hΦ2 : Φ2 m) (hΦ3 : Φ3 m)
    (hrw1 : RW m b1 n1) (hrw2 : RW m b2 n2) (hrw3 : RW m b3 n3)
    (hd12 : DisjointRegions b1 n1 b2 n2)
    (hd13 : DisjointRegions b1 n1 b3 n3)
    (hd23 : DisjointRegions b2 n2 b3 n3)
    (hn2 : n2 ≤ 2 ^ 64) (hn3 : n3 ≤ 2 ^ 64) :
    m ⊨ P1 ∗ P2 ∗ P3 :=
  HkdfExt.satisfies_three_blocks_opt hb1 hb2 hb3 hΦ1 hΦ2 hΦ3 hrw1 hrw2 hrw3
    (Or.inr (Or.inr hd12)) (Or.inr (Or.inr hd13)) (Or.inr (Or.inr hd23)) hn2 hn3

end CryptoVerification.LibsignalTripleRatchet
