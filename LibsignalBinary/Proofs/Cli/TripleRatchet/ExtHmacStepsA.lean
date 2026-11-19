/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceFirstHalf
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceSecondHalf
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ContractsExt
import LibsignalBinary.Proofs.CodeLayout

/-!
# `crypto::hmac_sha256` Symbolic-Offset Segments (`seg0a` through `seg1b1_post`)

Part A of the `RunsToE (tripleRatchetProgAtExt img.base ext)` segment proofs for
`libsignal_protocol::crypto::hmac_sha256` at `extHookStack` (`16384` B).
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.Cli.LibsignalTripleRatchet.ExtHmacX

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.CBC CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet.Extract (RunsToE S2Frame)
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalSession.CryptoHmacSha256

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff

theorem runsToE_hmac {prog : Program} {s : State} {P : State → Prop}
    (h : _root_.CryptoVerification.LibsignalSession.CryptoHmacSha256.RunsTo prog s P) : RunsToE prog s P := by
  intro hL
  obtain ⟨sf, hst, htr, hvregs, hP, hLf⟩ := h hL
  exact ⟨sf, hst, ⟨htr, hvregs⟩, hP, hLf⟩

attribute [local arm64_norm]
  Memory.read128 Memory.write128 MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write8_base_off_disjoint
  Memory.read8_write8_base_zero_off
  Memory.read8_write8_base_off_zero
  Memory.read8_write64_base_off_disjoint
  Memory.read8_write64_base_zero_off
  Memory.read8_write64_base_off_zero
  Memory.read8_write64_base_off_inbounds
  read32_write8_base_off_disjoint

theorem hmacSaved_of_s2Frame {s₀ : State} {hsp : BitVec 64} {m₁ m₂ : Memory}
    {rs : List (BitVec 64 × ℕ)}
    (hs : HmacSaved s₀ hsp m₁)
    (hrw : RW m₁ (hsp + 384#64) 96)
    (hf : S2Frame m₁ m₂ rs)
    (hd : ∀ r ∈ rs, DisjointRegions r.1 r.2 (hsp + 384#64) 96) :
    HmacSaved s₀ hsp m₂ := by
  rcases hs with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  have sub8 (off : BitVec 64) (hoff : (off - (hsp + 384#64)).toNat + 8 ≤ 96) :
      m₂.read64 off = m₁.read64 off := by
    have hd_off : ∀ r ∈ rs, DisjointRegions r.1 r.2 off 8 :=
      fun r hr => (hd r hr).sub_right off ⟨by decide, hoff⟩
    exact hf.read64_eq (hrw.sub hoff) hd_off
  exact ⟨(sub8 (hsp + 384#64) (by clear * -; bv_omega)).trans h1,
         (sub8 (hsp + 392#64) (by clear * -; bv_omega)).trans h2,
         (sub8 (hsp + 400#64) (by clear * -; bv_omega)).trans h3,
         (sub8 (hsp + 416#64) (by clear * -; bv_omega)).trans h4,
         (sub8 (hsp + 424#64) (by clear * -; bv_omega)).trans h5,
         (sub8 (hsp + 432#64) (by clear * -; bv_omega)).trans h6,
         (sub8 (hsp + 440#64) (by clear * -; bv_omega)).trans h7,
         (sub8 (hsp + 448#64) (by clear * -; bv_omega)).trans h8,
         (sub8 (hsp + 456#64) (by clear * -; bv_omega)).trans h9,
         (sub8 (hsp + 464#64) (by clear * -; bv_omega)).trans h10,
         (sub8 (hsp + 472#64) (by clear * -; bv_omega)).trans h11⟩

theorem s2Frame_trans_r7b_stack1024 {sp : BitVec 64} {m₀ m₁ m₂ : Memory}
    (hf1 : S2Frame m₀ m₁ [(sp - 17408#64, 17408)])
    (hf2 : Frame m₁ m₂ [(sp - 1024#64, 1024)]) :
    S2Frame m₀ m₂ [(sp - 17408#64, 17408)] := by
  refine hf1.trans ((S2Frame.of_frame hf2).mono fun a ha r hr => ?_)
  have h1 := ha (sp - 17408#64, 17408) (by simp)
  simp only [List.mem_singleton] at hr
  subst hr
  unfold OutsideRegion at h1 ⊢
  clear * - h1; bv_omega

theorem s2Frame_trans_pair_stk17408 {sp : BitVec 64} {m₀ m₁ m₂ : Memory}
    {a₁ : BitVec 64} {n₁ : ℕ} {a₂ : BitVec 64} {n₂ : ℕ}
    (hf1 : S2Frame m₀ m₁ [(sp - 17408#64, 17408)])
    (hf2 : S2Frame m₁ m₂ [(a₁, n₁), (a₂, n₂)])
    (hsub₁ : (a₁ - (sp - 17408#64)).toNat + n₁ ≤ 17408)
    (hsub₂ : (a₂ - (sp - 17408#64)).toNat + n₂ ≤ 17408) :
    S2Frame m₀ m₂ [(sp - 17408#64, 17408)] := by
  refine hf1.trans (hf2.mono fun a ha => ?_)
  have h1 := ha (sp - 17408#64, 17408) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  unfold OutsideRegion at h1 ⊢
  refine ⟨by clear * - h1 hsub₁; bv_omega, by clear * - h1 hsub₂; bv_omega⟩

theorem s2Frame_writeBytes_out_stk17408 {out sp : BitVec 64} {m₀ m : Memory}
    (hf : S2Frame m₀ m [(sp - 17408#64, 17408)])
    (bs : List (BitVec 8)) (hlen : bs.length = 32) :
    S2Frame m₀ (m.writeBytes out bs) [(out, 32), (sp - 17408#64, 17408)] := by
  have hag : AgreesOutside m (m.writeBytes out bs) out 32 :=
    hlen ▸ ProofLib.AgreesOutside.writeBytes_self m out bs
  refine (hf.mono fun a ha r hr => ha r (List.mem_cons_of_mem _ hr)).trans ?_
  exact S2Frame.of_frame (Frame.trans_agreesOutside (Frame.refl m _) hag)

structure StateH5X (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (byte : BitVec 8) (s₀ s : State) : Prop where
  pc_eq   : s.pc = s₀.readReg64 .lr
  status  : s.status = .Running
  callee  : CalleeSaved s₀ s
  out_eq  : s.mem.readBytes (s₀.readReg64 .x0) 32 = hmacWith F key [byte]
  frame   : S2Frame s₀.mem s.mem [(s₀.readReg64 .x0, 32), (s₀.sp - 17408#64, 17408)]

end CryptoVerification.Cli.LibsignalTripleRatchet.ExtHmacX
