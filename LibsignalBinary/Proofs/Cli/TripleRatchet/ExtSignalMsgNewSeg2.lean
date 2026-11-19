/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.AllocContracts4KExt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewEncodeTags123 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.TripleRatchet.Wire.NewEncodeTags456

/-!
# `<SignalMessage>::new` Segment 2 (`+0x278 .. +0x3dc`)

Proves `AllocContracts4K` segment lemmas for encoding protobuf tags 4, 5, and 6 of
`<SignalMessage>::new`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalTripleRatchet.ExtSignalMsgNewSeg2

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.Cli.LibsignalSpqrV1.M4
open CryptoVerification.InImageLift
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_ult_zero
attribute [local simp] bv_ult_zero

/-! ## `memcpy` and Stack Split Helpers -/

private theorem stackAt_encodeVarint_to_allocHook (sp : BitVec 64) :
    stackAt sp encodeVarintStack =
      stackAt sp allocHookStack ∗ memRegion (sp - 4256#64) 160 := by
  simp only [stackAt, encodeVarintStack, doReserveStack, finishGrowStack, allocHookStack]
  rw [show (4096 + 48 + 48 + 64 : Nat) = 160 + 4096 by decide,
    ProofLib.memRegion_split _ 160 4096 (by decide)]
  have e1 : sp - BitVec.ofNat 64 (160 + 4096) = sp - 4256#64 := by bv_arith
  have e2 : sp - 4256#64 + BitVec.ofNat 64 160 = sp - BitVec.ofNat 64 4096 := by bv_arith
  rw [e1, e2, sepConj_comm]

private theorem sessionMemcpyRegion4K_pre_eq (dst src : BitVec 64) (bs : List (BitVec 8))
    (s : State) (sp_cur : BitVec 64)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hlen : bs.length < 2 ^ 64)
    (hsp : s.sp = sp_cur) :
    (withStack sessionMemcpyRegionSpec allocHookStack).pre (dst, src, bs) s =
      ((src ↦ₛ bs) ∗ memRegion dst bs.length ∗ stackAt sp_cur allocHookStack) := by
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen]
  simp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, hx0, hx1, hx2, hsp,
    htoNat, and_self, pure_true, emp_sepConj, sepConj_assoc]
  ac_rfl

private theorem sessionMemcpyRegion4K_post_eq (dst src : BitVec 64) (bs : List (BitVec 8))
    (s0 sf : State) (sp_val : BitVec 64) (hsp0 : s0.sp = sp_val) :
    (withStack sessionMemcpyRegionSpec allocHookStack).post (dst, src, bs) s0 sf =
      (⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
        (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt sp_val allocHookStack) := by
  simp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, hsp0, sepConj_assoc]

private theorem signalMessageNew_seg2_seq_wpp' {prog : Program} {mid ret : BitVec 64}
    {s0 s : State} {P P1 F : SepProp} {P2 : State → SepProp} {φ : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (htr : s.trace = s0.trace)
    (h1 : SepWPp prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2 sm)) (PanicAllocPost s))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → φ sm →
      SepWPp prog ret sm (P2 sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨hpan_s, P_m, hmm, hp⟩ | ⟨_, hoom⟩⟩ :=
    h1 (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P2 sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ := h2 sm hpcm hrunm hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · have hm' : sm.mem ⊨ (P_m ∗ F) ∗ R := by rw [sepConj_assoc]; exact hmm
    have halloc := hp (F ∗ R) hmm
    rw [sepConj_assoc, satisfies_pure_sepConj] at halloc
    have halloc0 : allocFailedIn s0 sm ∧ s0.trace <+: sm.trace := by
      simpa [allocFailedIn, htr] using halloc.1
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_s, P_m ∗ F, hm', hpan sm (P_m ∗ F) halloc0⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

/-! ## Encode Tag 4 (`+0x278 → +0x2e0`) -/

end CryptoVerification.Cli.LibsignalTripleRatchet.ExtSignalMsgNewSeg2
