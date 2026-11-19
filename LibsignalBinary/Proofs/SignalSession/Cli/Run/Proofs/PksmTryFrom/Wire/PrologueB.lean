/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromLoop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrAt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W0Spec
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ParseLemmas
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.Prologue
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost

/-!
# `PreKeySignalMessage::try_from`: Unified Prologue Theorems (`+0x000 → +0x504 / +0x460`)

Combines the prologue branches with `PreKeyDecodeLoopF4OkW` / `PreKeyDecodeLoopF4Ok` into
`preKey_earlyErr_to_504_wpE` (`+0x000 → +0x504`) and `preKey_valid_to_460_wpW` /
`preKey_valid_to_460_wpX` (`+0x000 → +0x460`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding SepWPp
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

private abbrev SepWPp := @Wire.SepWPp
private abbrev SepWPp.frame_tryFrom := @Wire.SepWPp.frame_tryFrom
private abbrev SepWPp.bind := @Wire.SepWPp.bind
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre
private abbrev SepWPp.bind_frame_entails := @Wire.SepWPp.bind_frame_entails
private abbrev SepWPp.bind_frame_tryFrom := @Wire.SepWPp.bind_frame_tryFrom

attribute [local irreducible] Program.fetch Program.externAt?

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## `ProofLib.SepWPp` Bridge Combinators (for `W0Spec.PreKeyDecodeLoopF4Ok`) -/

private theorem plb_to_proofLib {prog : Program} {ret : BitVec 64} {s : Arm64.State} {P : SepProp}
    {Q Qp : Arm64.State → SepProp → Prop} (h : Wire.SepWPp prog ret s P Q Qp) :
    ProofLib.SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hq, _⟩ | hpan⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf, hq⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

private theorem plb_mono_pre_p {prog : Program} {ret : BitVec 64} {s : Arm64.State}
    {P P' : SepProp} {Q Qp : Arm64.State → SepProp → Prop}
    (hent : P ⊢ P') (h : ProofLib.SepWPp prog ret s P' Q Qp) :
    ProofLib.SepWPp prog ret s P Q Qp := by
  intro R hm hL
  exact h R (Satisfies.mono (sepConj_mono_left hent) hm) hL

private theorem plb_frame_tryFrom_p {prog : Program} {ret : BitVec 64} {s0 s : Arm64.State}
    {P F : SepProp} {Q Q' : Arm64.State → SepProp → Prop}
    (h : ProofLib.SepWPp prog ret s P Q' (tryFromQp s0))
    (hq : ∀ sf Pm, Q' sf Pm → Q sf (Pm ∗ F)) :
    ProofLib.SepWPp prog ret s (P ∗ F) Q (tryFromQp s0) := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  obtain ⟨sf, hsteps, ⟨hpc, hrun, Pm, hmm, hqm⟩ | ⟨hpan, P_f, hmp, hqp⟩ | ⟨_, hoom⟩⟩ :=
    h (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hmm
    exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pm ∗ F, hmm, hq sf Pm hqm⟩⟩
  · rw [← sepConj_assoc] at hmp
    exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, P_f ∗ F, hmp, tryFromQp_frame hqp⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem plb_bind_frame_tryFrom_p {prog : Program} {mid ret : BitVec 64} {s0 s : Arm64.State}
    {P F : SepProp} {Qm Q : Arm64.State → SepProp → Prop}
    (h1 : ProofLib.SepWPp prog mid s P Qm (tryFromQp s0))
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Qm sm Pm →
      ProofLib.SepWPp prog ret sm (Pm ∗ F) Q (tryFromQp s0)) :
    ProofLib.SepWPp prog ret s (P ∗ F) Q (tryFromQp s0) := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, hqm⟩ | ⟨hpan, P_f, hmp, hqp⟩ | ⟨_, hoom⟩⟩ :=
    h1 (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hmm
    obtain ⟨sf, hs', hout⟩ := h2 sm Pm hpc hrun hqm R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hs', hout⟩
  · rw [← sepConj_assoc] at hmp
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, P_f ∗ F, hmp, tryFromQp_frame hqp⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem plb_bind_frame_entails_p {prog : Program} {mid ret : BitVec 64} {s0 s : Arm64.State}
    {P P' F : SepProp} {R_st : Arm64.State → Prop} {Q : Arm64.State → SepProp → Prop}
    (h1 : ProofLib.SepWPp prog mid s P (fun sm Pm => R_st sm ∧ (Pm ⊢ P')) (tryFromQp s0))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → R_st sm →
      ProofLib.SepWPp prog ret sm (P' ∗ F) Q (tryFromQp s0)) :
    ProofLib.SepWPp prog ret s (P ∗ F) Q (tryFromQp s0) := by
  refine plb_bind_frame_tryFrom_p h1 ?_
  intro sm Pm hpc hrun ⟨hr, hent⟩
  exact plb_mono_pre_p (sepConj_mono_left hent) (h2 sm hpc hrun hr)

/-! ## `PreKeyDecodeLoopF4OkW` (`Wire.SepWPp` variant preserving `calleeSavedVRegs`) -/

private theorem plb_ofNat64_cons_sub_one (b0 : BitVec 8) (bs : List (BitVec 8)) :
    BitVec.ofNat 64 (b0 :: bs).length - 1#64 = BitVec.ofNat 64 bs.length := by
  simp only [List.length_cons]
  bv_omega

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
