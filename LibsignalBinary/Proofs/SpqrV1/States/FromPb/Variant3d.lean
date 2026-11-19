/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3c -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3b
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 3 (`Ct1Received`, `+692`) — Post-`uc` Composition

Post-`<EkSentCt1Received>::from_pb` and post-`<PolyEncoder>::from_pb` compositions for
`InnerState.ct1Received`.
-/

public section

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## `SepWPp` Call Combinator & Result Unpacking Helpers -/

theorem v3_sepWPp_call {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P_step F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P_step ∗ R') → (s.mem ⊨ spec.pre x s ∗ R'))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)))
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog target_pc s (P_step ∗ F) post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  refine SepWPp.call (x := x) (F := F) hcall hpc hrun hsp_align hlr
    (fun R' hm => by rw [sepConj_assoc] at hm; exact hpre (F ∗ R') hm)
    (fun sf code R' _ hm => by rw [hexit_eq] at hm; exact not_satisfies_false_sepConj hm)
    (hoom := fun sf R' _ hm => by rw [hoom_eq] at hm; exact False.elim (not_satisfies_false_sepConj hm))
    (fun sf _ hm => Satisfies.mono (sepConj_mono_left (hpan sf)) hm)
    (fun sf hpcf hrunf hspf hcsf => hnext sf hpcf hrunf hspf hcsf)

private theorem v3cr_loByte_shift8 (u0 : BitVec 64) :
    EncoderFromPb.loByte (u0 <<< 8) = 0#8 := by
  dsimp only [EncoderFromPb.loByte]; bv_kernel

private theorem v3cr_hiBytes7_shift8 (u0 : BitVec 64) :
    EncoderFromPb.hiBytes7 (u0 <<< 8) = EncoderFromPb.loBytes7 u0 := by
  simp only [EncoderFromPb.hiBytes7, EncoderFromPb.loBytes7, unpack64, List.drop, List.take,
    List.cons.injEq]
  refine ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
    by bv_kernel, by bv_kernel, by bv_kernel, trivial⟩

theorem v3cr_ekResult_err_unpack (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (e : StatesError) :
    ekSentCt1ReceivedResultAt A (F := F) a (.error e) ⊢
      ∃∗ w1896 : BitVec 64, ∃∗ w1904 : BitVec 64, ∃∗ w1912 : BitVec 64,
        ⌜w1896.extractLsb' 0 8 = 0#8⌝ ∗
        (a ↦₆₄ noneCap) ∗ ((a + 8#64) ↦₆₄ w1896) ∗
        ((a + 16#64) ↦₆₄ w1904) ∗ ((a + 24#64) ↦₆₄ w1912) ∗
        memRegion (a + 32#64) 72 := by
  dsimp only [ekSentCt1ReceivedResultAt]
  rw [ProofLib.memRegion_split' (b := a + 9#64) (n := 15) (k := 80)
        (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 72)
        (b' := a + 32#64) rfl (by bv_omega) (by decide)]
  have h15 := memRegion_15_entails_loBytes7_and_64 (a + 9#64)
  have ha16 : (a + 9#64) + 7#64 = a + 16#64 := by bv_omega
  rw [ha16] at h15
  have h8 : memRegion (a + 24#64) 8 ⊢ ∃∗ u : BitVec 64, ((a + 24#64) ↦₆₄ u) :=
    Entails.of_eq (ProofLib.memRegion_eight (a + 24#64))
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono h15 (sepConj_mono_left h8)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w1912
  apply Entails.sepExists_elim; intro w1904
  apply Entails.sepExists_elim; intro u0
  have hbw := (pointsTo64_split_1_7 (a + 8#64) (u0 <<< 8)).symm
  have ha9 : (a + 8#64) + 1#64 = a + 9#64 := by bv_omega
  rw [ha9, v3cr_loByte_shift8 u0, v3cr_hiBytes7_shift8 u0] at hbw
  refine Entails.sepExists_right (u0 <<< 8)
    (Entails.sepExists_right w1904 (Entails.sepExists_right w1912 ?_))
  have h0 : (u0 <<< 8).extractLsb' 0 8 = 0#8 := v3cr_loByte_shift8 u0
  refine Entails.pure_right h0 ?_
  rw [← sepConj_assoc ((a + 8#64) ↦₈ 0#8), hbw]
  exact Entails.of_eq (by ac_rfl)

/-! ## Sub-Compositions for `+4984`, `+1024`, `+1012`, `+924`, `+4884`, `+860` -/

theorem v3cr_ekSentCt1Received_from_pb_err_eq {F : ShaCompress}
    (pb : V1State.Unchunked.EkSentCt1Received) (e : StatesError)
    (h : Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) pb = .error e) :
    e = .err .stateDecode := by
  unfold Unchunked.SendEk.EkSentCt1Received.from_pb at h
  split at h <;> try (injection h with h; exact h.symm)
  split at h <;> first | contradiction | (injection h with h; exact h.symm)

theorem v3cr_states_from_pb_ct1Received_sendingEk_err_any_eq {F : ShaCompress}
    (u : V1State.Unchunked.EkSentCt1Received)
    (uc : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F))
    (pbEnc : PolynomialEncoder) (err : PolynomialError)
    (huc : Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) u = .ok uc)
    (henc : fromPbResult (pbToProtoPolyEncoder pbEnc) = .error err) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ct1Received { uc := some u, sendingEk := some pbEnc }) } =
    .error (.err .stateDecode) := by
  have henc' := fromPb_eq_ok (pbToProtoPolyEncoder pbEnc)
  rw [henc] at henc'
  simp only [States.from_pb, Chunked.SendEk.Ct1Received.from_pb, huc,
    encoderFromPbStateDecode, spqrPolyApi, henc', StatesResult.ofPanic, Except.mapError,
    Bind.bind, Except.bind, Functor.map, Except.map]

end CryptoVerification.SpqrV1.States.FromPb
