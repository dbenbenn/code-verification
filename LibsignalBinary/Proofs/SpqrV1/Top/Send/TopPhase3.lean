/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.TopRegions -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenPhase -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesBridge2
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Contracts
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Top
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeStep
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLen -- shake: keep

/-!
# `spqr::send::<HookRng>` Phase 3 and 4 Composition (`0x314d8 -> s0.x30`)

Composes Phase 3b–3c (`AfterStatesBridge1.lean`), Phase 3d–3e (`AfterStatesBridge2.lean`),
Phase 4 (`TopRegions.lean`), and the shared epilogue into `step_send_from_314d8`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
open CryptoVerification.CodeLayout
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Top.StateSize
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.NextChunk

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local simp, local arm64_norm, local wp_norm] ite_zero32_self ite_zero64_self

theorem encodeToVecOnPanic_congr {s0 s : State} (htr : s.trace = s0.trace) (sf : State) :
    encodeToVecOnPanic s sf = encodeToVecOnPanic s0 sf := by
  unfold encodeToVecOnPanic allocFailedIn; rw [htr]

theorem memRegion_sp_0_16_24_words (sp : BitVec 64) :
    memRegion sp 8 ∗ memRegion (sp + 16#64) 24 =
      ∃∗ v_20_old : BitVec 64, ∃∗ v_sp18 : BitVec 64, ∃∗ v_sp10 : BitVec 64, ∃∗ v0 : BitVec 64,
        (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗ ((sp + 0x20#64) ↦₆₄ v_20_old) := by
  have h20 : sp + 32#64 = sp + 0x20#64 := rfl
  rw [ProofLib.memRegion_eight sp,
      ProofLib.memRegion_split' (b := sp + 16#64) (n := 8) (k := 16) (b' := sp + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 24#64) (n := 8) (k := 8) (b' := sp + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 16#64), ProofLib.memRegion_eight (sp + 24#64), ProofLib.memRegion_eight (sp + 32#64), h20]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem sepWPp_bind_weaken_panic {prog : Program} {mid ret : BitVec 64} {s : State}
    {P : SepProp} {Q Q' Qp Qp' : State → SepProp → Prop}
    (h1 : SepWPp prog mid s P Q Qp)
    (hqp : ∀ sf P_f, Qp sf P_f → Qp' sf P_f)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Q sm Pm → SepWPp prog ret sm Pm Q' Qp') :
    SepWPp prog ret s P Q' Qp' :=
  sepWPp_bind (sepWPp_mono_post (fun _ _ h => h) hqp h1) h2

theorem optVersionNegotiationPBTail_to_proto (A : RustAlloc) (a30 w0 w1 : BitVec 64)
    (vn : Option VersionNegotiationPB) :
    (a30 ↦₆₄ w0) ∗ ((a30 + 8#64) ↦₆₄ w1) ∗
      DecodeState.optVersionNegotiationPBTailAt A w0 w1 (a30 + 16#64) vn ⊢
    ProtoRepr.optVersionNegotiationPBAt A a30 vn := by
  cases vn with
  | none =>
    unfold DecodeState.optVersionNegotiationPBTailAt ProtoRepr.optVersionNegotiationPBAt
    have hpull :
        ((a30 ↦₆₄ w0) ∗ ((a30 + 8#64) ↦₆₄ w1) ∗ ⌜w0 = LibsignalTripleRatchetRepr.noneCap⌝ ∗
          memRegion (a30 + 16#64) 32) =
        ⌜w0 = LibsignalTripleRatchetRepr.noneCap⌝ ∗
          ((a30 ↦₆₄ w0) ∗ ((a30 + 8#64) ↦₆₄ w1) ∗ memRegion (a30 + 16#64) 32) := by ac_rfl
    rw [hpull]
    apply Entails.pure_left; rintro rfl
    rw [ProofLib.memRegion_split' (b := a30 + 8#64) (n := 8) (k := 32) (b' := a30 + 16#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))
  | some v =>
    unfold DecodeState.optVersionNegotiationPBTailAt DecodeState.versionNegotiationPBTailAt
      ProtoRepr.optVersionNegotiationPBAt ProtoRepr.versionNegotiationPBAt ProtoRepr.rustBytesVecAt
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.trans (Entails.of_eq (show _ =
      ((a30 ↦₆₄ w0) ∗ ((a30 + 8#64) ↦₆₄ w1) ∗
        ((a30 + 16#64) ↦₆₄ BitVec.ofNat 64 v.authKey.length) ∗
        DecodeState.vecU8Heap A w0 w1 v.authKey) ∗
      (ProtoRepr.optChainParamsPBAt (a30 + 24#64) v.chainParams ∗
        ((a30 + 36#64) ↦₃₂ v.direction) ∗ ((a30 + 40#64) ↦₃₂ v.minVersion) ∗
        memRegion (a30 + 44#64) 4) by ac_rfl)) ?_
    exact sepConj_mono_left (words_to_vecU8 A a30 w0 w1 v.authKey)

/-! ### Pure Model Reduction Lemmas -/

open CryptoVerification.SpqrV1.Top.StateSize in
theorem sendChainPhase_raw_le (hkdf : HkdfFn) (chain : Option ChainPB)
    (vn : Option VersionNegotiationPB) (key : Option EpochSecret) (epoch : Epoch)
    {idx : BitVec 32} {msgKey : Bytes} {chainPb : Option ChainPB}
    (h : sendChainPhase hkdf chain vn key epoch = .ok (idx, msgKey, chainPb)) :
    optRaw rawChain chainPb ≤ optRaw rawChain chain + 624 := by
  unfold sendChainPhase at h
  rcases except_bind_eq_ok h with ⟨ch, hres, hstep⟩
  cases ch with
  | none =>
    unfold sendStepChain at hstep
    cases hk : key.isNone <;> simp only [hk, Bool.false_eq_true, ↓reduceIte] at hstep
    · contradiction
    · have hch : none = chainPb := (Prod.mk.inj (Prod.mk.inj (Except.ok.inj hstep)).2).2
      subst hch; simp
  | some c0 =>
    have hc0 := sendResolveChain_raw_le hkdf chain vn hres
    unfold sendStepChain at hstep
    have htail : ∀ c1 : Chain, rawChain c1.intoPb ≤ optRaw rawChain chain + 592 →
        (if epoch == 0#64 then .error (.panic .sendEpochUnderflow) else do
          let (chain2, (idx, mk)) ← SpqrApiResult.ofChainResult (c1.sendKey hkdf (epoch - 1#64))
          pure (idx, mk, some chain2.intoPb)) = .ok (idx, msgKey, chainPb) →
        optRaw rawChain chainPb ≤ optRaw rawChain chain + 624 := by
      intro c1 hc1 hs
      split at hs
      · contradiction
      · rcases except_bind_eq_ok hs with ⟨⟨c2, idx', mk'⟩, hsk, hp⟩
        rw [SpqrApiResult.ofChainResult_eq_ok] at hsk
        have hc2 := Chain.sendKey_raw_le hkdf c1 (epoch - 1#64) hsk
        have hch : some c2.intoPb = chainPb := (Prod.mk.inj (Prod.mk.inj (Except.ok.inj hp)).2).2
        subst hch; simp only [optRaw_some]; omega
    cases key with
    | none =>
      dsimp only [pure, Pure.pure, Except.pure, Bind.bind, Except.bind] at hstep
      exact htail c0 (by omega) hstep
    | some es =>
      dsimp only at hstep
      rcases except_bind_eq_ok hstep with ⟨c1, hae, hs⟩
      rw [SpqrApiResult.ofChainPanic_eq_ok] at hae
      have hc1 := Chain.addEpoch_raw_le hkdf c0 es hae
      exact htail c1 (by omega) hs

theorem sendPanics_of_statesSend_panic {F : ShaCompress} {K : MlKem}
    {stateBytes rest : Bytes} {pq : PqRatchetState} {v1 : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {p : StatesPanic}
    (hdec : Proto.spqrDecodeState stateBytes = .ok pq)
    (hinner : pq.inner = some (.v1 v1))
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0)
    (hsend0 : st0.send K rest = .error (.panic p)) :
    (spqrV1 F K).sendPanics stateBytes rest := by
  have hd := decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec
  have hinner_pb : (pqRatchetStateToPb pq).inner = some v1 := by
    unfold pqRatchetStateToPb; simp [hinner]
  have hfrom_deps := spqrDeps_statesFromPb_of_ok F K hfrom
  have hsend := send_of_statesFromPb_ok (spqrDeps F K) (spqrHkdfWith F) (tape := rest)
    hd hinner_pb hfrom_deps
  have hss : ((spqrDeps F K).statesSend st0 rest).1 = .error (.panic .v1) := by
    dsimp [spqrDeps, liftStatesResult]; rw [hsend0]
  apply spqrV1_sendPanics_of_panic (p := .v1)
  rw [hsend]; dsimp only; rw [hss]

theorem sendAfterStates_spqrDeps_eq {F : ShaCompress} {K : MlKem}
    (pq : PqRatchetState) (sOut : V1Send spqrPolyApi (spqrAuthApi F)) :
    sendAfterStates (spqrDeps F K) (spqrHkdfWith F) (pqRatchetStateToPb pq)
      sOut.msg sOut.key sOut.state =
      match sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch with
      | .error e => .error e
      | .ok (idx, msgKey, chainPb) =>
        .ok { state := PqRatchetState.encodeRaw
                { versionNegotiation := pq.versionNegotiation
                  chain := chainPb
                  inner := some (.v1 sOut.state.into_pb) }
              msg := sOut.msg.serialize idx
              key := if msgKey.isEmpty then none else some msgKey } := by
  have heq := sendAfterStates_eq_bind_sendChainPhase (spqrDeps F K) (spqrHkdfWith F)
    (pqRatchetStateToPb pq) sOut.msg sOut.key sOut.state
  rw [heq]
  have hch : (pqRatchetStateToPb pq).chain = pq.chain := rfl
  have hvn : (pqRatchetStateToPb pq).versionNegotiation = pq.versionNegotiation := rfl
  have hep : (spqrDeps F K).msgEpoch sOut.msg = sOut.msg.epoch := rfl
  rw [hch, hvn, hep]
  cases sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch with
  | error e => rfl
  | ok val =>
    rcases val with ⟨idx, msgKey, chainPb⟩
    dsimp only
    obtain ⟨tail, hser⟩ := message_serialize_eq_cons sOut.msg idx
    have hmser : (spqrDeps F K).msgSerialize sOut.msg idx = 1#8 :: tail := hser
    rw [hmser]
    have hv1 : (1#8 != Version.v1.toU8) = false := by decide
    simp only [hv1, Bool.false_eq_true, ↓reduceIte]
    rw [← hser]
    rfl

theorem send_eq_of_statesSend_ok {F : ShaCompress} {K : MlKem}
    {stateBytes rest rest' : Bytes} {pq : PqRatchetState} {v1 : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {sOut : V1Send spqrPolyApi (spqrAuthApi F)}
    (hdec : Proto.spqrDecodeState stateBytes = .ok pq)
    (hinner : pq.inner = some (.v1 v1))
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0)
    (hsend0 : st0.send K rest = .ok (sOut, rest')) :
    LibsignalSpqrV1.send (spqrDeps F K) (spqrHkdfWith F) stateBytes rest =
      (sendAfterStates (spqrDeps F K) (spqrHkdfWith F) (pqRatchetStateToPb pq)
        sOut.msg sOut.key sOut.state, rest') := by
  have hd := decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec
  have hinner_pb : (pqRatchetStateToPb pq).inner = some v1 := by
    unfold pqRatchetStateToPb; simp [hinner]
  have hfrom_deps := spqrDeps_statesFromPb_of_ok F K hfrom
  have hsend := send_of_statesFromPb_ok (spqrDeps F K) (spqrHkdfWith F) (tape := rest)
    hd hinner_pb hfrom_deps
  have hss : (spqrDeps F K).statesSend st0 rest = (.ok (sOut.msg, sOut.key, sOut.state), rest') := by
    dsimp [spqrDeps, liftStatesResult]; rw [hsend0]
  rw [hsend, hss]

theorem sendPanics_of_sendChainPhase_panic {F : ShaCompress} {K : MlKem}
    {stateBytes rest rest' : Bytes} {pq : PqRatchetState} {v1 : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {sOut : V1Send spqrPolyApi (spqrAuthApi F)}
    (hdec : Proto.spqrDecodeState stateBytes = .ok pq)
    (hinner : pq.inner = some (.v1 v1))
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0)
    (hsend0 : st0.send K rest = .ok (sOut, rest'))
    (hpan : (sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch).isPanic = true) :
    (spqrV1 F K).sendPanics stateBytes rest := by
  have hsend := send_eq_of_statesSend_ok hdec hinner hfrom hsend0
  have hafter := sendAfterStates_spqrDeps_eq (F := F) (K := K) pq sOut
  rcases hch : sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch with e | _
  · rcases e with err | p
    · rw [hch] at hpan; contradiction
    · apply spqrV1_sendPanics_of_panic (p := p)
      rw [hsend, hafter, hch]
  · rw [hch] at hpan; contradiction

theorem send_and_draws_of_sendChainPhase_error {F : ShaCompress} {K : MlKem}
    {stateBytes rest rest' : Bytes} {pq : PqRatchetState} {v1 : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {sOut : V1Send spqrPolyApi (spqrAuthApi F)}
    {err : LibsignalSpqrV1.Error}
    (hdec : Proto.spqrDecodeState stateBytes = .ok pq)
    (hinner : pq.inner = some (.v1 v1))
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0)
    (hsend0 : st0.send K rest = .ok (sOut, rest'))
    (hch : sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch = .error (.err err)) :
    (spqrV1 F K).send stateBytes rest = none ∧
    (spqrV1 F K).draws stateBytes rest = rest.length - rest'.length ∧
    ¬ (spqrV1 F K).sendPanics stateBytes rest := by
  have hsend := send_eq_of_statesSend_ok hdec hinner hfrom hsend0
  have hafter := sendAfterStates_spqrDeps_eq (F := F) (K := K) pq sOut
  refine ⟨spqrV1_send_of_err (by rw [hsend, hafter, hch]), ?_,
    spqrV1_not_sendPanics_of_err (by rw [hsend, hafter, hch])⟩
  rw [spqrV1_draws_eq, hsend]

theorem send_and_draws_of_sendChainPhase_ok {F : ShaCompress} {K : MlKem}
    {stateBytes rest rest' : Bytes} {pq : PqRatchetState} {v1 : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {sOut : V1Send spqrPolyApi (spqrAuthApi F)}
    {idx : BitVec 32} {msgKey : Bytes} {chainPb : Option ChainPB}
    {salt : CryptoGames.HKDF.Salt}
    (hdec : Proto.spqrDecodeState stateBytes = .ok pq)
    (hinner : pq.inner = some (.v1 v1))
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0)
    (hsend0 : st0.send K rest = .ok (sOut, rest'))
    (hch : sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch = .ok (idx, msgKey, chainPb))
    (hsalt : messageKeyToSalt? (if msgKey.isEmpty then none else some msgKey) = some salt) :
    (spqrV1 F K).send stateBytes rest =
      some (PqRatchetState.encodeRaw
              { versionNegotiation := pq.versionNegotiation
                chain := chainPb
                inner := some (.v1 sOut.state.into_pb) },
            salt, sOut.msg.serialize idx) ∧
    (spqrV1 F K).draws stateBytes rest = rest.length - rest'.length ∧
    ¬ (spqrV1 F K).sendPanics stateBytes rest := by
  have hsend := send_eq_of_statesSend_ok hdec hinner hfrom hsend0
  have hafter := sendAfterStates_spqrDeps_eq (F := F) (K := K) pq sOut
  refine ⟨spqrV1_send_of_ok (by rw [hsend, hafter, hch]) hsalt, ?_,
    spqrV1_not_sendPanics_of_ok (by rw [hsend, hafter, hch])⟩
  rw [spqrV1_draws_eq, hsend]

theorem sepWPp_weaken_panic {prog : Program} {ret : BitVec 64} {s : State}
    {P Fr : SepProp} {post : State → SepProp → Prop}
    {φ1 φ2 : State → Prop}
    (himp : ∀ sf, φ1 sf → φ2 sf)
    (h : SepWPp prog ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ1 sf⌝ ∗ anyHeap) ∗ Fr))) :
    SepWPp prog ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ2 sf⌝ ∗ anyHeap) ∗ Fr)) := by
  intro R hmR hL
  rcases h R hmR hL with ⟨sm, hsteps, hok | ⟨hpan, P_f, hmPf, hQf⟩ | hoom⟩
  · exact ⟨sm, hsteps, Or.inl hok⟩
  · refine ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, P_f, hmPf, fun hmFr => ?_⟩)⟩
    exact Satisfies.mono
      (sepConj_mono_left (sepConj_mono_left (Entails.pure_mono (himp sm))))
      (hQf hmFr)
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem allocFailedIn_of_trace_eq {s0 s1 sf : State} (htr : s1.trace = s0.trace) :
    (allocFailedIn s1 sf ∧ s1.trace <+: sf.trace) ↔
    (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) := by
  unfold allocFailedIn
  rw [htr]

theorem optVN_30_to_proto (A : RustAlloc) (sp w0 w1 : BitVec 64)
    (vn : Option VersionNegotiationPB) :
    ((sp + 0x30#64) ↦₆₄ w0) ∗ ((sp + 0x38#64) ↦₆₄ w1) ∗
      DecodeState.optVersionNegotiationPBTailAt A w0 w1 (sp + 0x40#64) vn ⊢
    ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) vn := by
  have h := optVersionNegotiationPBTail_to_proto A (sp + 0x30#64) w0 w1 vn
  simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using h

theorem memRegion_0_30_pre_arm (sp : BitVec 64) :
    memRegion sp 0x30 =
      memRegion sp 8 ∗ memRegion (sp + 0x8#64) 8 ∗
      memRegion (sp + 16#64) 16 ∗ memRegion (sp + 32#64) 16 := by
  rw [memRegion_0_30_eq sp,
      ProofLib.memRegion_split' (b := sp + 16#64) (n := 8) (k := 8) (b' := sp + 24#64) rfl (by bv_omega) (by decide)]
  ac_rfl

theorem memRegion_16_16_and_32_16_post_arm (sp : BitVec 64) :
    memRegion (sp + 16#64) 16 ∗ memRegion (sp + 32#64) 16 =
      memRegion (sp + 16#64) 24 ∗ memRegion (sp + 0x28#64) 8 := by
  rw [ProofLib.memRegion_split' (b := sp + 16#64) (n := 16) (k := 8) (b' := sp + 32#64) rfl (by bv_omega) (by decide),
      memRegion_32_16_eq_8_8 sp]
  ac_rfl

theorem pre_309cc_regions_eq (sp : BitVec 64) :
    memRegion sp 0x30 ∗ memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
      memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) =
    memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗
      memRegion (sp + 0x590#64) 920 ∗ statesSendPreArmScratch sp ∗
      memRegion sp 8 ∗ memRegion (sp + 0x8#64) 8 ∗ memRegion (sp + 16#64) 16 ∗
      memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
      memRegion (sp + 0xd90#64) 72 ∗ stackRestA sp ∗ stackRestC sp := by
  rw [memRegion_0_30_pre_arm sp, memRegion_b0_950_eq sp, memRegion_cf0_1f20_eq sp]
  unfold statesSendPreArmScratch
  ac_rfl

theorem post_3196_regions_eq (sp : BitVec 64) :
    memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 0x550#64) 38 ∗
      memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      statesSendPostArmScratch sp ∗
      memRegion sp 8 ∗ memRegion (sp + 0x8#64) 8 ∗ memRegion (sp + 16#64) 16 ∗
      memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
      memRegion (sp + 0xd90#64) 72 ∗ stackRestA sp ∗ stackRestC sp =
    memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
      memRegion (sp + 0x1060#64) 80 ∗ memRegion (sp + 0xcf0#64) 80 ∗
      memRegion (sp + 0xd40#64) 80 ∗ memRegion (sp + 0xde0#64) 80 ∗
      memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0x28#64) 8 ∗
      memRegion (sp + 0x8#64) 8 ∗ memRegion sp 8 ∗ memRegion (sp + 16#64) 24 ∗
      memRegion (sp + 1512#64) 136 ∗ stackRestB0_950 sp ∗
      memRegion (sp + 0xff0#64) 24 ∗ memRegion (sp + 4792#64) 840 ∗
      memRegion (sp + 7136#64) 16 ∗ stackRestCF0_1F20 sp := by
  have h1 := statesSendPostArmScratch_split sp
  have h2 := memRegion_16_16_and_32_16_post_arm sp
  have hff0 : (sp + 4080#64 : BitVec 64) = sp + 0xff0#64 := rfl
  rw [hff0] at h1
  unfold stackRestB0_950
  calc
    _ = (statesSendPostArmScratch sp ∗ stackRestC sp) ∗
        memRegion (sp + 0x590#64) 920 ∗
        (memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 0x550#64) 38 ∗
         memRegion (sp + 0x580#64) 16 ∗ memRegion sp 8 ∗
         memRegion (sp + 0x8#64) 8 ∗ memRegion (sp + 16#64) 16 ∗
         memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
         memRegion (sp + 0xd90#64) 72 ∗ stackRestA sp) := by ac_rfl
    _ = (memRegion (sp + 16#64) 16 ∗ memRegion (sp + 32#64) 16) ∗
        (memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
         memRegion (sp + 0x1060#64) 80 ∗ memRegion (sp + 0xcf0#64) 80 ∗
         memRegion (sp + 0xd40#64) 80 ∗ memRegion (sp + 0xde0#64) 80 ∗
         memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0x8#64) 8 ∗
         memRegion sp 8 ∗ memRegion (sp + 1512#64) 136 ∗
         (memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 0x550#64) 38 ∗
          memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 1648#64) 696 ∗ stackRestA sp) ∗
         memRegion (sp + 0xff0#64) 24 ∗ memRegion (sp + 4792#64) 840 ∗
         memRegion (sp + 7136#64) 16 ∗ stackRestCF0_1F20 sp) := by
      rw [h1, memRegion_590_920_eq sp]; ac_rfl
    _ = _ := by rw [h2]; ac_rfl

end CryptoVerification.SpqrV1.Top.Send
