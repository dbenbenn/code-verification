/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Final -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.TopRegions -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Statements
import LibsignalBinary.Proofs.SpqrV1.Drop.States1
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Contracts
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.Send.TopPhase3
import LibsignalBinary.Proofs.SpqrV1.Top.StateSize
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLen -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOk

/-!
# End-to-End Verification of `spqr::send::<HookRng>` (`0x3085c`)

Composes Phase 1 (`Final.lean`), Phase 2 (`StatesSendDispatch.lean`), and Phases 3–4
(`TopPhase3.lean`) to verify `spqr::send::<libsignal_session::HookRng>` (`SpqrSendV1Stmt`,
`DEV-SPQR5`).
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
open CryptoVerification CryptoVerification.CodeLayout CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.ChainProofs CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.MessageSerialize CryptoVerification.SpqrV1.Top.StateSize
open CryptoVerification.SpqrV1.States CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.IntoPb CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.GF.UnacceleratedMul CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.NextChunk

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
def rawInnerKeysUnsampled : V1State.InnerState → Nat
  | .keysUnsampled v => rawChKeysUnsampled v
  | _ => 0

def rawV1KeysUnsampled (v : V1State) : Nat :=
  optRaw rawInnerKeysUnsampled v.innerState

def rawPqInnerKeysUnsampled : PqRatchetState.Inner → Nat
  | .v1 v => rawV1KeysUnsampled v

def rawPqKeysUnsampled (m : PqRatchetState) : Nat :=
  optRaw rawPqInnerKeysUnsampled m.inner

private theorem branch_ite_ok {S : Type} {R : Prop} {c : Bool} [Decidable (c = true)]
    {a b : Except Proto.DecodeErr (S × Bytes)} {x : S × Bytes}
    (h : (if c then a else b) = .ok x)
    (ha : a = .ok x → R) (hb : b = .ok x → R) : R := by
  split at h
  · exact ha h
  · exact hb h

private theorem branch_skip_one {S : Type} {rawS : S → Nat} {s s' : S}
    {wt : Proto.WireType} {tag : BitVec 32} {rest rest' : Bytes} {depth : Nat}
    (h : Bind.bind (Proto.skipField wt tag rest depth) (fun bs' => Except.ok (s, bs')) = .ok (s', rest')) :
    rest'.length ≤ rest.length ∧ rawS s' ≤ rawS s + 1 * (rest.length - rest'.length + 1) := by
  rcases he : Proto.skipField wt tag rest depth with err | bs'
  · simp [he, Bind.bind, Except.bind] at h
  · simp only [he, Bind.bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨skipField_length_le he, Nat.le_add_right _ _⟩

@[simp, reducible] private def unOk1 {S : Type} (s : S) : Except Proto.DecodeErr (S × Bytes) → S
  | .ok (s', _) => s'
  | .error _ => s

private theorem bind_pair_ok1 {S α : Type} {e : Except Proto.DecodeErr (α × Bytes)}
    {k : α × Bytes → Except Proto.DecodeErr (S × Bytes)} {s s' : S} {rest' : Bytes}
    (h : Bind.bind e k = .ok (s', rest'))
    (hk : ∀ v bs', k (v, bs') = .ok (unOk1 s (k (v, bs')), bs')) :
    ∃ v, e = .ok (v, rest') ∧ s' = unOk1 s (k (v, rest')) := by
  rcases he : e with err | ⟨v, bs'⟩
  · simp [he, Bind.bind, Except.bind] at h
  · simp only [he, Bind.bind, Except.bind] at h
    rw [hk v bs'] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨v, rfl, rfl⟩

private theorem branch_oneof_zero {Sub : Type}
    {mergeSub : Sub → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (Sub × Bytes)}
    {rawSub : Sub → Nat} {Ksub : Nat}
    (hb : MergeFieldBound mergeSub rawSub Ksub)
    {s s' : Option V1State.InnerState} {prev : Sub}
    {k : Sub × Bytes → Except Proto.DecodeErr (Option V1State.InnerState × Bytes)}
    {wt : Proto.WireType} {rest rest' : Bytes} {depth : Nat}
    (h : Bind.bind (Proto.mergeMessage mergeSub wt prev rest depth) k = .ok (s', rest'))
    (hz : ∀ v, optRaw rawInnerKeysUnsampled (unOk1 s (k (v, rest'))) = 0)
    (hk : ∀ v bs', k (v, bs') = .ok (unOk1 s (k (v, bs')), bs') := by intro _ _; rfl) :
    rest'.length ≤ rest.length ∧
      optRaw rawInnerKeysUnsampled s' ≤ optRaw rawInnerKeysUnsampled s + 1 * (rest.length - rest'.length + 1) := by
  obtain ⟨v, he, rfl⟩ := bind_pair_ok1 h hk
  obtain ⟨hle, _⟩ := mergeMessage_raw_le hb he
  rw [hz v]
  exact ⟨hle, Nat.zero_le _⟩

private theorem branch_oneof_one {S Sub : Type}
    {mergeSub : Sub → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (Sub × Bytes)}
    {rawSub : Sub → Nat}
    {rawS : S → Nat}
    {s s' : S} {prev : Sub}
    {k : Sub × Bytes → Except Proto.DecodeErr (S × Bytes)}
    {wt : Proto.WireType} {rest rest' : Bytes} {depth : Nat}
    (h : Bind.bind (Proto.mergeMessage mergeSub wt prev rest depth) k = .ok (s', rest'))
    (hb : MergeFieldBound mergeSub rawSub 1)
    (hprev : rawSub prev ≤ rawS s) (hg : ∀ v, rawS (unOk1 s (k (v, rest'))) = rawSub v)
    (hk : ∀ v bs', k (v, bs') = .ok (unOk1 s (k (v, bs')), bs') := by intro _ _; rfl) :
    rest'.length ≤ rest.length ∧ rawS s' ≤ rawS s + 1 * (rest.length - rest'.length + 1) := by
  obtain ⟨v, he, rfl⟩ := bind_pair_ok1 h hk
  obtain ⟨hle, hv⟩ := mergeMessage_raw_le hb he
  rw [hg v]
  exact ⟨hle, by omega⟩

private theorem branch_optMessage_one {S Sub : Type} [Inhabited Sub]
    {mergeSub : Sub → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (Sub × Bytes)}
    {rawSub : Sub → Nat} {Ksub : Nat}
    {rawS : S → Nat}
    {s s' : S} {old : Option Sub}
    {k : Option Sub × Bytes → Except Proto.DecodeErr (S × Bytes)}
    {wt : Proto.WireType} {rest rest' : Bytes} {depth : Nat}
    (h : Bind.bind (Proto.mergeOptMessage mergeSub wt old rest depth) k = .ok (s', rest'))
    (hb : MergeFieldBound mergeSub rawSub Ksub) (hdef : rawSub default = 0)
    (hg : ∀ v, rawS (unOk1 s (k (v, rest'))) = rawS s)
    (hk : ∀ v bs', k (v, bs') = .ok (unOk1 s (k (v, bs')), bs') := by intro _ _; rfl) :
    rest'.length ≤ rest.length ∧ rawS s' ≤ rawS s + 1 * (rest.length - rest'.length + 1) := by
  obtain ⟨v, he, rfl⟩ := bind_pair_ok1 h hk
  obtain ⟨hle, _⟩ := mergeOptMessage_raw_le hb hdef he
  rw [hg v]
  exact ⟨hle, Nat.le_add_right _ _⟩

theorem mergeFieldBound_chKeysUnsampled_one :
    MergeFieldBound V1State.Chunked.KeysUnsampled.mergeField rawChKeysUnsampled 1 := by
  intro s tag wt rest depth s' rest' h
  unfold V1State.Chunked.KeysUnsampled.mergeField at h
  refine branch_ite_ok h (fun h => ?_) branch_skip_one
  obtain ⟨v, he, rfl⟩ := bind_pair_ok1 (s := s) h (fun _ _ => rfl)
  obtain ⟨hle, hv⟩ := mergeOptMessage_raw_le mergeFieldBound_ucKeysUnsampled rfl he
  exact ⟨hle, by simp only [unOk1, rawChKeysUnsampled]; omega⟩

theorem mergeFieldBound_innerKeysUnsampled :
    MergeFieldBound V1State.InnerState.merge (optRaw rawInnerKeysUnsampled) 1 := by
  intro s tag wt rest depth s' rest' h
  unfold V1State.InnerState.merge at h
  exact branch_ite_ok h
    (fun h => branch_oneof_one h mergeFieldBound_chKeysUnsampled_one
      (by cases s with | none => rfl | some is => cases is <;> exact Nat.le_refl _)
      (fun _ => rfl))
    (fun h => branch_ite_ok h (fun h => branch_oneof_zero mergeFieldBound_chKeysSampled h (fun _ => rfl))
    (fun h => branch_ite_ok h (fun h => branch_oneof_zero mergeFieldBound_chHeaderSent h (fun _ => rfl))
    (fun h => branch_ite_ok h (fun h => branch_oneof_zero mergeFieldBound_chCt1Received h (fun _ => rfl))
    (fun h => branch_ite_ok h (fun h => branch_oneof_zero mergeFieldBound_chEkSentCt1Received h (fun _ => rfl))
    (fun h => branch_ite_ok h (fun h => branch_oneof_zero mergeFieldBound_chNoHeaderReceived h (fun _ => rfl))
    (fun h => branch_ite_ok h (fun h => branch_oneof_zero mergeFieldBound_chHeaderReceived h (fun _ => rfl))
    (fun h => branch_ite_ok h (fun h => branch_oneof_zero mergeFieldBound_chCt1Sampled h (fun _ => rfl))
    (fun h => branch_ite_ok h (fun h => branch_oneof_zero mergeFieldBound_chEkReceivedCt1Sampled h (fun _ => rfl))
    (fun h => branch_ite_ok h (fun h => branch_oneof_zero mergeFieldBound_chCt1Acknowledged h (fun _ => rfl))
    (fun h => branch_ite_ok h (fun h => branch_oneof_zero mergeFieldBound_chCt2Sampled h (fun _ => rfl))
      branch_skip_one))))))))))

theorem mergeFieldBound_v1KeysUnsampled :
    MergeFieldBound V1State.mergeField rawV1KeysUnsampled 1 := by
  intro s tag wt rest depth s' rest' h
  unfold V1State.mergeField at h
  refine branch_ite_ok h (fun h => ?_) branch_skip_one
  obtain ⟨is', he, rfl⟩ := bind_pair_ok1 (s := s) h (fun _ _ => rfl)
  exact mergeFieldBound_innerKeysUnsampled s.innerState tag wt rest depth is' rest' he

theorem mergeFieldBound_pqInnerKeysUnsampled :
    MergeFieldBound PqRatchetState.Inner.merge (optRaw rawPqInnerKeysUnsampled) 1 := by
  intro s tag wt rest depth s' rest' h
  unfold PqRatchetState.Inner.merge at h
  exact branch_ite_ok h
    (fun h => branch_oneof_one h mergeFieldBound_v1KeysUnsampled
      (by cases s with | none => rfl | some is => cases is; exact Nat.le_refl _)
      (fun _ => rfl))
    branch_skip_one

theorem mergeFieldBound_pqKeysUnsampled :
    MergeFieldBound PqRatchetState.mergeField rawPqKeysUnsampled 1 := by
  intro s tag wt rest depth s' rest' h
  unfold PqRatchetState.mergeField at h
  refine branch_ite_ok h (fun h => branch_optMessage_one h mergeFieldBound_vn rfl (fun _ => rfl))
    (fun h => branch_ite_ok h (fun h => branch_optMessage_one h mergeFieldBound_chain rfl (fun _ => rfl))
    (fun h => branch_ite_ok h (fun h => ?_) branch_skip_one))
  obtain ⟨v, he, rfl⟩ := bind_pair_ok1 (s := s) h (fun _ _ => rfl)
  exact mergeFieldBound_pqInnerKeysUnsampled s.inner tag wt rest depth v rest' he

theorem spqrDecodeState_rawPqKeysUnsampled_le {bs : Bytes} {st : PqRatchetState}
    (h : Proto.spqrDecodeState bs = .ok st) : rawPqKeysUnsampled st ≤ bs.length := by
  unfold Proto.spqrDecodeState at h
  split at h
  · simp only [Except.ok.injEq] at h; subst h; simp [rawPqKeysUnsampled, optRaw]
  · rcases hdec : PqRatchetState.decode bs with e | st'
    · simp [hdec] at h
    · simp only [hdec, Except.ok.injEq] at h; subst h
      have hraw := mergeFieldsLoop_raw_le mergeFieldBound_pqKeysUnsampled bs.length default bs
        Proto.RECURSION_LIMIT st' hdec
      have hdef : rawPqKeysUnsampled default = 0 := rfl
      omega

theorem keysUnsampled_macKey_le_of_from_pb {F : ShaCompress} {pq : PqRatchetState} {v1 : V1State}
    {st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)} {bs : Bytes}
    (hdec : Proto.spqrDecodeState bs = .ok pq)
    (hinner : pq.inner = some (.v1 v1))
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok (.keysUnsampled st)) :
    st.uc.auth.macKey.length ≤ bs.length := by
  have h1 := spqrDecodeState_rawPqKeysUnsampled_le hdec
  have h2 : rawPqKeysUnsampled pq = rawV1KeysUnsampled v1 := by
    simp [rawPqKeysUnsampled, hinner, rawPqInnerKeysUnsampled]
  rcases States.from_pb_raw_le hfrom with ⟨hraw_from, _⟩
  have hmac := keysUnsampled_macKey_le_rawV1State st
  have hv1_eq : rawV1State v1 = rawV1KeysUnsampled v1 := by
    unfold States.from_pb at hfrom
    rcases his : v1.innerState with _ | is
    · rw [his] at hfrom; nomatch hfrom
    · rw [his] at hfrom
      cases is with
      | keysUnsampled ch =>
        simp [rawV1State, rawV1KeysUnsampled, his, rawInnerState, rawInnerKeysUnsampled]
      | keysSampled ch =>
        rcases hsub : Chunked.SendEk.KeysSampled.from_pb spqrPolyApi (spqrAuthApi F) ch with e | x <;>
          simp [hsub, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hfrom
      | headerSent ch =>
        rcases hsub : Chunked.SendEk.HeaderSent.from_pb spqrPolyApi (spqrAuthApi F) ch with e | x <;>
          simp [hsub, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hfrom
      | ct1Received ch =>
        rcases hsub : Chunked.SendEk.Ct1Received.from_pb spqrPolyApi (spqrAuthApi F) ch with e | x <;>
          simp [hsub, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hfrom
      | ekSentCt1Received ch =>
        rcases hsub : Chunked.SendEk.EkSentCt1Received.from_pb spqrPolyApi (spqrAuthApi F) ch with e | x <;>
          simp [hsub, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hfrom
      | noHeaderReceived ch =>
        rcases hsub : Chunked.SendCt.NoHeaderReceived.from_pb spqrPolyApi (spqrAuthApi F) ch with e | x <;>
          simp [hsub, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hfrom
      | headerReceived ch =>
        rcases hsub : Chunked.SendCt.HeaderReceived.from_pb spqrPolyApi (spqrAuthApi F) ch with e | x <;>
          simp [hsub, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hfrom
      | ct1Sampled ch =>
        rcases hsub : Chunked.SendCt.Ct1Sampled.from_pb spqrPolyApi (spqrAuthApi F) ch with e | x <;>
          simp [hsub, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hfrom
      | ekReceivedCt1Sampled ch =>
        rcases hsub : Chunked.SendCt.EkReceivedCt1Sampled.from_pb spqrPolyApi (spqrAuthApi F) ch with e | x <;>
          simp [hsub, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hfrom
      | ct1Acknowledged ch =>
        rcases hsub : Chunked.SendCt.Ct1Acknowledged.from_pb spqrPolyApi (spqrAuthApi F) ch with e | x <;>
          simp [hsub, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hfrom
      | ct2Sampled ch =>
        rcases hsub : Chunked.SendCt.Ct2Sampled.from_pb spqrPolyApi (spqrAuthApi F) ch with e | x <;>
          simp [hsub, Bind.bind, Except.bind, pure, Pure.pure, Except.pure] at hfrom
  omega

/-- Under `bs.length < 2 ^ 32` and `64 ≤ tape.length` (`DEV-SPQR5`), any `st0` decoded by
    `States.from_pb` with `statesPolyEncoderValid st0` either succeeds in `st0.send K tape`
    or is in the `.headerReceived` arm where `K.encaps1` returns `none`. -/
theorem statesSend_ok_or_headerReceived_encaps1_of_le_64 {F : ShaCompress} (K : MlKem)
    {pq : PqRatchetState} {v1 : V1State} {st0 : States spqrPolyApi (spqrAuthApi F)}
    {bs tape : Bytes}
    (hlen : bs.length < 2 ^ 32)
    (h64 : 64 ≤ tape.length)
    (hdec : Proto.spqrDecodeState bs = .ok pq)
    (hinner : pq.inner = some (.v1 v1))
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0)
    (hv : statesPolyEncoderValid st0) :
    (∃ sOut tape', st0.send K tape = .ok (sOut, tape')) ∨
    (∃ st, st0 = .headerReceived st ∧
      K.encaps1 st.uc.hdr ⟨tape.take 32, by rw [List.length_take]; omega⟩ = none ∧
      st0.send K tape = .error (.panic .encaps1Failed)) := by
  cases st0 with
  | keysUnsampled st =>
    have hk := keysUnsampled_macKey_le_of_from_pb hdec hinner hfrom
    exact Or.inl (send_keysUnsampled_ok_of_le_64 K st (by omega) h64)
  | keysSampled st => exact Or.inl (send_keysSampled_ok_of_valid K tape st hv)
  | headerSent st => exact Or.inl (send_headerSent_ok_of_valid K tape st hv)
  | ct1Received st => exact Or.inl (send_ct1Received_ok_of_valid K tape st hv)
  | ekSentCt1Received st => exact Or.inl ⟨_, _, rfl⟩
  | noHeaderReceived st => exact Or.inl ⟨_, _, rfl⟩
  | headerReceived st =>
    rcases send_headerReceived_ok_or_encaps1_of_le_32 (tape := tape) K st (by omega) with hok | ⟨henc, herr⟩
    · exact Or.inl hok
    · exact Or.inr ⟨st, rfl, henc, herr⟩
  | ct1Sampled st => exact Or.inl (send_ct1Sampled_ok_of_valid K tape st hv)
  | ekReceivedCt1Sampled st => exact Or.inl (send_ekReceivedCt1Sampled_ok_of_valid K tape st hv)
  | ct1Acknowledged st => exact Or.inl ⟨_, _, rfl⟩
  | ct2Sampled st => exact Or.inl (send_ct2Sampled_ok_of_valid K tape st hv)

end CryptoVerification.SpqrV1.Top.Send
