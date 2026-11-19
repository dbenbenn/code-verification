/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Defs
public import LibsignalBinary.Proofs.SpqrV1.Drop.States1a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Defs
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `spqr::send`: Post-`States::send` Panic Blocks, Shared Epilogue, and Error Cleanup

Representation bridges, overflow/assertion panic blocks (`0x33740`, `0x33d4c`), shared return
epilogue (`0x31a3c..0x31a94`), and chain error cleanup paths (`0x31764`, `0x31794`) for
`spqr::send::<HookRng>` (`0x3085c`).
-/

public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.CodeLayout
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.Prost.EncodeToVec hiding SepWP.done

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

theorem stackAt_spqrSendCallee_eq_statesIntoPb (sp : BitVec 64) :
    stackAt sp spqrSendCalleeStack =
      memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack)
        (spqrSendCalleeStack - statesIntoPbStackX) ∗
        stackAt sp statesIntoPbStackX :=
  ProofLib.stackAt_split_bottom sp statesIntoPbStackX
    (spqrSendCalleeStack - statesIntoPbStackX) (by decide)

theorem stackAt_spqrSendCallee_eq_chainFromPb (sp : BitVec 64) :
    stackAt sp spqrSendCalleeStack =
      memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack)
        (spqrSendCalleeStack - chainFromPbStackX) ∗
        stackAt sp chainFromPbStackX :=
  ProofLib.stackAt_split_bottom sp chainFromPbStackX
    (spqrSendCalleeStack - chainFromPbStackX) (by decide)

theorem stackAt_spqrSendCallee_eq_chainFromVN (sp : BitVec 64) :
    stackAt sp spqrSendCalleeStack =
      memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack)
        (spqrSendCalleeStack - chainFromVersionNegotiationStackX) ∗
        stackAt sp chainFromVersionNegotiationStackX :=
  ProofLib.stackAt_split_bottom sp chainFromVersionNegotiationStackX
    (spqrSendCalleeStack - chainFromVersionNegotiationStackX) (by decide)

theorem stackAt_spqrSendCallee_eq_chainAddEpoch (sp : BitVec 64) :
    stackAt sp spqrSendCalleeStack =
      memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack)
        (spqrSendCalleeStack - chainAddEpochStackX) ∗
        stackAt sp chainAddEpochStackX :=
  ProofLib.stackAt_split_bottom sp chainAddEpochStackX
    (spqrSendCalleeStack - chainAddEpochStackX) (by decide)

theorem stackAt_spqrSendCallee_eq_chainSendKey (sp : BitVec 64) :
    stackAt sp spqrSendCalleeStack =
      memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack)
        (spqrSendCalleeStack - chainSendKeyStackX) ∗
        stackAt sp chainSendKeyStackX :=
  ProofLib.stackAt_split_bottom sp chainSendKeyStackX
    (spqrSendCalleeStack - chainSendKeyStackX) (by decide)

theorem stackAt_spqrSendCallee_eq_chainIntoPb (sp : BitVec 64) :
    stackAt sp spqrSendCalleeStack =
      memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack)
        (spqrSendCalleeStack - chainIntoPbStackX) ∗
        stackAt sp chainIntoPbStackX :=
  ProofLib.stackAt_split_bottom sp chainIntoPbStackX
    (spqrSendCalleeStack - chainIntoPbStackX) (by decide)

theorem stackAt_spqrSendCallee_eq_messageSerialize (sp : BitVec 64) :
    stackAt sp spqrSendCalleeStack =
      memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack)
        (spqrSendCalleeStack - messageSerializeStackX) ∗
        stackAt sp messageSerializeStackX :=
  ProofLib.stackAt_split_bottom sp messageSerializeStackX
    (spqrSendCalleeStack - messageSerializeStackX) (by decide)

/-- Representation of `key : Option EpochSecret` at `0x314d8`:
    * `none`: `x21 = noneCap` (`0xFFFFFFFFFFFFFFFF#64`) and `memRegion (sp + 0x1bc0#64) 16`;
    * `some es`: `x21` is `es.secret` capacity (`x21.toNat < 2^63`), `x27` is `es.secret` pointer,
    `(sp + 0x1bc0) ↦₆₄ es.secret.length`, `(sp + 0x1bc8) ↦₆₄ es.epoch`. -/
def optEpochSecretAfterSlotAt (A : RustAlloc) (sp x21 x27 : BitVec 64) :
    Option EpochSecret → SepProp
  | none => ⌜x21 = noneCap⌝ ∗ memRegion (sp + 0x1bc0#64) 16
  | some es =>
    ⌜x21.toNat < 2 ^ 63⌝ ∗
      vecU8Buf A x21 x27 es.secret ∗
      ((sp + 0x1bc0#64) ↦₆₄ BitVec.ofNat 64 es.secret.length) ∗
      ((sp + 0x1bc8#64) ↦₆₄ es.epoch)

/-! ## Representation Bridges (`ProtoRepr.*PBAt` ↔ `Drop.proto*At`) -/

private theorem sepExists_const' {α : Type} [Inhabited α] (P : SepProp) :
    (∃∗ _ : α, P) = P :=
  ProofLib.Entails.antisymm
    (Entails.sepExists_elim fun _ => Entails.refl P)
    (Entails.sepExists_intro (P := fun _ : α => P) default)

private theorem sepExists_retract {G α : Type} (f : G → α) (mk : α → G)
    (h : ∀ x, f (mk x) = x) (P : α → SepProp) :
    (∃∗ g : G, P (f g)) = (∃∗ x : α, P x) :=
  ProofLib.Entails.antisymm
    (Entails.sepExists_elim fun g => Entails.sepExists_intro (P := P) (f g))
    (Entails.sepExists_elim fun x =>
      Entails.sepExists_right (Q := fun g => P (f g)) (mk x) (Entails.of_eq (by rw [h x])))

private theorem sepExists_prod' {α β : Type} (P : α × β → SepProp) :
    (∃∗ x : α × β, P x) = ∃∗ a : α, ∃∗ b : β, P (a, b) :=
  ProofLib.Entails.antisymm
    (Entails.sepExists_elim fun ⟨a, b⟩ =>
      Entails.sepExists_right (Q := fun a' => ∃∗ b' : β, P (a', b')) a
        (Entails.sepExists_intro (P := fun b' => P (a, b')) b))
    (Entails.sepExists_elim fun a =>
      Entails.sepExists_elim fun b =>
        Entails.sepExists_intro (P := P) (a, b))

open CryptoVerification.SpqrV1.ProtoRepr in
theorem optKeysUnsampledPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.KeysUnsampled) :
    optProtoUnchunkedKeysUnsampledAt A a opt =
      ∃∗ g : Unchunked2PBGhost, optKeysUnsampledPBPinnedAt A g a opt := by
  cases opt with
  | none =>
    simp only [optProtoUnchunkedKeysUnsampledAt, optKeysUnsampledPBPinnedAt]
    exact (sepExists_const' _).symm
  | some u =>
    exact unchunked2At_eq_exists_pinned A a u.epoch u.auth

open CryptoVerification.SpqrV1.ProtoRepr in
theorem optNoHeaderReceivedPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.NoHeaderReceived) :
    optProtoUnchunkedNoHeaderReceivedAt A a opt =
      ∃∗ g : Unchunked2PBGhost, optNoHeaderReceivedPBPinnedAt A g a opt := by
  cases opt with
  | none =>
    simp only [optProtoUnchunkedNoHeaderReceivedAt, optNoHeaderReceivedPBPinnedAt]
    exact (sepExists_const' _).symm
  | some u =>
    exact unchunked2At_eq_exists_pinned A a u.epoch u.auth

open CryptoVerification.SpqrV1.ProtoRepr in
theorem optCt2SentPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.Ct2Sent) :
    optProtoUnchunkedCt2SentAt A a opt =
      ∃∗ g : Unchunked2PBGhost, optCt2SentPBPinnedAt A g a opt := by
  cases opt with
  | none =>
    simp only [optProtoUnchunkedCt2SentAt, optCt2SentPBPinnedAt]
    exact (sepExists_const' _).symm
  | some u =>
    exact unchunked2At_eq_exists_pinned A a u.epoch u.auth

open CryptoVerification.SpqrV1.ProtoRepr in
theorem optHeaderReceivedPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.HeaderReceived) :
    optProtoUnchunkedHeaderReceivedAt A a opt =
      ∃∗ g : Unchunked3PBGhost, optHeaderReceivedPBPinnedAt A g a opt := by
  cases opt with
  | none =>
    simp only [optProtoUnchunkedHeaderReceivedAt, optHeaderReceivedPBPinnedAt]
    exact (sepExists_const' _).symm
  | some u =>
    exact unchunked3At_eq_exists_pinned A a u.epoch u.auth u.hdr

open CryptoVerification.SpqrV1.ProtoRepr in
theorem optHeaderSentPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.HeaderSent) :
    optProtoUnchunkedHeaderSentAt A a opt =
      ∃∗ g : Unchunked4PBGhost, optHeaderSentPBPinnedAt A g a opt := by
  cases opt with
  | none =>
    simp only [optProtoUnchunkedHeaderSentAt, optHeaderSentPBPinnedAt]
    exact (sepExists_const' _).symm
  | some u =>
    exact unchunked4At_eq_exists_pinned A a u.epoch u.auth u.ek u.dk

open CryptoVerification.SpqrV1.ProtoRepr in
theorem optEkSentCt1ReceivedPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.EkSentCt1Received) :
    optProtoUnchunkedEkSentCt1ReceivedAt A a opt =
      ∃∗ g : Unchunked4PBGhost, optEkSentCt1ReceivedPBPinnedAt A g a opt := by
  cases opt with
  | none =>
    simp only [optProtoUnchunkedEkSentCt1ReceivedAt, optEkSentCt1ReceivedPBPinnedAt]
    exact (sepExists_const' _).symm
  | some u =>
    exact unchunked4At_eq_exists_pinned A a u.epoch u.auth u.dk u.ct1

open CryptoVerification.SpqrV1.ProtoRepr in
theorem optCt1SentEkReceivedPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.Ct1SentEkReceived) :
    optProtoUnchunkedCt1SentEkReceivedAt A a opt =
      ∃∗ g : Unchunked5PBGhost, optCt1SentEkReceivedPBPinnedAt A g a opt := by
  cases opt with
  | none =>
    simp only [optProtoUnchunkedCt1SentEkReceivedAt, optCt1SentEkReceivedPBPinnedAt]
    exact (sepExists_const' _).symm
  | some u =>
    exact unchunked5At_eq_exists_pinned A a u.epoch u.auth u.es u.ek u.ct1

open CryptoVerification.SpqrV1.ProtoRepr in
theorem optProtoPolyEncoderAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (opt : Option PolynomialEncoder) :
    Poly.optProtoPolynomialEncoderAt A a (opt.map pbToProtoPolyEncoder) =
      ∃∗ g : PolynomialEncoderPBGhost, optPolynomialEncoderPBPinnedAt A g a opt := by
  rw [← optPolynomialEncoderPBAt_eq_exists_pinned]
  cases opt <;> rfl

open CryptoVerification.SpqrV1.ProtoRepr in
theorem optProtoPolyDecoderAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (opt : Option PolynomialDecoder) :
    Poly.optProtoPolynomialDecoderAt A a (opt.map pbToProtoPolyDecoder) =
      ∃∗ g : PolynomialDecoderPBGhost, optPolynomialDecoderPBPinnedAt A g a opt := by
  rw [← optPolynomialDecoderPBAt_eq_exists_pinned]
  cases opt <;> rfl

open CryptoVerification.SpqrV1.ProtoRepr in
theorem protoChunkedHeaderSentAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (s : V1State.Chunked.HeaderSent) :
    protoChunkedHeaderSentAt A a s =
      ∃∗ g : ChunkedHeaderSentPBGhost, chunkedHeaderSentPBPinnedAt A g a s := by
  rw [← chunkedHeaderSentPBAt_eq_exists_pinned]
  unfold protoChunkedHeaderSentAt chunkedHeaderSentPBAt
  rw [optProtoPolyEncoderAt_eq_exists_pinned, optProtoPolyDecoderAt_eq_exists_pinned,
    optPolynomialEncoderPBAt_eq_exists_pinned, optPolynomialDecoderPBAt_eq_exists_pinned]
  cases s.uc <;> rfl

open CryptoVerification.SpqrV1.ProtoRepr in
theorem protoChunkedCt1SampledAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (s : V1State.Chunked.Ct1Sampled) :
    protoChunkedCt1SampledAt A a s =
      ∃∗ g : ChunkedCt1SampledPBGhost, chunkedCt1SampledPBPinnedAt A g a s := by
  rw [← chunkedCt1SampledPBAt_eq_exists_pinned]
  unfold protoChunkedCt1SampledAt chunkedCt1SampledPBAt
  rw [optProtoPolyEncoderAt_eq_exists_pinned, optProtoPolyDecoderAt_eq_exists_pinned,
    optPolynomialEncoderPBAt_eq_exists_pinned, optPolynomialDecoderPBAt_eq_exists_pinned]
  cases s.uc <;> rfl

private theorem sepExists_swap2 {α β : Type} (P : α → β → SepProp) :
    (∃∗ b : β, ∃∗ a : α, P a b) = ∃∗ x : α × β, P x.1 x.2 :=
  ProofLib.Entails.antisymm
    (Entails.sepExists_elim fun b =>
      Entails.sepExists_elim fun a =>
        Entails.sepExists_intro (P := fun x : α × β => P x.1 x.2) (a, b))
    (Entails.sepExists_elim fun ⟨a, b⟩ =>
      Entails.sepExists_right (Q := fun b' => ∃∗ a' : α, P a' b') b
        (Entails.sepExists_intro (P := fun a' => P a' b) a))

open CryptoVerification.SpqrV1.ProtoRepr in
theorem protoInnerStateAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (is : V1State.InnerState) :
    protoInnerStateAt A a is =
      ∃∗ g : V1StatePBGhost, v1StateInnerPBPinnedAt A g a is := by
  cases is with
  | keysUnsampled v =>
    dsimp only [protoInnerStateAt, protoChunkedKeysUnsampledAt, v1StateInnerPBPinnedAt]
    rw [optKeysUnsampledPBAt_eq_exists_pinned, sepExists_sepConj_left, sepExists_sepConj_right]
    exact (sepExists_retract (fun g : V1StatePBGhost => g.a.gKeysUnsampled)
      (fun x => { (default : V1StatePBGhost) with a := { (default : V1StatePBGhostA) with gKeysUnsampled := x } }) (fun _ => rfl) _).symm
  | keysSampled v =>
    dsimp only [protoInnerStateAt, protoChunkedKeysSampledAt, v1StateInnerPBPinnedAt]
    have ha : (a + 8#64) + 104#64 = a + 112#64 := by bv_omega
    rw [ha, optHeaderSentPBAt_eq_exists_pinned, optProtoPolyEncoderAt_eq_exists_pinned]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_swap2, sepConj_assoc]
    exact (sepExists_retract (fun g : V1StatePBGhost => g.a.gKeysSampled)
      (fun x => { (default : V1StatePBGhost) with a := { (default : V1StatePBGhostA) with gKeysSampled := x } }) (fun _ => rfl) _).symm
  | headerSent v =>
    dsimp only [protoInnerStateAt, v1StateInnerPBPinnedAt]
    rw [protoChunkedHeaderSentAt_eq_exists_pinned, sepExists_sepConj_left, sepExists_sepConj_right]
    exact (sepExists_retract (fun g : V1StatePBGhost => g.a.gHeaderSent)
      (fun x => { (default : V1StatePBGhost) with a := { (default : V1StatePBGhostA) with gHeaderSent := x } }) (fun _ => rfl) _).symm
  | ct1Received v =>
    dsimp only [protoInnerStateAt, protoChunkedCt1ReceivedAt, v1StateInnerPBPinnedAt]
    have ha : (a + 8#64) + 104#64 = a + 112#64 := by bv_omega
    rw [ha, optEkSentCt1ReceivedPBAt_eq_exists_pinned, optProtoPolyEncoderAt_eq_exists_pinned]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_swap2, sepConj_assoc]
    exact (sepExists_retract (fun g : V1StatePBGhost => g.a.gCt1Received)
      (fun x => { (default : V1StatePBGhost) with a := { (default : V1StatePBGhostA) with gCt1Received := x } }) (fun _ => rfl) _).symm
  | ekSentCt1Received v =>
    dsimp only [protoInnerStateAt, protoChunkedEkSentCt1ReceivedAt, v1StateInnerPBPinnedAt]
    have ha : (a + 8#64) + 104#64 = a + 112#64 := by bv_omega
    rw [ha, optEkSentCt1ReceivedPBAt_eq_exists_pinned, optProtoPolyDecoderAt_eq_exists_pinned]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_swap2, sepConj_assoc]
    exact (sepExists_retract (fun g : V1StatePBGhost => g.a.gEkSentCt1Received)
      (fun x => { (default : V1StatePBGhost) with a := { (default : V1StatePBGhostA) with gEkSentCt1Received := x } }) (fun _ => rfl) _).symm
  | noHeaderReceived v =>
    dsimp only [protoInnerStateAt, protoChunkedNoHeaderReceivedAt, v1StateInnerPBPinnedAt]
    have ha : (a + 8#64) + 40#64 = a + 48#64 := by bv_omega
    rw [ha, optProtoPolyDecoderAt_eq_exists_pinned, optNoHeaderReceivedPBAt_eq_exists_pinned]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_swap2, sepConj_assoc]
    exact (sepExists_retract (fun g : V1StatePBGhost => g.a.gNoHeaderReceived)
      (fun x => { (default : V1StatePBGhost) with a := { (default : V1StatePBGhostA) with gNoHeaderReceived := x } }) (fun _ => rfl) _).symm
  | headerReceived v =>
    dsimp only [protoInnerStateAt, protoChunkedHeaderReceivedAt, v1StateInnerPBPinnedAt]
    have ha : (a + 8#64) + 80#64 = a + 88#64 := by bv_omega
    rw [ha, optHeaderReceivedPBAt_eq_exists_pinned, optProtoPolyDecoderAt_eq_exists_pinned]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_swap2, sepConj_assoc]
    exact (sepExists_retract (fun g : V1StatePBGhost => g.b.gHeaderReceived)
      (fun x => { (default : V1StatePBGhost) with b := { (default : V1StatePBGhostB) with gHeaderReceived := x } }) (fun _ => rfl) _).symm
  | ct1Sampled v =>
    dsimp only [protoInnerStateAt, v1StateInnerPBPinnedAt]
    rw [protoChunkedCt1SampledAt_eq_exists_pinned]
    exact (sepExists_retract (fun g : V1StatePBGhost => g.b.gCt1Sampled)
      (fun x => { (default : V1StatePBGhost) with b := { (default : V1StatePBGhostB) with gCt1Sampled := x } }) (fun _ => rfl) _).symm
  | ekReceivedCt1Sampled v =>
    dsimp only [protoInnerStateAt, protoChunkedEkReceivedCt1SampledAt, v1StateInnerPBPinnedAt]
    have ha : (a + 8#64) + 128#64 = a + 136#64 := by bv_omega
    rw [ha, optCt1SentEkReceivedPBAt_eq_exists_pinned, optProtoPolyEncoderAt_eq_exists_pinned]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_swap2, sepConj_assoc]
    exact (sepExists_retract (fun g : V1StatePBGhost => g.b.gEkReceivedCt1Sampled)
      (fun x => { (default : V1StatePBGhost) with b := { (default : V1StatePBGhostB) with gEkReceivedCt1Sampled := x } }) (fun _ => rfl) _).symm
  | ct1Acknowledged v =>
    dsimp only [protoInnerStateAt, protoChunkedCt1AcknowledgedAt, v1StateInnerPBPinnedAt]
    have ha : (a + 8#64) + 128#64 = a + 136#64 := by bv_omega
    have hct1 : optProtoUnchunkedCt1SentAt A (a + 8#64) v.uc =
        ∃∗ g : Unchunked5PBGhost, optCt1SentPBPinnedAt A g (a + 8#64) v.uc := by
      rw [← optCt1SentPBAt_eq_exists_pinned]; cases v.uc <;> rfl
    rw [ha, hct1, optProtoPolyDecoderAt_eq_exists_pinned]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_swap2, sepConj_assoc]
    exact (sepExists_retract (fun g : V1StatePBGhost => g.b.gCt1Acknowledged)
      (fun x => { (default : V1StatePBGhost) with b := { (default : V1StatePBGhostB) with gCt1Acknowledged := x } }) (fun _ => rfl) _).symm
  | ct2Sampled v =>
    dsimp only [protoInnerStateAt, protoChunkedCt2SampledAt, v1StateInnerPBPinnedAt]
    have ha : (a + 8#64) + 56#64 = a + 64#64 := by bv_omega
    rw [ha, optProtoPolyEncoderAt_eq_exists_pinned, optCt2SentPBAt_eq_exists_pinned]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_swap2, sepConj_assoc]
    exact (sepExists_retract (fun g : V1StatePBGhost => g.b.gCt2Sampled)
      (fun x => { (default : V1StatePBGhost) with b := { (default : V1StatePBGhostB) with gCt2Sampled := x } }) (fun _ => rfl) _).symm

theorem v1StatePBAt_eq_optProtoInnerStateAt (A : RustAlloc) (a : BitVec 64)
    (v1 : V1State) :
    CryptoVerification.SpqrV1.ProtoRepr.v1StatePBAt A a v1 =
      optProtoInnerStateAt A a v1.innerState := by
  rcases v1 with ⟨inner⟩
  cases inner with
  | none =>
    unfold CryptoVerification.SpqrV1.ProtoRepr.v1StatePBAt
      CryptoVerification.SpqrV1.ProtoRepr.v1StatePBPinnedAt optProtoInnerStateAt
    exact sepExists_const' _
  | some is =>
    exact (protoInnerStateAt_eq_exists_pinned A a is).symm

theorem optPqRatchetInnerPBAt_eq_proto (A : RustAlloc) (a : BitVec 64)
    (opt : Option PqRatchetState.Inner) :
    optPqRatchetInnerPBAt A a opt = optProtoPqRatchetInnerAt A a opt := by
  cases opt with
  | none => rfl
  | some i =>
    cases i with
    | v1 v1 => exact v1StatePBAt_eq_optProtoInnerStateAt A a v1

theorem pqRatchetStatePBAt_eq_protoPqRatchetStateAt (A : RustAlloc) (a : BitVec 64)
    (st : PqRatchetState) :
    pqRatchetStatePBAt A a st = protoPqRatchetStateAt A a st := by
  unfold pqRatchetStatePBAt protoPqRatchetStateAt
  rw [optPqRatchetInnerPBAt_eq_proto]

/-! ## Panic Blocks (`0x33740` and `0x33d4c`) -/

/-- Slot `sp + 0x60..0xb0` (`80` bytes) after matching `state_pb.chain` with `x23`:
    - if `x23 = noneCap`: `(sp + 0x60#64) ↦₆₄ noneCap ∗ memRegion (sp + 0x68#64) 72`
    - if `x23 ≠ noneCap`: `memRegion (sp + 0x60#64) 80` -/
@[expose] def chainOrigSlotAt (sp x23 : BitVec 64) : SepProp :=
  if x23 = noneCap then
    ((sp + 0x60#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x68#64) 72
  else
    memRegion (sp + 0x60#64) 80

theorem chainOrigSlotAt_none (sp : BitVec 64) :
    chainOrigSlotAt sp noneCap =
      (((sp + 0x60#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x68#64) 72) := by
  unfold chainOrigSlotAt; simp

theorem chainOrigSlotAt_of_ne {sp x23 : BitVec 64} (hne : x23 ≠ noneCap) :
    chainOrigSlotAt sp x23 = memRegion (sp + 0x60#64) 80 := by
  unfold chainOrigSlotAt; simp [hne]

theorem chainOrigSlotAt_entails_memRegion_80 (sp x23 : BitVec 64) :
    chainOrigSlotAt sp x23 ⊢ memRegion (sp + 0x60#64) 80 := by
  unfold chainOrigSlotAt
  split
  · rw [ProofLib.memRegion_split' (b := sp + 0x60#64) (n := 8) (k := 72)
          (b' := sp + 0x68#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)
  · exact Entails.refl _

theorem ult_sub_one_false_of_pos {cap : BitVec 64} (hlt : cap.toNat < 2 ^ 63)
    (hc0 : ¬(cap == 0#64) = true) :
    (cap + 1#64).ult (cap - 1#64) = false := by
  have hne : cap ≠ 0#64 := by rwa [beq_iff_eq] at hc0
  have hpos : 1 ≤ cap.toNat := Nat.pos_of_ne_zero (fun h => hne (BitVec.eq_of_toNat_eq (by simpa using h)))
  have hadd : (cap + 1#64).toNat = cap.toNat + 1 := by
    rw [BitVec.toNat_add]; change (cap.toNat + 1) % 18446744073709551616 = cap.toNat + 1; omega
  have hsub : (cap - 1#64).toNat = cap.toNat - 1 :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr hpos)
  unfold BitVec.ult
  rw [hadd, hsub, decide_eq_false_iff_not]
  omega

theorem ule_sub_one_true_of_pos {cap : BitVec 64} (hlt : cap.toNat < 2 ^ 63)
    (hc0 : ¬(cap == 0#64) = true) :
    (cap - 1#64).ule (cap + 1#64) = true := by
  have hne : cap ≠ 0#64 := by rwa [beq_iff_eq] at hc0
  have hpos : 1 ≤ cap.toNat := Nat.pos_of_ne_zero (fun h => hne (BitVec.eq_of_toNat_eq (by simpa using h)))
  have hadd : (cap + 1#64).toNat = cap.toNat + 1 := by
    rw [BitVec.toNat_add]; change (cap.toNat + 1) % 18446744073709551616 = cap.toNat + 1; omega
  have hsub : (cap - 1#64).toNat = cap.toNat - 1 :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr hpos)
  unfold BitVec.ule
  rw [hadd, hsub, decide_eq_true_eq]
  omega

theorem vecU8Heap_entails_dealloc (A : RustAlloc) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    DecodeState.vecU8Heap A cap ptr bs ⊢
      ⌜cap.toNat < 2 ^ 63⌝ ∗ vecCapPtrDealloc A cap ptr := by
  unfold DecodeState.vecU8Heap vecCapPtrDealloc
  apply Entails.pure_left
  rintro ⟨hle, hcap_lt, _⟩
  refine Entails.pure_right hcap_lt ?_
  by_cases hc : cap = 0#64
  · subst hc; simp; exact Entails.refl _
  · have hc0 : ¬(cap = 0) := hc
    have hc_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hc
    simp only [hc0, hc_beq, Bool.false_eq_true, ↓reduceIte]
    have hbound : bs.length + (cap.toNat - bs.length) ≤ 2 ^ 64 := by omega
    have hjoin :
        (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ⊢
          memRegion ptr cap.toNat := by
      have hsplit := ProofLib.memRegion_split ptr bs.length (cap.toNat - bs.length) hbound
      have hlen : bs.length + (cap.toNat - bs.length) = cap.toNat := Nat.add_sub_of_le hle
      rw [hlen] at hsplit
      rw [hsplit]
      exact sepConj_mono_left (ProofLib.pointsToBytes_entails_memRegion ptr bs)
    exact sepConj_mono_right hjoin

theorem optEpochSecretRegSlotAt_some_entails_dealloc (A : RustAlloc) (sp x21 x27 : BitVec 64)
    (es : EpochSecret) :
    optEpochSecretRegSlotAt A sp x21 x27 (some es) ⊢
      ⌜x21.toNat < 2 ^ 63⌝ ∗
        memRegion (sp + 0x1bc0#64) 16 ∗
        vecCapPtrDealloc A x21 x27 := by
  unfold optEpochSecretRegSlotAt
  apply Entails.pure_left; intro _
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right
    (vecU8Heap_entails_dealloc A x21 x27 es.secret))) ?_
  have h16 :
      ((sp + 0x1bc0#64) ↦₆₄ BitVec.ofNat 64 es.secret.length) ∗
        ((sp + 0x1bc8#64) ↦₆₄ es.epoch) ⊢
        memRegion (sp + 0x1bc0#64) 16 := by
    rw [ProofLib.memRegion_split' (b := sp + 0x1bc0#64) (n := 8) (k := 8)
          (b' := sp + 0x1bc8#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono
      (ProofLib.pointsTo64_entails_memRegion _ _)
      (ProofLib.pointsTo64_entails_memRegion _ _)
  rw [← sepConj_assoc]
  refine Entails.trans (sepConj_mono_left h16) ?_
  exact Entails.of_eq (by ac_rfl)

theorem optChainParamsPBAt_proto_eq (a : BitVec 64) (cp : Option ChainParamsPB) :
    CryptoVerification.SpqrV1.ProtoRepr.optChainParamsPBAt a cp =
      ChainFromVersionNegotiation.optChainParamsPBAt a cp :=
  (ChainFrom.optChainParamsPBAt_eq_protoRepr a cp).symm

theorem versionNegotiationPBAt_eq_exists_pin (A : RustAlloc) (a : BitVec 64)
    (v : VersionNegotiationPB) :
    CryptoVerification.SpqrV1.ProtoRepr.versionNegotiationPBAt A a v =
      (∃∗ pin : VecPin,
        ChainFromVersionNegotiation.versionNegotiationPBAt A pin a v) :=
  ChainFrom.versionNegotiationPBAt_protoRepr_eq_exists A a v

theorem memRegion_72_split_byte (ret : BitVec 64) :
    memRegion ret 72 =
      (∃∗ d0 : BitVec 64, ret ↦₆₄ d0) ∗
      (∃∗ b1 : BitVec 8, (ret + 8#64) ↦₈ b1) ∗
      memRegion (ret + 9#64) 63 := by
  rw [ProofLib.memRegion_split' (b := ret) (n := 8) (k := 64) (b' := ret + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := ret + 8#64) (n := 1) (k := 63) (b' := ret + 9#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight ret,
      ProofLib.memRegion_one (ret + 8#64)]

theorem sendResultAt_none_of_byte (A : RustAlloc) (ret : BitVec 64) (b8 : BitVec 8) :
    (ret ↦₆₄ 18446744073709551615#64) ∗ ((ret + 8#64) ↦₈ b8) ∗ memRegion (ret + 9#64) 63 ⊢
      spqrSendResultAt A ret none := by
  unfold spqrSendResultAt LibsignalTripleRatchetRepr.errTag
  rw [ProofLib.memRegion_split' (b := ret + 8#64) (n := 1) (k := 63) (b' := ret + 9#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo8_entails_memRegion _ _))

@[local simp, local arm64_norm, local wp_norm]
theorem extractLsb_lo_append64 (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem extractLsb_hi_append64 (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by bv_kernel

theorem memRegion_72_split_words3 (ret : BitVec 64) :
    memRegion ret 72 =
      (∃∗ d0 : BitVec 64, ret ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (ret + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (ret + 16#64) ↦₆₄ d2) ∗
      (∃∗ d3 : BitVec 64, (ret + 24#64) ↦₆₄ d3) ∗
      memRegion (ret + 32#64) 40 := by
  rw [ProofLib.memRegion_split' (b := ret) (n := 8) (k := 64) (b' := ret + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := ret + 8#64) (n := 8) (k := 56) (b' := ret + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 16#64) (n := 8) (k := 48) (b' := ret + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 24#64) (n := 8) (k := 40) (b' := ret + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight ret,
      ProofLib.memRegion_eight (ret + 8#64),
      ProofLib.memRegion_eight (ret + 16#64),
      ProofLib.memRegion_eight (ret + 24#64)]

theorem sendResultAt_none_of_words3 (A : RustAlloc) (ret w1 w2 w3 : BitVec 64) :
    (ret ↦₆₄ 18446744073709551615#64) ∗ ((ret + 8#64) ↦₆₄ w1) ∗ ((ret + 16#64) ↦₆₄ w2) ∗
      ((ret + 24#64) ↦₆₄ w3) ∗ memRegion (ret + 32#64) 40 ⊢
      spqrSendResultAt A ret none := by
  unfold spqrSendResultAt LibsignalTripleRatchetRepr.errTag
  rw [ProofLib.memRegion_split' (b := ret + 8#64) (n := 8) (k := 56) (b' := ret + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 16#64) (n := 8) (k := 48) (b' := ret + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 24#64) (n := 8) (k := 40) (b' := ret + 32#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))))

theorem memRegion_72_split_dwords_words (ret : BitVec 64) :
    memRegion ret 72 =
      (∃∗ d0 : BitVec 64, ret ↦₆₄ d0) ∗
      (∃∗ w0 : BitVec 32, (ret + 8#64) ↦₃₂ w0) ∗
      (∃∗ w1 : BitVec 32, (ret + 12#64) ↦₃₂ w1) ∗
      (∃∗ d2 : BitVec 64, (ret + 16#64) ↦₆₄ d2) ∗
      (∃∗ d3 : BitVec 64, (ret + 24#64) ↦₆₄ d3) ∗
      memRegion (ret + 32#64) 40 := by
  rw [ProofLib.memRegion_split' (b := ret) (n := 8) (k := 64) (b' := ret + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := ret + 8#64) (n := 4) (k := 60) (b' := ret + 12#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 12#64) (n := 4) (k := 56) (b' := ret + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 16#64) (n := 8) (k := 48) (b' := ret + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 24#64) (n := 8) (k := 40) (b' := ret + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight ret,
      ProofLib.memRegion_four (ret + 8#64),
      ProofLib.memRegion_four (ret + 12#64),
      ProofLib.memRegion_eight (ret + 16#64),
      ProofLib.memRegion_eight (ret + 24#64)]

theorem sendResultAt_none_of_dwords_words (A : RustAlloc) (ret : BitVec 64)
    (d0 d1 : BitVec 32) (w2 w3 : BitVec 64) :
    (ret ↦₆₄ 18446744073709551615#64) ∗ ((ret + 8#64) ↦₃₂ d0) ∗ ((ret + 12#64) ↦₃₂ d1) ∗
      ((ret + 16#64) ↦₆₄ w2) ∗ ((ret + 24#64) ↦₆₄ w3) ∗ memRegion (ret + 32#64) 40 ⊢
      spqrSendResultAt A ret none := by
  unfold spqrSendResultAt LibsignalTripleRatchetRepr.errTag
  rw [ProofLib.memRegion_split' (b := ret + 8#64) (n := 4) (k := 60) (b' := ret + 12#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 12#64) (n := 4) (k := 56) (b' := ret + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 16#64) (n := 8) (k := 48) (b' := ret + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 24#64) (n := 8) (k := 40) (b' := ret + 32#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right
    (sepConj_mono (ProofLib.pointsTo32_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo32_entails_memRegion _ _)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)))))

end CryptoVerification.SpqrV1.Top.Send
