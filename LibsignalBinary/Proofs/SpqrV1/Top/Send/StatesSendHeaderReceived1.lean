/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampled2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOk

/-!
# `spqr::send::<HookRng>`: Inlined `States::send` `.headerReceived` Arm (Part 1: `+1312..+1680`)

**Checked by Lean.**

Verifies the first half (`0x30d7c`, `entry + 1312#64 .. + 1680#64`) of the inlined
`.headerReceived` arm of `<States>::send`: RNG draw, `encapsulate1`, `hkdf_to_vec`, and
`<Authenticator>::update`.
-/

public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.GF.UnacceleratedMul CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Drop CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero

theorem chunkedStatesAt_headerReceived_unfold (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    chunkedStatesAt A a (.headerReceived st) =
      ((a ↦₆₄ 8#64) ∗
       chunkedHeaderReceivedAt A (a + 8#64) st ∗
       memRegion (a + 488#64) 440) := by
  simp only [chunkedStatesAt, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

@[simp] theorem encaps1_ct1_len (K : MlKem) (hdr : Header) (rand : List.Vector (BitVec 8) 32)
    {ct1 : List.Vector (BitVec 8) 960} {es : List.Vector (BitVec 8) 2080} {ss : List.Vector (BitVec 8) 32}
    (_h : K.encaps1 hdr rand = some (ct1, es, ss)) :
    ct1.toList.length = 960 :=
  List.Vector.toList_length _

@[simp] theorem encaps1_es_len (K : MlKem) (hdr : Header) (rand : List.Vector (BitVec 8) 32)
    {ct1 : List.Vector (BitVec 8) 960} {es : List.Vector (BitVec 8) 2080} {ss : List.Vector (BitVec 8) 32}
    (_h : K.encaps1 hdr rand = some (ct1, es, ss)) :
    es.toList.length = 2080 :=
  List.Vector.toList_length _

@[simp] theorem encaps1_ss_len (K : MlKem) (hdr : Header) (rand : List.Vector (BitVec 8) 32)
    {ct1 : List.Vector (BitVec 8) 960} {es : List.Vector (BitVec 8) 2080} {ss : List.Vector (BitVec 8) 32}
    (_h : K.encaps1 hdr rand = some (ct1, es, ss)) :
    ss.toList.length = 32 :=
  List.Vector.toList_length _

/-- Big-endian 8-byte encoding of an `Epoch` (`u64::to_be_bytes`). -/
@[expose] def epochBeBytes (v : BitVec 64) : Bytes :=
  [ v.extractLsb' 56 8, v.extractLsb' 48 8, v.extractLsb' 40 8, v.extractLsb' 32 8,
    v.extractLsb' 24 8, v.extractLsb' 16 8, v.extractLsb'  8 8, v.extractLsb'  0 8 ]

theorem hkdfToVec_32_eq {F : ShaCompress} (salt ikm info : Bytes) :
    hkdfToVec F salt ikm info 32 = .ok (hkdfToVecUnchecked F salt ikm info 32) :=
  hkdfToSlice_of_le F salt ikm info (by decide)

theorem unchunkedSendCt1_of_ok {F : ShaCompress} (K : MlKem)
    (self : Unchunked.SendCt.HeaderReceived (spqrAuthApi F)) {tape : Bytes} (h : 32 ≤ tape.length)
    {ct1 : List.Vector (BitVec 8) 960} {es : List.Vector (BitVec 8) 2080} {ss : List.Vector (BitVec 8) 32}
    (hencaps : K.encaps1 self.hdr ⟨tape.take 32, by rw [List.length_take]; omega⟩ = some (ct1, es, ss)) :
    let info := sckaKeyInfoPrefix ++ epochBeBytes self.epoch
    let secret := hkdfToVecUnchecked F (List.replicate 32 0#8) ss.toList info 32
    let auth' := self.auth.update F self.epoch secret
    let uc' : Unchunked.SendCt.Ct1Sent (spqrAuthApi F) :=
      { epoch := self.epoch, auth := auth', hdr := self.hdr, es := es.toList, ct1 := ct1.toList }
    self.send_ct1 K tape =
      .ok (uc', ct1.toList, { epoch := self.epoch, secret := secret }, tape.drop 32) := by
  dsimp only
  unfold Unchunked.SendCt.HeaderReceived.send_ct1
  rw [encaps1_of_le_32 K self.hdr h, hencaps]
  change (do
    let secret ← liftSpqrPanic (hkdfToVec F (List.replicate 32 0#8) ss.toList
      (sckaKeyInfoPrefix ++ epochBeBytes self.epoch) 32)
    let auth ← liftSpqrPanic (.ok (self.auth.update F self.epoch secret))
    Except.ok (({ epoch := self.epoch, auth := auth, hdr := self.hdr, es := es.toList, ct1 := ct1.toList } :
        Unchunked.SendCt.Ct1Sent (spqrAuthApi F)),
      ct1.toList, ({ epoch := self.epoch, secret := secret } : EpochSecret), tape.drop 32)) = _
  rw [hkdfToVec_32_eq]
  rfl

theorem send_ct1_chunk_of_ok {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) {tape : Bytes} (h : 32 ≤ tape.length)
    {ct1 : List.Vector (BitVec 8) 960} {es : List.Vector (BitVec 8) 2080} {ss : List.Vector (BitVec 8) 32}
    {sending_ct1 sending_ct1' : PolyEncoder} {chunk : Chunk}
    (hencaps : K.encaps1 st.uc.hdr ⟨tape.take 32, by rw [List.length_take]; omega⟩ = some (ct1, es, ss))
    (henc : expectEncodeBytes spqrPolyApi "v1/chunked/send_ct.rs:131" ct1.toList = .ok sending_ct1)
    (hnc : sending_ct1.nextChunk = .ok (sending_ct1', chunk)) :
    let info := sckaKeyInfoPrefix ++ epochBeBytes st.uc.epoch
    let secret := hkdfToVecUnchecked F (List.replicate 32 0#8) ss.toList info 32
    let auth' := st.uc.auth.update F st.uc.epoch secret
    let uc' : Unchunked.SendCt.Ct1Sent (spqrAuthApi F) :=
      { epoch := st.uc.epoch, auth := auth', hdr := st.uc.hdr, es := es.toList, ct1 := ct1.toList }
    st.send_ct1_chunk K tape =
      .ok ({ uc := uc', sending_ct1 := sending_ct1', receiving_ek := st.receiving_ek },
        chunk, { epoch := st.uc.epoch, secret := secret }, tape.drop 32) := by
  dsimp only
  have hnc' : spqrPolyApi.next_chunk sending_ct1 = .ok (sending_ct1', chunk) := by
    change sending_ct1.nextChunk.mapError PolyPanic.toSpqrPanic = .ok (sending_ct1', chunk)
    rw [hnc]; rfl
  unfold Chunked.SendCt.HeaderReceived.send_ct1_chunk
  rw [unchunkedSendCt1_of_ok K st.uc h hencaps]
  simp only [henc, hnc', Bind.bind, Except.bind, liftM, monadLift, MonadLift.monadLift, liftSpqrPanic]

theorem send_ct1_chunk_of_nextChunk_err {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) {tape : Bytes} (h : 32 ≤ tape.length)
    {ct1 : List.Vector (BitVec 8) 960} {es : List.Vector (BitVec 8) 2080} {ss : List.Vector (BitVec 8) 32}
    {sending_ct1 : PolyEncoder} {p : PolyPanic}
    (hencaps : K.encaps1 st.uc.hdr ⟨tape.take 32, by rw [List.length_take]; omega⟩ = some (ct1, es, ss))
    (henc : expectEncodeBytes spqrPolyApi "v1/chunked/send_ct.rs:131" ct1.toList = .ok sending_ct1)
    (hnc : sending_ct1.nextChunk = .error p) :
    st.send_ct1_chunk K tape = .error (.spqr p.toSpqrPanic) := by
  have hnc' : spqrPolyApi.next_chunk sending_ct1 = .error p.toSpqrPanic := by
    change sending_ct1.nextChunk.mapError PolyPanic.toSpqrPanic = .error p.toSpqrPanic
    rw [hnc]; rfl
  unfold Chunked.SendCt.HeaderReceived.send_ct1_chunk
  rw [unchunkedSendCt1_of_ok K st.uc h hencaps]
  simp only [henc, hnc', Bind.bind, Except.bind, liftM, monadLift, MonadLift.monadLift, liftSpqrPanic]

theorem chunkedHeaderReceivedAt_unfold (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    chunkedHeaderReceivedAt A a st =
      (authenticatorAt A a st.uc.auth ∗
       vecU8 A (a + 48#64) st.uc.hdr ∗
       ((a + 72#64) ↦₆₄ st.uc.epoch) ∗
       polyDecoderAt A (a + 80#64) st.receiving_ek) := by
  simp only [chunkedHeaderReceivedAt, unchunkedHeaderReceivedAt,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem zeroed_entails_memRegion (ptr : BitVec 64) (n : Nat) :
    (ptr ↦ₛ List.replicate n 0#8) ⊢ memRegion ptr n := by
  have h := pointsToBytes_entails_memRegion ptr (List.replicate n 0#8)
  rwa [List.length_replicate] at h

/-- Residual heap ownership of `vecU8At A a cap ptr bs` after borrowing `(ptr ↦ₛ bs)`. -/
@[expose] def vecU8Rest (A : RustAlloc) (cap ptr : BitVec 64) (bs : Bytes) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
  if cap = 0 then emp
  else
    A.live ptr cap.toNat 1 ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)

theorem vecU8At_expose_rest {A : RustAlloc} (a cap ptr : BitVec 64) (bs : Bytes) :
    vecU8At A a cap ptr bs ⊢
    ⌜bs.length < 2 ^ 63⌝ ∗
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
    (ptr ↦ₛ bs) ∗ vecU8Rest A cap ptr bs := by
  unfold vecU8At vecHeader vecU8Rest
  by_cases hc : cap = 0#64
  · subst hc
    simp only [show (0#64 : BitVec 64) = 0 from rfl, ↓reduceIte,
      show (0 : BitVec 64).toNat = 0 from rfl, sepConj_emp, sepConj_assoc]
    have hcomm :
        (a ↦₆₄ 0) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ⌜bs.length ≤ 0 ∧ 0 < 2 ^ 63 ∧ ptr ≠ 0⌝ =
        ⌜bs.length ≤ 0 ∧ 0 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (a ↦₆₄ 0) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) := by ac_rfl
    rw [hcomm]
    refine Entails.pure_left fun ⟨hle, hlt, hp⟩ => ?_
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    simp only [pointsToBytes_nil, sepConj_emp, emp_sepConj, List.length_nil]
    refine Entails.pure_right hlt ?_
    have hcomm2 :
        (a ↦₆₄ 0) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 0) ∗
        ⌜0 ≤ 0 ∧ 0 < 2 ^ 63 ∧ ptr ≠ 0⌝ =
        ⌜0 ≤ 0 ∧ 0 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ((a ↦₆₄ 0) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 0)) := by ac_rfl
    rw [hcomm2]
    exact Entails.pure_right ⟨hle, hlt, hp⟩ (Entails.refl _)
  · have hc0 : cap ≠ 0 := hc
    simp only [hc0, ↓reduceIte, sepConj_assoc]
    have hcomm :
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) =
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ A.live ptr cap.toNat 1 ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) := by ac_rfl
    rw [hcomm]
    refine Entails.pure_left fun ⟨hle, hlt, hp⟩ => ?_
    refine Entails.pure_right (by omega) ?_
    have hcomm2 :
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr cap.toNat 1 ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) =
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
         (ptr ↦ₛ bs) ∗ A.live ptr cap.toNat 1 ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by ac_rfl
    rw [hcomm2]
    exact Entails.pure_right ⟨hle, hlt, hp⟩ (Entails.refl _)

theorem vecU8_fold_rest {A : RustAlloc} (a cap ptr : BitVec 64) (bs : Bytes) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗ vecU8Rest A cap ptr bs ⊢
    vecU8 A a bs := by
  unfold vecU8
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  unfold vecU8At vecHeader vecU8Rest
  by_cases hc : cap = 0#64
  · subst hc
    simp only [show (0#64 : BitVec 64) = 0 from rfl, ↓reduceIte,
      show (0 : BitVec 64).toNat = 0 from rfl, sepConj_emp, sepConj_assoc]
    have hcomm :
        (a ↦₆₄ 0) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ ⌜bs.length ≤ 0 ∧ 0 < 2 ^ 63 ∧ ptr ≠ 0⌝ =
        ⌜bs.length ≤ 0 ∧ 0 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (a ↦₆₄ 0) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) := by ac_rfl
    rw [hcomm]
    refine Entails.pure_left fun ⟨hle, hlt, hp⟩ => ?_
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    simp only [pointsToBytes_nil, sepConj_emp, List.length_nil]
    have hcomm2 :
        (a ↦₆₄ 0) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 0) ∗
        ⌜0 ≤ 0 ∧ 0 < 2 ^ 63 ∧ ptr ≠ 0⌝ =
        ⌜0 ≤ 0 ∧ 0 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ((a ↦₆₄ 0) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 0)) := by ac_rfl
    rw [hcomm2]
    exact Entails.pure_right ⟨hle, hlt, hp⟩ (Entails.refl _)
  · have hc0 : cap ≠ 0 := hc
    simp only [hc0, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)

theorem exists_words4_of_len32 (bs : List (BitVec 8)) (h : bs.length = 32) :
    ∃ w0 w1 w2 w3 : BitVec 64, ∀ a : BitVec 64,
      (a ↦ₛ bs) = words4At a w0 w1 w2 w3 := by
  obtain ⟨w0, w1, w2, w3, hw⟩ :=
    CryptoVerification.SpqrV1.Top.MessageSerialize.list_eq_unpack64_4_of_len32 bs h
  refine ⟨w0, w1, w2, w3, fun a => ?_⟩
  rw [hw, CryptoVerification.SpqrV1.Top.MessageSerialize.pointsToBytes_unpack64_4_eq a]
  rfl

theorem sepWPp_intro_rodata {prog : Program} {ret : BitVec 64} {s : State}
    {roAddr : BitVec 64} {roBytes : List (BitVec 8)} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hro : ∀ {R : SepProp}, (s.mem ⊨ R) → (s.mem ⊨ (roAddr ↦ᵣ roBytes) ∗ R))
    (h : SepWPp prog ret s ((roAddr ↦ᵣ roBytes) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hPR hL
  apply h R ?_ hL
  rw [sepConj_assoc]
  exact hro hPR

@[expose] def sckaInfoW0 : BitVec 64 := 0x505f6c616e676953#64
@[expose] def sckaInfoW1 : BitVec 64 := 0x5f31565f414b4351#64
@[expose] def sckaInfoW2 : BitVec 64 := 0x3836374d454b4c4d#64
@[expose] def sckaInfoW3 : BitVec 64 := 0x654b20414b43533a#64

theorem sckaKeyInfoPrefix_eq_unpack64 :
    sckaKeyInfoPrefix =
      unpack64 sckaInfoW0 ++
        (unpack64 sckaInfoW1 ++
          (unpack64 sckaInfoW2 ++
            (unpack64 sckaInfoW3 ++ [0x79#8]))) := by
  rfl_kernel

theorem unpack64_rev64_eq_epochBeBytes (v : BitVec 64) :
    unpack64 (Arm64.rev64 v) = epochBeBytes v :=
  unpack64_rev64_eq_toBEBytes v

theorem sepWPp_intro_rodata64 {prog : Program} {ret : BitVec 64} {s : State}
    {roAddr : BitVec 64} {w : BitVec 64} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hro : ∀ {R : SepProp}, (s.mem ⊨ R) → (s.mem ⊨ (roAddr ↦₆₄ᵣ w) ∗ R))
    (h : SepWPp prog ret s ((roAddr ↦₆₄ᵣ w) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hPR hL
  apply h R ?_ hL
  rw [sepConj_assoc]
  exact hro hPR

theorem memRegion_41_eq_infoSlots (a : BitVec 64) :
    memRegion a 41 =
      (∃∗ d0 : BitVec 64, a ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (a + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (a + 16#64) ↦₆₄ d2) ∗
      (∃∗ d3 : BitVec 64, (a + 24#64) ↦₆₄ d3) ∗
      (∃∗ b32 : BitVec 8, (a + 32#64) ↦₈ b32) ∗
      (∃∗ d33 : BitVec 64, (a + 33#64) ↦₆₄ d33) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 32) (k := 9) (b' := a + 32#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 1) (k := 8) (b' := a + 33#64) rfl (by bv_omega) (by decide),
      memRegion_32_eq_words4 a,
      ProofLib.memRegion_one (a + 32#64),
      ProofLib.memRegion_eight (a + 33#64)]
  ac_rfl

theorem infoSlots_entails_pointsToBytes (a epoch : BitVec 64) :
    (a ↦₆₄ sckaInfoW0) ∗
      ((a + 8#64) ↦₆₄ sckaInfoW1) ∗
      ((a + 16#64) ↦₆₄ sckaInfoW2) ∗
      ((a + 24#64) ↦₆₄ sckaInfoW3) ∗
      ((a + 32#64) ↦₈ 0x79#8) ∗
      ((a + 33#64) ↦₆₄ Arm64.rev64 epoch) ⊢
    (a ↦ₛ (sckaKeyInfoPrefix ++ epochBeBytes epoch)) := by
  rw [sckaKeyInfoPrefix_eq_unpack64]
  simp only [List.append_assoc, List.singleton_append]
  rw [pointsToBytes_append a (unpack64 sckaInfoW0), unpack64_length,
      pointsToBytes_append (a + 8#64) (unpack64 sckaInfoW1), unpack64_length,
      show (a + 8#64) + 8#64 = a + 16#64 by bv_omega,
      pointsToBytes_append (a + 16#64) (unpack64 sckaInfoW2), unpack64_length,
      show (a + 16#64) + 8#64 = a + 24#64 by bv_omega,
      pointsToBytes_append (a + 24#64) (unpack64 sckaInfoW3), unpack64_length,
      show (a + 24#64) + 8#64 = a + 32#64 by bv_omega,
      pointsToBytes_cons (a + 32#64) 0x79#8,
      show (a + 32#64) + 1#64 = a + 33#64 by bv_omega,
      ← unpack64_rev64_eq_epochBeBytes epoch,
      ← pointsTo64_eq_pointsToBytes a sckaInfoW0,
      ← pointsTo64_eq_pointsToBytes (a + 8#64) sckaInfoW1,
      ← pointsTo64_eq_pointsToBytes (a + 16#64) sckaInfoW2,
      ← pointsTo64_eq_pointsToBytes (a + 24#64) sckaInfoW3,
      ← pointsTo64_eq_pointsToBytes (a + 33#64) (Arm64.rev64 epoch)]
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_32_split_24_8 (a : BitVec 64) :
    memRegion a 32 = memRegion a 24 ∗ memRegion (a + 24#64) 8 :=
  ProofLib.memRegion_split' (b := a) (n := 24) (k := 8) (b' := a + 24#64) rfl rfl (by decide)

theorem memRegion_32_16_eq_words2 (sp : BitVec 64) :
    memRegion (sp + 32#64) 16 =
      (∃∗ d0 : BitVec 64, (sp + 32#64) ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (sp + 40#64) ↦₆₄ d1) := by
  rw [ProofLib.memRegion_split' (b := sp + 32#64) (n := 8) (k := 8) (b' := sp + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 32#64), ProofLib.memRegion_eight (sp + 40#64)]

/-! ## Sub-Step 2 (`entry + 1504#64 -> entry + 1680#64`) -/

theorem pointsTo8_and_ct1_entails_memRegion_961 (sp : BitVec 64) (b0 : BitVec 8)
    (ct1 : List.Vector (BitVec 8) 960) :
    ((sp + 4704#64) ↦₈ b0) ∗ ((sp + 4705#64) ↦ₛ ct1.toList) ⊢ memRegion (sp + 4704#64) 961 := by
  have h1 : ((sp + 4704#64) ↦₈ b0) ⊢ memRegion (sp + 4704#64) 1 := by
    rw [ProofLib.memRegion_one (sp + 4704#64)]
    exact ProofLib.Entails.sepExists_intro b0
  have h2 := pointsToBytes_entails_memRegion (sp + 4705#64) ct1.toList
  rw [List.Vector.toList_length] at h2
  rw [ProofLib.memRegion_split' (b := sp + 4704#64) (n := 1) (k := 960) (b' := sp + 4705#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono h1 h2

theorem fold_authenticatorAt_of_inline_local (A : RustAlloc) (g : AuthenticatorGhost)
    (a : BitVec 64) (auth : Authenticator) :
    authInlineWordsAt g a auth ∗ authHeapBufs A g auth ⊢ authenticatorAt A a auth := by
  rw [← authenticatorPinAt_eq_inline_heap A g a auth]
  exact authenticatorPinAt_entails_authenticatorAt A g a auth

theorem sp_add_4704_orr_1_eq {sp : BitVec 64} (hsp : (sp &&& 15#64 == 0#64) = true) :
    ((sp + 4704#64) ||| 1#64) = sp + 4705#64 := by
  have hsp' : sp &&& 15#64 = 0#64 := eq_of_beq hsp
  revert hsp'; bv_bits

theorem epochBeBytes_length (v : BitVec 64) : (epochBeBytes v).length = 8 := rfl

theorem vecU8_len32_expose_7536 {A : RustAlloc} (sp : BitVec 64) (bs : Bytes) (hlen : bs.length = 32) :
    vecU8 A (sp + 7536#64) bs ⊢
    (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
      ⌜32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0 ∧ (cap == 0#64) = false⌝ ∗
      (((sp + 7536#64) ↦₆₄ cap) ∗
       ((sp + 7544#64) ↦₆₄ ptr) ∗
       ((sp + 7552#64) ↦₆₄ 32#64) ∗
       A.live ptr cap.toNat 1 ∗
       (ptr ↦ₛ bs) ∗
       memRegion (ptr + 32#64) (cap.toNat - 32))) := by
  unfold vecU8
  apply ProofLib.Entails.sepExists_elim; intro cap
  apply ProofLib.Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  unfold vecU8At vecHeader
  rw [hlen, show (sp + 7536#64) + 8#64 = sp + 7544#64 by bv_omega,
      show (sp + 7536#64) + 16#64 = sp + 7552#64 by bv_omega,
      show BitVec.ofNat 64 32 = 32#64 from rfl]
  have hcomm :
      (((sp + 7536#64) ↦₆₄ cap) ∗ ((sp + 7544#64) ↦₆₄ ptr) ∗ ((sp + 7552#64) ↦₆₄ 32#64)) ∗
      ⌜32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗ memRegion (ptr + 32#64) (cap.toNat - 32)) =
      ⌜32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (((sp + 7536#64) ↦₆₄ cap) ∗ ((sp + 7544#64) ↦₆₄ ptr) ∗ ((sp + 7552#64) ↦₆₄ 32#64) ∗
       (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗ memRegion (ptr + 32#64) (cap.toNat - 32))) := by
    ac_rfl
  rw [hcomm]
  refine Entails.pure_left fun ⟨hle, hlt, hp⟩ => ?_
  have hc : cap ≠ 0 := by intro h0; subst h0; revert hle; decide
  simp only [hc, ↓reduceIte]
  exact Entails.pure_right ⟨hle, hlt, hp, beq_false_of_ne hc⟩ (Entails.of_eq (by ac_rfl))

end CryptoVerification.SpqrV1.Top.Send
