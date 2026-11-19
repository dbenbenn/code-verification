/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Defs
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Defs
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChain
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `spqr::send`: Return Assembly, Epoch Dealloc, and Initial `PqRatchetState` Drop

Return struct assembly (`0x320a4..0x32114`), consumed epoch-secret check (`0x32114..0x32134`),
and `versionNegotiation` / `chain` / `none` / `.keysUnsampled` drop steps (`0x32134..0x32490`)
in `spqr::send::<HookRng>`.
-/

public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification
open CryptoVerification.CodeLayout
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Prost.EncodeToVec hiding SepWP.done

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

private theorem send_noneCap2_add_two_beq_zero :
    (0xfffffffffffffffe#64 + 2#64 == 0#64) = true := rfl

private theorem send_noneCap2_add_two_bne_zero :
    (0xfffffffffffffffe#64 + 2#64 != 0#64) = false := rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr v1StatePBPinnedAt
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero Drop.noneCap_add_two_beq_zero
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  send_noneCap2_add_two_beq_zero send_noneCap2_add_two_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero

theorem pqRatchetStatePBPinnedAt_entails_proto (A : RustAlloc) (g : PqRatchetStatePBGhost)
    (a : BitVec 64) (st : PqRatchetState) :
    pqRatchetStatePBPinnedAt A g a st ⊢ Drop.protoPqRatchetStateAt A a st := by
  rw [← pqRatchetStatePBAt_eq_protoPqRatchetStateAt, pqRatchetStatePBAt_eq_exists_pinned]
  exact Entails.sepExists_right g (Entails.refl _)

private theorem encodeVarintLoop_len_le_fin (fuel : Nat) (a : BitVec 64) :
    (encodeVarintLoop fuel a).length ≤ fuel := by
  induction fuel generalizing a with
  | zero => simp [encodeVarintLoop]
  | succ fuel ih =>
    simp only [encodeVarintLoop]; split
    · simp
    · simp only [List.length_cons]; have := ih (a >>> 7); omega

private theorem encode_varint_len_le_fin (a : BitVec 64) (into : Bytes) :
    (CryptoVerification.LibsignalSpqrV1.encode_varint a into).length ≤ into.length + 10 := by
  change (into ++ encodeVarintLoop MAX_VARINT_BYTES_LEN a).length ≤ into.length + 10
  rw [List.length_append]
  have h := encodeVarintLoop_len_le_fin MAX_VARINT_BYTES_LEN a
  have hm : MAX_VARINT_BYTES_LEN = 10 := rfl; omega

private theorem encode_chunk_len_le_fin {P : PolyApi} (c : P.Chunk) (into : Bytes) :
    (encode_chunk c into).length ≤ into.length + 42 := by
  dsimp only [encode_chunk]
  rw [List.length_append, List.Vector.toList_length]
  have h := encode_varint_len_le_fin ((P.chunkIndex c).zeroExtend 64) into
  omega

/-- Every serialized SPQR message `msg.serialize index` has length `≤ 64 < 2 ^ 32`, discharging
    `hmsg_len : msgBytes.length < 2 ^ 32` in `spqrSendResultAt` / `step_send_finish_320a4`. -/
theorem message_serialize_length_lt_pow32 {P : PolyApi} (msg : Message P) (index : BitVec 32) :
    (msg.serialize index).length < 2 ^ 32 := by
  dsimp only [Message.serialize]
  have h1 := encode_varint_len_le_fin msg.epoch [1#8]
  have h2 := encode_varint_len_le_fin (index.zeroExtend 64) (encode_varint msg.epoch [1#8])
  set into2 := encode_varint (index.zeroExtend 64) (encode_varint msg.epoch [1#8]) ++
    [(MessageType.from_payload msg.payload).toU8]
  have h2' : into2.length ≤ 22 := by
    rw [List.length_append, List.length_singleton]
    simp only [List.length_singleton] at h1
    omega
  cases msg.payload with
  | none | ct1Ack _ => exact Nat.lt_of_le_of_lt h2' (by decide)
  | hdr c | ek c | ekCt1Ack c | ct1 c | ct2 c =>
    exact Nat.lt_of_le_of_lt (encode_chunk_len_le_fin c into2) (by omega)

/-! ## 2. Tail-Deallocation Helpers at `0x31a4c` (`+4592`) and `0x31a50` (`+4596`) -/

theorem send_stackAt_callee_eq_allocHook (sp : BitVec 64) :
    stackAt sp spqrSendCalleeStack =
      memRegion (sp - 123008#64) (spqrSendCalleeStack - allocHookStack) ∗
        stackAt sp allocHookStack :=
  ProofLib.stackAt_split_bottom sp allocHookStack
    (spqrSendCalleeStack - allocHookStack) (by decide)

theorem send_stackAt_callee_eq_dropStack32 (sp : BitVec 64) :
    stackAt sp spqrSendCalleeStack =
      memRegion (sp - 123008#64) (spqrSendCalleeStack - dropStack32) ∗
        stackAt sp dropStack32 :=
  ProofLib.stackAt_split_bottom sp dropStack32
    (spqrSendCalleeStack - dropStack32) (by decide)

theorem stackAt_spqrSendCallee_eq_dropStack48 (sp : BitVec 64) :
    stackAt sp spqrSendCalleeStack =
      memRegion (sp - 123008#64) (spqrSendCalleeStack - dropStack48) ∗
        stackAt sp dropStack48 :=
  ProofLib.stackAt_split_bottom sp dropStack48
    (spqrSendCalleeStack - dropStack48) (by decide)

theorem stackAt_spqrSendCallee_eq_dropStack64 (sp : BitVec 64) :
    stackAt sp spqrSendCalleeStack =
      memRegion (sp - 123008#64) (spqrSendCalleeStack - dropStack64) ∗
        stackAt sp dropStack64 :=
  ProofLib.stackAt_split_bottom sp dropStack64
    (spqrSendCalleeStack - dropStack64) (by decide)

attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_lo_append64 extractLsb_hi_append64

/-- Stack slots `[sp + 8]`, `[sp + 24]`, `[sp + 40]` holding the optional 32-byte message key
    (`key : CryptoGames.HKDF.Salt`) at `0x320a4`:
    - `none`: `[sp + 8] = mkPtr`, `[sp + 24] = 0#64`, `[sp + 40] = mkCap`, and `vecU8Heap A mkCap mkPtr []`
    - `some k`: `[sp + 8] = mkPtr`, `[sp + 24] = 32#64`, `[sp + 40] = mkCap`, and `vecU8Heap A mkCap mkPtr k.toList` -/
@[expose] def optMsgKeySlotsAt (A : RustAlloc) (sp : BitVec 64) :
    CryptoGames.HKDF.Salt → SepProp
  | none =>
    ∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
      ((sp + 8#64) ↦₆₄ mkPtr) ∗
      ((sp + 24#64) ↦₆₄ 0#64) ∗
      ((sp + 40#64) ↦₆₄ mkCap) ∗
      DecodeState.vecU8Heap A mkCap mkPtr []
  | some k =>
    ∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
      ((sp + 8#64) ↦₆₄ mkPtr) ∗
      ((sp + 24#64) ↦₆₄ 32#64) ∗
      ((sp + 40#64) ↦₆₄ mkCap) ∗
      DecodeState.vecU8Heap A mkCap mkPtr k.toList

theorem vecU8_expose_words (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        DecodeState.vecU8Heap A cap ptr bs := by
  unfold vecU8
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  unfold vecU8At vecHeader DecodeState.vecU8Heap
  exact Entails.of_eq (by ac_rfl)

theorem words_to_vecU8 (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      DecodeState.vecU8Heap A cap ptr bs ⊢
      vecU8 A a bs := by
  unfold vecU8
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  unfold vecU8At vecHeader DecodeState.vecU8Heap
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_16_words2 (a : BitVec 64) :
    memRegion a 16 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 8) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64)]

theorem words2_to_memRegion_16 (a w0 w1 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ⊢ memRegion a 16 := by
  rw [memRegion_16_words2 a]
  exact sepConj_mono (Entails.sepExists_right w0 (Entails.refl _))
    (Entails.sepExists_right w1 (Entails.refl _))

theorem memRegion_48_words6 (a : BitVec 64) :
    memRegion a 48 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (a + 16#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (a + 24#64) ↦₆₄ w3) ∗
      (∃∗ w4 : BitVec 64, (a + 32#64) ↦₆₄ w4) ∗
      (∃∗ w5 : BitVec 64, (a + 40#64) ↦₆₄ w5) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 40) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 32) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 24) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 16) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 8) (b' := a + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64), ProofLib.memRegion_eight (a + 24#64),
      ProofLib.memRegion_eight (a + 32#64), ProofLib.memRegion_eight (a + 40#64)]

theorem words6_to_memRegion_48 (a w0 w1 w2 w3 w4 w5 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
    ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ⊢
      memRegion a 48 := by
  rw [memRegion_48_words6 a]
  exact sepConj_mono (Entails.sepExists_right w0 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right w1 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right w2 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right w3 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right w4 (Entails.refl _))
      (Entails.sepExists_right w5 (Entails.refl _))))))

theorem memRegion_24_words3' (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (a + 16#64) ↦₆₄ w2) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 16) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 8) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64)]

theorem words3_to_memRegion_24' (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢ memRegion a 24 := by
  rw [memRegion_24_words3' a]
  exact sepConj_mono (Entails.sepExists_right w0 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right w1 (Entails.refl _))
      (Entails.sepExists_right w2 (Entails.refl _)))

theorem memRegion_72_split_48_24 (ret : BitVec 64) :
    memRegion ret 72 = memRegion ret 48 ∗ memRegion (ret + 48#64) 24 := by
  rw [ProofLib.memRegion_split' (b := ret) (n := 48) (k := 24) (b' := ret + 48#64)
        rfl rfl (by decide)]

theorem memRegion_24_split_8_16 (a : BitVec 64) :
    memRegion a 24 = (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗ memRegion (a + 8#64) 16 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 16) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_eight a]

theorem sendResultAt_some_of_parts (A : RustAlloc) (ret : BitVec 64)
    (stBytes msgBytes : Bytes) (key : CryptoGames.HKDF.Salt)
    (hmsg_len : msgBytes.length < 2 ^ 32) :
    vecU8 A ret stBytes ∗ vecU8 A (ret + 24#64) msgBytes ∗
      spqrSendKeyAt A (ret + 48#64) key ⊢
      spqrSendResultAt A ret (some (stBytes, key, msgBytes)) := by
  dsimp only [spqrSendResultAt]
  refine Entails.trans
    (Entails.pure_right hmsg_len (Entails.refl _))
    (Entails.of_eq (by ac_rfl))

theorem optKeyAt_none_of_word (A : RustAlloc) (a : BitVec 64) :
    (a ↦₆₄ 18446744073709551615#64) ∗ memRegion (a + 8#64) 16 ⊢
      spqrSendKeyAt A a none := by
  unfold spqrSendKeyAt noneCap
  exact Entails.refl _

theorem optKeyAt_some_of_words (A : RustAlloc) (a cap ptr : BitVec 64)
    (k : List.Vector (BitVec 8) 32) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 32#64) ∗
      DecodeState.vecU8Heap A cap ptr k.toList ⊢
      spqrSendKeyAt A a (some k) := by
  have hlen : BitVec.ofNat 64 k.toList.length = 32#64 := by
    simp [List.Vector.toList_length]
  unfold spqrSendKeyAt
  rw [← hlen]
  exact words_to_vecU8 A a cap ptr k.toList

@[local simp, local arm64_norm, local wp_norm]
theorem ite_zero32_self (P : Prop) [Decidable P] :
    (if P then (0#32 : BitVec 32) else 0#32) = 0#32 := by
  split <;> rfl

@[local simp, local arm64_norm, local wp_norm]
theorem ite_zero64_self (P : Prop) [Decidable P] :
    (if P then (0#64 : BitVec 64) else 0#64) = 0#64 := by
  split <;> rfl

theorem pqRatchetStatePBPinnedAt_cap_bounds {A : RustAlloc} {g : PqRatchetStatePBGhost}
    {a : BitVec 64} {st : PqRatchetState} {R : SepProp} {m : Memory}
    (hm : m ⊨ pqRatchetStatePBPinnedAt A g a st ∗ R) :
    (optChainCap g.chain st.chain + 1#64 == 0#64) = !st.chain.isSome ∧
      (optChainCap g.chain st.chain + 1#64 != 0#64) = st.chain.isSome := by
  rw [pqRatchetStatePBPinnedAt, optChainPBPinnedAt_eq A g.chain (a + 48#64) st.chain] at hm
  exact optChainRest_cap_bounds (A := A) (g := g.chain) (p := a + 48#64)
    (R := optVersionNegotiationPBPinnedAt A g.vn a st.versionNegotiation ∗
      ((a + 48#64) ↦₆₄ optChainCap g.chain st.chain) ∗
      optPqRatchetInnerPBPinnedAt A g.inner (a + 128#64) st.inner ∗ R)
    (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm)

end CryptoVerification.SpqrV1.Top.Send
