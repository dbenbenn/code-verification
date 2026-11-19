/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.KeyDeriveBase
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym130 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym433 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.RegChain
import ProofLib.Sep
import ProofLib.SepLogic.Entry

public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero BitVec.add_assoc
attribute [local wp_norm] BitVec.add_assoc
attribute [local simp, local wp_norm, local arm64_norm] extractLsb0_8_append56

/-!
# Segment S4 (`ConsumeMsgKey`) Proofs for `try_decrypt_with_state`

Verifies Segment S4 (`+0x3e4 → +0x5b8 / +0x30c`), formatting the remote `ProtocolAddress`, calling
`RatchetState::consume_message_key`, dropping the formatted `Display` string, and transitioning to
`PqRecvState` (`Ok mkg`) or `ErrTailState` (`Err e`).
-/

@[local simp, local wp_norm, local arm64_norm]
private theorem extractLsb32_32_append32 (hi lo : BitVec 32) :
    (hi ++ lo).extractLsb' 32 32 = hi := by bv_kernel

private theorem entails_of_false {Q : SepProp} : (⌜False⌝ : SepProp) ⊢ Q := by
  rw [← sepConj_emp ⌜False⌝]
  exact Entails.pure_left False.elim

private theorem focus_weaken_bi {prog : Program} {ret : BitVec 64} {s : State}
    {Full T Q F : SepProp} {Rest : State → SepProp → Prop} {oom : State → SepProp}
    (hEnt : T ⊢ Q)
    (h : SepWP prog ret s (Q ∗ F) Rest oom)
    (hf : Full ⊢ T ∗ F := by first | sep_accu | bi_frame) :
    SepWP prog ret s Full Rest oom :=
  SepWP.weaken_pre (Entails.trans hf (sepConj_mono_left hEnt)) h

private theorem pointsToBytes4_eq (a : BitVec 64) (b0 b1 b2 b3 : BitVec 8) :
    (a ↦ₛ [b0, b1, b2, b3]) = (a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) := by
  rw [pointsTo32_eq_pointsToBytes]
  dsimp only [unpack32]
  have e0 : ∀ (u3 u2 u1 u0 : BitVec 8), (u3 ++ u2 ++ u1 ++ u0).extractLsb' 0 8 = u0 := by
    intro _ _ _ _; bv_kernel
  have e1 : ∀ (u3 u2 u1 u0 : BitVec 8), (u3 ++ u2 ++ u1 ++ u0).extractLsb' 8 8 = u1 := by
    intro _ _ _ _; bv_kernel
  have e2 : ∀ (u3 u2 u1 u0 : BitVec 8), (u3 ++ u2 ++ u1 ++ u0).extractLsb' 16 8 = u2 := by
    intro _ _ _ _; bv_kernel
  have e3 : ∀ (u3 u2 u1 u0 : BitVec 8), (u3 ++ u2 ++ u1 ++ u0).extractLsb' 24 8 = u3 := by
    intro _ _ _ _; bv_kernel
  rw [e0, e1, e2, e3]

private theorem split_bytes_4 {bs : List (BitVec 8)} {n : Nat} (h : bs.length = 4 + n) :
    ∃ (w : BitVec 32) (rest : List (BitVec 8)),
      rest.length = n ∧
      ∀ a : BitVec 64, (a ↦ₛ bs) = (a ↦₃₂ w) ∗ ((a + 4#64) ↦ₛ rest) := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, rest⟩⟩⟩⟩
  · simp only [List.length_nil] at h; omega
  · simp only [List.length_cons, List.length_nil] at h; omega
  · simp only [List.length_cons, List.length_nil] at h; omega
  · simp only [List.length_cons, List.length_nil] at h; omega
  · simp only [List.length_cons] at h
    refine ⟨b3 ++ b2 ++ b1 ++ b0, rest, by omega, fun a => ?_⟩
    have hsplit := pointsToBytes_append a [b0, b1, b2, b3] rest
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at hsplit
    change (a ↦ₛ ([b0, b1, b2, b3] ++ rest)) = _
    rw [hsplit, pointsToBytes4_eq]

private theorem split_bytes_4_end {bs : List (BitVec 8)} (h : bs.length = 4) :
    ∃ (w : BitVec 32), ∀ a : BitVec 64, (a ↦ₛ bs) = (a ↦₃₂ w) := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, rest⟩⟩⟩⟩⟩
  · cases h
  · cases h
  · cases h
  · cases h
  · exact ⟨b3 ++ b2 ++ b1 ++ b0, fun a => pointsToBytes4_eq a b0 b1 b2 b3⟩
  · simp only [List.length_cons] at h; omega

private theorem chainKeyBytes_len (ck : ChainKey) :
    (chainKeyBytes ck).length = 36 := by
  simp [chainKeyBytes, keyToBytes32, leBytes]

private theorem split_chainKeyBytes (ck : ChainKey) :
    ∃ (w0 w1 w2 w3 w4 w5 w6 w7 w8 : BitVec 32),
      (∀ a : BitVec 64,
        (a ↦ₛ (chainKeyBytes ck).drop 20) =
          (a ↦₆₄ (w6 ++ w5)) ∗ ((a + 8#64) ↦₆₄ (w8 ++ w7))) ∧
      (∀ a : BitVec 64,
        (a ↦ₛ (chainKeyBytes ck).take 20) =
          (a ↦₆₄ (w1 ++ w0)) ∗ ((a + 8#64) ↦₆₄ (w3 ++ w2)) ∗ ((a + 16#64) ↦₃₂ w4)) ∧
      (∀ a : BitVec 64,
        (a ↦ₛ chainKeyBytes ck) =
          (a ↦₆₄ (w1 ++ w0)) ∗ ((a + 8#64) ↦₆₄ (w3 ++ w2)) ∗
          ((a + 16#64) ↦₆₄ (w5 ++ w4)) ∗ ((a + 24#64) ↦₆₄ (w7 ++ w6)) ∗
          ((a + 32#64) ↦₃₂ w8)) := by
  have hlen := chainKeyBytes_len ck
  have htake_len : ((chainKeyBytes ck).take 20).length = 20 := by simp [hlen]
  have hdrop_len : ((chainKeyBytes ck).drop 20).length = 16 := by simp [hlen]
  obtain ⟨w0, r1, hr1, hw0⟩ := split_bytes_4 (n := 16) htake_len
  obtain ⟨w1, r2, hr2, hw1⟩ := split_bytes_4 (n := 12) hr1
  obtain ⟨w2, r3, hr3, hw2⟩ := split_bytes_4 (n := 8) hr2
  obtain ⟨w3, r4, hr4, hw3⟩ := split_bytes_4 (n := 4) hr3
  obtain ⟨w4, hw4⟩ := split_bytes_4_end hr4
  obtain ⟨w5, d1, hd1, hw5⟩ := split_bytes_4 (n := 12) hdrop_len
  obtain ⟨w6, d2, hd2, hw6⟩ := split_bytes_4 (n := 8) hd1
  obtain ⟨w7, d3, hd3, hw7⟩ := split_bytes_4 (n := 4) hd2
  obtain ⟨w8, hw8⟩ := split_bytes_4_end hd3
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, ?_, ?_, ?_⟩
  · intro a
    rw [hw5, hw6, hw7, hw8, ← pointsTo32_merge64 a w5 w6, ← pointsTo32_merge64 (a + 8#64) w7 w8]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  · intro a
    rw [hw0, hw1, hw2, hw3, hw4, ← pointsTo32_merge64 a w0 w1, ← pointsTo32_merge64 (a + 8#64) w2 w3]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  · intro a
    have happ : chainKeyBytes ck = (chainKeyBytes ck).take 20 ++ (chainKeyBytes ck).drop 20 :=
      (List.take_append_drop 20 (chainKeyBytes ck)).symm
    conv_lhs => rw [happ]
    rw [pointsToBytes_append, htake_len,
      hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8,
      ← pointsTo32_merge64 a w0 w1,
      ← pointsTo32_merge64 (a + 8#64) w2 w3,
      ← pointsTo32_merge64 (a + 16#64) w4 w5,
      ← pointsTo32_merge64 (a + 24#64) w6 w7]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem realign_416_436 (sp : BitVec 64) (w4 w5 w6 w7 w8 : BitVec 32) :
    ((sp + 416#64) ↦₃₂ w4) ∗ ((sp + 420#64) ↦₆₄ (w6 ++ w5)) ∗ ((sp + 428#64) ↦₆₄ (w8 ++ w7)) ⊢
    ((sp + 416#64) ↦₆₄ (w5 ++ w4)) ∗ ((sp + 424#64) ↦₆₄ (w7 ++ w6)) ∗ ((sp + 432#64) ↦₃₂ w8) := by
  have h65 := (pointsTo32_merge64 (sp + 420#64) w5 w6).symm
  have h87 := (pointsTo32_merge64 (sp + 428#64) w7 w8).symm
  have h54 := (pointsTo32_merge64 (sp + 416#64) w4 w5).symm
  have h76 := (pointsTo32_merge64 (sp + 424#64) w6 w7).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h65 h87 h54 h76
  rw [h65, h87, h54, h76]
  have heq :
      ((sp + 416#64) ↦₃₂ w4) ∗ (((sp + 420#64) ↦₃₂ w5) ∗ ((sp + 424#64) ↦₃₂ w6)) ∗
        (((sp + 428#64) ↦₃₂ w7) ∗ ((sp + 432#64) ↦₃₂ w8)) =
      (((sp + 416#64) ↦₃₂ w4) ∗ ((sp + 420#64) ↦₃₂ w5)) ∗
        (((sp + 424#64) ↦₃₂ w6) ∗ ((sp + 428#64) ↦₃₂ w7)) ∗
        ((sp + 432#64) ↦₃₂ w8) := by ac_rfl
  rw [heq]
  exact Entails.refl _

private theorem mut_exec_bind {σ α β : Type} (m : Mut σ α) (k : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= k) s =
      match (Mut.exec m s).1 with
      | .ok a => Mut.exec (k a) (Mut.exec m s).2
      | .error e => (.error e, (Mut.exec m s).2) := by
  change (match m s with | (r, s') => ExceptT.bindCont k r s') =
    match (m s).1 with
    | .ok a => (k a).run (m s).2
    | .error e => (.error e, (m s).2)
  cases m s with
  | mk r s' =>
    cases r <;> rfl

private theorem mut_exec_get {σ : Type} (s : σ) :
    Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl

private theorem mut_exec_liftE {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r : Mut σ α) s = (r, s) := by
  cases r <;> rfl

private theorem takeSkippedKey_senderChain (their : PublicKey) (counter : BitVec 32) (s : RatchetState) :
    (Mut.exec (RatchetState.takeSkippedKey their counter) s).2.senderChain = s.senderChain := by
  unfold RatchetState.takeSkippedKey
  rw [mut_exec_bind, mut_exec_get]
  dsimp only
  split
  · split
    · split
      · split <;> rfl
      · rfl
    · rfl
  · rfl

private theorem storeSkippedKey_senderChain (their : PublicKey) (key : MessageKeyGenerator) (s : RatchetState) :
    (Mut.exec (RatchetState.storeSkippedKey their key) s).2.senderChain = s.senderChain := by
  unfold RatchetState.storeSkippedKey
  rw [mut_exec_bind, mut_exec_get]
  dsimp only
  split
  · split <;> rfl
  · rfl

private theorem setReceiverChainKey_senderChain (their : PublicKey) (ck : ChainKey) (s : RatchetState) :
    (Mut.exec (RatchetState.setReceiverChainKey their ck) s).2.senderChain = s.senderChain := by
  unfold RatchetState.setReceiverChainKey
  rw [mut_exec_bind, mut_exec_get]
  dsimp only
  split
  · split <;> rfl
  · rfl

private theorem advanceChain_senderChain (F : ShaCompress) (their : PublicKey) (counter : BitVec 32) :
    ∀ (fuel : Nat) (ck : ChainKey) (s : RatchetState),
      (Mut.exec (RatchetState.advanceChain F their counter fuel ck) s).2.senderChain = s.senderChain
  | 0, ck, s => rfl
  | fuel + 1, ck, s => by
    unfold RatchetState.advanceChain
    split
    · rw [mut_exec_bind]
      have h1 := storeSkippedKey_senderChain their (ck.messageKeys F) s
      cases hst : (Mut.exec (RatchetState.storeSkippedKey their (ck.messageKeys F)) s).1 with
      | error e => exact h1
      | ok u =>
        dsimp only
        rw [mut_exec_bind, mut_exec_liftE]
        cases hnk : ck.nextChainKey F with
        | error e => exact h1
        | ok ck' =>
          dsimp only
          exact (advanceChain_senderChain F their counter fuel ck' _).trans h1
    · rfl

private theorem consumeMessageKey_senderChain (F : ShaCompress) (their : PublicKey) (ck : ChainKey)
    (counter : BitVec 32) (msgType : MessageType) (s : RatchetState) :
    (Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType) s).2.senderChain = s.senderChain := by
  unfold RatchetState.consumeMessageKey
  dsimp only
  split
  · rw [mut_exec_bind]
    have h1 := takeSkippedKey_senderChain their counter s
    cases htk : (Mut.exec (RatchetState.takeSkippedKey their counter) s).1 with
    | error e => exact h1
    | ok o => cases o <;> exact h1
  · rw [mut_exec_bind, mut_exec_get]
    dsimp only
    split
    · rfl
    · rw [mut_exec_bind]
      have hadv := advanceChain_senderChain F their counter (counter - ck.index).toNat ck s
      cases hadv1 : (Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) s).1 with
      | error e => exact hadv
      | ok ck' =>
        dsimp only
        rw [mut_exec_bind, mut_exec_liftE]
        cases hnk : ck'.nextChainKey F with
        | error e => exact hadv
        | ok nextCk =>
          dsimp only
          rw [mut_exec_bind]
          have hset := setReceiverChainKey_senderChain their nextCk
            (Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) s).2
          cases (Mut.exec (RatchetState.setReceiverChainKey their nextCk)
            (Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) s).2).1 <;>
            exact hset.trans hadv

private def ErrWordsRel (A : RustAlloc) (e : SignalProtocolError)
    (w416 w424 w432 w440 : BitVec 64) (restHeap : SepProp) : Prop :=
  match e with
  | .duplicatedMessage i c =>
    w416 = c ++ i ∧ restHeap = emp
  | .invalidMessage t .tooFarInFuture =>
    ∃ hi : BitVec 56,
      w432 = BitVec.ofNat 64 tooFarInFutureStr.length ∧
      w440 = hi ++ msgTypeByte t ∧
      tooFarInFutureStr.length ≤ w416.toNat ∧ w416.toNat < 2 ^ 63 ∧ w424 ≠ 0 ∧
      restHeap = (if w416 = 0 then emp else A.live w424 w416.toNat 1 ∗
        (w424 ↦ₛ tooFarInFutureStr) ∗
        memRegion (w424 + BitVec.ofNat 64 tooFarInFutureStr.length)
          (w416.toNat - tooFarInFutureStr.length))
  | _ => False

private theorem resultAt_err_unpack (A : RustAlloc) (sp : BitVec 64) (e : SignalProtocolError) :
    consumeMessageKeyResultAt A (sp + 400#64) (.error e) ⊢
    ∃∗ w416 : BitVec 64, ∃∗ w424 : BitVec 64, ∃∗ w432 : BitVec 64,
    ∃∗ w440 : BitVec 64, ∃∗ w448 : BitVec 64, ∃∗ restHeap : SepProp,
      ⌜ErrWordsRel A e w416 w424 w432 w440 restHeap ∧ speTag e + 2#64 ≠ 0#64⌝ ∗
      ((sp + 400#64) ↦₃₂ 2#32) ∗
      memRegion (sp + 404#64) 4 ∗
      ((sp + 408#64) ↦₆₄ speTag e) ∗
      ((sp + 416#64) ↦₆₄ w416) ∗
      ((sp + 424#64) ↦₆₄ w424) ∗
      ((sp + 432#64) ↦₆₄ w432) ∗
      ((sp + 440#64) ↦₆₄ w440) ∗
      ((sp + 448#64) ↦₆₄ w448) ∗
      memRegion (sp + 456#64) 32 ∗
      restHeap := by
  unfold consumeMessageKeyResultAt
  split
  · next r heq => cases heq
  · next i c heq =>
    injection heq with heq; subst heq
    dsimp only [speTag, ErrWordsRel]
    have htag : errDuplicatedMessage = speWord 23 := rfl
    have hne : speWord 23 + 2#64 ≠ 0#64 := by decide
    have hmerge : ((sp + 416#64) ↦₃₂ i) ∗ ((sp + 420#64) ↦₃₂ c) = ((sp + 416#64) ↦₆₄ (c ++ i)) := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_merge64 (sp + 416#64) i c
    have hmr64 : memRegion (sp + 424#64) 64 = cells (sp + 424#64) 4 ∗ memRegion (sp + 456#64) 32 := by
      sep_interval_eq
    simp only [BitVec.add_assoc, BitVec.reduceAdd, htag, ← sepConj_assoc]
    rw [sepConj_assoc _ ((sp + 416#64) ↦₃₂ i), hmerge, hmr64]
    simp only [cells_succ, cells_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd,
      sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w424 => Entails.sepExists_elim fun w432 =>
      Entails.sepExists_elim fun w440 => Entails.sepExists_elim fun w448 => ?_
    refine Entails.sepExists_right (c ++ i) (Entails.sepExists_right w424
      (Entails.sepExists_right w432 (Entails.sepExists_right w440
      (Entails.sepExists_right w448 (Entails.sepExists_right emp ?_)))))
    have hp : (c ++ i = c ++ i ∧ emp = (emp : SepProp)) ∧ speWord 23 + 2#64 ≠ 0#64 :=
      ⟨⟨rfl, rfl⟩, hne⟩
    bi_entail
  · next t heq =>
    injection heq with heq; subst heq
    unfold speTag ErrWordsRel vecU8 vecU8At vecHeader
    rw [pointsToBytes_singleton]
    have htag : errInvalidMessage = speWord 24 := rfl
    have hne : speWord 24 + 2#64 ≠ 0#64 := by decide
    have hmr47 : memRegion (sp + 441#64) 47 =
        memRegion (sp + 441#64) 7 ∗ cells (sp + 448#64) 1 ∗ memRegion (sp + 456#64) 32 := by
      sep_interval_eq
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmr47 ⊢
    rw [htag, hmr47]
    simp only [cells_succ, cells_zero, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w448 =>
      Entails.sepExists_elim fun cap =>
      Entails.sepExists_elim fun ptr => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Entails.pure_left fun ⟨h1, h2, h3⟩ => ?_
    have h440 := pointsTo8_memRegion7_to_64 (sp + 440#64) (msgTypeByte t)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h440
    refine Entails.trans (by bi_frame) (Entails.trans (sepConj_mono_left h440) ?_)
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun hi => ?_
    refine Entails.sepExists_right cap (Entails.sepExists_right ptr
      (Entails.sepExists_right (BitVec.ofNat 64 tooFarInFutureStr.length)
      (Entails.sepExists_right (hi ++ msgTypeByte t)
      (Entails.sepExists_right w448
      (Entails.sepExists_right
        (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ tooFarInFutureStr) ∗
          memRegion (ptr + BitVec.ofNat 64 tooFarInFutureStr.length)
            (cap.toNat - tooFarInFutureStr.length)) ?_)))))
    exact Entails.pure_right ⟨⟨hi, rfl, rfl, h1, h2, h3, rfl⟩, hne⟩ (by bi_entail)
  · exact entails_of_false

private theorem speBodyAt_err_pack (A : RustAlloc) (sp : BitVec 64) (e : SignalProtocolError)
    (w416 w424 w432 w440 w448 : BitVec 64) (restHeap : SepProp)
    (hrel : ErrWordsRel A e w416 w424 w432 w440 restHeap) :
    ((sp + 360#64) ↦₆₄ w416) ∗
    ((sp + 368#64) ↦₆₄ w424) ∗
    ((sp + 376#64) ↦₆₄ w432) ∗
    ((sp + 384#64) ↦₆₄ w440) ∗
    ((sp + 392#64) ↦₆₄ w448) ∗
    restHeap ⊢
    speBodyAt A (utf8 "decrypt") (sp + 360#64) e := by
  unfold ErrWordsRel at hrel
  split at hrel
  · next i c =>
    rcases hrel with ⟨rfl, rfl⟩
    simp only [speBodyAt, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
    have hsplit : ((sp + 360#64) ↦₆₄ (c ++ i)) =
        ((sp + 360#64) ↦₃₂ i) ∗ ((sp + 364#64) ↦₃₂ c) := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using (pointsTo32_merge64 (sp + 360#64) i c).symm
    rw [hsplit]
    sep_interval
  · next t =>
    rcases hrel with ⟨hi, rfl, rfl, h1, h2, h3, hrest⟩
    dsimp only [speBodyAt, invalidMessageStrAt, vecU8, vecU8At, vecHeader]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left]
    refine Entails.sepExists_right w416 (Entails.sepExists_right w424 ?_)
    rw [← hrest]; clear hrest
    have h384 := pointsTo64_to_8_memRegion7 (sp + 384#64) hi (msgTypeByte t)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h384
    refine Entails.trans (by bi_frame) (Entails.trans (sepConj_mono_left h384) ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    exact Entails.pure_right ⟨h1, h2, h3⟩ (by sep_interval)
  · exact hrel.elim

private theorem cmk_sp56_pack_rest (sp : BitVec 64) (msgW c : BitVec 32) (locA remA : BitVec 64)
    (rest : SepProp) :
    memRegion sp 28 ∗ ((sp + 28#64) ↦₃₂ msgW) ∗ ((sp + 32#64) ↦₆₄ locA) ∗
    ((sp + 40#64) ↦₃₂ c) ∗ memRegion (sp + 44#64) 4 ∗ ((sp + 48#64) ↦₆₄ remA) ∗ rest ⊢
    memRegion sp 56 ∗ rest := by
  sep_interval

private theorem empty_vecU8_intro (A : RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢
    vecU8 A v [] := by
  unfold vecU8 vecU8At vecHeader
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat]
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 1#64 ?_)
  simp only [↓reduceIte, sepConj_emp]
  have h1 : 0 ≤ (0#64).toNat := by decide
  have h2 : (0#64).toNat < 2 ^ 63 := by decide
  have h3 : (1#64 : BitVec 64) ≠ 0#64 := by decide
  bi_entail

private theorem cmk_ok_post_sp320 (sp : BitVec 64) :
    memRegion (sp + 320#64) 784 =
      memRegion (sp + 320#64) 80 ∗ memRegion (sp + 400#64) 4 ∗ memRegion (sp + 404#64) 4 ∗
      memRegion (sp + 408#64) 8 ∗ memRegion (sp + 416#64) 8 ∗ memRegion (sp + 424#64) 8 ∗
      memRegion (sp + 432#64) 8 ∗ memRegion (sp + 440#64) 8 ∗ memRegion (sp + 448#64) 8 ∗
      memRegion (sp + 456#64) 8 ∗ memRegion (sp + 464#64) 8 ∗ memRegion (sp + 472#64) 8 ∗
      memRegion (sp + 480#64) 8 ∗ memRegion (sp + 488#64) 616 := by
  sep_interval_eq

private theorem cmk_ok_post_sp1116 (sp : BitVec 64) :
    memRegion (sp + 1116#64) 292 =
      memRegion (sp + 1116#64) 4 ∗ memRegion (sp + 1120#64) 8 ∗ memRegion (sp + 1128#64) 8 ∗
      memRegion (sp + 1136#64) 8 ∗ memRegion (sp + 1144#64) 8 ∗ memRegion (sp + 1152#64) 8 ∗
      memRegion (sp + 1160#64) 8 ∗ memRegion (sp + 1168#64) 112 ∗ memRegion (sp + 1280#64) 8 ∗
      memRegion (sp + 1288#64) 8 ∗ memRegion (sp + 1296#64) 8 ∗ memRegion (sp + 1304#64) 8 ∗
      memRegion (sp + 1312#64) 96 := by
  sep_interval_eq

private theorem cmk_err_post_sp400 (sp : BitVec 64) :
    memRegion (sp + 400#64) 1008 =
      memRegion (sp + 400#64) 4 ∗ memRegion (sp + 404#64) 4 ∗ memRegion (sp + 408#64) 8 ∗
      memRegion (sp + 416#64) 8 ∗ memRegion (sp + 424#64) 8 ∗ memRegion (sp + 432#64) 8 ∗
      memRegion (sp + 440#64) 8 ∗ memRegion (sp + 448#64) 8 ∗ memRegion (sp + 456#64) 32 ∗
      memRegion (sp + 488#64) 792 ∗ memRegion (sp + 1280#64) 8 ∗ memRegion (sp + 1288#64) 8 ∗
      memRegion (sp + 1296#64) 8 ∗ memRegion (sp + 1304#64) 8 ∗ memRegion (sp + 1312#64) 96 := by
  sep_interval_eq

private theorem cmk_ok_pre_sp0 (sp : BitVec 64) :
    memRegion sp 28 = memRegion sp 16 ∗ cells (sp + 16#64) 1 ∗ memRegion (sp + 24#64) 4 := by
  sep_interval_eq

private theorem cmk_ok_pre_sp436 (sp : BitVec 64) :
    memRegion (sp + 436#64) 52 = memRegion (sp + 436#64) 4 ∗ memRegion (sp + 440#64) 48 := by
  sep_interval_eq

private theorem cmk_ok_pre_sp440 (sp : BitVec 64) :
    memRegion (sp + 440#64) 48 = cells (sp + 440#64) 6 := by
  sep_interval_eq

private theorem cmk_ok_pre_sp488 (sp : BitVec 64) :
    memRegion (sp + 488#64) 920 =
      memRegion (sp + 488#64) 616 ∗ cells (sp + 1104#64) 8 ∗
      memRegion (sp + 1168#64) 112 ∗ cells (sp + 1280#64) 4 ∗ memRegion (sp + 1312#64) 96 := by
  sep_interval_eq

private theorem cmk_ok_split1112 (sp : BitVec 64) (lo hi : BitVec 32) :
    ((sp + 1112#64) ↦₆₄ (hi ++ lo)) ⊢ ((sp + 1112#64) ↦₃₂ lo) ∗ memRegion (sp + 1116#64) 4 := by
  have hs := (pointsTo32_merge64 (sp + 1112#64) lo hi).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hs
  rw [hs]; sep_interval

private theorem cmk_merge64 (sp off off4 : BitVec 64) (lo hi : BitVec 32)
    (h : off + 4#64 = off4 := by rfl) :
    ((sp + off) ↦₃₂ lo) ∗ ((sp + off4) ↦₃₂ hi) ⊢ ((sp + off) ↦₆₄ (hi ++ lo)) := by
  subst h; rw [← BitVec.add_assoc, pointsTo32_merge64 (sp + off) lo hi]; exact Entails.refl _

private theorem cmk_err_pre_sp320 (sp : BitVec 64) :
    memRegion (sp + 320#64) 80 = memRegion (sp + 320#64) 40 ∗ cells (sp + 360#64) 5 := by
  sep_interval_eq

private theorem cmk_err_pre_sp488 (sp : BitVec 64) :
    memRegion (sp + 488#64) 920 =
      memRegion (sp + 488#64) 792 ∗ cells (sp + 1280#64) 4 ∗ memRegion (sp + 1312#64) 96 := by
  sep_interval_eq

private def trNonRatchetAt (A : RustAlloc) (sp : BitVec 64) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) : SepProp :=
  vecU8At A (sp + 232#64) trG.pq.cap trG.pq.ptr tr.pqrState ∗
  ((sp + 256#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
  ((sp + 288#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)

private theorem trAt_split_ratchet (A : RustAlloc) (sp : BitVec 64) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) :
    trAt A (sp + 56#64) trG tr =
      ⌜∀ sc, tr.ratchet.senderChain = some sc →
        Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes⌝ ∗
      ratchetAt A (sp + 56#64) trG.ratchet tr.ratchet ∗
      trNonRatchetAt A sp trG tr := by
  unfold trAt trNonRatchetAt
  rw [BitVec.add_assoc, show (56#64 : BitVec 64) + 0xb0#64 = 232#64 by rfl,
    BitVec.add_assoc, show (56#64 : BitVec 64) + 0xc8#64 = 256#64 by rfl,
    BitVec.add_assoc, show (56#64 : BitVec 64) + 0xe8#64 = 288#64 by rfl]

private def signalMessageNonTheirAt (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) : SepProp :=
  ⌜macLength + 1 ≤ m.serialized.length ∧ m.serialized.length < 2 ^ 40 ∧
    m.ciphertext.length < 2 ^ 40 ∧ m.pqRatchet.length < 2 ^ 40 ∧
    (∀ ad, m.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
    vecU8At A a g.pqCap g.pqPtr m.pqRatchet ∗
    boxU8At A (a + 0x18#64) g.ctPtr m.ciphertext ∗
    boxU8At A (a + 0x28#64) g.serPtr m.serialized ∗
    optBoxU8At A (a + 0x58#64) g.addrPtr m.addresses ∗
    ((a + 0x68#64) ↦₃₂ m.counter) ∗ ((a + 0x6c#64) ↦₃₂ m.previousCounter) ∗
    ((a + 0x70#64) ↦₈ m.messageVersion) ∗ memRegion (a + 0x71#64) 7

private theorem signalMessageAt_split_their (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) :
    signalMessageAt A g a m =
      ((a + 56#64) ↦ₛ m.senderRatchetKey.bytes.toList) ∗
      signalMessageNonTheirAt A g a m := by
  unfold signalMessageAt signalMessageNonTheirAt
  ac_rfl

namespace KeyDeriveCallees

end KeyDeriveCallees

private theorem steps_call_out_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc : BitVec 64} {spec : Spec α} (x : α)
    {sm : State} {F R : SepProp} {Out : State → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : sm.pc = entry) (hrun : sm.status = .Running) (hsp : sm.spAligned = true)
    (hlr : sm.readReg64 .lr = ret_pc)
    (hcl : LibsignalCodeRoLoaded lsmpl sm.mem)
    (hL : prog.CodeLoaded sm.mem)
    (hpre : sm.mem ⊨ spec.pre x sm ∗ (F ∗ R))
    (hpanic : ∀ sf, sf.status = .Panicked → (sf.mem ⊨ (spec.onPanic x sm sf ∗ F) ∗ R) → Out sf)
    (hnext : ∀ sf, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sm.sp → sf.spAligned = true → CalleeSavedPreserved sm sf →
      LibsignalCodeRoLoaded lsmpl sf.mem → prog.CodeLoaded sf.mem →
      (sf.mem ⊨ (spec.post x sm sf ∗ F) ∗ R) →
      ∃ s', Steps prog sf s' ∧ Out s')
    (hexit : ∀ sf code R', (sf.mem ⊨ spec.onExit x code sm sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h)
    (hoom : ∀ sf R', (sf.mem ⊨ spec.onOom x sm sf ∗ R') → False := by
      intro _ _ h; exact not_satisfies_false_sepConj h) :
    ∃ s', Steps prog sm s' ∧ Out s' := by
  obtain ⟨s', hsteps, hout | hout⟩ :=
    steps_call_placed x hcall hpc hrun hsp hlr hcl hL hpre hpanic
      (fun sf h1 h2 h3 h4 h5 h6 h7 h8 =>
        let ⟨s', hs, ho⟩ := hnext sf h1 h2 h3 h4 h5 h6 h7 h8
        ⟨s', hs, Or.inl ho⟩) hexit hoom
  · exact ⟨s', hsteps, hout⟩
  · exact ⟨s', hsteps, hout⟩

private theorem steps_call_out_placed_cro [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc : BitVec 64} {spec : Spec α} (x : α)
    {sm : State} {F R : SepProp} {Out : State → Prop}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hpc : sm.pc = entry) (hrun : sm.status = .Running) (hsp : sm.spAligned = true)
    (hlr : sm.readReg64 .lr = ret_pc)
    (hcl : LibsignalCodeRoLoaded lsmpl sm.mem)
    (hL : prog.CodeLoaded sm.mem)
    (hpre : sm.mem ⊨ spec.pre x sm ∗ (F ∗ R))
    (hpanic : ∀ sf, sf.status = .Panicked → (sf.mem ⊨ (spec.onPanic x sm sf ∗ F) ∗ R) → Out sf)
    (hnext : ∀ sf, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sm.sp → sf.spAligned = true → CalleeSavedPreserved sm sf →
      LibsignalCodeRoLoaded lsmpl sf.mem → prog.CodeLoaded sf.mem →
      (sf.mem ⊨ (spec.post x sm sf ∗ F) ∗ R) →
      ∃ s', Steps prog sf s' ∧ Out s')
    (hexit : ∀ sf code R', (sf.mem ⊨ spec.onExit x code sm sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h)
    (hoom : ∀ sf R', (sf.mem ⊨ spec.onOom x sm sf ∗ R') → False := by
      intro _ _ h; exact not_satisfies_false_sepConj h) :
    ∃ s', Steps prog sm s' ∧ Out s' := by
  have hpre' : sm.mem ⊨ (withLsCodeRoLoaded lsmpl spec).pre x sm ∗ (F ∗ R) := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl, hpre⟩
  exact steps_call_out_placed x hcall hpc hrun hsp hlr hcl hL hpre' hpanic hnext hexit hoom

namespace KeyDeriveCallees

theorem consumeMsgKey_cmk_ok_159_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (x : TryDecryptGhost) (trG' : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (r2 : RatchetState) (mkg : MessageKeyGenerator)
    (draws : Nat) (R : SepProp) (s0 : State)
    {sp dispCap dispPtr : BitVec 64} {dispBs : List (BitVec 8)} {msgW : BitVec 32}
    (hsp0_al : s0.spAligned = true)
    (hsp_al' : (sp &&& 15#64 == 0#64) = true)
    (hdealloc : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hsp_def : s0.sp - 1504#64 = sp)
    (hdisp1 : dispBs.length ≤ dispCap.toNat)
    (hdisp2 : dispCap.toNat < 2 ^ 63)
    (hmsgW_byte : msgW.setWidth 8 = msgTypeByte x.msgType)
    (sf2 : State)
    (hpcf2 : sf2.pc = (blkPl_131).base + 1144#64)
    (hrunf2 : sf2.status = .Running)
    (hsp_f2 : sf2.sp = sp)
    (hsp_alf2 : sf2.spAligned = true)
    (hx19_f2 : sf2.readReg64 .x19 = x.ret)
    (hx20_f2 : sf2.readReg64 .x20 = sp + 320#64)
    (hx21_f2 : sf2.readReg64 .x21 = x.ss)
    (hx22_f2 : sf2.readReg64 .x22 = x.msgA)
    (hx23_f2 : sf2.readReg64 .x23 = sp + 1280#64)
    (hx25_f2 : sf2.readReg64 .x25 = sp + 400#64)
    (hx27_f2 : sf2.readReg64 .x27 = dispPtr)
    (hx28_f2 : sf2.readReg64 .x28 = dispCap)
    (hfp_f2 : sf2.readReg64 .fp = sp + 1408#64)
    (htr_f2' : sf2.trace = s0.trace)
    (hvregs_f2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0)
    (hclf2 : LibsignalCodeRoLoaded lsmpl sf2.mem)
    (hLf2 : ((blkPC_131).rebase (blkPl_131).base H).CodeLoaded sf2.mem)
    (hm_post2 : sf2.mem ⊨
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
       (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
         (dispPtr ↦ₛ dispBs) ∗
         memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
       consumeMessageKeyResultAt A (sp + 400#64) (.ok mkg) ∗
       memRegion x.ret 48 ∗
       memRegion sp 28 ∗
       ((sp + 28#64) ↦₃₂ msgW) ∗
       ((sp + 32#64) ↦₆₄ x.locA) ∗
       ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 44#64) 4 ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 320#64) 80 ∗
       memRegion (sp + 488#64) 920 ∗
       protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       tapeAfter ctl x.cur x.rest draws ∗
       logOff tryDecryptPlacedImg ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool) ∗ R) :
    ∃ s', Steps ((blkPC_131).rebase (blkPl_131).base H) sf2 s' ∧
      ((∃ trG'', PqRecvStatePlaced (blkPl_131).base A ctl x trG'' { tr with ratchet := r2 } st1 mkg draws R s0 s') ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R))) := by
  dsimp only [consumeMessageKeyResultAt, vecU8, vecU8At, vecHeader] at hm_post2
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_post2
  rcases hm_post2 with ⟨seedCap, seedPtr, hm_post2⟩
  simp only [sepConj_pure_left_comm, satisfies_pure_sepConj] at hm_post2
  rcases hm_post2 with ⟨⟨hseed1, hseed2, hseed3⟩, hm_post2⟩
  simp only [← sepConj_assoc] at hm_post2
  refine steps_of_sepWP_placed hm_post2 hLf2 hclf2
    (mid := (blkPl_131).base + 1396#64)
    (RegMid := fun sm3 =>
      (sm3.readReg64 .x24).setWidth 32 = 1#32 ∧
      sm3.readReg64 .x19 = x.ret ∧
      sm3.readReg64 .x20 = sp + 320#64 ∧
      sm3.readReg64 .x21 = x.ss ∧
      sm3.readReg64 .x22 = x.msgA ∧
      sm3.readReg64 .x23 = sp + 1280#64 ∧
      sm3.readReg64 .x25 = sp + 400#64 ∧
      sm3.readReg64 .x27 = dispPtr ∧
      sm3.readReg64 .x28 = dispCap ∧
      sm3.readReg64 .fp = sp + 1408#64 ∧
      sm3.sp = sp ∧ sm3.spAligned = true ∧ sm3.trace = s0.trace ∧
      calleeSavedVRegs sm3 = calleeSavedVRegs s0)
    (P_mid :=
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
      (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
        (dispPtr ↦ₛ dispBs) ∗
        memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
      (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
        (seedPtr ↦ₛ mkg.seed) ∗
        memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
          (seedCap.toNat - mkg.seed.length)) ∗
      ((sp + 400#64) ↦₃₂ 1#32) ∗
      memRegion (sp + 404#64) 4 ∗
      ((sp + 408#64) ↦₆₄ seedCap) ∗
      ((sp + 416#64) ↦₆₄ seedPtr) ∗
      ((sp + 424#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((sp + 432#64) ↦₃₂ mkg.counter) ∗
      memRegion (sp + 436#64) 52 ∗
      memRegion x.ret 48 ∗
      memRegion sp 28 ∗
      ((sp + 28#64) ↦₃₂ msgW) ∗
      ((sp + 32#64) ↦₆₄ x.locA) ∗
      ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
      memRegion (sp + 44#64) 4 ∗
      ((sp + 48#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 320#64) 80 ∗
      memRegion (sp + 488#64) 920 ∗
      protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      tapeAfter ctl x.cur x.rest draws ∗
      logOff tryDecryptPlacedImg ∗
      stackAt sp tryDecryptSubStack ∗
      tryDecryptSavedRegs s0.sp s0 ∗
      A.pool) ?_ ?_
  · wp_conv_pre => simp only [sepConj_assoc]
    wp_steps
    wp_done
  · intro sm3 hpc3 hrun3 hcl3 hL3
      ⟨hx24_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx25_3, hx27_3, hx28_3,
       hfp3, hsp3, hsp_al3, htr3, hvregs3⟩
      hm3
    refine steps_of_sepWP_placed hm3 hL3 hcl3
      (mid := (blkPl_131).base + 1444#64)
      (RegMid := fun sm4 =>
        (sm4.readReg64 .x24).setWidth 32 = 1#32 ∧
        sm4.readReg64 .x19 = x.ret ∧
        sm4.readReg64 .x20 = sp + 320#64 ∧
        sm4.readReg64 .x21 = x.ss ∧
        sm4.readReg64 .x22 = x.msgA ∧
        sm4.readReg64 .x23 = sp + 1280#64 ∧
        sm4.readReg64 .x25 = sp + 400#64 ∧
        sm4.readReg64 .x27 = dispPtr ∧
        sm4.readReg64 .x28 = dispCap ∧
        sm4.readReg64 .fp = sp + 1408#64 ∧
        sm4.sp = sp ∧ sm4.spAligned = true ∧ sm4.trace = s0.trace ∧
        calleeSavedVRegs sm4 = calleeSavedVRegs s0)
      (P_mid :=
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
        trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
        (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
          (dispPtr ↦ₛ dispBs) ∗
          memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
        (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
          (seedPtr ↦ₛ mkg.seed) ∗
          memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
            (seedCap.toNat - mkg.seed.length)) ∗
        memRegion x.ret 48 ∗
        memRegion sp 16 ∗
        ((sp + 16#64) ↦₆₄ seedPtr) ∗
        memRegion (sp + 24#64) 4 ∗
        ((sp + 28#64) ↦₃₂ msgW) ∗
        ((sp + 32#64) ↦₆₄ x.locA) ∗
        ((sp + 40#64) ↦₆₄ seedCap) ∗
        ((sp + 48#64) ↦₆₄ x.remA) ∗
        memRegion (sp + 320#64) 784 ∗
        ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
        ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
        memRegion (sp + 1116#64) 292 ∗
        protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        tapeAfter ctl x.cur x.rest draws ∗
        logOff tryDecryptPlacedImg ∗
        stackAt sp tryDecryptSubStack ∗
        tryDecryptSavedRegs s0.sp s0 ∗
        A.pool) ?_ ?_
    · wp_conv_pre =>
        rw [cmk_ok_pre_sp436 sp,
          memRegion_four (sp + 404#64),
          memRegion_four (sp + 436#64),
          memRegion_four (sp + 44#64)]
        simp only [sepConj_assoc]
      wp_pull_exists
      rename_i pad44 pad436 pad404
      refine focus_weaken_bi (cmk_merge64 sp 432#64 436#64 mkg.counter pad436) ?_
      refine focus_weaken_bi (cmk_merge64 sp 40#64 44#64 x.msg.counter pad44) ?_
      wp_conv_pre =>
        rw [cmk_ok_pre_sp0 sp, cmk_ok_pre_sp440 sp, cmk_ok_pre_sp488 sp]
        simp only [cells_succ, cells_zero, sepConj_emp, sepExists_sepConj_left,
          sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      wp_pull_exists
      wp_steps
      refine focus_weaken_bi (cmk_ok_split1112 sp mkg.counter pad436) ?_
      refine focus_weaken_bi (pointsTo32_entails_memRegion (sp + 400#64) 1#32) ?_
      refine focus_weaken_bi (pointsTo32_entails_memRegion (sp + 404#64) pad404) ?_
      rw [cmk_ok_post_sp320 sp, cmk_ok_post_sp1116 sp]; wp_done
    · intro sm4 hpc4 hrun4 hcl4 hL4
        ⟨hx24_4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx25_4, hx27_4, hx28_4,
         hfp4, hsp4, hsp_al4, htr4, hvregs4⟩
        hm4
      by_cases hcap : dispCap = 0
      · simp only [hcap, ↓reduceIte, emp_sepConj] at hm4
        subst hcap
        refine steps_of_sepWP_placed hm4 hL4 hcl4
          (mid := (blkPl_131).base + 1464#64)
          (RegMid := fun sf =>
            (sf.readReg64 .x24).setWidth 32 = 1#32 ∧
            sf.readReg64 .x19 = x.ret ∧
            sf.readReg64 .x20 = sp + 320#64 ∧
            sf.readReg64 .x21 = x.ss ∧
            sf.readReg64 .x22 = x.msgA ∧
            sf.readReg64 .x23 = sp + 1280#64 ∧
            sf.readReg64 .x25 = sp + 400#64 ∧
            sf.readReg64 .fp = sp + 1408#64 ∧
            sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s0.trace ∧
            calleeSavedVRegs sf = calleeSavedVRegs s0)
          (P_mid :=
            sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
            trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
            (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
              (seedPtr ↦ₛ mkg.seed) ∗
              memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
                (seedCap.toNat - mkg.seed.length)) ∗
            memRegion x.ret 48 ∗
            memRegion sp 16 ∗
            ((sp + 16#64) ↦₆₄ seedPtr) ∗
            memRegion (sp + 24#64) 4 ∗
            ((sp + 28#64) ↦₃₂ msgW) ∗
            ((sp + 32#64) ↦₆₄ x.locA) ∗
            ((sp + 40#64) ↦₆₄ seedCap) ∗
            ((sp + 48#64) ↦₆₄ x.remA) ∗
            memRegion (sp + 320#64) 784 ∗
            ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
            ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
            memRegion (sp + 1116#64) 292 ∗
            protocolAddressAt A x.rem x.remA ∗
            protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗
            tapeAfter ctl x.cur x.rest draws ∗
            logOff tryDecryptPlacedImg ∗
            stackAt sp tryDecryptSubStack ∗
            tryDecryptSavedRegs s0.sp s0 ∗
            A.pool) ?_ ?_
        · wp_steps
          wp_done
        · intro sf hpcf hrunf hclf _
            ⟨hx24_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx25_f, hfp_f, hsp_f, hsp_alf, htr_f, hvregs_f⟩
            hmf
          subst hsp_def
          refine ⟨sf, .refl _, Or.inl ⟨trG', ?_⟩⟩
          have hpc_s5 : sf.pc = segPqRecvPC_at (blkPl_131).base := by
            rw [hpcf]
          have hfp_f' : sf.readReg64 .x29 = s0.sp - 96#64 := by
            change sf.readReg64 .fp = s0.sp - 96#64
            rw [hfp_f]; exact (sp_fp_eq rfl).symm
          refine ⟨hpc_s5, ⟨hrunf, hsp_f, hsp0_al, hsp_alf, hfp_f', htr_f, hclf, hvregs_f⟩,
            hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f,
            seedCap, seedPtr, msgW, hmsgW_byte, hseed1, hseed2, hseed3, ?_⟩
          dsimp only [tryDecryptCommonHeap]
          simp only [sepConj_assoc] at hmf ⊢
          arm64_sep_close
      · simp only [hcap, ↓reduceIte] at hm4
        have hcap_beq : (dispCap == 0#64) = false := beq_false_of_ne hcap
        refine steps_of_sepWP_placed hm4 hL4 hcl4
          (mid := lsρ lsRustDeallocSym)
          (RegMid := fun sm5 =>
            sm5.readReg64 .x0 = dispPtr ∧
            sm5.readReg64 .x1 = dispCap ∧
            sm5.readReg64 .x2 = 1#64 ∧
            (sm5.readReg64 .x24).setWidth 32 = 1#32 ∧
            sm5.readReg64 .x19 = x.ret ∧
            sm5.readReg64 .x20 = sp + 320#64 ∧
            sm5.readReg64 .x21 = x.ss ∧
            sm5.readReg64 .x22 = x.msgA ∧
            sm5.readReg64 .x23 = sp + 1280#64 ∧
            sm5.readReg64 .x25 = sp + 400#64 ∧
            sm5.readReg64 .fp = sp + 1408#64 ∧
            sm5.readReg64 .lr = (blkPl_131).base + 1464#64 ∧
            sm5.sp = sp ∧ sm5.spAligned = true ∧ sm5.trace = s0.trace ∧
            calleeSavedVRegs sm5 = calleeSavedVRegs s0)
          (P_mid :=
            sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
            trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
            A.live dispPtr dispCap.toNat 1 ∗
            memRegion dispPtr dispCap.toNat ∗
            (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
              (seedPtr ↦ₛ mkg.seed) ∗
              memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
                (seedCap.toNat - mkg.seed.length)) ∗
            memRegion x.ret 48 ∗
            memRegion sp 16 ∗
            ((sp + 16#64) ↦₆₄ seedPtr) ∗
            memRegion (sp + 24#64) 4 ∗
            ((sp + 28#64) ↦₃₂ msgW) ∗
            ((sp + 32#64) ↦₆₄ x.locA) ∗
            ((sp + 40#64) ↦₆₄ seedCap) ∗
            ((sp + 48#64) ↦₆₄ x.remA) ∗
            memRegion (sp + 320#64) 784 ∗
            ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
            ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
            memRegion (sp + 1116#64) 292 ∗
            protocolAddressAt A x.rem x.remA ∗
            protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗
            tapeAfter ctl x.cur x.rest draws ∗
            logOff tryDecryptPlacedImg ∗
            stackAt sp tryDecryptSubStack ∗
            tryDecryptSavedRegs s0.sp s0 ∗
            A.pool) ?_ ?_
        · wp_conv_pre => simp only [sepConj_assoc]
          wp_steps
          refine focus_weaken_bi (buf_to_mr dispPtr dispBs dispCap.toNat hdisp1 hdisp2) ?_
          wp_done
        · intro sm5 hpc5 hrun5 hcl5 hL5
            ⟨hx0_5, hx1_5, hx2_5, hx24_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5,
             hx25_5, hfp5, hlr5, hsp5, hsp_al5, htr5, hvregs5⟩
            hm5
          have hstack_dealloc := stackAt_sub sp tryDecryptSubStack allocHookStack (by decide) (by decide)
          have hpre_dealloc : sm5.mem ⊨
              (rustDeallocSpec A).pre (dispPtr, dispCap.toNat, 1) sm5 ∗
              ((sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
                trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
                (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
                  (seedPtr ↦ₛ mkg.seed) ∗
                  memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
                    (seedCap.toNat - mkg.seed.length)) ∗
                memRegion x.ret 48 ∗
                memRegion sp 16 ∗
                ((sp + 16#64) ↦₆₄ seedPtr) ∗
                memRegion (sp + 24#64) 4 ∗
                ((sp + 28#64) ↦₃₂ msgW) ∗
                ((sp + 32#64) ↦₆₄ x.locA) ∗
                ((sp + 40#64) ↦₆₄ seedCap) ∗
                ((sp + 48#64) ↦₆₄ x.remA) ∗
                memRegion (sp + 320#64) 784 ∗
                ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
                ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
                memRegion (sp + 1116#64) 292 ∗
                protocolAddressAt A x.rem x.remA ∗
                protocolAddressAt A x.loc x.locA ∗
                signalMessageAt A x.msgG x.msgA x.msg ∗
                tapeAfter ctl x.cur x.rest draws ∗
                logOff tryDecryptPlacedImg ∗
                memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
                  (tryDecryptSubStack - allocHookStack) ∗
                tryDecryptSavedRegs s0.sp s0) ∗ R) := by
            dsimp only [rustDeallocSpec]
            rw [hsp5, sepConj_assoc, satisfies_pure_sepConj]
            refine ⟨⟨hx0_5, by rw [hx1_5], by rw [hx2_5]; rfl⟩, ?_⟩
            rw [hstack_dealloc] at hm5
            simp only [sepConj_assoc] at hm5 ⊢
            arm64_sep_close
          refine steps_call_out_placed (dispPtr, dispCap.toNat, 1) hdealloc
            hpc5 hrun5 hsp_al5 hlr5 hcl5 hL5 hpre_dealloc ?_ ?_
          · intro sf _ hpost
            dsimp only [rustDeallocSpec] at hpost
            rw [sepConj_assoc] at hpost
            exact (not_satisfies_false_sepConj hpost).elim
          · intro sf hpcf hrunf hspf hsp_alf hcsf hclf _ hpost
            have hx24_f : (sf.readReg64 .x24).setWidth 32 = 1#32 := by
              rw [show sf.readReg64 .x24 = sm5.readReg64 .x24 by reg_chain]; exact hx24_5
            have hfp_f_sp : sf.readReg64 .fp = sp + 1408#64 := by reg_chain
            dsimp only [rustDeallocSpec] at hpost
            rw [hsp5, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
            rcases hpost with ⟨htr_f, hpost⟩
            subst hsp_def
            refine ⟨sf, .refl _, Or.inl ⟨trG', ?_⟩⟩
            have hpc_s5 : sf.pc = segPqRecvPC_at (blkPl_131).base := by
              rw [hpcf]
            have hfp_f : sf.readReg64 .x29 = s0.sp - 96#64 := by
              change sf.readReg64 .fp = s0.sp - 96#64
              rw [hfp_f_sp]; exact (sp_fp_eq rfl).symm
            refine ⟨hpc_s5, ⟨hrunf, by reg_chain, hsp0_al, hsp_alf, hfp_f, by reg_chain, hclf, by reg_chain⟩,
              by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, hx24_f,
              by reg_chain, seedCap, seedPtr, msgW, hmsgW_byte, hseed1, hseed2, hseed3, ?_⟩
            dsimp only [tryDecryptCommonHeap]
            rw [hstack_dealloc]
            simp only [sepConj_assoc] at hpost ⊢
            arm64_sep_close

theorem consumeMsgKey_cmk_err_159_placed [LibsignalPlacement] (_C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (_parse : UuidParser) (H : String → Option (State → State))
    (x : TryDecryptGhost) (trG' : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (r2 : RatchetState) (e : SignalProtocolError)
    (draws : Nat) (R : SepProp) (s0 : State)
    {sp dispCap dispPtr : BitVec 64} {dispBs : List (BitVec 8)} {msgW : BitVec 32}
    (hne_panic : e ≠ .panic)
    (hsp0_al : s0.spAligned = true)
    (hsp_al' : (sp &&& 15#64 == 0#64) = true)
    (hdealloc : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hsp_def : s0.sp - 1504#64 = sp)
    (hdisp1 : dispBs.length ≤ dispCap.toNat)
    (hdisp2 : dispCap.toNat < 2 ^ 63)
    (sf2 : State)
    (hpcf2 : sf2.pc = (blkPl_131).base + 1144#64)
    (hrunf2 : sf2.status = .Running)
    (hsp_f2 : sf2.sp = sp)
    (hsp_alf2 : sf2.spAligned = true)
    (hx19_f2 : sf2.readReg64 .x19 = x.ret)
    (hx20_f2 : sf2.readReg64 .x20 = sp + 320#64)
    (_hx23_f2 : sf2.readReg64 .x23 = sp + 1280#64)
    (hx25_f2 : sf2.readReg64 .x25 = sp + 400#64)
    (hx27_f2 : sf2.readReg64 .x27 = dispPtr)
    (hx28_f2 : sf2.readReg64 .x28 = dispCap)
    (hfp_f2 : sf2.readReg64 .fp = sp + 1408#64)
    (htr_f2' : sf2.trace = s0.trace)
    (hvregs_f2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0)
    (hclf2 : LibsignalCodeRoLoaded lsmpl sf2.mem)
    (hLf2 : ((blkPC_131).rebase (blkPl_131).base H).CodeLoaded sf2.mem)
    (hm_post2 : sf2.mem ⊨
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
       (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
         (dispPtr ↦ₛ dispBs) ∗
         memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
       consumeMessageKeyResultAt A (sp + 400#64) (.error e) ∗
       memRegion x.ret 48 ∗
       memRegion sp 28 ∗
       ((sp + 28#64) ↦₃₂ msgW) ∗
       ((sp + 32#64) ↦₆₄ x.locA) ∗
       ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 44#64) 4 ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 320#64) 80 ∗
       memRegion (sp + 488#64) 920 ∗
       protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       tapeAfter ctl x.cur x.rest draws ∗
       logOff tryDecryptPlacedImg ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool) ∗ R) :
    ∃ s', Steps ((blkPC_131).rebase (blkPl_131).base H) sf2 s' ∧
      ((e ≠ .panic ∧ ∃ trG'',
          ErrTailStatePlaced (blkPl_131).base A ctl x trG'' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
       (s'.status = .Panicked ∧
         ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
         (s'.mem ⊨ anyHeap ∗ R))) := by
  have hm_err : sf2.mem ⊨
      (∃∗ w416 : BitVec 64, ∃∗ w424 : BitVec 64, ∃∗ w432 : BitVec 64,
       ∃∗ w440 : BitVec 64, ∃∗ w448 : BitVec 64, ∃∗ restHeap : SepProp,
        ⌜ErrWordsRel A e w416 w424 w432 w440 restHeap ∧ speTag e + 2#64 ≠ 0#64⌝ ∗
        ((sp + 400#64) ↦₃₂ 2#32) ∗
        memRegion (sp + 404#64) 4 ∗
        ((sp + 408#64) ↦₆₄ speTag e) ∗
        ((sp + 416#64) ↦₆₄ w416) ∗
        ((sp + 424#64) ↦₆₄ w424) ∗
        ((sp + 432#64) ↦₆₄ w432) ∗
        ((sp + 440#64) ↦₆₄ w440) ∗
        ((sp + 448#64) ↦₆₄ w448) ∗
        memRegion (sp + 456#64) 32 ∗
        restHeap) ∗
      ((sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
        trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
        (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
          (dispPtr ↦ₛ dispBs) ∗
          memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
        memRegion x.ret 48 ∗
        memRegion sp 56 ∗
        memRegion (sp + 320#64) 80 ∗
        memRegion (sp + 488#64) 920 ∗
        protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        tapeAfter ctl x.cur x.rest draws ∗
        logOff tryDecryptPlacedImg ∗
        stackAt sp tryDecryptSubStack ∗
        tryDecryptSavedRegs s0.sp s0 ∗
        A.pool) ∗ R) := by
    have hm_post3 := Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (cmk_sp56_pack_rest sp msgW x.msg.counter x.locA x.remA _))))))) hm_post2
    generalize sessionStateAt A x.ss x.G.afterTrFrom st1 = ssH,
      trAt A (sp + 56#64) trG' { tr with ratchet := r2 } = trH,
      protocolAddressAt A x.rem x.remA = remH, protocolAddressAt A x.loc x.locA = locH,
      signalMessageAt A x.msgG x.msgA x.msg = msgH, tapeAfter ctl x.cur x.rest draws = tapeH at hm_post3 ⊢
    refine Satisfies.mono ?_ hm_post3
    refine Entails.trans ?_ (sepConj_mono_left (resultAt_err_unpack A sp e))
    bi_entail
  simp only [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hm_err
  rcases hm_err with ⟨w416, w424, w432, w440, w448, restHeap, hm_err⟩
  rw [satisfies_pure_sepConj] at hm_err
  rcases hm_err with ⟨⟨hrel, htag_ne⟩, hm_err⟩
  simp only [← sepConj_assoc] at hm_err
  refine steps_of_sepWP_placed hm_err hLf2 hclf2
    (mid := (blkPl_131).base + 1180#64)
    (RegMid := fun sm3 =>
      sm3.readReg64 .x19 = x.ret ∧
      sm3.readReg64 .x20 = sp + 320#64 ∧
      sm3.readReg64 .x26 = speTag e ∧
      sm3.readReg64 .x27 = dispPtr ∧
      sm3.readReg64 .x28 = dispCap ∧
      sm3.readReg64 .fp = sp + 1408#64 ∧
      sm3.sp = sp ∧ sm3.spAligned = true ∧ sm3.trace = s0.trace ∧
      calleeSavedVRegs sm3 = calleeSavedVRegs s0)
    (P_mid :=
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
      (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
        (dispPtr ↦ₛ dispBs) ∗
        memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
      memRegion x.ret 48 ∗
      memRegion sp 56 ∗
      memRegion (sp + 320#64) 40 ∗
      speBodyAt A (utf8 "decrypt") (sp + 360#64) e ∗
      memRegion (sp + 400#64) 1008 ∗
      protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      tapeAfter ctl x.cur x.rest draws ∗
      logOff tryDecryptPlacedImg ∗
      stackAt sp tryDecryptSubStack ∗
      tryDecryptSavedRegs s0.sp s0 ∗
      A.pool) ?_ ?_
  · wp_conv_pre =>
      rw [cmk_err_pre_sp320 sp, cmk_err_pre_sp488 sp]
      simp only [cells_succ, cells_zero, sepConj_emp, sepExists_sepConj_left,
        sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    wp_pull_exists
    have htag_beq : (speTag e + 2#64 == 0#64) = false := beq_false_of_ne htag_ne
    have htag_beq0 : (speTag e + 2#64 + 0#64 == 0#64) = false := by
      rw [BitVec.add_zero]; exact htag_beq
    wp_steps
    refine focus_weaken_bi
      (speBodyAt_err_pack A sp e w416 w424 w432 w440 w448 restHeap hrel) ?_
    refine focus_weaken_bi (pointsTo32_entails_memRegion (sp + 400#64) 2#32) ?_
    rw [cmk_err_post_sp400 sp]; wp_done
  · intro sm3 hpc3 hrun3 hcl3 hL3
      ⟨hx19_3, hx20_3, hx26_3, hx27_3, hx28_3, hfp3, hsp3, hsp_al3, htr3, hvregs3⟩
      hm3
    have herr_tail : ∀ st4 : State,
        st4.pc = (blkPl_131).base + 1200#64 → st4.status = .Running →
        st4.sp = sp → st4.spAligned = true →
        st4.readReg64 .fp = sp + 1408#64 → st4.trace = s0.trace →
        calleeSavedVRegs st4 = calleeSavedVRegs s0 →
        LibsignalCodeRoLoaded lsmpl st4.mem →
        ((blkPC_131).rebase (blkPl_131).base H).CodeLoaded st4.mem →
        st4.readReg64 .x19 = x.ret →
        st4.readReg64 .x20 = sp + 320#64 →
        st4.readReg64 .x26 = speTag e →
        (st4.mem ⊨
          (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
           trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
           memRegion x.ret 48 ∗
           memRegion sp 56 ∗
           memRegion (sp + 320#64) 40 ∗
           speBodyAt A (utf8 "decrypt") (sp + 360#64) e ∗
           memRegion (sp + 400#64) 1008 ∗
           protocolAddressAt A x.rem x.remA ∗
           protocolAddressAt A x.loc x.locA ∗
           signalMessageAt A x.msgG x.msgA x.msg ∗
           tapeAfter ctl x.cur x.rest draws ∗
           logOff tryDecryptPlacedImg ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool) ∗ R) →
        ∃ s', Steps ((blkPC_131).rebase (blkPl_131).base H) st4 s' ∧
          ((e ≠ .panic ∧ ∃ trG'',
              ErrTailStatePlaced (blkPl_131).base A ctl x trG'' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
             (s'.mem ⊨ anyHeap ∗ R))) := by
      intro st4 hpc4 hrun4 hsp4 hsp_al4 hfp4 htr4 hvregs4 hcl4 hL4 hx19_4 hx20_4 hx26_4 hm4
      refine steps_of_sepWP_placed hm4 hL4 hcl4
        (mid := (blkPl_131).base + 780#64)
        (RegMid := fun sf =>
          sf.readReg64 .x19 = x.ret ∧
          sf.readReg64 .x20 = sp + 320#64 ∧
          sf.readReg64 .x26 = speTag e ∧
          sf.readReg64 .fp = sp + 1408#64 ∧
          sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s0.trace ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0)
        (P_mid :=
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
          memRegion x.ret 48 ∗
          memRegion sp 56 ∗
          memRegion (sp + 320#64) 40 ∗
          speBodyAt A (utf8 "decrypt") (sp + 360#64) e ∗
          memRegion (sp + 400#64) 1008 ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗
          tapeAfter ctl x.cur x.rest draws ∗
          logOff tryDecryptPlacedImg ∗
          stackAt sp tryDecryptSubStack ∗
          tryDecryptSavedRegs s0.sp s0 ∗
          A.pool) ?_ ?_
      · wp_steps
        wp_done
      · intro sf hpcf hrunf hclf _ ⟨hx19_f, hx20_f, hx26_f, hfp_f, hsp_f, hsp_alf, htr_f, hvregs_f⟩ hmf
        subst hsp_def
        refine ⟨sf, .refl _, Or.inl ⟨hne_panic, trG', ?_⟩⟩
        have hpc_err : sf.pc = errTailPC_at (blkPl_131).base := by
          rw [hpcf]
        have hfp_f' : sf.readReg64 .x29 = s0.sp - 96#64 := by
          change sf.readReg64 .fp = s0.sp - 96#64
          rw [hfp_f]; exact (sp_fp_eq rfl).symm
        refine ⟨hpc_err, ⟨hrunf, hsp_f, hsp0_al, hsp_alf, hfp_f', htr_f, hclf, hvregs_f⟩,
          hx19_f, hx20_f, hx26_f, ?_⟩
        dsimp only [tryDecryptCommonHeap]
        simp only [sepConj_assoc] at hmf ⊢
        arm64_sep_close
    by_cases hcap : dispCap = 0
    · simp only [hcap, ↓reduceIte, emp_sepConj] at hm3
      subst hcap
      refine steps_of_sepWP_placed hm3 hL3 hcl3
        (mid := (blkPl_131).base + 1200#64)
        (RegMid := fun st4 =>
          st4.readReg64 .x19 = x.ret ∧
          st4.readReg64 .x20 = sp + 320#64 ∧
          st4.readReg64 .x26 = speTag e ∧
          st4.readReg64 .fp = sp + 1408#64 ∧
          st4.sp = sp ∧ st4.spAligned = true ∧ st4.trace = s0.trace ∧
          calleeSavedVRegs st4 = calleeSavedVRegs s0)
        (P_mid :=
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
          memRegion x.ret 48 ∗
          memRegion sp 56 ∗
          memRegion (sp + 320#64) 40 ∗
          speBodyAt A (utf8 "decrypt") (sp + 360#64) e ∗
          memRegion (sp + 400#64) 1008 ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗
          tapeAfter ctl x.cur x.rest draws ∗
          logOff tryDecryptPlacedImg ∗
          stackAt sp tryDecryptSubStack ∗
          tryDecryptSavedRegs s0.sp s0 ∗
          A.pool) ?_ ?_
      · wp_steps
        wp_done
      · intro st4 hpc4 hrun4 hcl4 hL4 ⟨hx19_4, hx20_4, hx26_4, hfp4, hsp4, hsp_al4, htr4, hvregs4⟩ hm4
        exact herr_tail st4 hpc4 hrun4 hsp4 hsp_al4 hfp4 htr4 hvregs4 hcl4 hL4 hx19_4 hx20_4 hx26_4 hm4
    · simp only [hcap, ↓reduceIte] at hm3
      have hcap_beq : (dispCap == 0#64) = false := beq_false_of_ne hcap
      refine steps_of_sepWP_placed hm3 hL3 hcl3
        (mid := lsρ lsRustDeallocSym)
        (RegMid := fun sm4 =>
          sm4.readReg64 .x0 = dispPtr ∧
          sm4.readReg64 .x1 = dispCap ∧
          sm4.readReg64 .x2 = 1#64 ∧
          sm4.readReg64 .x19 = x.ret ∧
          sm4.readReg64 .x20 = sp + 320#64 ∧
          sm4.readReg64 .x26 = speTag e ∧
          sm4.readReg64 .fp = sp + 1408#64 ∧
          sm4.readReg64 .lr = (blkPl_131).base + 1200#64 ∧
          sm4.sp = sp ∧ sm4.spAligned = true ∧ sm4.trace = s0.trace ∧
          calleeSavedVRegs sm4 = calleeSavedVRegs s0)
        (P_mid :=
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
          A.live dispPtr dispCap.toNat 1 ∗
          memRegion dispPtr dispCap.toNat ∗
          memRegion x.ret 48 ∗
          memRegion sp 56 ∗
          memRegion (sp + 320#64) 40 ∗
          speBodyAt A (utf8 "decrypt") (sp + 360#64) e ∗
          memRegion (sp + 400#64) 1008 ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗
          tapeAfter ctl x.cur x.rest draws ∗
          logOff tryDecryptPlacedImg ∗
          stackAt sp tryDecryptSubStack ∗
          tryDecryptSavedRegs s0.sp s0 ∗
          A.pool) ?_ ?_
      · wp_conv_pre => simp only [sepConj_assoc]
        wp_steps
        refine focus_weaken_bi (buf_to_mr dispPtr dispBs dispCap.toNat hdisp1 hdisp2) ?_
        wp_done
      · intro sm4 hpc4 hrun4 hcl4 hL4
          ⟨hx0_4, hx1_4, hx2_4, hx19_4, hx20_4, hx26_4, hfp4, hlr4, hsp4, hsp_al4, htr4, hvregs4⟩
          hm4
        have hstack_dealloc := stackAt_sub sp tryDecryptSubStack allocHookStack (by decide) (by decide)
        have hpre_dealloc : sm4.mem ⊨
            (rustDeallocSpec A).pre (dispPtr, dispCap.toNat, 1) sm4 ∗
            ((sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
              trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
              memRegion x.ret 48 ∗
              memRegion sp 56 ∗
              memRegion (sp + 320#64) 40 ∗
              speBodyAt A (utf8 "decrypt") (sp + 360#64) e ∗
              memRegion (sp + 400#64) 1008 ∗
              protocolAddressAt A x.rem x.remA ∗
              protocolAddressAt A x.loc x.locA ∗
              signalMessageAt A x.msgG x.msgA x.msg ∗
              tapeAfter ctl x.cur x.rest draws ∗
              logOff tryDecryptPlacedImg ∗
              memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
                (tryDecryptSubStack - allocHookStack) ∗
              tryDecryptSavedRegs s0.sp s0) ∗ R) := by
          dsimp only [rustDeallocSpec]
          rw [hsp4, sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hx0_4, by rw [hx1_4], by rw [hx2_4]; rfl⟩, ?_⟩
          rw [hstack_dealloc] at hm4
          simp only [sepConj_assoc] at hm4 ⊢
          arm64_sep_close
        refine steps_call_out_placed (dispPtr, dispCap.toNat, 1) hdealloc
          hpc4 hrun4 hsp_al4 hlr4 hcl4 hL4 hpre_dealloc ?_ ?_
        · intro sf _ hpost
          dsimp only [rustDeallocSpec] at hpost
          rw [sepConj_assoc] at hpost
          exact (not_satisfies_false_sepConj hpost).elim
        · intro st5 hpc5 hrun5 hsp5 hsp_al5 hcs5 hcl5 hL5 hpost5
          dsimp only [rustDeallocSpec] at hpost5
          rw [hsp4, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost5
          rcases hpost5 with ⟨htr5, hpost5⟩
          refine herr_tail st5 hpc5 hrun5 (by reg_chain) hsp_al5 (by reg_chain) (by reg_chain) (by reg_chain)
            hcl5 hL5 (by reg_chain) (by reg_chain) (by reg_chain) ?_
          rw [hstack_dealloc]
          simp only [sepConj_assoc] at hpost5 ⊢
          arm64_sep_close

end KeyDeriveCallees

@[expose] def cmkRawSpecPlaced [LibsignalPlacement] (F : ShaCompress) (A : RustAlloc) :
    Spec CryptoVerification.LibsignalSession.ConsumeMessageKeyGhost :=
  { pre := fun x s =>
      ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.theirA ∧ s.readReg64 .x2 = x.ckA ∧
        (s.readReg64 .x3).setWidth 32 = x.counter ∧
        (s.readReg64 .x4).setWidth 8 = msgTypeByte x.msgType ∧ s.readReg64 .x8 = x.ret⌝ ∗
      ratchetAt A x.self x.G x.st ∗
      (x.theirA ↦ₛ x.their.bytes.toList) ∗ (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
      memRegion x.ret 88 ∗ logOff tryDecryptPlacedImg ∗
      stackAt s.sp CryptoVerification.LibsignalSession.cmkStack ∗ A.pool
    post := fun x s0 sf =>
      ⌜(x.model F).1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
      (∃∗ G' : RatchetGhost,
        ⌜x.G.AgreeExcept G' (x.touched F)⌝ ∗ ratchetAt A x.self G' (x.model F).2) ∗
      CryptoVerification.LibsignalSessionRepr.consumeMessageKeyResultAt A x.ret (x.model F).1 ∗
      (x.theirA ↦ₛ x.their.bytes.toList) ∗ memRegion x.ckA 36 ∗
      logOff tryDecryptPlacedImg ∗
      stackAt s0.sp CryptoVerification.LibsignalSession.cmkStack ∗ A.pool
    onPanic := fun x s0 sf =>
      ⌜((x.model F).1 = .error .panic ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

namespace KeyDeriveCallees

theorem consumeMsgKey_cmk_ok_549_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (x : TryDecryptGhost) (trG' : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (r2 : RatchetState) (mkg : MessageKeyGenerator)
    (draws : Nat) (R : SepProp) (s0 : State)
    {sp dispCap dispPtr : BitVec 64} {dispBs : List (BitVec 8)} {msgW : BitVec 32}
    (hsp0_al : s0.spAligned = true)
    (hsp_al' : (sp &&& 15#64 == 0#64) = true)
    (hdealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hsp_def : s0.sp - 1504#64 = sp)
    (hdisp1 : dispBs.length ≤ dispCap.toNat)
    (hdisp2 : dispCap.toNat < 2 ^ 63)
    (hmsgW_byte : msgW.setWidth 8 = msgTypeByte x.msgType)
    (sf2 : State)
    (hpcf2 : sf2.pc = (blkPl_434).base + 1144#64)
    (hrunf2 : sf2.status = .Running)
    (hsp_f2 : sf2.sp = sp)
    (hsp_alf2 : sf2.spAligned = true)
    (hx19_f2 : sf2.readReg64 .x19 = x.ret)
    (hx20_f2 : sf2.readReg64 .x20 = sp + 320#64)
    (hx21_f2 : sf2.readReg64 .x21 = x.ss)
    (hx22_f2 : sf2.readReg64 .x22 = x.msgA)
    (hx23_f2 : sf2.readReg64 .x23 = sp + 1280#64)
    (hx25_f2 : sf2.readReg64 .x25 = sp + 400#64)
    (hx27_f2 : sf2.readReg64 .x27 = dispPtr)
    (hx28_f2 : sf2.readReg64 .x28 = dispCap)
    (hfp_f2 : sf2.readReg64 .fp = sp + 1408#64)
    (htr_f2' : sf2.trace = s0.trace)
    (hvregs_f2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0)
    (hclf2 : LibsignalCodeRoLoaded lsmpl sf2.mem)
    (hLf2 : ((blkPC_434).rebase (blkPl_434).base H).CodeLoaded sf2.mem)
    (hm_post2 : sf2.mem ⊨
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
       (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
         (dispPtr ↦ₛ dispBs) ∗
         memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
       consumeMessageKeyResultAt A (sp + 400#64) (.ok mkg) ∗
       memRegion x.ret 48 ∗
       memRegion sp 28 ∗
       ((sp + 28#64) ↦₃₂ msgW) ∗
       ((sp + 32#64) ↦₆₄ x.locA) ∗
       ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 44#64) 4 ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 320#64) 80 ∗
       memRegion (sp + 488#64) 920 ∗
       protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       tapeAfter ctl x.cur x.rest draws ∗
       logOff tryDecryptPlacedImg ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool) ∗ R) :
    ∃ s', Steps ((blkPC_434).rebase (blkPl_434).base H) sf2 s' ∧
      ((∃ trG'', PqRecvStatePlaced (blkPl_434).base A ctl x trG'' { tr with ratchet := r2 } st1 mkg draws R s0 s') ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R))) := by
  dsimp only [consumeMessageKeyResultAt, vecU8, vecU8At, vecHeader] at hm_post2
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_post2
  rcases hm_post2 with ⟨seedCap, seedPtr, hm_post2⟩
  simp only [sepConj_pure_left_comm, satisfies_pure_sepConj] at hm_post2
  rcases hm_post2 with ⟨⟨hseed1, hseed2, hseed3⟩, hm_post2⟩
  simp only [← sepConj_assoc] at hm_post2
  refine steps_of_sepWP_placed hm_post2 hLf2 hclf2
    (mid := (blkPl_434).base + 1396#64)
    (RegMid := fun sm3 =>
      (sm3.readReg64 .x24).setWidth 32 = 1#32 ∧
      sm3.readReg64 .x19 = x.ret ∧
      sm3.readReg64 .x20 = sp + 320#64 ∧
      sm3.readReg64 .x21 = x.ss ∧
      sm3.readReg64 .x22 = x.msgA ∧
      sm3.readReg64 .x23 = sp + 1280#64 ∧
      sm3.readReg64 .x25 = sp + 400#64 ∧
      sm3.readReg64 .x27 = dispPtr ∧
      sm3.readReg64 .x28 = dispCap ∧
      sm3.readReg64 .fp = sp + 1408#64 ∧
      sm3.sp = sp ∧ sm3.spAligned = true ∧ sm3.trace = s0.trace ∧
      calleeSavedVRegs sm3 = calleeSavedVRegs s0)
    (P_mid :=
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
      (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
        (dispPtr ↦ₛ dispBs) ∗
        memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
      (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
        (seedPtr ↦ₛ mkg.seed) ∗
        memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
          (seedCap.toNat - mkg.seed.length)) ∗
      ((sp + 400#64) ↦₃₂ 1#32) ∗
      memRegion (sp + 404#64) 4 ∗
      ((sp + 408#64) ↦₆₄ seedCap) ∗
      ((sp + 416#64) ↦₆₄ seedPtr) ∗
      ((sp + 424#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((sp + 432#64) ↦₃₂ mkg.counter) ∗
      memRegion (sp + 436#64) 52 ∗
      memRegion x.ret 48 ∗
      memRegion sp 28 ∗
      ((sp + 28#64) ↦₃₂ msgW) ∗
      ((sp + 32#64) ↦₆₄ x.locA) ∗
      ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
      memRegion (sp + 44#64) 4 ∗
      ((sp + 48#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 320#64) 80 ∗
      memRegion (sp + 488#64) 920 ∗
      protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      tapeAfter ctl x.cur x.rest draws ∗
      logOff tryDecryptPlacedImg ∗
      stackAt sp tryDecryptSubStack ∗
      tryDecryptSavedRegs s0.sp s0 ∗
      A.pool) ?_ ?_
  · wp_conv_pre => simp only [sepConj_assoc]
    wp_steps
    wp_done
  · intro sm3 hpc3 hrun3 hcl3 hL3
      ⟨hx24_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx25_3, hx27_3, hx28_3,
       hfp3, hsp3, hsp_al3, htr3, hvregs3⟩
      hm3
    refine steps_of_sepWP_placed hm3 hL3 hcl3
      (mid := (blkPl_434).base + 1444#64)
      (RegMid := fun sm4 =>
        (sm4.readReg64 .x24).setWidth 32 = 1#32 ∧
        sm4.readReg64 .x19 = x.ret ∧
        sm4.readReg64 .x20 = sp + 320#64 ∧
        sm4.readReg64 .x21 = x.ss ∧
        sm4.readReg64 .x22 = x.msgA ∧
        sm4.readReg64 .x23 = sp + 1280#64 ∧
        sm4.readReg64 .x25 = sp + 400#64 ∧
        sm4.readReg64 .x27 = dispPtr ∧
        sm4.readReg64 .x28 = dispCap ∧
        sm4.readReg64 .fp = sp + 1408#64 ∧
        sm4.sp = sp ∧ sm4.spAligned = true ∧ sm4.trace = s0.trace ∧
        calleeSavedVRegs sm4 = calleeSavedVRegs s0)
      (P_mid :=
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
        trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
        (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
          (dispPtr ↦ₛ dispBs) ∗
          memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
        (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
          (seedPtr ↦ₛ mkg.seed) ∗
          memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
            (seedCap.toNat - mkg.seed.length)) ∗
        memRegion x.ret 48 ∗
        memRegion sp 16 ∗
        ((sp + 16#64) ↦₆₄ seedPtr) ∗
        memRegion (sp + 24#64) 4 ∗
        ((sp + 28#64) ↦₃₂ msgW) ∗
        ((sp + 32#64) ↦₆₄ x.locA) ∗
        ((sp + 40#64) ↦₆₄ seedCap) ∗
        ((sp + 48#64) ↦₆₄ x.remA) ∗
        memRegion (sp + 320#64) 784 ∗
        ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
        ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
        memRegion (sp + 1116#64) 292 ∗
        protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        tapeAfter ctl x.cur x.rest draws ∗
        logOff tryDecryptPlacedImg ∗
        stackAt sp tryDecryptSubStack ∗
        tryDecryptSavedRegs s0.sp s0 ∗
        A.pool) ?_ ?_
    · wp_conv_pre =>
        rw [cmk_ok_pre_sp436 sp,
          memRegion_four (sp + 404#64),
          memRegion_four (sp + 436#64),
          memRegion_four (sp + 44#64)]
        simp only [sepConj_assoc]
      wp_pull_exists
      rename_i pad44 pad436 pad404
      refine focus_weaken_bi (cmk_merge64 sp 432#64 436#64 mkg.counter pad436) ?_
      refine focus_weaken_bi (cmk_merge64 sp 40#64 44#64 x.msg.counter pad44) ?_
      wp_conv_pre =>
        rw [cmk_ok_pre_sp0 sp, cmk_ok_pre_sp440 sp, cmk_ok_pre_sp488 sp]
        simp only [cells_succ, cells_zero, sepConj_emp, sepExists_sepConj_left,
          sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      wp_pull_exists
      wp_steps
      refine focus_weaken_bi (cmk_ok_split1112 sp mkg.counter pad436) ?_
      refine focus_weaken_bi (pointsTo32_entails_memRegion (sp + 400#64) 1#32) ?_
      refine focus_weaken_bi (pointsTo32_entails_memRegion (sp + 404#64) pad404) ?_
      rw [cmk_ok_post_sp320 sp, cmk_ok_post_sp1116 sp]; wp_done
    · intro sm4 hpc4 hrun4 hcl4 hL4
        ⟨hx24_4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx25_4, hx27_4, hx28_4,
         hfp4, hsp4, hsp_al4, htr4, hvregs4⟩
        hm4
      by_cases hcap : dispCap = 0
      · simp only [hcap, ↓reduceIte, emp_sepConj] at hm4
        subst hcap
        refine steps_of_sepWP_placed hm4 hL4 hcl4
          (mid := (blkPl_434).base + 1464#64)
          (RegMid := fun sf =>
            (sf.readReg64 .x24).setWidth 32 = 1#32 ∧
            sf.readReg64 .x19 = x.ret ∧
            sf.readReg64 .x20 = sp + 320#64 ∧
            sf.readReg64 .x21 = x.ss ∧
            sf.readReg64 .x22 = x.msgA ∧
            sf.readReg64 .x23 = sp + 1280#64 ∧
            sf.readReg64 .x25 = sp + 400#64 ∧
            sf.readReg64 .fp = sp + 1408#64 ∧
            sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s0.trace ∧
            calleeSavedVRegs sf = calleeSavedVRegs s0)
          (P_mid :=
            sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
            trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
            (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
              (seedPtr ↦ₛ mkg.seed) ∗
              memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
                (seedCap.toNat - mkg.seed.length)) ∗
            memRegion x.ret 48 ∗
            memRegion sp 16 ∗
            ((sp + 16#64) ↦₆₄ seedPtr) ∗
            memRegion (sp + 24#64) 4 ∗
            ((sp + 28#64) ↦₃₂ msgW) ∗
            ((sp + 32#64) ↦₆₄ x.locA) ∗
            ((sp + 40#64) ↦₆₄ seedCap) ∗
            ((sp + 48#64) ↦₆₄ x.remA) ∗
            memRegion (sp + 320#64) 784 ∗
            ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
            ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
            memRegion (sp + 1116#64) 292 ∗
            protocolAddressAt A x.rem x.remA ∗
            protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗
            tapeAfter ctl x.cur x.rest draws ∗
            logOff tryDecryptPlacedImg ∗
            stackAt sp tryDecryptSubStack ∗
            tryDecryptSavedRegs s0.sp s0 ∗
            A.pool) ?_ ?_
        · wp_steps
          wp_done
        · intro sf hpcf hrunf hclf _
            ⟨hx24_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx25_f, hfp_f, hsp_f, hsp_alf, htr_f, hvregs_f⟩
            hmf
          subst hsp_def
          refine ⟨sf, .refl _, Or.inl ⟨trG', ?_⟩⟩
          have hpc_s5 : sf.pc = segPqRecvPC_at (blkPl_434).base := by
            rw [hpcf]
          have hfp_f' : sf.readReg64 .x29 = s0.sp - 96#64 := by
            change sf.readReg64 .fp = s0.sp - 96#64
            rw [hfp_f]; exact (sp_fp_eq rfl).symm
          refine ⟨hpc_s5, ⟨hrunf, hsp_f, hsp0_al, hsp_alf, hfp_f', htr_f, hclf, hvregs_f⟩,
            hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f,
            seedCap, seedPtr, msgW, hmsgW_byte, hseed1, hseed2, hseed3, ?_⟩
          dsimp only [tryDecryptCommonHeap]
          simp only [sepConj_assoc] at hmf ⊢
          arm64_sep_close
      · simp only [hcap, ↓reduceIte] at hm4
        have hcap_beq : (dispCap == 0#64) = false := beq_false_of_ne hcap
        refine steps_of_sepWP_placed hm4 hL4 hcl4
          (mid := lsρ lsRustDeallocSym)
          (RegMid := fun sm5 =>
            sm5.readReg64 .x0 = dispPtr ∧
            sm5.readReg64 .x1 = dispCap ∧
            sm5.readReg64 .x2 = 1#64 ∧
            (sm5.readReg64 .x24).setWidth 32 = 1#32 ∧
            sm5.readReg64 .x19 = x.ret ∧
            sm5.readReg64 .x20 = sp + 320#64 ∧
            sm5.readReg64 .x21 = x.ss ∧
            sm5.readReg64 .x22 = x.msgA ∧
            sm5.readReg64 .x23 = sp + 1280#64 ∧
            sm5.readReg64 .x25 = sp + 400#64 ∧
            sm5.readReg64 .fp = sp + 1408#64 ∧
            sm5.readReg64 .lr = (blkPl_434).base + 1464#64 ∧
            sm5.sp = sp ∧ sm5.spAligned = true ∧ sm5.trace = s0.trace ∧
            calleeSavedVRegs sm5 = calleeSavedVRegs s0)
          (P_mid :=
            sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
            trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
            A.live dispPtr dispCap.toNat 1 ∗
            memRegion dispPtr dispCap.toNat ∗
            (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
              (seedPtr ↦ₛ mkg.seed) ∗
              memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
                (seedCap.toNat - mkg.seed.length)) ∗
            memRegion x.ret 48 ∗
            memRegion sp 16 ∗
            ((sp + 16#64) ↦₆₄ seedPtr) ∗
            memRegion (sp + 24#64) 4 ∗
            ((sp + 28#64) ↦₃₂ msgW) ∗
            ((sp + 32#64) ↦₆₄ x.locA) ∗
            ((sp + 40#64) ↦₆₄ seedCap) ∗
            ((sp + 48#64) ↦₆₄ x.remA) ∗
            memRegion (sp + 320#64) 784 ∗
            ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
            ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
            memRegion (sp + 1116#64) 292 ∗
            protocolAddressAt A x.rem x.remA ∗
            protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗
            tapeAfter ctl x.cur x.rest draws ∗
            logOff tryDecryptPlacedImg ∗
            stackAt sp tryDecryptSubStack ∗
            tryDecryptSavedRegs s0.sp s0 ∗
            A.pool) ?_ ?_
        · wp_conv_pre => simp only [sepConj_assoc]
          wp_steps
          refine focus_weaken_bi (buf_to_mr dispPtr dispBs dispCap.toNat hdisp1 hdisp2) ?_
          wp_done
        · intro sm5 hpc5 hrun5 hcl5 hL5
            ⟨hx0_5, hx1_5, hx2_5, hx24_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5,
             hx25_5, hfp5, hlr5, hsp5, hsp_al5, htr5, hvregs5⟩
            hm5
          have hstack_dealloc := stackAt_sub sp tryDecryptSubStack allocHookStack (by decide) (by decide)
          have hpre_dealloc : sm5.mem ⊨
              (rustDeallocSpec A).pre (dispPtr, dispCap.toNat, 1) sm5 ∗
              ((sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
                trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
                (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
                  (seedPtr ↦ₛ mkg.seed) ∗
                  memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length)
                    (seedCap.toNat - mkg.seed.length)) ∗
                memRegion x.ret 48 ∗
                memRegion sp 16 ∗
                ((sp + 16#64) ↦₆₄ seedPtr) ∗
                memRegion (sp + 24#64) 4 ∗
                ((sp + 28#64) ↦₃₂ msgW) ∗
                ((sp + 32#64) ↦₆₄ x.locA) ∗
                ((sp + 40#64) ↦₆₄ seedCap) ∗
                ((sp + 48#64) ↦₆₄ x.remA) ∗
                memRegion (sp + 320#64) 784 ∗
                ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
                ((sp + 1112#64) ↦₃₂ mkg.counter) ∗
                memRegion (sp + 1116#64) 292 ∗
                protocolAddressAt A x.rem x.remA ∗
                protocolAddressAt A x.loc x.locA ∗
                signalMessageAt A x.msgG x.msgA x.msg ∗
                tapeAfter ctl x.cur x.rest draws ∗
                logOff tryDecryptPlacedImg ∗
                memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
                  (tryDecryptSubStack - allocHookStack) ∗
                tryDecryptSavedRegs s0.sp s0) ∗ R) := by
            dsimp only [rustDeallocSpec]
            rw [hsp5, sepConj_assoc, satisfies_pure_sepConj]
            refine ⟨⟨hx0_5, by rw [hx1_5], by rw [hx2_5]; rfl⟩, ?_⟩
            rw [hstack_dealloc] at hm5
            simp only [sepConj_assoc] at hm5 ⊢
            arm64_sep_close
          refine steps_call_out_placed (dispPtr, dispCap.toNat, 1) hdealloc
            hpc5 hrun5 hsp_al5 hlr5 hcl5 hL5 hpre_dealloc ?_ ?_
          · intro sf _ hpost
            dsimp only [rustDeallocSpec] at hpost
            rw [sepConj_assoc] at hpost
            exact (not_satisfies_false_sepConj hpost).elim
          · intro sf hpcf hrunf hspf hsp_alf hcsf hclf _ hpost
            have hx24_f : (sf.readReg64 .x24).setWidth 32 = 1#32 := by
              rw [show sf.readReg64 .x24 = sm5.readReg64 .x24 by reg_chain]; exact hx24_5
            have hfp_f_sp : sf.readReg64 .fp = sp + 1408#64 := by reg_chain
            dsimp only [rustDeallocSpec] at hpost
            rw [hsp5, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
            rcases hpost with ⟨htr_f, hpost⟩
            subst hsp_def
            refine ⟨sf, .refl _, Or.inl ⟨trG', ?_⟩⟩
            have hpc_s5 : sf.pc = segPqRecvPC_at (blkPl_434).base := by
              rw [hpcf]
            have hfp_f : sf.readReg64 .x29 = s0.sp - 96#64 := by
              change sf.readReg64 .fp = s0.sp - 96#64
              rw [hfp_f_sp]; exact (sp_fp_eq rfl).symm
            refine ⟨hpc_s5, ⟨hrunf, by reg_chain, hsp0_al, hsp_alf, hfp_f, by reg_chain, hclf, by reg_chain⟩,
              by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, hx24_f,
              by reg_chain, seedCap, seedPtr, msgW, hmsgW_byte, hseed1, hseed2, hseed3, ?_⟩
            dsimp only [tryDecryptCommonHeap]
            rw [hstack_dealloc]
            simp only [sepConj_assoc] at hpost ⊢
            arm64_sep_close

theorem consumeMsgKey_cmk_err_549_placed [LibsignalPlacement] (_C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (_parse : UuidParser) (H : String → Option (State → State))
    (x : TryDecryptGhost) (trG' : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (r2 : RatchetState) (e : SignalProtocolError)
    (draws : Nat) (R : SepProp) (s0 : State)
    {sp dispCap dispPtr : BitVec 64} {dispBs : List (BitVec 8)} {msgW : BitVec 32}
    (hne_panic : e ≠ .panic)
    (hsp0_al : s0.spAligned = true)
    (hsp_al' : (sp &&& 15#64 == 0#64) = true)
    (hdealloc : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hsp_def : s0.sp - 1504#64 = sp)
    (hdisp1 : dispBs.length ≤ dispCap.toNat)
    (hdisp2 : dispCap.toNat < 2 ^ 63)
    (sf2 : State)
    (hpcf2 : sf2.pc = (blkPl_434).base + 1144#64)
    (hrunf2 : sf2.status = .Running)
    (hsp_f2 : sf2.sp = sp)
    (hsp_alf2 : sf2.spAligned = true)
    (hx19_f2 : sf2.readReg64 .x19 = x.ret)
    (hx20_f2 : sf2.readReg64 .x20 = sp + 320#64)
    (_hx23_f2 : sf2.readReg64 .x23 = sp + 1280#64)
    (hx25_f2 : sf2.readReg64 .x25 = sp + 400#64)
    (hx27_f2 : sf2.readReg64 .x27 = dispPtr)
    (hx28_f2 : sf2.readReg64 .x28 = dispCap)
    (hfp_f2 : sf2.readReg64 .fp = sp + 1408#64)
    (htr_f2' : sf2.trace = s0.trace)
    (hvregs_f2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0)
    (hclf2 : LibsignalCodeRoLoaded lsmpl sf2.mem)
    (hLf2 : ((blkPC_434).rebase (blkPl_434).base H).CodeLoaded sf2.mem)
    (hm_post2 : sf2.mem ⊨
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
       (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
         (dispPtr ↦ₛ dispBs) ∗
         memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
       consumeMessageKeyResultAt A (sp + 400#64) (.error e) ∗
       memRegion x.ret 48 ∗
       memRegion sp 28 ∗
       ((sp + 28#64) ↦₃₂ msgW) ∗
       ((sp + 32#64) ↦₆₄ x.locA) ∗
       ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 44#64) 4 ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 320#64) 80 ∗
       memRegion (sp + 488#64) 920 ∗
       protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       tapeAfter ctl x.cur x.rest draws ∗
       logOff tryDecryptPlacedImg ∗
       stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool) ∗ R) :
    ∃ s', Steps ((blkPC_434).rebase (blkPl_434).base H) sf2 s' ∧
      ((e ≠ .panic ∧ ∃ trG'',
          ErrTailStatePlaced (blkPl_434).base A ctl x trG'' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
       (s'.status = .Panicked ∧
         ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
         (s'.mem ⊨ anyHeap ∗ R))) := by
  have hm_err : sf2.mem ⊨
      (∃∗ w416 : BitVec 64, ∃∗ w424 : BitVec 64, ∃∗ w432 : BitVec 64,
       ∃∗ w440 : BitVec 64, ∃∗ w448 : BitVec 64, ∃∗ restHeap : SepProp,
        ⌜ErrWordsRel A e w416 w424 w432 w440 restHeap ∧ speTag e + 2#64 ≠ 0#64⌝ ∗
        ((sp + 400#64) ↦₃₂ 2#32) ∗
        memRegion (sp + 404#64) 4 ∗
        ((sp + 408#64) ↦₆₄ speTag e) ∗
        ((sp + 416#64) ↦₆₄ w416) ∗
        ((sp + 424#64) ↦₆₄ w424) ∗
        ((sp + 432#64) ↦₆₄ w432) ∗
        ((sp + 440#64) ↦₆₄ w440) ∗
        ((sp + 448#64) ↦₆₄ w448) ∗
        memRegion (sp + 456#64) 32 ∗
        restHeap) ∗
      ((sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
        trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
        (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
          (dispPtr ↦ₛ dispBs) ∗
          memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
        memRegion x.ret 48 ∗
        memRegion sp 56 ∗
        memRegion (sp + 320#64) 80 ∗
        memRegion (sp + 488#64) 920 ∗
        protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        tapeAfter ctl x.cur x.rest draws ∗
        logOff tryDecryptPlacedImg ∗
        stackAt sp tryDecryptSubStack ∗
        tryDecryptSavedRegs s0.sp s0 ∗
        A.pool) ∗ R) := by
    have hm_post3 := Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (cmk_sp56_pack_rest sp msgW x.msg.counter x.locA x.remA _))))))) hm_post2
    generalize sessionStateAt A x.ss x.G.afterTrFrom st1 = ssH,
      trAt A (sp + 56#64) trG' { tr with ratchet := r2 } = trH,
      protocolAddressAt A x.rem x.remA = remH, protocolAddressAt A x.loc x.locA = locH,
      signalMessageAt A x.msgG x.msgA x.msg = msgH, tapeAfter ctl x.cur x.rest draws = tapeH at hm_post3 ⊢
    refine Satisfies.mono ?_ hm_post3
    refine Entails.trans ?_ (sepConj_mono_left (resultAt_err_unpack A sp e))
    bi_entail
  simp only [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hm_err
  rcases hm_err with ⟨w416, w424, w432, w440, w448, restHeap, hm_err⟩
  rw [satisfies_pure_sepConj] at hm_err
  rcases hm_err with ⟨⟨hrel, htag_ne⟩, hm_err⟩
  simp only [← sepConj_assoc] at hm_err
  refine steps_of_sepWP_placed hm_err hLf2 hclf2
    (mid := (blkPl_434).base + 1180#64)
    (RegMid := fun sm3 =>
      sm3.readReg64 .x19 = x.ret ∧
      sm3.readReg64 .x20 = sp + 320#64 ∧
      sm3.readReg64 .x26 = speTag e ∧
      sm3.readReg64 .x27 = dispPtr ∧
      sm3.readReg64 .x28 = dispCap ∧
      sm3.readReg64 .fp = sp + 1408#64 ∧
      sm3.sp = sp ∧ sm3.spAligned = true ∧ sm3.trace = s0.trace ∧
      calleeSavedVRegs sm3 = calleeSavedVRegs s0)
    (P_mid :=
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
      (if dispCap = 0 then emp else A.live dispPtr dispCap.toNat 1 ∗
        (dispPtr ↦ₛ dispBs) ∗
        memRegion (dispPtr + BitVec.ofNat 64 dispBs.length) (dispCap.toNat - dispBs.length)) ∗
      memRegion x.ret 48 ∗
      memRegion sp 56 ∗
      memRegion (sp + 320#64) 40 ∗
      speBodyAt A (utf8 "decrypt") (sp + 360#64) e ∗
      memRegion (sp + 400#64) 1008 ∗
      protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      tapeAfter ctl x.cur x.rest draws ∗
      logOff tryDecryptPlacedImg ∗
      stackAt sp tryDecryptSubStack ∗
      tryDecryptSavedRegs s0.sp s0 ∗
      A.pool) ?_ ?_
  · wp_conv_pre =>
      rw [cmk_err_pre_sp320 sp, cmk_err_pre_sp488 sp]
      simp only [cells_succ, cells_zero, sepConj_emp, sepExists_sepConj_left,
        sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    wp_pull_exists
    have htag_beq : (speTag e + 2#64 == 0#64) = false := beq_false_of_ne htag_ne
    have htag_beq0 : (speTag e + 2#64 + 0#64 == 0#64) = false := by
      rw [BitVec.add_zero]; exact htag_beq
    wp_steps
    refine focus_weaken_bi
      (speBodyAt_err_pack A sp e w416 w424 w432 w440 w448 restHeap hrel) ?_
    refine focus_weaken_bi (pointsTo32_entails_memRegion (sp + 400#64) 2#32) ?_
    rw [cmk_err_post_sp400 sp]; wp_done
  · intro sm3 hpc3 hrun3 hcl3 hL3
      ⟨hx19_3, hx20_3, hx26_3, hx27_3, hx28_3, hfp3, hsp3, hsp_al3, htr3, hvregs3⟩
      hm3
    have herr_tail : ∀ st4 : State,
        st4.pc = (blkPl_434).base + 1200#64 → st4.status = .Running →
        st4.sp = sp → st4.spAligned = true →
        st4.readReg64 .fp = sp + 1408#64 → st4.trace = s0.trace →
        calleeSavedVRegs st4 = calleeSavedVRegs s0 →
        LibsignalCodeRoLoaded lsmpl st4.mem →
        ((blkPC_434).rebase (blkPl_434).base H).CodeLoaded st4.mem →
        st4.readReg64 .x19 = x.ret →
        st4.readReg64 .x20 = sp + 320#64 →
        st4.readReg64 .x26 = speTag e →
        (st4.mem ⊨
          (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
           trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
           memRegion x.ret 48 ∗
           memRegion sp 56 ∗
           memRegion (sp + 320#64) 40 ∗
           speBodyAt A (utf8 "decrypt") (sp + 360#64) e ∗
           memRegion (sp + 400#64) 1008 ∗
           protocolAddressAt A x.rem x.remA ∗
           protocolAddressAt A x.loc x.locA ∗
           signalMessageAt A x.msgG x.msgA x.msg ∗
           tapeAfter ctl x.cur x.rest draws ∗
           logOff tryDecryptPlacedImg ∗
           stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗
           A.pool) ∗ R) →
        ∃ s', Steps ((blkPC_434).rebase (blkPl_434).base H) st4 s' ∧
          ((e ≠ .panic ∧ ∃ trG'',
              ErrTailStatePlaced (blkPl_434).base A ctl x trG'' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
             (s'.mem ⊨ anyHeap ∗ R))) := by
      intro st4 hpc4 hrun4 hsp4 hsp_al4 hfp4 htr4 hvregs4 hcl4 hL4 hx19_4 hx20_4 hx26_4 hm4
      refine steps_of_sepWP_placed hm4 hL4 hcl4
        (mid := (blkPl_434).base + 780#64)
        (RegMid := fun sf =>
          sf.readReg64 .x19 = x.ret ∧
          sf.readReg64 .x20 = sp + 320#64 ∧
          sf.readReg64 .x26 = speTag e ∧
          sf.readReg64 .fp = sp + 1408#64 ∧
          sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s0.trace ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0)
        (P_mid :=
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
          memRegion x.ret 48 ∗
          memRegion sp 56 ∗
          memRegion (sp + 320#64) 40 ∗
          speBodyAt A (utf8 "decrypt") (sp + 360#64) e ∗
          memRegion (sp + 400#64) 1008 ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗
          tapeAfter ctl x.cur x.rest draws ∗
          logOff tryDecryptPlacedImg ∗
          stackAt sp tryDecryptSubStack ∗
          tryDecryptSavedRegs s0.sp s0 ∗
          A.pool) ?_ ?_
      · wp_steps
        wp_done
      · intro sf hpcf hrunf hclf _ ⟨hx19_f, hx20_f, hx26_f, hfp_f, hsp_f, hsp_alf, htr_f, hvregs_f⟩ hmf
        subst hsp_def
        refine ⟨sf, .refl _, Or.inl ⟨hne_panic, trG', ?_⟩⟩
        have hpc_err : sf.pc = errTailPC_at (blkPl_434).base := by
          rw [hpcf]
        have hfp_f' : sf.readReg64 .x29 = s0.sp - 96#64 := by
          change sf.readReg64 .fp = s0.sp - 96#64
          rw [hfp_f]; exact (sp_fp_eq rfl).symm
        refine ⟨hpc_err, ⟨hrunf, hsp_f, hsp0_al, hsp_alf, hfp_f', htr_f, hclf, hvregs_f⟩,
          hx19_f, hx20_f, hx26_f, ?_⟩
        dsimp only [tryDecryptCommonHeap]
        simp only [sepConj_assoc] at hmf ⊢
        arm64_sep_close
    by_cases hcap : dispCap = 0
    · simp only [hcap, ↓reduceIte, emp_sepConj] at hm3
      subst hcap
      refine steps_of_sepWP_placed hm3 hL3 hcl3
        (mid := (blkPl_434).base + 1200#64)
        (RegMid := fun st4 =>
          st4.readReg64 .x19 = x.ret ∧
          st4.readReg64 .x20 = sp + 320#64 ∧
          st4.readReg64 .x26 = speTag e ∧
          st4.readReg64 .fp = sp + 1408#64 ∧
          st4.sp = sp ∧ st4.spAligned = true ∧ st4.trace = s0.trace ∧
          calleeSavedVRegs st4 = calleeSavedVRegs s0)
        (P_mid :=
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
          memRegion x.ret 48 ∗
          memRegion sp 56 ∗
          memRegion (sp + 320#64) 40 ∗
          speBodyAt A (utf8 "decrypt") (sp + 360#64) e ∗
          memRegion (sp + 400#64) 1008 ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗
          tapeAfter ctl x.cur x.rest draws ∗
          logOff tryDecryptPlacedImg ∗
          stackAt sp tryDecryptSubStack ∗
          tryDecryptSavedRegs s0.sp s0 ∗
          A.pool) ?_ ?_
      · wp_steps
        wp_done
      · intro st4 hpc4 hrun4 hcl4 hL4 ⟨hx19_4, hx20_4, hx26_4, hfp4, hsp4, hsp_al4, htr4, hvregs4⟩ hm4
        exact herr_tail st4 hpc4 hrun4 hsp4 hsp_al4 hfp4 htr4 hvregs4 hcl4 hL4 hx19_4 hx20_4 hx26_4 hm4
    · simp only [hcap, ↓reduceIte] at hm3
      have hcap_beq : (dispCap == 0#64) = false := beq_false_of_ne hcap
      refine steps_of_sepWP_placed hm3 hL3 hcl3
        (mid := lsρ lsRustDeallocSym)
        (RegMid := fun sm4 =>
          sm4.readReg64 .x0 = dispPtr ∧
          sm4.readReg64 .x1 = dispCap ∧
          sm4.readReg64 .x2 = 1#64 ∧
          sm4.readReg64 .x19 = x.ret ∧
          sm4.readReg64 .x20 = sp + 320#64 ∧
          sm4.readReg64 .x26 = speTag e ∧
          sm4.readReg64 .fp = sp + 1408#64 ∧
          sm4.readReg64 .lr = (blkPl_434).base + 1200#64 ∧
          sm4.sp = sp ∧ sm4.spAligned = true ∧ sm4.trace = s0.trace ∧
          calleeSavedVRegs sm4 = calleeSavedVRegs s0)
        (P_mid :=
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
          A.live dispPtr dispCap.toNat 1 ∗
          memRegion dispPtr dispCap.toNat ∗
          memRegion x.ret 48 ∗
          memRegion sp 56 ∗
          memRegion (sp + 320#64) 40 ∗
          speBodyAt A (utf8 "decrypt") (sp + 360#64) e ∗
          memRegion (sp + 400#64) 1008 ∗
          protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗
          tapeAfter ctl x.cur x.rest draws ∗
          logOff tryDecryptPlacedImg ∗
          stackAt sp tryDecryptSubStack ∗
          tryDecryptSavedRegs s0.sp s0 ∗
          A.pool) ?_ ?_
      · wp_conv_pre => simp only [sepConj_assoc]
        wp_steps
        refine focus_weaken_bi (buf_to_mr dispPtr dispBs dispCap.toNat hdisp1 hdisp2) ?_
        wp_done
      · intro sm4 hpc4 hrun4 hcl4 hL4
          ⟨hx0_4, hx1_4, hx2_4, hx19_4, hx20_4, hx26_4, hfp4, hlr4, hsp4, hsp_al4, htr4, hvregs4⟩
          hm4
        have hstack_dealloc := stackAt_sub sp tryDecryptSubStack allocHookStack (by decide) (by decide)
        have hpre_dealloc : sm4.mem ⊨
            (rustDeallocSpec A).pre (dispPtr, dispCap.toNat, 1) sm4 ∗
            ((sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
              trAt A (sp + 56#64) trG' { tr with ratchet := r2 } ∗
              memRegion x.ret 48 ∗
              memRegion sp 56 ∗
              memRegion (sp + 320#64) 40 ∗
              speBodyAt A (utf8 "decrypt") (sp + 360#64) e ∗
              memRegion (sp + 400#64) 1008 ∗
              protocolAddressAt A x.rem x.remA ∗
              protocolAddressAt A x.loc x.locA ∗
              signalMessageAt A x.msgG x.msgA x.msg ∗
              tapeAfter ctl x.cur x.rest draws ∗
              logOff tryDecryptPlacedImg ∗
              memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack)
                (tryDecryptSubStack - allocHookStack) ∗
              tryDecryptSavedRegs s0.sp s0) ∗ R) := by
          dsimp only [rustDeallocSpec]
          rw [hsp4, sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hx0_4, by rw [hx1_4], by rw [hx2_4]; rfl⟩, ?_⟩
          rw [hstack_dealloc] at hm4
          simp only [sepConj_assoc] at hm4 ⊢
          arm64_sep_close
        refine steps_call_out_placed (dispPtr, dispCap.toNat, 1) hdealloc
          hpc4 hrun4 hsp_al4 hlr4 hcl4 hL4 hpre_dealloc ?_ ?_
        · intro sf _ hpost
          dsimp only [rustDeallocSpec] at hpost
          rw [sepConj_assoc] at hpost
          exact (not_satisfies_false_sepConj hpost).elim
        · intro st5 hpc5 hrun5 hsp5 hsp_al5 hcs5 hcl5 hL5 hpost5
          dsimp only [rustDeallocSpec] at hpost5
          rw [hsp4, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost5
          rcases hpost5 with ⟨htr5, hpost5⟩
          refine herr_tail st5 hpc5 hrun5 (by reg_chain) hsp_al5 (by reg_chain) (by reg_chain) (by reg_chain)
            hcl5 hL5 (by reg_chain) (by reg_chain) (by reg_chain) ?_
          rw [hstack_dealloc]
          simp only [sepConj_assoc] at hpost5 ⊢
          arm64_sep_close

end KeyDeriveCallees

end CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive
