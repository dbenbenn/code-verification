/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Defs
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Statements
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecrypt
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchet
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailProof
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChain
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeys
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetProof
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ConsumeMsgKey
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepMain
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Model
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecv
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Root
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMac
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Extract
import LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeys
import ProofLib.SepLogic.Entry

/-!
# `try_decrypt_with_state::<HookRng>` over SPQR V1 (`TryDecryptV1RunStmt`)

Derives `TryDecryptV1RunStmt` from `SpqrRecvV1Stmt` via a widened message-key layout (`optKeyAtW`):
on `Ordering::Greater` with `msg.index = 0`, `spqr::recv` returns `Ok(Some(vec![]))` (`DEV-SPQR2`),
representing an absent message key by an empty `Vec<u8>`, while `generate_keys` treats an empty
salt slice identically to `None` (`DEV-LS25`).
-/

public section

namespace CryptoVerification.LibsignalSpqrV1.M4

set_option autoImplicit false

open Arm64 ProofLib CryptoGames CryptoGames.HKDF CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt

/-! ## Widened `spqr::recv` Contract -/

/-- Widened 24-byte `spqr::MessageKey` layout at `a` (`DEV-SPQR2`): `none` is either the niche
    (`noneCap`) or an empty `Vec<u8>` (`cap = 0`, dangling pointer); `some k` is a 32-byte `Vec<u8>`. -/
@[expose] def optKeyAtW (A : RustAlloc) (a : BitVec 64) : Salt → SepProp
  | none => ∃∗ niche : Bool, if niche then spqrSendKeyAt A a none else vecU8 A a []
  | some k => vecU8 A a k.toList

/-- `spqrRecvResultAt` with the widened key layout (`optKeyAtW`). -/
@[expose] def recvResultAtW (A : RustAlloc) (r : BitVec 64) :
    Except Bool (List (BitVec 8) × Salt) → SepProp
  | .ok (st', key) => vecU8 A r st' ∗ optKeyAtW A (r + 24#64) key
  | .error sd =>
    (r ↦₆₄ errTag) ∗ (∃∗ d : BitVec 8, ⌜(d = 0#8 ↔ sd = true)⌝ ∗ ((r + 8#64) ↦₈ d)) ∗
      memRegion (r + 9#64) 39

/-- Every message key returned by `spqrV1Recv` is either empty (`DEV-SPQR2`) or 32 bytes long
    (drawn from `KeyHistory` or a 64-byte `ChainEpochDirection::nextKeyInternal` HKDF split). -/
theorem spqrV1Recv_key_shape (F : ShaCompress) (K : MlKem) (st msg st' : List (BitVec 8))
    (k : List (BitVec 8)) (h : (spqrV1Recv F K).recv st msg = .ok (st', some k)) :
    k = [] ∨ k.length = 32 := by
  rw [spqrV1Recv_eq] at h
  dsimp only [toSpqrRecvModel] at h
  cases hrecv : recv (spqrDeps F K) (spqrHkdfWith F) st msg with
  | error e =>
    rw [hrecv] at h
    cases e <;> contradiction
  | ok r =>
    rw [hrecv] at h
    injection h with h
    rcases Prod.mk.inj h with ⟨_, hk⟩
    by_cases hgt0 : ∃ pre stPb,
        msgPreamble msg = Except.ok pre ∧
        decodeState (spqrDeps F K) st = Except.ok stPb ∧
        (stateVersion stPb).toU8 ≠ 0#8 ∧
        pre.version > (stateVersion stPb).toU8 ∧
        pre.index = 0#32
    · rcases hgt0 with ⟨pre, stPb, hpre, hdec, hcv0, hgt, hidx0⟩
      have hcv0' : ((stateVersion stPb).toU8 == 0#8) = false := beq_eq_false_iff_ne.mpr hcv0
      unfold recv at hrecv
      simp only [hpre, hdec, hcv0', hgt, hidx0, SpqrApiResult.ofError, SpqrApiResult.ofChainResult,
        Chain.recvKey, Bind.bind, Except.bind, beq_self_eq_true, Bool.and_self,
        Bool.false_eq_true, ↓reduceIte] at hrecv
      repeat' (first | contradiction | split at hrecv)
      all_goals
        injection hrecv with hrecv
        subst hrecv
        injection hk with hk
        exact Or.inl hk.symm
    · exact Or.inr
        (recv_some_key_length_32_unless_greater_index_zero (spqrDeps F K) F st msg hrecv hk hgt0)

private theorem h41_recvResultAtX_entails_recvResultAtW (F : ShaCompress) (K : MlKem)
    (A : RustAlloc) (ret : BitVec 64) (st msg : List (BitVec 8)) :
    recvResultExactKeyAt A ret ((spqrV1Recv F K).recv st msg) ⊢
      recvResultAtW A ret ((spqrV1 F K).recv st msg) := by
  have hshape := spqrV1Recv_key_shape F K st msg
  rw [spqrV1Recv_eq] at hshape ⊢
  rw [spqrV1_eq]
  dsimp only [toSpqrRecvModel, toSpqrModel] at hshape ⊢
  cases hrecv : recv (spqrDeps F K) (spqrHkdfWith F) st msg with
  | error e =>
    cases e <;> exact Entails.refl _
  | ok r =>
    dsimp only
    cases hkey : r.key with
    | none =>
      exact sepConj_mono_right (Entails.sepExists_right true (Entails.refl _))
    | some k =>
      rcases hshape r.state k (by simp only [hrecv, hkey]) with rfl | hlen
      · exact sepConj_mono_right (Entails.sepExists_right false (Entails.refl _))
      · have hne : (some k : MessageKey) ≠ some [] := by
          intro h
          injection h with hk
          subst hk
          contradiction
        rw [recvKeyToSalt?_of_ne hne]
        dsimp only [messageKeyToSalt?]
        rw [dite_eq_left hlen]
        exact Entails.refl _

/-- `generateKeysSpec` with the key argument in the widened layout (`optKeyAtW`). -/
@[expose] def generateKeysSpecW (F : ShaCompress) (A : RustAlloc) : Spec GenerateKeysGhost :=
  { generateKeysSpec F A with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.genA ∧ s.readReg64 .x1 = x.pqrKeyA ∧ s.readReg64 .x8 = x.ret ∧
        x.g.seed.length = 32⌝ ∗
        mkgAt A x.genA x.g ∗ optKeyAtW A x.pqrKeyA x.pqrKey ∗ memRegion x.ret 84 ∗
        A.pool ∗ stackAt s.sp generateKeysStack }

private theorem optKeyAtW_eq_optKeyRecvAt (A : RustAlloc) (a : BitVec 64) (k : Salt) :
    optKeyAtW A a k = spqrRecvKeyAt A a k := by
  cases k <;> rfl

private theorem h42b_pqr_len_lt {A : RustAlloc} {g : SignalMessageGhost} {a : BitVec 64}
    {m : SignalMessage} {Q : SepProp} {mem : Memory}
    (h : mem ⊨ KeyDerive.signalMessageRestAt A g a m ∗ Q) :
    m.pqRatchet.length < 2 ^ 40 := by
  unfold KeyDerive.signalMessageRestAt at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  exact h.1.2.2.2.1

private theorem h42b_spqrRecvStack_le {sp0 sp : BitVec 64}
    (hstack : rootStack ≤ sp0.toNat) (hsp : sp0 - 1504#64 = sp) :
    spqrRecvStack ≤ sp.toNat := by
  subst hsp
  have h1 : rootStack = 262144 := rfl
  have h2 : spqrRecvStack = 131072 := rfl
  rw [BitVec.toNat_sub_of_le]
  · simp only [BitVec.toNat_ofNat]
    omega
  · rw [BitVec.le_def]
    simp only [BitVec.toNat_ofNat]
    omega

private abbrev h42b_optKeyRestW := KeyDerive.optKeyRest

private theorem h42b_optKeyAtW_split (A : RustAlloc) (a : BitVec 64) (pqrKey : Salt) :
    optKeyAtW A a pqrKey ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        h42b_optKeyRestW A w0 w1 w2 pqrKey ∗
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) := by
  rw [optKeyAtW_eq_optKeyRecvAt]
  exact KeyDerive.optKeyAt_split A a pqrKey

private theorem h42b_optKeyAtW_fold (A : RustAlloc) (a w0 w1 w2 : BitVec 64) (pqrKey : Salt) :
    h42b_optKeyRestW A w0 w1 w2 pqrKey ∗
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢
      optKeyAtW A a pqrKey := by
  rw [optKeyAtW_eq_optKeyRecvAt]
  exact KeyDerive.optKeyAt_fold A a w0 w1 w2 pqrKey

private theorem h42b_pqr_len_lt_of_pre {P F R : SepProp} {A : RustAlloc}
    {g : SignalMessageGhost} {a : BitVec 64} {m : SignalMessage} {mem : Memory}
    (h : mem ⊨ P ∗ ((KeyDerive.signalMessageRestAt A g a m ∗ F) ∗ R)) :
    m.pqRatchet.length < 2 ^ 40 := by
  have h' : mem ⊨ KeyDerive.signalMessageRestAt A g a m ∗ (F ∗ R ∗ P) := by
    have heq : P ∗ ((KeyDerive.signalMessageRestAt A g a m ∗ F) ∗ R) =
        KeyDerive.signalMessageRestAt A g a m ∗ (F ∗ R ∗ P) := by ac_rfl
    exact heq ▸ h
  exact h42b_pqr_len_lt h'

private theorem h42b_attach_left {prog : Program} {s : State} {A B : State → Prop} {c : Prop}
    (hc : c) (h : ∃ s', Steps prog s s' ∧ (A s' ∨ B s')) :
    ∃ s', Steps prog s s' ∧ ((A s' ∧ c) ∨ B s') := by
  obtain ⟨s', hs, h | h⟩ := h
  · exact ⟨s', hs, Or.inl ⟨h, hc⟩⟩
  · exact ⟨s', hs, Or.inr h⟩

end CryptoVerification.LibsignalSpqrV1.M4
