/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3c -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.HooksE.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.ModelBridge -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.ModelProofs.AdvanceAndFrame
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBob
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.CanonPreservation
import LibsignalBinary.Proofs.E2E.Run.RecvPure
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Model
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.Open -- shake: keep
import LibsignalBinary.Proofs.E2E.Reach.BundleCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.OpenDeserId

/-!
# Stage P3 Hypothesis Discharges and `tryDecryptFromRecord` Model Bridge

Discharges key-encoding, scalar-clamping, address-distinctness (`UuidNamesDistinct`), and
unconditional no-panic (`receiverChains = []`) side conditions on `initializeRecipientSession`, and
proves equivalence between `pqxdhTryDecryptModel` and `SessionState.tryDecryptFromRecord` together
with `CanonSession` preservation.
-/

public section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

namespace P3P4

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
  CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts
open CryptoVerification.LibsignalTripleRatchet.Decrypt.Model
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.Run CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Record CryptoVerification.E2E.RecordX
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore

/-! ## 1. Key, Buffer, Clamping, and Address-Distinctness Discharges -/

theorem bytesToBv8_eq_ofU8 (bs : List UInt8) :
    bytesToBv8 bs = ofU8 bs :=
  ResponderCore.bytesToBv8_eq_ofU8 bs

@[simp]
theorem bytesToBv8_vecU8 (v : List.Vector (BitVec 8) 32) :
    bytesToBv8 (vecU8 v) = v.toList :=
  ResponderCore.bytesToBv8_vecU8 v

@[simp]
theorem length_bytesToBv8_vecU8 (v : List.Vector (BitVec 8) 32) :
    (bytesToBv8 (vecU8 v)).length = 32 := by
  rw [bytesToBv8_vecU8]
  exact v.toList_length

theorem bytesToBv8_encodeEC_vecU8 (v : List.Vector (BitVec 8) 32) :
    bytesToBv8 (Model.encodeEC (vecU8 v)) = (⟨v⟩ : PublicKey).serialize := by
  change bytesToBv8 ((5 : UInt8) :: vecU8 v) = 5#8 :: v.toList
  change 5#8 :: bytesToBv8 (vecU8 v) = 5#8 :: v.toList
  rw [bytesToBv8_vecU8]

@[simp]
theorem length_bytesToBv8_encodeEC_vecU8 (v : List.Vector (BitVec 8) 32) :
    (bytesToBv8 (Model.encodeEC (vecU8 v))).length = 33 := by
  rw [bytesToBv8_encodeEC_vecU8]
  simp [PublicKey.serialize]

theorem acceptKeys_rootKey_chainKey_props {P : Primitives} {inp : AcceptKeysInput} {dk : DRKey}
    (hWF : StructuralPrims P) (hacc : Model.acceptKeys P inp = some dk) : (bytesToBv8
    dk.rootKey).length = 32 ∧ (bytesToBv8 dk.chainKey).length = 32 ∧ keyToBytes32 (HKDF.bytesToKey32
    (ofU8 dk.rootKey)) = bytesToBv8 dk.rootKey ∧ keyToBytes32 (HKDF.bytesToKey32 (ofU8 dk.chainKey))
    = bytesToBv8 dk.chainKey := by
  obtain ⟨hrk_len, _, hck_len⟩ := acceptKeys_some_lengths hWF hacc
  have hrk_bv_len : (bytesToBv8 dk.rootKey).length = 32 := by
    simpa [bytesToBv8] using hrk_len
  have hck_bv_len : (bytesToBv8 dk.chainKey).length = 32 := by
    simpa [bytesToBv8] using hck_len
  have hrk_ofU8_len : (ofU8 dk.rootKey).length = 32 := by
    rwa [← bytesToBv8_eq_ofU8]
  have hck_ofU8_len : (ofU8 dk.chainKey).length = 32 := by
    rwa [← bytesToBv8_eq_ofU8]
  refine ⟨hrk_bv_len, hck_bv_len, ?_, ?_⟩
  · rw [bytesToBv8_eq_ofU8]
    exact Keys.keyToBytes32_bytesToKey32 (ofU8 dk.rootKey) hrk_ofU8_len
  · rw [bytesToBv8_eq_ofU8]
    exact Keys.keyToBytes32_bytesToKey32 (ofU8 dk.chainKey) hck_ofU8_len

private theorem stackAt_sub_split (sp : BitVec 64) (n m : Nat) (h1 : m ≤ n)
    (h2 : n ≤ 2 ^ 64) :
    stackAt sp n = memRegion (sp - BitVec.ofNat 64 n) (n - m) ∗ stackAt sp m := by
  unfold stackAt
  exact memRegion_split' (b := sp - BitVec.ofNat 64 n) (b' := sp - BitVec.ofNat 64 m)
    (N := n) (n := n - m) (k := m) (by omega)
    (by
      have h : BitVec.ofNat 64 n = BitVec.ofNat 64 (n - m) + BitVec.ofNat 64 m := by
        rw [← BitVec.ofNat_add, Nat.sub_add_cancel h1]
      rw [h]; bv_lin)
    (by omega)

/-! ## 2. Unconditional No-Panic on `initializeRecipientSession` -/

private theorem rootCreateChain_ok_index {C : Crypto} {rk newRk : RootKey} {their : PublicKey}
    {our : PrivateKey} {recvCk : ChainKey} (h : rootCreateChain C rk their our = .ok (newRk,
    recvCk)) : recvCk.index = 0#32 := by
  unfold rootCreateChain at h
  split at h
  · cases h
  · injection h with hp
    injection hp with _ hck
    rw [← hck]
    rfl

/-- On `r.receiverChains = []`, `ensureReceiverChain` either fails with `e ≠ .panic` or succeeds
with a fresh chain at `recvCk.index = 0#32` and `r1.receiverChains = [⟨their, some recvCk, []⟩]`. -/
theorem ensureReceiverChain_index_zero_or_err_ne_panic (C : Crypto) (their : PublicKey)
    (coins : BitVec 256) (r : RatchetState) (hrc : r.receiverChains = []) : (∃ e r1, Mut.exec
    (RatchetState.ensureReceiverChain C their coins) r = (.error e, r1) ∧ e ≠ .panic) ∨ (∃ recvCk
    r1, Mut.exec (RatchetState.ensureReceiverChain C their coins) r = (.ok recvCk, r1) ∧
    recvCk.index = 0#32 ∧ r1.maxForwardJumps = r.maxForwardJumps ∧ r1.receiverChains = [⟨their, some
    recvCk, []⟩]) := by
  have hfind : r.findReceiverChainKey their = .ok none := by
    unfold RatchetState.findReceiverChainKey RatchetState.findReceiverChainIndex
    rw [hrc]
    rfl
  rw [ensureReceiverChain_of_find_none hfind]
  cases hsc : r.senderChain with
  | none =>
    left
    refine ⟨_, _, dhRatchetStep_of_senderChain_none hsc, by decide⟩
  | some sc =>
    cases hcc1 : rootCreateChain C r.rootKey their sc.ratchetKey.privateKey with
    | error e1 =>
      left
      refine ⟨e1, _, dhRatchetStep_of_first_createChain_error hsc hcc1, ?_⟩
      rw [rootCreateChain_error_eq hcc1]; decide
    | ok p1 =>
      rcases p1 with ⟨newRk, recvCk⟩
      cases hcc2 : rootCreateChain C newRk their (KeyPair.generate C coins).privateKey with
      | error e2 =>
        left
        refine ⟨e2, _, dhRatchetStep_of_second_createChain_error hsc hcc1 hcc2, ?_⟩
        rw [rootCreateChain_error_eq hcc2]; decide
      | ok p2 =>
        rcases p2 with ⟨finalRk, sendCk⟩
        right
        refine ⟨recvCk, _, dhRatchetStep_of_both_createChain_ok hsc hcc1 hcc2,
          rootCreateChain_ok_index hcc1, rfl, ?_⟩
        dsimp only
        rw [hrc, List.nil_append]
        rfl

/-! ## 3. Model Equivalence (`pqxdhTryDecryptModel` = `tryDecryptFromRecord`) and `CanonSession` -/

/-- For `st0 = initializeRecipientSession ...`, `st0.version = 4#32`. -/
@[simp]
theorem initSession_version_eq (ourIdentity theirIdentity : IdentityKey) (sendingKeyPair : KeyPair)
    (rootKey chainKey pqrKey : BitVec 256) : (initializeRecipientSession spqrOffB ourIdentity
    theirIdentity sendingKeyPair
      rootKey chainKey pqrKey).version = 4#32 :=
  rfl

private theorem leBytes_four_eq_unpack32 (w : BitVec 32) :
    leBytes 4 w.toNat = unpack32 w := by
  unfold leBytes unpack32 BitVec.extractLsb'
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.map, Nat.shiftRight_eq_div_pow]
  rfl

end P3P4

end CryptoVerification.E2E.Pqxdh.ResponderClosure
