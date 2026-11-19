/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.M4.Decrypt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Defs
public import LibsignalBinary.Proofs.TripleRatchet.TrapRng -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Defs
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Getters.Defs
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchet
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.IdentityKeys
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.LoadRatchetProof
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ConsumeMsgKey
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStepDefs
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecv
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.KeyDeriveBase
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMac
import LibsignalBinary.Proofs.Cli.TripleRatchet.RunAssembly.DecryptAssembly
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Model
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Root
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.Entry

/-!
# CLI SPQR V1 Ratchet Decryption Assembly

Composes the widened `spqr::recv` and `generate_keys` segments (`PqRecvDeriveSpecWT`) with the
remaining `try_decrypt_with_state` seams to prove `tryDecryptT_run_of_seamW` and
`tryDecryptV1_run_of_recvV1` on the CLI image.
-/

public section

namespace CryptoVerification.LibsignalSpqrV1.M4

set_option autoImplicit false

open Arm64 ProofLib CryptoGames CryptoGames.HKDF CryptoGames.LibsignalSession CryptoVerification.RustHeap

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Decrypt

/-! ## 1. Widened `PqRecv` + `DeriveKeys` Contract -/

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
