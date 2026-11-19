/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.Specs
import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.HashOne
import ProofLib.Hoare.Hooks
public import ProofLib.GenDecodes
public import ProofLib.VCGen

/-!
# SipHash-1-3 Framing and Call-Site Corollaries

Symbol-offset guards, framing from `addrBorrowAt` to full `protocolAddressAt`
(`hashOneAddr36_ok`), and call-site `subroutine_ok` corollaries for all callers of
`RandomState::hash_one::<&ProtocolAddress>`.
-/

public section

namespace CryptoVerification.E2E.InMem.SipHashBin

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.InMem.SipHashModel

/-! ## Symbol Offset Guards -/

private theorem protocolAddressAt_eq_addrBorrowAt (A : RustAlloc) (g : AddrGhost) (addr : BitVec 64)
    (hpos : 0 < g.name.bytes.length) :
    protocolAddressAt A g addr =
      ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
      addrBorrowAt addr g.name.ptr g.name.bytes g.device ∗
      (addr ↦₆₄ g.name.cap) ∗
      A.live g.name.ptr g.name.cap.toNat 1 ∗
      memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
        (g.name.cap.toNat - g.name.bytes.length) ∗
      memRegion (addr + 25#64) 7 := by
  have hvec :
      vecGhostAt A g.name addr =
        ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
        (addr ↦₆₄ g.name.cap) ∗ ((addr + 8#64) ↦₆₄ g.name.ptr) ∗
        ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
        (g.name.ptr ↦ₛ g.name.bytes) ∗
        A.live g.name.ptr g.name.cap.toNat 1 ∗
        memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
          (g.name.cap.toNat - g.name.bytes.length) := by
    unfold vecGhostAt vecU8At vecHeader
    have h1 :
        ((addr ↦₆₄ g.name.cap ∗ (addr + 8#64) ↦₆₄ g.name.ptr ∗
            (addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
          ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          if g.name.cap = 0 then emp
          else A.live g.name.ptr g.name.cap.toNat 1 ∗ g.name.ptr ↦ₛ g.name.bytes ∗
            memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
              (g.name.cap.toNat - g.name.bytes.length)) ⊢
        (⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          addr ↦₆₄ g.name.cap ∗ (addr + 8#64) ↦₆₄ g.name.ptr ∗
          (addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length ∗
          g.name.ptr ↦ₛ g.name.bytes ∗ A.live g.name.ptr g.name.cap.toNat 1 ∗
          memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
            (g.name.cap.toNat - g.name.bytes.length)) := by
      rw [sepConj_pure_left_comm]
      apply Entails.pure_left; rintro ⟨hlen, hcap_lt, hptr⟩
      have hne : g.name.cap ≠ 0 := by
        intro h0; rw [h0] at hlen; change g.name.bytes.length ≤ 0 at hlen; omega
      simp only [hne, ↓reduceIte]
      apply Entails.pure_right ⟨hlen, hcap_lt, hptr⟩
      have hcomm :
          (((addr ↦₆₄ g.name.cap) ∗ ((addr + 8#64) ↦₆₄ g.name.ptr) ∗
              ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length)) ∗
            (A.live g.name.ptr g.name.cap.toNat 1 ∗ (g.name.ptr ↦ₛ g.name.bytes) ∗
              memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
                (g.name.cap.toNat - g.name.bytes.length))) =
          ((addr ↦₆₄ g.name.cap) ∗ ((addr + 8#64) ↦₆₄ g.name.ptr) ∗
            ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
            (g.name.ptr ↦ₛ g.name.bytes) ∗ A.live g.name.ptr g.name.cap.toNat 1 ∗
            memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
              (g.name.cap.toNat - g.name.bytes.length)) := by ac_rfl
      rw [hcomm]; exact Entails.refl _
    have h2 :
        (⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          addr ↦₆₄ g.name.cap ∗ (addr + 8#64) ↦₆₄ g.name.ptr ∗
          (addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length ∗
          g.name.ptr ↦ₛ g.name.bytes ∗ A.live g.name.ptr g.name.cap.toNat 1 ∗
          memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
            (g.name.cap.toNat - g.name.bytes.length)) ⊢
        ((addr ↦₆₄ g.name.cap ∗ (addr + 8#64) ↦₆₄ g.name.ptr ∗
            (addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
          ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          if g.name.cap = 0 then emp
          else A.live g.name.ptr g.name.cap.toNat 1 ∗ g.name.ptr ↦ₛ g.name.bytes ∗
            memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
              (g.name.cap.toNat - g.name.bytes.length)) := by
      apply Entails.pure_left; rintro ⟨hlen, hcap_lt, hptr⟩
      have hne : g.name.cap ≠ 0 := by
        intro h0; rw [h0] at hlen; change g.name.bytes.length ≤ 0 at hlen; omega
      rw [sepConj_pure_left_comm]
      apply Entails.pure_right ⟨hlen, hcap_lt, hptr⟩
      simp only [hne, ↓reduceIte]
      have hcomm :
          ((addr ↦₆₄ g.name.cap) ∗ ((addr + 8#64) ↦₆₄ g.name.ptr) ∗
            ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
            (g.name.ptr ↦ₛ g.name.bytes) ∗ A.live g.name.ptr g.name.cap.toNat 1 ∗
            memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
              (g.name.cap.toNat - g.name.bytes.length)) =
          (((addr ↦₆₄ g.name.cap) ∗ ((addr + 8#64) ↦₆₄ g.name.ptr) ∗
              ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length)) ∗
            (A.live g.name.ptr g.name.cap.toNat 1 ∗ (g.name.ptr ↦ₛ g.name.bytes) ∗
              memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
                (g.name.cap.toNat - g.name.bytes.length))) := by ac_rfl
      rw [hcomm]; exact Entails.refl _
    exact sepProp_eq_of_entails h1 h2
  unfold protocolAddressAt addrBorrowAt
  rw [hvec]
  change (⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
      (addr ↦₆₄ g.name.cap) ∗ ((addr + 8#64) ↦₆₄ g.name.ptr) ∗
      ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
      (g.name.ptr ↦ₛ g.name.bytes) ∗
      A.live g.name.ptr g.name.cap.toNat 1 ∗
      memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
        (g.name.cap.toNat - g.name.bytes.length)) ∗
      ((addr + 24#64) ↦₈ g.device) ∗ memRegion (addr + 25#64) 7 = _
  ac_rfl

end CryptoVerification.E2E.InMem.SipHashBin
