/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.Accept -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKit -- proof-setup: allow-public-import
import ProofLib.ProgramReflection.SortedFresh
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# Owned-Error Rejecting Contract for `Pqxdh::accept` (`0x23920`)

Strengthens the rejecting branch (`Model.acceptKeys P inp = none`) of `Pqxdh::accept` so the
104-byte `Result<HandshakeKeys, SignalProtocolError>` output slot exposes `speWordsAt` together
with `pqxdhAcceptErrPayloadAt` (retaining the 28-byte heap `String` buffer on tag-24
`InvalidMessage` or witnessing tag-10 `InvalidKeyAgreement`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace CryptoVerification.E2E.Pqxdh.ResponderCore

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.Initiator
open Model

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff
attribute [-arm64_norm] List.append_assoc

/-- Owned heap payload of the `SignalProtocolError` returned by `pqxdhAccept` when
`Model.acceptKeys P inp = none`:
- `isStr = true`: tag 24 (`InvalidMessage`, `0x8000000000000018#64`) with heap `String` buffer at
  `(cap = w2, ptr = w3, len = w4)`,
- `isStr = false`: tag 10 (`InvalidKeyAgreement`, `0x800000000000000a#64`), plain payload. -/
@[expose] def pqxdhAcceptErrPayloadAt (A : RustAlloc) (errTag w2 w3 w4 : BitVec 64) : SepProp :=
  ∃∗ isStr : Bool,
    if isStr then
      ⌜errTag = 0x8000000000000018#64⌝ ∗
      ∃∗ bs : List (BitVec 8),
        ⌜BitVec.ofNat 64 bs.length = w4 ∧ bs.length ≤ w2.toNat ∧ w2.toNat < 2 ^ 63 ∧ w3 ≠ 0#64⌝ ∗
        (if w2 = 0#64 then emp
         else A.live w3 w2.toNat 1 ∗ (w3 ↦ₛ bs) ∗
           memRegion (w3 + BitVec.ofNat 64 bs.length) (w2.toNat - bs.length))
    else ⌜errTag = 0x800000000000000a#64⌝

/-- Owned-payload refinement of `pqxdhAcceptErrStrong2At` for the 104-byte
`Result<HandshakeKeys, SignalProtocolError>` sret slot `outPtr` of `Pqxdh::accept`. -/
@[expose] def pqxdhAcceptErrOwnedAt (A : RustAlloc) (outPtr : BitVec 64) : SepProp :=
  (outPtr ↦₃₂ 1#32) ∗
  memRegion (outPtr + 4#64) 4 ∗
  ∃∗ errTag : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
  ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
    ⌜errTag ≠ pollReadyOkWord ∧ errTag ≠ 0xfffffffffffffffd#64⌝ ∗
    speWordsAt (outPtr + 8#64) errTag w2 w3 w4 w5 w6 ∗
    pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
    memRegion (outPtr + 56#64) 48

private theorem outPtr_tail64_to_spe_tail (outPtr : BitVec 64) (b40 : BitVec 8) :
    ((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63 ⊢
      ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
        ((outPtr + 40#64) ↦₆₄ w5) ∗ ((outPtr + 48#64) ↦₆₄ w6) ∗ memRegion (outPtr + 56#64) 48 := by
  have hb40 : ((outPtr + 40#64) ↦₈ b40) ⊢ memRegion (outPtr + 40#64) 1 := by
    rw [memRegion_one]
    exact Entails.sepExists_right b40 (Entails.refl _)
  refine Entails.trans (sepConj_mono_left hb40) ?_
  have hm64 :
      memRegion (outPtr + 40#64) 1 ∗ memRegion (outPtr + 41#64) 63 =
        (∃∗ w5 : BitVec 64, (outPtr + 40#64) ↦₆₄ w5) ∗
        (∃∗ w6 : BitVec 64, (outPtr + 48#64) ↦₆₄ w6) ∗
        memRegion (outPtr + 56#64) 48 := by
    rw [← ProofLib.memRegion_split' (b := outPtr + 40#64) (n := 1) (k := 63)
          (b' := outPtr + 41#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := outPtr + 40#64) (n := 8) (k := 56)
          (b' := outPtr + 48#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := outPtr + 48#64) (n := 8) (k := 48)
          (b' := outPtr + 56#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight (outPtr + 40#64),
        ProofLib.memRegion_eight (outPtr + 48#64)]
  rw [hm64]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.sepExists_elim fun w6 => Entails.sepExists_elim fun w5 =>
    Entails.sepExists_right w5 (Entails.sepExists_right w6 (Entails.refl _))

private theorem outPtr_err104_owned_merge (A : RustAlloc) (outPtr errTag w2 w3 w4 : BitVec 64)
    (b40 : BitVec 8) (hw1 : errTag ≠ pollReadyOkWord ∧ errTag ≠ 0xfffffffffffffffd#64) :
    pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
    (outPtr ↦₃₂ 1#32) ∗
    memRegion (outPtr + 4#64) 4 ∗
    ((outPtr + 8#64) ↦₆₄ errTag) ∗
    ((outPtr + 16#64) ↦₆₄ w2) ∗
    ((outPtr + 24#64) ↦₆₄ w3) ∗
    ((outPtr + 32#64) ↦₆₄ w4) ∗
    ((outPtr + 40#64) ↦₈ b40) ∗
    memRegion (outPtr + 41#64) 63 ⊢
    pqxdhAcceptErrOwnedAt A outPtr := by
  have hrearr :
      pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
      ((outPtr ↦₃₂ 1#32) ∗ (memRegion (outPtr + 4#64) 4 ∗ (((outPtr + 8#64) ↦₆₄ errTag) ∗
        (((outPtr + 16#64) ↦₆₄ w2) ∗ (((outPtr + 24#64) ↦₆₄ w3) ∗ (((outPtr + 32#64) ↦₆₄ w4) ∗
          (((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63))))))) =
      (outPtr ↦₃₂ 1#32) ∗ (memRegion (outPtr + 4#64) 4 ∗
        ((((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63) ∗
          (((outPtr + 8#64) ↦₆₄ errTag) ∗ ((outPtr + 16#64) ↦₆₄ w2) ∗
            ((outPtr + 24#64) ↦₆₄ w3) ∗ ((outPtr + 32#64) ↦₆₄ w4) ∗
            pqxdhAcceptErrPayloadAt A errTag w2 w3 w4))) := by ac_rfl
  rw [hrearr]
  unfold pqxdhAcceptErrOwnedAt
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine Entails.trans (sepConj_mono_left (outPtr_tail64_to_spe_tail outPtr b40)) ?_
  simp only [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun w5 => Entails.sepExists_elim fun w6 => ?_
  refine Entails.sepExists_right errTag (Entails.sepExists_right w2 (Entails.sepExists_right w3
    (Entails.sepExists_right w4 (Entails.sepExists_right w5 (Entails.sepExists_right w6 ?_)))))
  rw [pure_sepConj_of_true hw1]
  simp only [speWordsAt, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

private theorem pqxdhAcceptErrPayloadAt_tag10_intro (A : RustAlloc) (w2 w3 w4 : BitVec 64) :
    emp ⊢ pqxdhAcceptErrPayloadAt A 0x800000000000000a#64 w2 w3 w4 := by
  unfold pqxdhAcceptErrPayloadAt
  refine Entails.sepExists_right false ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [← sepConj_emp ⌜True⌝, pure_sepConj_of_true trivial emp]
  exact Entails.refl _

private theorem outPtr_err104_owned_tag10_merge (A : RustAlloc) (outPtr w2 w3 w4 : BitVec 64)
    (b40 : BitVec 8) :
    (outPtr ↦₃₂ 1#32) ∗
    memRegion (outPtr + 4#64) 4 ∗
    ((outPtr + 8#64) ↦₆₄ 0x800000000000000a#64) ∗
    ((outPtr + 16#64) ↦₆₄ w2) ∗
    ((outPtr + 24#64) ↦₆₄ w3) ∗
    ((outPtr + 32#64) ↦₆₄ w4) ∗
    ((outPtr + 40#64) ↦₈ b40) ∗
    memRegion (outPtr + 41#64) 63 ⊢
    pqxdhAcceptErrOwnedAt A outPtr := by
  rw [← emp_sepConj ((outPtr ↦₃₂ 1#32) ∗ _)]
  exact Entails.trans
    (sepConj_mono_left (pqxdhAcceptErrPayloadAt_tag10_intro A w2 w3 w4))
    (outPtr_err104_owned_merge A outPtr 0x800000000000000a#64 w2 w3 w4 b40 (by decide))

private theorem err28_payload_intro (A : RustAlloc) (ptr u2 u3 : BitVec 64) (hptr : ptr ≠ 0#64) :
    memRegion ptr 12 ∗ ((ptr + 12#64) ↦₆₄ u2) ∗ ((ptr + 20#64) ↦₆₄ u3) ∗ A.live ptr 28 1 ⊢
      pqxdhAcceptErrPayloadAt A 0x8000000000000018#64 28#64 ptr 28#64 := by
  have hm12 : memRegion ptr 12 =
      (∃∗ q0 : BitVec 64, ptr ↦₆₄ q0) ∗ (∃∗ q1 : BitVec 32, (ptr + 8#64) ↦₃₂ q1) := by
    rw [ProofLib.memRegion_split' (b := ptr) (n := 8) (k := 4)
          (b' := ptr + 8#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight ptr, memRegion_four (ptr + 8#64)]
  rw [hm12, sepConj_assoc, sepExists_sepConj_left]
  refine Entails.sepExists_elim fun q0 => ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun q1 => ?_
  unfold pqxdhAcceptErrPayloadAt
  refine Entails.sepExists_right true ?_
  simp only [↓reduceIte]
  rw [pure_sepConj_of_true trivial]
  let bs : List (BitVec 8) := unpack64 q0 ++ (unpack32 q1 ++ (unpack64 u2 ++ unpack64 u3))
  refine Entails.sepExists_right bs ?_
  have hbs_len : bs.length = 28 := by
    simp [bs, unpack64_length, unpack32_length]
  have hpure :
      BitVec.ofNat 64 bs.length = 28#64 ∧
      bs.length ≤ (28#64 : BitVec 64).toNat ∧
      (28#64 : BitVec 64).toNat < 2 ^ 63 ∧
      ptr ≠ 0#64 := by
    rw [hbs_len]
    exact ⟨rfl, by decide, by decide, hptr⟩
  rw [pure_sepConj_of_true hpure]
  have h28_ne : (28#64 : BitVec 64) ≠ 0#64 := by decide
  simp only [h28_ne, ↓reduceIte, hbs_len]
  have h28_nat : (28#64 : BitVec 64).toNat = 28 := rfl
  rw [h28_nat, Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp]
  have hpts :
      (ptr ↦ₛ bs) =
        (ptr ↦₆₄ q0) ∗ ((ptr + 8#64) ↦₃₂ q1) ∗ ((ptr + 12#64) ↦₆₄ u2) ∗ ((ptr + 20#64) ↦₆₄ u3) := by
    dsimp only [bs]
    rw [pointsToBytes_append, unpack64_length,
        pointsToBytes_append, unpack32_length,
        pointsToBytes_append, unpack64_length,
        ← pointsTo64_eq_pointsToBytes,
        ← pointsTo32_eq_pointsToBytes,
        ← pointsTo64_eq_pointsToBytes,
        ← pointsTo64_eq_pointsToBytes]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  rw [hpts]
  exact Entails.of_eq (by ac_rfl)

/-! ## Rejecting `Pqxdh::accept` proof (`trTrapProgAt`) -/

end CryptoVerification.E2E.Pqxdh.ResponderCore
