/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs

/-!
# Stage P2 Substages P2.1 and P2.2

Composes basic-block lemmas with `StageP2PureCallees` and `SignedPreKeyStoreKitOkImgE` on
`tripleRatchetProgAtExt img.base ext` to prove `stageP2_sub1_kits` (`+0x0868 → +0x0f14`) and CPS
`stageP2_sub2_kits` (`+0x0f14 → +0x1460` or `+0x0f38` Arm 1).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  protocolAddressAt decryptPrekeySavedRegsAt

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

theorem p2_pkSerStack_le_pure : publicKeySerializeStack ≤ stageP2PureAndErrStack :=
  Nat.le_trans (by decide : publicKeySerializeStack ≤ stageP2aStack) p2_stageP2a_le_pure

theorem p2_prom1248_le_pure : 1248 ≤ stageP2PureAndErrStack :=
  Nat.le_trans (by decide : 1248 ≤ stageP2aStack) p2_stageP2a_le_pure

theorem p2_kp176_le_pure : 176 ≤ stageP2PureAndErrStack :=
  Nat.le_trans (by decide : 176 ≤ stageP2aStack) p2_stageP2a_le_pure

theorem p2_spkShim_le_spkGetCallStack {A : RustAlloc} {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A b) :
    spkKit.getShimStack ≤ spkGetCallStack spkKit :=
  Nat.le_max_left _ _

theorem p2_spkPoll_le_spkGetCallStack {A : RustAlloc} {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A b) :
    spkKit.getPollStack ≤ spkGetCallStack spkKit :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

theorem p2_pure_le_spkGetCallStack {A : RustAlloc} {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A b) :
    stageP2PureAndErrStack ≤ spkGetCallStack spkKit :=
  Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

theorem p2_signedPreKeyStructAt_unpack (A : RustAlloc) (out : BitVec 64)
    (m : SignedPreKeyRecordStructure) :
    signedPreKeyStructAt A out m ⊢
      ∃∗ pubCap : BitVec 64, ∃∗ pubPtr : BitVec 64,
      ∃∗ privCap : BitVec 64, ∃∗ privPtr : BitVec 64,
      ∃∗ sigCap : BitVec 64, ∃∗ sigPtr : BitVec 64,
      ∃∗ pad32 : BitVec 32,
        preKeyRecordOut64At out
          pubCap pubPtr (BitVec.ofNat 64 m.publicKey.length)
          privCap privPtr (BitVec.ofNat 64 m.privateKey.length)
          sigCap sigPtr ∗
        ((out + 0x40#64) ↦₆₄ BitVec.ofNat 64 m.signature.length) ∗
        ((out + 0x48#64) ↦₆₄ m.timestamp) ∗
        ((out + 0x50#64) ↦₆₄ (pad32 ++ m.id)) ∗
        vecU8Buf A pubCap pubPtr m.publicKey ∗
        vecU8Buf A privCap privPtr m.privateKey ∗
        vecU8Buf A sigCap sigPtr m.signature := by
  unfold signedPreKeyStructAt RustHeap.vecU8
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun sigCap => Entails.sepExists_elim fun sigPtr =>
    Entails.sepExists_elim fun privCap => Entails.sepExists_elim fun privPtr =>
    Entails.sepExists_elim fun pubCap => Entails.sepExists_elim fun pubPtr => ?_
  rw [ProofLib.memRegion_four (out + 0x54#64)]
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun pad32 => ?_
  refine Entails.sepExists_right pubCap (Entails.sepExists_right pubPtr
    (Entails.sepExists_right privCap (Entails.sepExists_right privPtr
    (Entails.sepExists_right sigCap (Entails.sepExists_right sigPtr
    (Entails.sepExists_right pad32 ?_))))))
  rw [LibsignalTripleRatchet.Wire.vecU8At_eq_header_buf,
      LibsignalTripleRatchet.Wire.vecU8At_eq_header_buf,
      LibsignalTripleRatchet.Wire.vecU8At_eq_header_buf]
  dsimp only [vecHeader, preKeyRecordOut64At]
  have hp80 : ((out + 0x50#64) ↦₃₂ m.id) ∗ ((out + 0x54#64) ↦₃₂ pad32) =
      ((out + 0x50#64) ↦₆₄ (pad32 ++ m.id)) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair (out + 0x50#64) m.id pad32
  rw [hp80]
  sep_norm
  exact Entails.of_eq (by ac_rfl)

theorem p2_preKeyRecordOut64_tail_to_memRegion88
    (out w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : BitVec 64) :
    preKeyRecordOut64At out w0 w1 w2 w3 w4 w5 w6 w7 ∗
      ((out + 0x40#64) ↦₆₄ w8) ∗ ((out + 0x48#64) ↦₆₄ w9) ∗ ((out + 0x50#64) ↦₆₄ w10) ⊢
      memRegion out 88 := by
  dsimp only [preKeyRecordOut64At]
  rw [ProofLib.memRegion_split out 8 80 (by decide),
      ProofLib.memRegion_split (out + 8#64) 8 72 (by decide),
      ProofLib.memRegion_split (out + 8#64 + 8#64) 8 64 (by decide),
      ProofLib.memRegion_split (out + 8#64 + 8#64 + 8#64) 8 56 (by decide),
      ProofLib.memRegion_split (out + 8#64 + 8#64 + 8#64 + 8#64) 8 48 (by decide),
      ProofLib.memRegion_split (out + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 40 (by decide),
      ProofLib.memRegion_split (out + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
      ProofLib.memRegion_split (out + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
      ProofLib.memRegion_split (out + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
      ProofLib.memRegion_split (out + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  sep_norm
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (sepConj_mono (pointsTo64_entails_memRegion _ _)
                  (sepConj_mono (pointsTo64_entails_memRegion _ _)
                    (sepConj_mono (pointsTo64_entails_memRegion _ _)
                      (pointsTo64_entails_memRegion _ _))))))))))

theorem p2_vecU8Buf_nonempty (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hlen : 0 < bs.length) :
    vecU8Buf A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ cap ≠ 0#64 ∧
        cap ≠ 0xfffffffffffffffe#64 ∧ cap ≠ 0xffffffffffffffff#64⌝ ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) := by
  unfold vecU8Buf
  refine Entails.pure_left fun ⟨hle, hlt, _⟩ => ?_
  have hcap_pos : 0 < cap.toNat := Nat.lt_of_lt_of_le hlen hle
  have hnz : cap ≠ 0#64 := fun hc => by subst hc; simp at hcap_pos
  have hcap0 : (cap = 0) = False := eq_false hnz
  have hne2 : cap ≠ 0xfffffffffffffffe#64 := fun hc => by subst hc; norm_num at hlt
  have hne1 : cap ≠ 0xffffffffffffffff#64 := fun hc => by subst hc; norm_num at hlt
  simp only [hcap0, ↓reduceIte]
  exact Entails.pure_right ⟨hle, hlt, hnz, hne2, hne1⟩ (Entails.refl _)

theorem p2_vecU8Buf_rejoin (ptr cap : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length ≤ cap.toNat) :
    (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ⊢
      memRegion ptr cap.toNat := by
  have hlt : cap.toNat < 2 ^ 64 := cap.isLt
  have hsplit : cap.toNat = bs.length + (cap.toNat - bs.length) := (Nat.add_sub_of_le hle).symm
  conv => rhs; rw [hsplit, ProofLib.memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega)]
  exact sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)

theorem p2_vecU8Buf_zero (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A 0#64 ptr bs ⊢ emp := by
  unfold vecU8Buf
  have h0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [h0, ↓reduceIte]
  exact Entails.pure_left fun _ => Entails.refl emp

theorem p2_vecU8Buf_dealloc_nonzero (A : RustAlloc) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) (hcap_ne : cap ≠ 0#64) :
    vecU8Buf A cap ptr bs ⊢ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  unfold vecU8Buf
  exact Entails.pure_left fun ⟨hle, _, _⟩ => p2_vecBuf_dealloc_nonzero A cap ptr bs hcap_ne hle

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
