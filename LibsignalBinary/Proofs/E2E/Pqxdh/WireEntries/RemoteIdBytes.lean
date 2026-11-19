/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.Specs
public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import Lean
import ProofLib.ProgramReflection.SortedFresh
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Glue
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<SessionRecord>::remote_identity_key_bytes` (`0x17c94`)

Proves `remoteIdentityKeyBytes_sp2_ok` and `remoteIdentityKeyBytes_ok` on `tripleRatchetProgAt` and
`tripleRatchetProg`.
-/

public section

namespace CryptoVerification.E2E.Pqxdh.WireEntries

open Arm64 ProofLib CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.E2E.Bin

set_option warningAsError false
set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
private theorem stackAt_remoteIdBytes (sp : BitVec 64) :
    stackAt sp (128 + publicKeySerializeStack) =
      stackAt (sp - 128#64) publicKeySerializeStack ∗
      memRegion (sp - 128#64) 8 ∗
      (∃∗ s8 : BitVec 64, (sp - 120#64) ↦₆₄ s8) ∗
      (∃∗ s16 : BitVec 16, (sp - 112#64) ↦₁₆ s16) ∗
      memRegion (sp - 110#64) 6 ∗
      memRegion (sp - 104#64) 34 ∗
      memRegion (sp - 70#64) 6 ∗
      (∃∗ c0 : BitVec 64, (sp - 64#64) ↦₆₄ c0) ∗
      (∃∗ c1 : BitVec 64, (sp - 56#64) ↦₆₄ c1) ∗
      (∃∗ c2 : BitVec 64, (sp - 48#64) ↦₆₄ c2) ∗
      (∃∗ s58 : BitVec 32, (sp - 40#64) ↦₃₂ s58) ∗
      (∃∗ s5c : BitVec 16, (sp - 36#64) ↦₁₆ s5c) ∗
      memRegion (sp - 34#64) 2 ∗
      (∃∗ c3 : BitVec 64, (sp - 32#64) ↦₆₄ c3) ∗
      (∃∗ c4 : BitVec 64, (sp - 24#64) ↦₆₄ c4) ∗
      (∃∗ c5 : BitVec 64, (sp - 16#64) ↦₆₄ c5) ∗
      (∃∗ c6 : BitVec 64, (sp - 8#64) ↦₆₄ c6) := by
  unfold stackAt publicKeySerializeStack allocHookStack
  rw [show (128 + (4096 + 32) : Nat) = 4128 + 128 from rfl,
      ProofLib.memRegion_split' (b := sp - 4256#64) (n := 4128) (k := 128)
        (b' := sp - 128#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 128#64) (n := 8) (k := 120)
        (b' := sp - 120#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 120#64) (n := 8) (k := 112)
        (b' := sp - 112#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 112#64) (n := 2) (k := 110)
        (b' := sp - 110#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 110#64) (n := 6) (k := 104)
        (b' := sp - 104#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 104#64) (n := 34) (k := 70)
        (b' := sp - 70#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 70#64) (n := 6) (k := 64)
        (b' := sp - 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 64#64) (n := 8) (k := 56)
        (b' := sp - 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 56#64) (n := 8) (k := 48)
        (b' := sp - 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 48#64) (n := 8) (k := 40)
        (b' := sp - 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 40#64) (n := 4) (k := 36)
        (b' := sp - 36#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 36#64) (n := 2) (k := 34)
        (b' := sp - 34#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 34#64) (n := 2) (k := 32)
        (b' := sp - 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 32#64) (n := 8) (k := 24)
        (b' := sp - 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 24#64) (n := 8) (k := 16)
        (b' := sp - 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 16#64) (n := 8) (k := 8)
        (b' := sp - 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp - 120#64),
      memRegion_two (sp - 112#64),
      ProofLib.memRegion_eight (sp - 64#64),
      ProofLib.memRegion_eight (sp - 56#64),
      ProofLib.memRegion_eight (sp - 48#64),
      memRegion_four (sp - 40#64),
      memRegion_two (sp - 36#64),
      ProofLib.memRegion_eight (sp - 32#64),
      ProofLib.memRegion_eight (sp - 24#64),
      ProofLib.memRegion_eight (sp - 16#64),
      ProofLib.memRegion_eight (sp - 8#64)]
  have hsub : sp - 4256#64 = sp - 128#64 - BitVec.ofNat 64 publicKeySerializeStack := by
    change sp - 4256#64 = sp - 128#64 - 4128#64
    bv_omega
  rw [hsub]

private theorem stackAt_publicKeySerialize_to_allocHook (sp : BitVec 64) :
    stackAt sp publicKeySerializeStack =
      memRegion (sp - 4128#64) 32 ∗ stackAt sp allocHookStack := by
  unfold stackAt publicKeySerializeStack allocHookStack
  exact ProofLib.memRegion_split' (b := sp - 4128#64) (n := 32) (k := 4096)
    (b' := sp - 4096#64) rfl (by bv_omega) (by decide)

private theorem stackAt_publicKeySerialize_to_remoteIdentityKey (sp : BitVec 64) :
    stackAt sp publicKeySerializeStack =
      memRegion (sp - 4128#64) 3984 ∗ stackAt sp remoteIdentityKeyStack := by
  unfold stackAt publicKeySerializeStack allocHookStack remoteIdentityKeyStack
  exact ProofLib.memRegion_split' (b := sp - 4128#64) (n := 3984) (k := 144)
    (b' := sp - 144#64) rfl (by bv_omega) (by decide)

/-- The 6 disjoint chunks (`4 + 2 + 8 + 8 + 8 + 2 = 32` bytes) used by `0x17d28..0x17d7c`
to shift `peerKey.publicKey.bytes` from `sp + 0x1a` down to `sp + 0x18`. -/
@[expose] def pkShiftChunks (a : BitVec 64) (v0 : BitVec 32) (v4 : BitVec 16)
    (v6 v14 v22 : BitVec 64) (v30 : BitVec 16) : SepProp :=
  (a ↦₃₂ v0) ∗ ((a + 4#64) ↦₁₆ v4) ∗ ((a + 6#64) ↦₆₄ v6) ∗
  ((a + 14#64) ↦₆₄ v14) ∗ ((a + 22#64) ↦₆₄ v22) ∗ ((a + 30#64) ↦₁₆ v30)

private theorem pkShiftChunks_sp_102 (sp : BitVec 64)
    (v0 : BitVec 32) (v4 : BitVec 16) (v6 v14 v22 : BitVec 64) (v30 : BitVec 16) :
    pkShiftChunks (sp - 102#64) v0 v4 v6 v14 v22 v30 =
      ((sp - 102#64) ↦₃₂ v0) ∗ ((sp - 98#64) ↦₁₆ v4) ∗ ((sp - 96#64) ↦₆₄ v6) ∗
      ((sp - 88#64) ↦₆₄ v14) ∗ ((sp - 80#64) ↦₆₄ v22) ∗ ((sp - 72#64) ↦₁₆ v30) := by
  dsimp only [pkShiftChunks]
  have h4  : sp - 102#64 + 4#64  = sp - 98#64 := by bv_omega
  have h6  : sp - 102#64 + 6#64  = sp - 96#64 := by bv_omega
  have h14 : sp - 102#64 + 14#64 = sp - 88#64 := by bv_omega
  have h22 : sp - 102#64 + 22#64 = sp - 80#64 := by bv_omega
  have h30 : sp - 102#64 + 30#64 = sp - 72#64 := by bv_omega
  rw [h4, h6, h14, h22, h30]

private theorem pkShiftChunks_sp_104 (sp : BitVec 64)
    (v0 : BitVec 32) (v4 : BitVec 16) (v6 v14 v22 : BitVec 64) (v30 : BitVec 16) :
    pkShiftChunks (sp - 104#64) v0 v4 v6 v14 v22 v30 =
      ((sp - 104#64) ↦₃₂ v0) ∗ ((sp - 100#64) ↦₁₆ v4) ∗ ((sp - 98#64) ↦₆₄ v6) ∗
      ((sp - 90#64) ↦₆₄ v14) ∗ ((sp - 82#64) ↦₆₄ v22) ∗ ((sp - 74#64) ↦₁₆ v30) := by
  dsimp only [pkShiftChunks]
  have h4  : sp - 104#64 + 4#64  = sp - 100#64 := by bv_omega
  have h6  : sp - 104#64 + 6#64  = sp - 98#64  := by bv_omega
  have h14 : sp - 104#64 + 14#64 = sp - 90#64  := by bv_omega
  have h22 : sp - 104#64 + 22#64 = sp - 82#64  := by bv_omega
  have h30 : sp - 104#64 + 30#64 = sp - 74#64  := by bv_omega
  rw [h4, h6, h14, h22, h30]

private theorem exists_pkShiftChunks_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ (v0 : BitVec 32) (v4 : BitVec 16) (v6 v14 v22 : BitVec 64) (v30 : BitVec 16),
      ∀ a : BitVec 64, (a ↦ₛ bs) = pkShiftChunks a v0 v4 v6 v14 v22 v30 := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5,
    _ | ⟨b6, _ | ⟨b7, _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13,
    _ | ⟨b14, _ | ⟨b15, _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21,
    _ | ⟨b22, _ | ⟨b23, _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29,
    _ | ⟨b30, _ | ⟨b31, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (simp only [List.length_cons, List.length_nil] at h; omega)
  refine ⟨b3 ++ b2 ++ b1 ++ b0, b5 ++ b4,
    b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7 ++ b6,
    b21 ++ b20 ++ b19 ++ b18 ++ b17 ++ b16 ++ b15 ++ b14,
    b29 ++ b28 ++ b27 ++ b26 ++ b25 ++ b24 ++ b23 ++ b22,
    b31 ++ b30, fun a => ?_⟩
  dsimp only [pkShiftChunks]
  rw [← pointsToBytes4_eq_pointsTo32, ← pointsToBytes2_eq_pointsTo16,
      ← pointsToBytes8_eq_pointsTo64, ← pointsToBytes8_eq_pointsTo64,
      ← pointsToBytes8_eq_pointsTo64, ← pointsToBytes2_eq_pointsTo16]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem memRegion_34_split_dest (sp : BitVec 64) :
    memRegion (sp - 104#64) 34 =
      (∃∗ d0 : BitVec 32, (sp - 104#64) ↦₃₂ d0) ∗
      (∃∗ d4 : BitVec 16, (sp - 100#64) ↦₁₆ d4) ∗
      (∃∗ d6 : BitVec 64, (sp - 98#64) ↦₆₄ d6) ∗
      (∃∗ d14 : BitVec 64, (sp - 90#64) ↦₆₄ d14) ∗
      (∃∗ d22 : BitVec 64, (sp - 82#64) ↦₆₄ d22) ∗
      (∃∗ d30 : BitVec 16, (sp - 74#64) ↦₁₆ d30) ∗
      (∃∗ d32 : BitVec 16, (sp - 72#64) ↦₁₆ d32) := by
  rw [ProofLib.memRegion_split' (b := sp - 104#64) (n := 4) (k := 30)
        (b' := sp - 100#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 100#64) (n := 2) (k := 28)
        (b' := sp - 98#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 98#64) (n := 8) (k := 20)
        (b' := sp - 90#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 90#64) (n := 8) (k := 12)
        (b' := sp - 82#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 82#64) (n := 8) (k := 4)
        (b' := sp - 74#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 74#64) (n := 2) (k := 2)
        (b' := sp - 72#64) rfl (by bv_omega) (by decide),
      memRegion_four (sp - 104#64), memRegion_two (sp - 100#64),
      ProofLib.memRegion_eight (sp - 98#64), ProofLib.memRegion_eight (sp - 90#64),
      ProofLib.memRegion_eight (sp - 82#64), memRegion_two (sp - 74#64),
      memRegion_two (sp - 72#64)]

private theorem shift_source_to_memRegion34 (sp : BitVec 64)
    (v0 : BitVec 32) (v4 : BitVec 16) (v6 v14 v22 : BitVec 64) (v30 : BitVec 16) :
    (((sp - 104#64) ↦₈ 0#8) ∗ ((sp - 103#64) ↦₈ 1#8) ∗
     ((sp - 102#64) ↦₃₂ v0) ∗ ((sp - 98#64) ↦₁₆ v4) ∗ ((sp - 96#64) ↦₆₄ v6) ∗
     ((sp - 88#64) ↦₆₄ v14) ∗ ((sp - 80#64) ↦₆₄ v22) ∗ ((sp - 72#64) ↦₁₆ v30)) ⊢
      memRegion (sp - 104#64) 34 := by
  rw [ProofLib.memRegion_split' (b := sp - 104#64) (n := 1) (k := 33)
        (b' := sp - 103#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 103#64) (n := 1) (k := 32)
        (b' := sp - 102#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 102#64) (n := 4) (k := 28)
        (b' := sp - 98#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 98#64) (n := 2) (k := 26)
        (b' := sp - 96#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 96#64) (n := 8) (k := 18)
        (b' := sp - 88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 88#64) (n := 8) (k := 10)
        (b' := sp - 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 80#64) (n := 8) (k := 2)
        (b' := sp - 72#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo8_entails_memRegion _ _)
    (sepConj_mono (pointsTo8_entails_memRegion _ _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
        (sepConj_mono (pointsTo16_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (pointsTo16_entails_memRegion _ _)))))))

private theorem shift_dest_to_memRegion34 (sp : BitVec 64)
    (v0 : BitVec 32) (v4 : BitVec 16) (v6 v14 v22 : BitVec 64) (v30 v32 : BitVec 16) :
    (((sp - 104#64) ↦₃₂ v0) ∗ ((sp - 100#64) ↦₁₆ v4) ∗ ((sp - 98#64) ↦₆₄ v6) ∗
     ((sp - 90#64) ↦₆₄ v14) ∗ ((sp - 82#64) ↦₆₄ v22) ∗ ((sp - 74#64) ↦₁₆ v30) ∗
     ((sp - 72#64) ↦₁₆ v32)) ⊢
      memRegion (sp - 104#64) 34 := by
  rw [ProofLib.memRegion_split' (b := sp - 104#64) (n := 4) (k := 30)
        (b' := sp - 100#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 100#64) (n := 2) (k := 28)
        (b' := sp - 98#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 98#64) (n := 8) (k := 20)
        (b' := sp - 90#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 90#64) (n := 8) (k := 12)
        (b' := sp - 82#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 82#64) (n := 8) (k := 4)
        (b' := sp - 74#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 74#64) (n := 2) (k := 2)
        (b' := sp - 72#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo16_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo16_entails_memRegion _ _)
              (pointsTo16_entails_memRegion _ _))))))

private theorem truncate16_zeroExtend32_idem (v : BitVec 16) :
    BitVec.truncate 16 (BitVec.zeroExtend 32 v) = v :=
  (BitVec.setWidth_setWidth_of_le v (by decide)).trans (BitVec.setWidth_eq v)

private theorem memRegion_out32_split (out : BitVec 64) :
    memRegion out 32 =
      (∃∗ o0 : BitVec 64, out ↦₆₄ o0) ∗
      (∃∗ o1 : BitVec 64, (out + 8#64) ↦₆₄ o1) ∗
      (∃∗ o2 : BitVec 64, (out + 16#64) ↦₆₄ o2) ∗
      (∃∗ o3 : BitVec 64, (out + 24#64) ↦₆₄ o3) := by
  rw [memRegion_split out 8 24 (by decide),
      memRegion_split (out + 8#64) 8 16 (by decide),
      memRegion_split (out + 8#64 + 8#64) 8 8 (by decide),
      ProofLib.memRegion_eight, ProofLib.memRegion_eight,
      ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

/-! ## `sessionRecordAt` Exposure -/

/-- Rest of `sessionRecordAt` not touched by `remote_identity_key_bytes`. -/
@[expose] def sessionRecordRestAt (A : RustAlloc) (recPtr : BitVec 64) (G : SessionGhost)
    (s : Session (List (BitVec 8))) : SepProp :=
  vecAt A 24 8 (fun (_ : Unit) _ => emp) recPtr 0#64 8#64 [] ∗
  ⌜PendingRel G.pending s.pendingPreKey ∧ KyberRel G.kyber s.pendingKyberPreKey ∧
    G.alice.bytes = s.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 s.remoteRegistrationId.toNat ∧
    (G.regIds.drop 4).take 4 = leBytes 4 s.localRegistrationId.toNat⌝ ∗
  ⌜PublicKey.deserialize G.localIk.bytes = .ok s.state.localIdentity.publicKey ∧
    (match s.state.remoteIdentity with
     | none => G.remoteIk.bytes = []
     | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
    G.chains.length = s.state.receiverChains.length ∧
    G.pending.isSome = s.state.pendingPreKey ∧ G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧ (s.state.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
  ((recPtr + 0x18#64 + 8#64) ↦₆₄ G.localIk.ptr) ∗
  ((recPtr + 0x18#64 + 16#64) ↦₆₄ BitVec.ofNat 64 G.localIk.bytes.length) ∗
  vecU8Buf A G.localIk.cap G.localIk.ptr G.localIk.bytes ∗
  vecU8At A (recPtr + 0x18#64 + asm64% ssRootKeyOff) G.root.cap G.root.ptr (HMAC.keyToBytes32
    s.state.rootKey) ∗
  vecAt A (asm% chainSize) (asm% chainAlign) (chainAt A) (recPtr + 0x18#64 + asm64%
    ssReceiverChainsOff)
    G.chainsCap G.chainsPtr (G.chains.zip s.state.receiverChains) ∗
  vecGhostAt A G.alice (recPtr + 0x18#64 + asm64% ssAliceBaseKeyOff) ∗
  vecU8At A (recPtr + 0x18#64 + asm64% ssPqRatchetStateOff) G.pq.cap G.pq.ptr s.state.pqRatchetState
    ∗
  optSenderChainAt A (recPtr + 0x18#64 + asm64% ssSenderChainOff) G.sender s.state.senderChain ∗
  optTailVecAt A (asm% pendingPreKeySize) (recPtr + 0x18#64 + asm64% ssPendingPreKeyOff) G.pending ∗
  optTailVecAt A (asm% pendingKyberPreKeySize) (recPtr + 0x18#64 + asm64% ssPendingKyberPreKeyOff)
    G.kyber ∗
  ((recPtr + 0x18#64 + asm64% ssSessionVersionOff) ↦₃₂ s.state.sessionVersion) ∗
  ((recPtr + 0x18#64 + asm64% ssPreviousCounterOff) ↦₃₂ s.state.previousCounter) ∗
  ((recPtr + 0x18#64 + asm64% ssRegistrationIdsOff) ↦ₛ G.regIds)

private theorem sessionRecordAt_expose_remoteId (A : RustAlloc) (recPtr : BitVec 64)
    (G : SessionGhost) (s : Session (List (BitVec 8))) :
    sessionRecordAt A recPtr ⟨0#64, 8#64, some G⟩ ⟨some s⟩ =
      ((recPtr + 0x18#64) ↦₆₄ G.localIk.cap) ∗
      vecGhostAt A G.remoteIk (recPtr + 0x18#64 + 0x18#64) ∗
      sessionRecordRestAt A recPtr G s := by
  unfold sessionRecordAt sessionStateReprAt sessionStateAt sessionRecordRestAt
  dsimp only
  have hloc : vecGhostAt A G.localIk (recPtr + 0x18#64) =
      (((recPtr + 0x18#64) ↦₆₄ G.localIk.cap) ∗
       ((recPtr + 0x18#64 + 8#64) ↦₆₄ G.localIk.ptr) ∗
       ((recPtr + 0x18#64 + 16#64) ↦₆₄ BitVec.ofNat 64 G.localIk.bytes.length)) ∗
      vecU8Buf A G.localIk.cap G.localIk.ptr G.localIk.bytes := by
    unfold vecGhostAt
    exact vecU8At_eq_header_sep_buf A (recPtr + 0x18#64) G.localIk.cap G.localIk.ptr G.localIk.bytes
  rw [hloc]
  ac_rfl

private theorem sessionRecordAt_localIk_and_remoteId {A : RustAlloc} {recPtr : BitVec 64}
    {G : SessionGhost} {s : Session (List (BitVec 8))} {m : Memory} {R : SepProp}
    (h : m ⊨ sessionRecordAt A recPtr ⟨0#64, 8#64, some G⟩ ⟨some s⟩ ∗ R) :
    G.localIk.cap.toNat < 2 ^ 63 ∧
    (match s.state.remoteIdentity with
     | none => G.remoteIk.bytes = []
     | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) := by
  have hrec := Satisfies.of_sep_left h
  unfold sessionRecordAt sessionStateReprAt at hrec
  dsimp only at hrec
  have hss := Satisfies.of_sep_right (Satisfies.of_sep_right hrec)
  unfold sessionStateAt at hss
  have hpure := Satisfies.of_sep_left hss
  rw [satisfies_pure] at hpure
  have hloc := Satisfies.of_sep_left (Satisfies.of_sep_right hss)
  unfold vecGhostAt vecU8At at hloc
  have hcap := Satisfies.of_sep_left (Satisfies.of_sep_right hloc)
  rw [satisfies_pure] at hcap
  exact ⟨hcap.2.1, hpure.2.1⟩

private theorem cond_eq_adds_false_of_ult {cap : BitVec 64}
    (h : cap.ult 0x8000000000000000#64 = true) :
    ConditionHolds .EQ (addsPState64 cap 1#64) = false := by
  rw [conditionHolds_eq_addsPState64, beq_eq_false_iff_ne]
  simp only [BitVec.ult, decide_eq_true_eq] at h
  bv_omega

private theorem cond_eq_adds_false_of_lt63 {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    ConditionHolds .EQ (addsPState64 cap 1#64) = false := by
  apply cond_eq_adds_false_of_ult
  rw [BitVec.ult_eq_decide, decide_eq_true_iff]
  exact h

private theorem vecU8_intro_33 (A : RustAlloc) (out ptr : BitVec 64) (bs : List (BitVec 8))
    (hlen : bs.length = 33) (hptr : ptr ≠ 0#64) :
    (((out + 8#64) ↦₆₄ 33#64) ∗
     ((out + 16#64) ↦₆₄ ptr) ∗
     ((out + 24#64) ↦₆₄ 33#64) ∗
     A.live ptr 33 1 ∗
     (ptr ↦ₛ bs)) ⊢
    vecU8 A (out + 8#64) bs := by
  refine Entails.trans ?_ (vecU8At_entails_vecU8 A (out + 8#64) 33#64 ptr bs)
  rw [vecU8At_eq_header_sep_buf]
  unfold vecHeader vecU8Buf
  have h1 : (out + 8#64) + 8#64 = out + 16#64 := by bv_omega
  have h2 : (out + 8#64) + 16#64 = out + 24#64 := by bv_omega
  have h3 : (33#64 : BitVec 64) ≠ 0 := by decide
  rw [h1, h2, hlen, ite_eq_right_iff.mpr fun h => absurd h h3]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.sub_self,
    memRegion_zero, sepConj_emp, BitVec.ofNat_eq_ofNat]
  rw [show (((out + 8#64) ↦₆₄ 33#64) ∗ ((out + 16#64) ↦₆₄ ptr) ∗ ((out + 24#64) ↦₆₄ 33#64)) ∗
        (⌜33 ≤ 33 ∧ 33 < 9223372036854775808 ∧ ptr ≠ 0#64⌝ ∗
          (A.live ptr 33 1 ∗ (ptr ↦ₛ bs))) =
      ⌜33 ≤ 33 ∧ 33 < 9223372036854775808 ∧ ptr ≠ 0#64⌝ ∗
        (((out + 8#64) ↦₆₄ 33#64) ∗ ((out + 16#64) ↦₆₄ ptr) ∗ ((out + 24#64) ↦₆₄ 33#64) ∗
         A.live ptr 33 1 ∗ (ptr ↦ₛ bs)) by ac_rfl]
  exact Entails.pure_right ⟨by decide, by decide, hptr⟩ (Entails.refl _)

private theorem allocFailedIn_trans {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  simpa only [allocFailedIn, htr] using h

private theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

/-! ## Main Subroutine Proof (`0x17c94`) -/

end CryptoVerification.E2E.Pqxdh.WireEntries
