/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepDefs
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Defs
public import LibsignalBinary.Proofs.TripleRatchet.TrapRng -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Defs
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Getters.Defs
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SignalSession.Coins.Defs
import ProofLib.SepLogic.WPp

/-!
# `try_decrypt_with_state` Segment S3 (`DhStep`) Definitions and Callee Bridges

Defines the S3 commit checkpoint (`DhCommitState` at `+0x8ac`) and `signal_session_coins_fill`
callee specialization lemmas for segment S3 of `try_decrypt_with_state`.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open CryptoVerification.LibsignalTripleRatchet.Decrypt

open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.tapeAfter_zero_eq (ctl cur : BitVec 64) (rest : List (BitVec 8)) :
    tapeAfter ctl cur rest 0 =
      (ctl ↦₆₄ cur) ∗ ((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗ (cur ↦ₛ rest) := by
  unfold tapeAfter
  simp only [BitVec.add_zero, Nat.sub_zero]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.hookRngFillAfter0_ok (ctl : BitVec 64) :
    HookOk (rngFillHook ctl) (rngFillAfter0Spec ctl) := by
  intro ⟨dst, len, cur, rest⟩ R s0 hrun hpre _
  simp only [rngFillAfter0Spec, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.tapeAfter_zero_eq, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hdst, hlen⟩, hmem⟩
  have hmem_ctl : s0.mem ⊨ (ctl ↦₆₄ cur) ∗
      (((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗ memRegion dst len ∗ (cur ↦ₛ rest) ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) hmem
    ac_rfl
  have hcur : s0.mem.read64 ctl = cur := (IsBlock.pointsTo64 ctl cur).read hmem_ctl
  have hmem_c8 : s0.mem ⊨ ((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗
      ((ctl ↦₆₄ cur) ∗ memRegion dst len ∗ (cur ↦ₛ rest) ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) hmem
    ac_rfl
  have hc8_raw : s0.mem.read64 (ctl + 8#64) = BitVec.ofNat 64 rest.length :=
    (IsBlock.pointsTo64 (ctl + 8#64) (BitVec.ofNat 64 rest.length)).read hmem_c8
  have hrest_lt64 : rest.length < 2 ^ 64 := by
    by_cases hpos : 0 < rest.length
    · have hmem_disj : s0.mem ⊨ (ctl ↦₆₄ cur) ∗ ((cur ↦ₛ rest) ∗
          (((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗ memRegion dst len ∗ R)) := by
        refine Satisfies.mono (Entails.of_eq ?_) hmem
        ac_rfl
      have hdisj := IsBlock.disjoint (IsBlock.pointsTo64 ctl cur) (IsBlock.pointsToBytes cur rest)
        (by decide) hpos hmem_disj
      have h2 := hdisj.2
      have hlt : (ctl - cur).toNat < 2 ^ 64 := (ctl - cur).isLt
      omega
    · omega
  have hrem : (s0.mem.read64 (ctl + 8#64)).toNat = rest.length := by
    rw [hc8_raw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrest_lt64]
  set k := min len rest.length
  have hk_le_rest : k ≤ rest.length := Nat.min_le_right len rest.length
  have hk_le_len : k ≤ len := Nat.min_le_left len rest.length
  have hrest_split : rest = rest.take k ++ rest.drop k := (List.take_append_drop k rest).symm
  have htake_len : (rest.take k).length = k := List.length_take_of_le hk_le_rest
  have hmem_cur : s0.mem ⊨ (cur ↦ₛ rest.take k) ∗
      (((cur + BitVec.ofNat 64 k) ↦ₛ rest.drop k) ∗
        (ctl ↦₆₄ cur) ∗ ((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗
        memRegion dst len ∗ R) := by
    have h1 : (cur ↦ₛ rest) =
        (cur ↦ₛ rest.take k) ∗ ((cur + BitVec.ofNat 64 k) ↦ₛ rest.drop k) := by
      conv_lhs => rw [hrest_split]
      rw [pointsToBytes_append, htake_len]
    refine Satisfies.mono (Entails.of_eq ?_) hmem
    rw [h1]
    ac_rfl
  obtain ⟨_, hread_cur_raw⟩ := (IsBlock.pointsToBytes cur (rest.take k)).read hmem_cur
  have hread_cur : s0.mem.readBytes cur k = rest.take k := by
    rwa [htake_len] at hread_cur_raw
  have hmem_dst : s0.mem ⊨ memRegion dst len ∗
      ((ctl ↦₆₄ cur) ∗ ((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗ (cur ↦ₛ rest) ∗ R) :=
    hmem
  have hlen_le64 : len ≤ 2 ^ 64 := by
    by_cases hlen0 : 0 < len
    · have hmem_disj2 : s0.mem ⊨ (ctl ↦₆₄ cur) ∗ (memRegion dst len ∗
          (((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗ (cur ↦ₛ rest) ∗ R)) := by
        refine Satisfies.mono (Entails.of_eq ?_) hmem
        ac_rfl
      have hdisj2 := IsBlock.disjoint (IsBlock.pointsTo64 ctl cur) (IsBlock.memRegion dst len)
        (by decide) hlen0 hmem_disj2
      have h2 := hdisj2.2
      have hlt : (ctl - dst).toNat < 2 ^ 64 := (ctl - dst).isLt
      omega
    · omega
  set bytes := rest.take k ++ List.replicate (len - k) 0#8
  have hbytes_len : bytes.length = len := by
    simp only [bytes, List.length_append, htake_len, List.length_replicate]
    omega
  set m1 := s0.mem.write64 ctl (cur + BitVec.ofNat 64 k)
  have hcur_cw : s0.mem.canWrite ctl 8 = true :=
    (IsBlock.pointsTo64 ctl cur).canWrite (by decide) hmem_ctl
  have hkf1 : Memory.KeepsFrozen s0.mem m1 :=
    Memory.keepsFrozen_write64 hcur_cw (cur + BitVec.ofNat 64 k)
  have hm1_raw : m1 ⊨ (ctl ↦₆₄ (cur + BitVec.ofNat 64 k)) ∗
      (((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗ memRegion dst len ∗ (cur ↦ₛ rest) ∗ R) :=
    (IsBlock.pointsTo64 ctl cur).write64 hmem_ctl (cur + BitVec.ofNat 64 k)
  have hm1_c8 : m1 ⊨ ((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 rest.length) ∗
      ((ctl ↦₆₄ (cur + BitVec.ofNat 64 k)) ∗ memRegion dst len ∗ (cur ↦ₛ rest) ∗ R) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm1_raw
    ac_rfl
  set m2 := m1.write64 (ctl + 8#64) (BitVec.ofNat 64 (rest.length - k))
  have hc8_cw : m1.canWrite (ctl + 8#64) 8 = true :=
    (IsBlock.pointsTo64 (ctl + 8#64) (BitVec.ofNat 64 rest.length)).canWrite (by decide) hm1_c8
  have hkf2 : Memory.KeepsFrozen m1 m2 :=
    Memory.keepsFrozen_write64 hc8_cw (BitVec.ofNat 64 (rest.length - k))
  have hm2_raw : m2 ⊨ ((ctl + 8#64) ↦₆₄ BitVec.ofNat 64 (rest.length - k)) ∗
      ((ctl ↦₆₄ (cur + BitVec.ofNat 64 k)) ∗ memRegion dst len ∗ (cur ↦ₛ rest) ∗ R) :=
    (IsBlock.pointsTo64 (ctl + 8#64) (BitVec.ofNat 64 rest.length)).write64 hm1_c8
      (BitVec.ofNat 64 (rest.length - k))
  have hm2_dst : m2 ⊨ memRegion dst bytes.length ∗
      (tapeAfter ctl cur rest k ∗ R) := by
    rw [hbytes_len]
    refine Satisfies.mono (Entails.of_eq ?_) hm2_raw
    unfold tapeAfter
    ac_rfl
  have hbytes_le64 : bytes.length ≤ 2 ^ 64 := hbytes_len ▸ hlen_le64
  have hkf3 : Memory.KeepsFrozen m2 (m2.writeBytes dst bytes) :=
    keepsFrozen_writeBytes_of_memRegion bytes hbytes_le64 hm2_dst
  have hm3 : m2.writeBytes dst bytes ⊨ (dst ↦ₛ bytes) ∗ (tapeAfter ctl cur rest k ∗ R) :=
    satisfies_writeBytes bytes hbytes_le64 hm2_dst
  dsimp only [rngFillHook, retHook]
  refine ⟨?_, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
  · rw [hdst, hlen, hcur, hrem, hread_cur]
    exact (hkf1.trans hkf2).trans hkf3
  · dsimp only [rngFillAfter0Spec]
    rw [hdst, hlen, hcur, hrem, hread_cur, rngFillBytes_eq rest len]
    simp only [State.trace_setPC, State.trace_setMem, State.mem_setPC, State.mem_setMem,
      sepConj_assoc, satisfies_pure_sepConj, true_and]
    exact hm3

namespace ChainArrayBytes

end ChainArrayBytes

namespace DhStepCallees

end DhStepCallees

end CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep
