/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FrameAndKeyBytes -- proof-setup: allow-public-import
import ProofLib
import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.ConsumeMessageKey.MessageTypeBv -- shake: keep
public meta import Lean
public meta import ProofLib.GenDecodes
public meta import ProofLib.ProgramReflection
public meta import ProofLib.SepLogic.CodeLookup
public meta import ProofLib.VCGen
import LibsignalBinary.Proofs.CodeLayout

public section

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000
set_option autoImplicit false

namespace CryptoVerification.LibsignalSession.AdvanceEpilogue

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.SessionModel

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm]
theorem Int64_mk_toBitVec (u : UInt64) : ({ toUInt64 := u } : Int64).toBitVec = u.toBitVec := rfl

@[local arm64_norm]
theorem UInt64_ofNat_toBitVec (n : Nat) : (OfNat.ofNat n : UInt64).toBitVec = BitVec.ofNat 64 n := rfl

@[local arm64_norm]
theorem UInt64_mk_toBitVec (bv : BitVec 64) : ({ toBitVec := bv } : UInt64).toBitVec = bv := rfl

@[local arm64_norm]
theorem BitVec_ofFin_eq_ofNat {w n : Nat} (h : n < 2 ^ w) :
    (BitVec.ofFin ⟨n, h⟩) = BitVec.ofNat w n := by
  apply BitVec.eq_of_toNat_eq
  exact (Nat.mod_eq_of_lt h).symm

macro "advanceEpilogue_cc_close" : tactic => `(tactic| (
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, applyWriteback,
    State.advancePC_eq_setPC, State.setPC_setPC, State.writeReg64_setPC, State.setPState_setPC,
    State.setPState_setPState, State.writeReg64_setPState, State.setMem_setPC, State.setMem_setMem,
    State.writeReg64_setMem, State.setPState_setMem, State.writeReg64_writeReg64_same,
    arm64_norm, *]
  done))

theorem allocFailedIn_of_eq {s0 sf : State} (h : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  refine ⟨?_, ⟨[allocFailedEvent], h.symm⟩⟩
  simp [allocFailedIn, h]

theorem leBytes_four_eq_unpack32 (w : BitVec 32) :
    leBytes 4 w.toNat = unpack32 w := by
  simp only [leBytes, unpack32, List.range, List.range.loop, List.map]
  have h0 : BitVec.ofNat 8 (w.toNat / 256 ^ 0) = w.setWidth 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]
  have h1 : BitVec.ofNat 8 (w.toNat / 256 ^ 1) = (w >>> 8).setWidth 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h2 : BitVec.ofNat 8 (w.toNat / 256 ^ 2) = (w >>> 16).setWidth 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h3 : BitVec.ofNat 8 (w.toNat / 256 ^ 3) = (w >>> 24).setWidth 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [h0, h1, h2, h3]
  unfold BitVec.extractLsb'
  rfl

theorem pointsToBytes_chainKeyBytes_eq (a : BitVec 64) (ck : ChainKey) :
    (a ↦ₛ chainKeyBytes ck) = (a ↦ₛ keyToBytes32 ck.key) ∗ ((a + 32#64) ↦₃₂ ck.index) := by
  unfold chainKeyBytes
  have hlen : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  rw [pointsToBytes_append, hlen, leBytes_four_eq_unpack32, ← pointsTo32_eq_pointsToBytes]

theorem chainKey_key_idx_entails_memRegion (a : BitVec 64) (ck : ChainKey) :
    (a ↦ₛ keyToBytes32 ck.key) ∗ ((a + 32#64) ↦₃₂ ck.index) ⊢ memRegion a 36 := by
  rw [← pointsToBytes_chainKeyBytes_eq]
  have hlen : (chainKeyBytes ck).length = 36 := by simp [chainKeyBytes, leBytes, keyToBytes32]
  have h := pointsToBytes_entails_memRegion a (chainKeyBytes ck)
  rwa [hlen] at h

theorem stackAt_7712_split_4096 (sp : BitVec 64) :
    stackAt sp 7712 = memRegion (sp - 7712#64) 3616 ∗ stackAt sp allocHookStack := by
  unfold stackAt allocHookStack
  rw [show (7712 : Nat) = 3616 + 4096 from rfl, memRegion_split (sp - 7712#64) 3616 4096 (by decide)]
  have h : sp - 7712#64 + 3616#64 = sp - 4096#64 := by bv_arith
  rw [h]

theorem SepWPp.conseq_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P ⊢ P') (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp :=
  fun R hm hL => h R (Satisfies.mono (sepConj_mono_left hP) hm) hL

theorem SepWPp.pure_elim3 {prog : Program} {ret : BitVec 64} {s : State}
    {P1 P2 P3 : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (P1 ∗ P2 ∗ P3) Q Qp) :
    SepWPp prog ret s (P1 ∗ P2 ∗ ⌜φ⌝ ∗ P3) Q Qp := by
  have heq : (P1 ∗ P2 ∗ ⌜φ⌝ ∗ P3) = (⌜φ⌝ ∗ (P1 ∗ P2 ∗ P3)) := by ac_rfl
  rw [heq]
  exact SepWPp.pure_elim h

theorem pure_and_entails_pure_sep_of {P P' Q : Prop} {R : SepProp}
    (h : P → P' ∧ Q) :
    ⌜P⌝ ∗ R ⊢ ⌜P'⌝ ∗ (⌜Q⌝ ∗ R) := by
  apply Entails.pure_left
  intro hp
  rcases h hp with ⟨hp', hq⟩
  exact Entails.pure_right hp' (Entails.pure_right hq (Entails.refl R))

theorem ule_false_of_lt {a b : BitVec 64} (h : a < b) : b.ule a = false := by
  rw [BitVec.lt_def] at h
  rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]
  omega

theorem leBytes4_eq_unpack32 (w : BitVec 32) :
    leBytes 4 w.toNat = unpack32 w := by
  unfold leBytes unpack32
  have h0 : BitVec.ofNat 8 (w.toNat / 256 ^ 0) = w.extractLsb' 0 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb'_toNat]
  have h1 : BitVec.ofNat 8 (w.toNat / 256 ^ 1) = w.extractLsb' 8 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have h2 : BitVec.ofNat 8 (w.toNat / 256 ^ 2) = w.extractLsb' 16 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have h3 : BitVec.ofNat 8 (w.toNat / 256 ^ 3) = w.extractLsb' 24 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  change [BitVec.ofNat 8 (w.toNat / 256 ^ 0), BitVec.ofNat 8 (w.toNat / 256 ^ 1),
          BitVec.ofNat 8 (w.toNat / 256 ^ 2), BitVec.ofNat 8 (w.toNat / 256 ^ 3)] = _
  rw [h0, h1, h2, h3]

theorem chainKeyBytes_pointsTo (a : BitVec 64) (ck : ChainKey) :
    (a ↦ₛ chainKeyBytes ck) = (a ↦ₛ keyToBytes32 ck.key) ∗ ((a + 32#64) ↦₃₂ ck.index) := by
  unfold chainKeyBytes
  rw [pointsToBytes_append, length_keyToBytes32, leBytes4_eq_unpack32, ← pointsTo32_eq_pointsToBytes]

end CryptoVerification.LibsignalSession.AdvanceEpilogue
