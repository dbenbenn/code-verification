/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneSysrootExt
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
public section

namespace CryptoVerification.SpqrV1.Top.EncodeVarint

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSpqrV1
  (encodeVarintLoop MAX_VARINT_BYTES_LEN GrowOneCall newCapU8 growOneU8Spec growOneU8Name SpqrHooks)
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[expose] def SpqrEncVarintCalleeSaved (s0 s : State) : Prop :=
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs s = calleeSavedVRegs s0 ∧
  StepInv s0 s

theorem SpqrEncVarintCalleeSaved.refl (s : State) : SpqrEncVarintCalleeSaved s s :=
  ⟨rfl, rfl, rfl, rfl, StepInv.refl s⟩

theorem SpqrEncVarintCalleeSaved.trans {s0 s1 s2 : State}
    (h1 : SpqrEncVarintCalleeSaved s0 s1) (h2 : SpqrEncVarintCalleeSaved s1 s2) :
    SpqrEncVarintCalleeSaved s0 s2 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
   h2.2.2.2.1.trans h1.2.2.2.1,
   h1.2.2.2.2.trans h2.2.2.2.2⟩

theorem SpqrEncVarintCalleeSaved.of_calleeSavedPreserved {s1 s2 : State}
    (h : CalleeSavedPreserved s1 s2) (hinv : StepInv s1 s2) : SpqrEncVarintCalleeSaved s1 s2 :=
  ⟨h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2, hinv⟩

theorem sp_sub_80_aligned {sp : BitVec 64} (h : sp &&& 15#64 = 0#64) :
    (sp - 80#64) &&& 15#64 = 0#64 := by
  bv_bits

@[scoped simp]
theorem encodeVarintLoop_10_eq (a : BitVec 64) :
    encodeVarintLoop MAX_VARINT_BYTES_LEN a = encodeVarint a :=
  encodeVarintLoop_eq_encodeVarintAux 10 a

@[scoped simp, scoped arm64_norm]
theorem ule_128_eq_not_ult_128 (v : BitVec 64) :
    (128#64).ule v = !v.ult 128#64 := by
  rw [BitVec.ule_eq_decide, BitVec.ult_eq_decide]
  change decide (128 ≤ v.toNat) = !decide (v.toNat < 128)
  by_cases h : v.toNat < 128
  · have h' : ¬ (128 ≤ v.toNat) := by omega
    simp [h, h']
  · have h' : 128 ≤ v.toNat := by omega
    simp [h, h']

@[scoped simp, scoped arm64_norm]
theorem not_len_lt_ofNat_len (n : Nat) : ¬ n < (BitVec.ofNat 64 n).toNat := by
  rw [BitVec.toNat_ofNat]
  exact Nat.not_lt.mpr (Nat.mod_le n (2 ^ 64))

@[scoped simp, scoped arm64_norm]
theorem len_beq_cap_false {cap : BitVec 64} {n : Nat} (hlt : n < cap.toNat) :
    (BitVec.ofNat 64 n == cap) = false := by
  have h := cap_beq_len_false hlt
  rw [beq_eq_false_iff_ne] at h ⊢
  exact Ne.symm h

@[scoped simp, scoped arm64_norm]
theorem len_bne_cap_true {cap : BitVec 64} {n : Nat} (hlt : n < cap.toNat) :
    (BitVec.ofNat 64 n != cap) = true := by
  simp [bne, len_beq_cap_false hlt]

theorem origLen_add_step {origLen : BitVec 64} {curBs : List (BitVec 8)} (byte : BitVec 8)
    (k1 k : BitVec 64) (hk : k1 + 1#64 = k)
    (horig : origLen + k1 = BitVec.ofNat 64 curBs.length) :
    origLen + k = BitVec.ofNat 64 (curBs ++ [byte]).length := by
  rw [← hk, ← BitVec.add_assoc, horig, bv_len_add_one]

theorem stackAt_spqrEncodeVarint_eq (sp : BitVec 64) :
    stackAt sp spqrEncodeVarintStackX =
      stackAt (sp - 80#64) extHookStack ∗
      (∃∗ v80 : BitVec 64, ∃∗ v72 : BitVec 64, ∃∗ v64 : BitVec 64, ∃∗ v56 : BitVec 64,
       ∃∗ v48 : BitVec 64, ∃∗ v40 : BitVec 64, ∃∗ v32 : BitVec 64, ∃∗ v24 : BitVec 64,
       ∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
        ((sp - 80#64) ↦₆₄ v80) ∗ ((sp - 72#64) ↦₆₄ v72) ∗
        ((sp - 64#64) ↦₆₄ v64) ∗ ((sp - 56#64) ↦₆₄ v56) ∗
        ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
        ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
        ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) := by
  change stackAt sp (extHookStack + 8 * 10) = _
  rw [ProofLib.stackAt_split_cells sp extHookStack 10 (by decide)]
  congr 1
  cells_unfold

/-! ## Callee helper: `<alloc::raw_vec::RawVec<u8>>::grow_one` -/

theorem newCapU8_bounds {cap : BitVec 64} {len : Nat}
    (hcap : cap.toNat = len) (hlen : len < 2 ^ 62) :
    max (2 * cap.toNat) 8 < 2 ^ 63 ∧
    (newCapU8 cap).toNat = max (2 * cap.toNat) 8 ∧
    newCapU8 cap ≠ 0 ∧
    len < (newCapU8 cap).toNat ∧
    cap.toNat ≤ (newCapU8 cap).toNat := by
  unfold newCapU8
  have hmax : max (2 * cap.toNat) 8 < 2 ^ 63 := by omega
  have htoNat : (BitVec.ofNat 64 (max (2 * cap.toNat) 8)).toNat = max (2 * cap.toNat) 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hne : BitVec.ofNat 64 (max (2 * cap.toNat) 8) ≠ 0 := by
    intro heq
    have := congrArg BitVec.toNat heq
    rw [htoNat] at this
    change max (2 * cap.toNat) 8 = 0 at this
    omega
  refine ⟨hmax, htoNat, hne, ?_, ?_⟩ <;> omega

theorem vecU8Buf_eq_for_growOne (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hcap : cap.toNat = bs.length) :
    vecU8Buf A cap ptr bs =
      ⌜cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0 then emp else A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs)) := by
  unfold vecU8Buf
  have hpure : (bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) =
      (cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) := by
    apply propext; constructor
    · rintro ⟨_, h2, h3⟩; exact ⟨h2, h3⟩
    · rintro ⟨h2, h3⟩; exact ⟨by omega, h2, h3⟩
  rw [hpure]
  by_cases h0 : cap = 0
  · simp [h0]
  · simp only [h0, ↓reduceIte, hcap, Nat.sub_self, memRegion_zero, sepConj_emp]

theorem grow_frame_reassoc (A : RustAlloc) (v newCap p' sp : BitVec 64)
    (curBs : List (BitVec 8)) (byte : BitVec 8) (F : SepProp) :
    ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗ vecU8Buf A newCap p' (curBs ++ [byte]) ∗
      A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗
      (((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [byte]).length) ∗ F) =
    ((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [byte]).length) ∗
      vecU8Buf A newCap p' (curBs ++ [byte]) ∗ A.pool ∗ stackAt (sp - 80#64) extHookStack) ∗ F := by ac_rfl

/-! ## Continuation-Byte Stages 1..2 -/

end CryptoVerification.SpqrV1.Top.EncodeVarint
