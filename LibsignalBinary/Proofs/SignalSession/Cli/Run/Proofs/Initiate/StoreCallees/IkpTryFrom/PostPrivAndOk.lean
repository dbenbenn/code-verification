/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IkpTryFrom.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSome
import ProofLib.SepLogic.WPp

/-!
# `IdentityKeyPair::try_from` Private-Key Validation and `Ok` Assembly

32-byte key cell decompositions, scalar-clamp / key-length checks, and `Ok(IdentityKeyPair)` output
assembly (`+396..+568 → +812`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IkpTryFrom

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

section PostPrivStateSimp

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_ikp (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_ikp (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPState_ikp (s : State) (ps : PState) : (s.setPState ps).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_advancePC_ikp (s : State) : s.advancePC.sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg64_gpr_ikp (s : State) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg64 (Reg.gpr idx) val).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg32_gpr_ikp (s : State) (idx : BitVec 5) (val : BitVec 32) :
    (s.writeReg32 (Reg.gpr idx) val).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_writeReg_gpr_ikp (s : State) (w : Width) (idx : BitVec 5) (val : BitVec 64) :
    (s.writeReg w (Reg.gpr idx) val).sp = s.sp := by cases w <;> cases s <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_ikp (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_ikp (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPState_ikp (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg64 r = s.readReg64 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_ikp (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_ikp (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPState_ikp (s : State) (ps : PState) (r : Reg) :
    (s.setPState ps).readReg32 r = s.readReg32 r := by cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_ikp (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_ikp (s : State) (m : Memory) (w : RegWidth) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPState_ikp (s : State) (ps : PState) (w : RegWidth) (r : Reg) :
    (s.setPState ps).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl

@[local arm64_norm ↓]
theorem bfm32_clamp_ikp1 : ∀ b : BitVec 8,
    (Arm64.evalBitfield .W32 .BFM 64#64 (b.zeroExtend 64) 0 5).setWidth 8 =
      (b &&& 0x7f#8) ||| 0x40#8 := by decide

@[local arm64_norm ↓]
theorem bfm32_clamp_ikp2 : ∀ b : BitVec 8,
    (Arm64.evalBitfield .W32 .BFM 64#64 ((b.zeroExtend 32).zeroExtend 64) 0 5).setWidth 8 =
      (b &&& 0x7f#8) ||| 0x40#8 := by decide

end PostPrivStateSimp

/-! ## 32-byte cell decompositions for `PublicKey` (7 cells) and `PrivateKey` / `clampScalar` (9 cells) -/

@[expose] def pkCells (w0 : BitVec 64) (b8 : BitVec 8) (w9 : BitVec 32) (h13 : BitVec 16)
    (w15 w23 : BitVec 64) (b31 : BitVec 8) (a : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₈ b8) ∗ ((a + 9#64) ↦₃₂ w9) ∗ ((a + 13#64) ↦₁₆ h13) ∗
  ((a + 15#64) ↦₆₄ w15) ∗ ((a + 23#64) ↦₆₄ w23) ∗ ((a + 31#64) ↦₈ b31)

@[expose] def skCells (b0 : BitVec 8) (w1 : BitVec 32) (h5 h7 : BitVec 16) (w9 : BitVec 32)
    (h13 : BitVec 16) (w15 w23 : BitVec 64) (b31 : BitVec 8) (a : BitVec 64) : SepProp :=
  (a ↦₈ b0) ∗ ((a + 1#64) ↦₃₂ w1) ∗ ((a + 5#64) ↦₁₆ h5) ∗ ((a + 7#64) ↦₁₆ h7) ∗
  ((a + 9#64) ↦₃₂ w9) ∗ ((a + 13#64) ↦₁₆ h13) ∗ ((a + 15#64) ↦₆₄ w15) ∗
  ((a + 23#64) ↦₆₄ w23) ∗ ((a + 31#64) ↦₈ b31)

theorem pointsToBytes8_exists (l : List (BitVec 8)) (h : l.length = 8) :
    ∃ w : BitVec 64, ∀ a : BitVec 64, (a ↦ₛ l) = (a ↦₆₄ w) := by
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try simp at h
  exact ⟨b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0, fun a => pointsToBytes8_eq_pointsTo64 a ..⟩

theorem pointsToBytes4_exists (l : List (BitVec 8)) (h : l.length = 4) :
    ∃ w : BitVec 32, ∀ a : BitVec 64, (a ↦ₛ l) = (a ↦₃₂ w) := by
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | _⟩⟩⟩⟩ <;> try simp at h
  exact ⟨b3 ++ b2 ++ b1 ++ b0, fun a => pointsToBytes4_eq_pointsTo32 a ..⟩

theorem pointsToBytes2_exists (l : List (BitVec 8)) (h : l.length = 2) :
    ∃ w : BitVec 16, ∀ a : BitVec 64, (a ↦ₛ l) = (a ↦₁₆ w) := by
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | _⟩⟩ <;> try simp at h
  exact ⟨b1 ++ b0, fun a => pointsToBytes2_eq_pointsTo16 a ..⟩

theorem pointsToBytes1_exists (l : List (BitVec 8)) (h : l.length = 1) :
    ∃ b : BitVec 8, ∀ a : BitVec 64, (a ↦ₛ l) = (a ↦₈ b) := by
  rcases l with _ | ⟨b0, _ | _⟩ <;> try simp at h
  exact ⟨b0, fun a => by rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]⟩

theorem pointsToBytes32_exists_pkCells (bs : List (BitVec 8)) (h : bs.length = 32) :
    ∃ (w0 : BitVec 64) (b8 : BitVec 8) (w9 : BitVec 32) (h13 : BitVec 16)
      (w15 w23 : BitVec 64) (b31 : BitVec 8),
      ∀ a : BitVec 64, (a ↦ₛ bs) = pkCells w0 b8 w9 h13 w15 w23 b31 a := by
  obtain ⟨w0, hw0⟩ := pointsToBytes8_exists (bs.take 8) (by simp [h])
  obtain ⟨b8, hb8⟩ := pointsToBytes1_exists ((bs.drop 8).take 1) (by simp [h])
  obtain ⟨w9, hw9⟩ := pointsToBytes4_exists ((bs.drop 9).take 4) (by simp [h])
  obtain ⟨h13, hh13⟩ := pointsToBytes2_exists ((bs.drop 13).take 2) (by simp [h])
  obtain ⟨w15, hw15⟩ := pointsToBytes8_exists ((bs.drop 15).take 8) (by simp [h])
  obtain ⟨w23, hw23⟩ := pointsToBytes8_exists ((bs.drop 23).take 8) (by simp [h])
  obtain ⟨b31, hb31⟩ := pointsToBytes1_exists (bs.drop 31) (by simp [h])
  refine ⟨w0, b8, w9, h13, w15, w23, b31, fun a => ?_⟩
  have s1 := pointsToBytes_take_drop a bs 8 (by omega)
  have s2 := pointsToBytes_take_drop (a + 8#64) (bs.drop 8) 1 (by simp [h])
  have s3 := pointsToBytes_take_drop (a + 9#64) (bs.drop 9) 4 (by simp [h])
  have s4 := pointsToBytes_take_drop (a + 13#64) (bs.drop 13) 2 (by simp [h])
  have s5 := pointsToBytes_take_drop (a + 15#64) (bs.drop 15) 8 (by simp [h])
  have s6 := pointsToBytes_take_drop (a + 23#64) (bs.drop 23) 8 (by simp [h])
  simp only [List.drop_drop, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at s1 s2 s3 s4 s5 s6
  rw [← s1, ← s2, ← s3, ← s4, ← s5, ← s6,
    hw0, hb8, hw9, hh13, hw15, hw23, hb31]
  unfold pkCells
  ac_rfl

theorem pointsToBytes32_decomp9 {l : List (BitVec 8)} (hl : l.length = 32)
    {b0 : BitVec 8} {w1 : BitVec 32} {h5 h7 : BitVec 16} {w9 : BitVec 32}
    {h13 : BitVec 16} {w15 w23 : BitVec 64} {b31 : BitVec 8}
    (hb0 : l.take 1 = [b0])
    (hw1 : ∀ a, (a ↦ₛ (l.drop 1).take 4) = (a ↦₃₂ w1))
    (hh5 : ∀ a, (a ↦ₛ (l.drop 5).take 2) = (a ↦₁₆ h5))
    (hh7 : ∀ a, (a ↦ₛ (l.drop 7).take 2) = (a ↦₁₆ h7))
    (hw9 : ∀ a, (a ↦ₛ (l.drop 9).take 4) = (a ↦₃₂ w9))
    (hh13 : ∀ a, (a ↦ₛ (l.drop 13).take 2) = (a ↦₁₆ h13))
    (hw15 : ∀ a, (a ↦ₛ (l.drop 15).take 8) = (a ↦₆₄ w15))
    (hw23 : ∀ a, (a ↦ₛ (l.drop 23).take 8) = (a ↦₆₄ w23))
    (hb31 : l.drop 31 = [b31]) (a : BitVec 64) :
    (a ↦ₛ l) = skCells b0 w1 h5 h7 w9 h13 w15 w23 b31 a := by
  have s0 := pointsToBytes_take_drop a l 1 (by omega)
  have s1 := pointsToBytes_take_drop (a + 1#64) (l.drop 1) 4 (by simp [hl])
  have s2 := pointsToBytes_take_drop (a + 5#64) (l.drop 5) 2 (by simp [hl])
  have s3 := pointsToBytes_take_drop (a + 7#64) (l.drop 7) 2 (by simp [hl])
  have s4 := pointsToBytes_take_drop (a + 9#64) (l.drop 9) 4 (by simp [hl])
  have s5 := pointsToBytes_take_drop (a + 13#64) (l.drop 13) 2 (by simp [hl])
  have s6 := pointsToBytes_take_drop (a + 15#64) (l.drop 15) 8 (by simp [hl])
  have s7 := pointsToBytes_take_drop (a + 23#64) (l.drop 23) 8 (by simp [hl])
  simp only [List.drop_drop, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at s0 s1 s2 s3 s4 s5 s6 s7
  rw [← s0, ← s1, ← s2, ← s3, ← s4, ← s5, ← s6, ← s7,
    hb0, hw1, hh5, hh7, hw9, hh13, hw15, hw23, hb31,
    pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  unfold skCells
  ac_rfl

theorem vector32_exists_skCells (sk : List.Vector (BitVec 8) 32) :
    ∃ (b0 : BitVec 8) (w1 : BitVec 32) (h5 h7 : BitVec 16) (w9 : BitVec 32)
      (h13 : BitVec 16) (w15 w23 : BitVec 64) (b31 : BitVec 8),
      (∀ a : BitVec 64, (a ↦ₛ sk.1) =
        skCells b0 w1 h5 h7 w9 h13 w15 w23 b31 a) ∧
      (∀ a : BitVec 64, (a ↦ₛ (Ratchet.clampScalar sk).1) =
        skCells (b0 &&& 0xf8#8) w1 h5 h7 w9 h13 w15 w23 ((b31 &&& 0x7f#8) ||| 0x40#8) a) := by
  rcases sk with ⟨l, hl⟩
  set cl := (Ratchet.clampScalar ⟨l, hl⟩).1
  have hcl : cl.length = 32 := (Ratchet.clampScalar ⟨l, hl⟩).2
  have hmid : ∀ i : Nat, 1 ≤ i → i < 31 → cl[i]? = l[i]? := by
    intro i hi1 hi2
    simp only [cl, Ratchet.clampScalar, List.Vector.set, List.Vector.get]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have hdrop_take : ∀ k n : Nat, k + n ≤ 30 →
      (cl.drop (k + 1)).take n = (l.drop (k + 1)).take n := by
    intro k n hkn
    ext i
    by_cases hi : i < n
    · simp only [List.getElem?_take_of_lt hi, List.getElem?_drop]
      rw [hmid (k + 1 + i) (by omega) (by omega)]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  obtain ⟨w1, hw1⟩ := pointsToBytes4_exists ((l.drop 1).take 4) (by simp [hl])
  obtain ⟨h5, hh5⟩ := pointsToBytes2_exists ((l.drop 5).take 2) (by simp [hl])
  obtain ⟨h7, hh7⟩ := pointsToBytes2_exists ((l.drop 7).take 2) (by simp [hl])
  obtain ⟨w9, hw9⟩ := pointsToBytes4_exists ((l.drop 9).take 4) (by simp [hl])
  obtain ⟨h13, hh13⟩ := pointsToBytes2_exists ((l.drop 13).take 2) (by simp [hl])
  obtain ⟨w15, hw15⟩ := pointsToBytes8_exists ((l.drop 15).take 8) (by simp [hl])
  obtain ⟨w23, hw23⟩ := pointsToBytes8_exists ((l.drop 23).take 8) (by simp [hl])
  refine ⟨l[0]'(by omega), w1, h5, h7, w9, h13, w15, w23, l[31]'(by omega), ?_, ?_⟩
  · intro a
    refine pointsToBytes32_decomp9 hl ?_ hw1 hh5 hh7 hw9 hh13 hw15 hw23 ?_ a
    · rcases l with _ | ⟨x0, xs⟩; · simp at hl
      rfl
    · rw [List.drop_eq_getElem_cons (by omega),
        List.drop_eq_nil_of_le (show l.length ≤ 32 by omega)]
  · intro a
    refine pointsToBytes32_decomp9 hcl ?_
      (fun p => by rw [hdrop_take 0 4 (by decide)]; exact hw1 p)
      (fun p => by rw [hdrop_take 4 2 (by decide)]; exact hh5 p)
      (fun p => by rw [hdrop_take 6 2 (by decide)]; exact hh7 p)
      (fun p => by rw [hdrop_take 8 4 (by decide)]; exact hw9 p)
      (fun p => by rw [hdrop_take 12 2 (by decide)]; exact hh13 p)
      (fun p => by rw [hdrop_take 14 8 (by decide)]; exact hw15 p)
      (fun p => by rw [hdrop_take 22 8 (by decide)]; exact hw23 p)
      ?_ a
    · rw [List.take_one]
      rcases l with _ | ⟨x0, _ | ⟨x1, xs⟩⟩ <;> try simp at hl
      rfl
    · rw [List.drop_eq_getElem_cons (by omega),
        List.drop_eq_nil_of_le (show cl.length ≤ 32 by omega)]
      congr 1
      have hset31 : ∀ (xs : List (BitVec 8)) (hxs : xs.length = 32) (v0 v31 : BitVec 8),
          ((xs.set 0 v0).set 31 v31)[31]'(by simp [hxs]) = v31 := by
        intro xs hxs v0 v31
        rw [List.getElem_set_self]
      exact hset31 l hl _ _

/-! ## Stack scratch `[sp' .. sp' + 32)` & output `Ok` buffer splitting/folding helpers -/

@[expose] def ikpScratch32 (sw8 : BitVec 64) (sb16 : BitVec 8) (sw24 : BitVec 32) (sh28 : BitVec 16)
    (sp' : BitVec 64) : SepProp :=
  memRegion sp' 8 ∗ ((sp' + 8#64) ↦₆₄ sw8) ∗ ((sp' + 16#64) ↦₈ sb16) ∗
  memRegion (sp' + 17#64) 7 ∗ ((sp' + 24#64) ↦₃₂ sw24) ∗ ((sp' + 28#64) ↦₁₆ sh28) ∗
  memRegion (sp' + 30#64) 2

theorem memRegion32_split_scratch (sp' : BitVec 64) :
    memRegion sp' 32 ⊢
      ∃∗ sh28 : BitVec 16, ∃∗ sw24 : BitVec 32, ∃∗ sb16 : BitVec 8, ∃∗ sw8 : BitVec 64,
        ikpScratch32 sw8 sb16 sw24 sh28 sp' := by
  have hm2 : ∀ a : BitVec 64, memRegion a 2 ⊢ ∃∗ v : BitVec 16, a ↦₁₆ v := by
    intro a
    rw [memRegion_eq_exists_bytes a 2 (by decide)]
    refine Entails.sepExists_elim fun bs => Entails.pure_left fun hlen => ?_
    obtain ⟨v, hv⟩ := pointsToBytes2_exists bs hlen
    rw [hv a]
    exact sepExists_intro _ v
  rw [Prost.memRegion_split sp' 8 24 (by decide),
    Prost.memRegion_split (sp' + 8#64) 8 16 (by decide),
    Prost.memRegion_split (sp' + 8#64 + 8#64) 1 15 (by decide),
    Prost.memRegion_split (sp' + 8#64 + 8#64 + 1#64) 7 8 (by decide),
    Prost.memRegion_split (sp' + 8#64 + 8#64 + 1#64 + 7#64) 4 4 (by decide),
    Prost.memRegion_split (sp' + 8#64 + 8#64 + 1#64 + 7#64 + 4#64) 2 2 (by decide),
    ProofLib.memRegion_eight (sp' + 8#64), memRegion_one]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (memRegion_four_entails (sp' + 24#64))
        (sepConj_mono_left (hm2 (sp' + 28#64)))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, ikpScratch32]
  exact Entails.refl _

theorem ikpScratch32_entails_memRegion32 (sw8 : BitVec 64) (sb16 : BitVec 8)
    (sw24 : BitVec 32) (sh28 : BitVec 16) (sp' : BitVec 64) :
    ikpScratch32 sw8 sb16 sw24 sh28 sp' ⊢ memRegion sp' 32 := by
  unfold ikpScratch32
  have hm4 : ((sp' + 24#64) ↦₃₂ sw24) ⊢ memRegion (sp' + 24#64) 4 := by
    rw [pointsTo32_eq_pointsToBytes]
    exact pointsToBytes_entails_memRegion (sp' + 24#64) (unpack32 sw24)
  have hm2 : ((sp' + 28#64) ↦₁₆ sh28) ⊢ memRegion (sp' + 28#64) 2 := by
    rw [pointsTo16_eq_pointsToBytes]
    exact pointsToBytes_entails_memRegion (sp' + 28#64) (unpack16 sh28)
  have hm1 : ((sp' + 16#64) ↦₈ sb16) ⊢ memRegion (sp' + 16#64) 1 := by
    rw [memRegion_one]; exact sepExists_intro _ sb16
  rw [Prost.memRegion_split sp' 8 24 (by decide),
    Prost.memRegion_split (sp' + 8#64) 8 16 (by decide),
    Prost.memRegion_split (sp' + 8#64 + 8#64) 1 15 (by decide),
    Prost.memRegion_split (sp' + 8#64 + 8#64 + 1#64) 7 8 (by decide),
    Prost.memRegion_split (sp' + 8#64 + 8#64 + 1#64 + 7#64) 4 4 (by decide),
    Prost.memRegion_split (sp' + 8#64 + 8#64 + 1#64 + 7#64 + 4#64) 2 2 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_right
    (sepConj_mono (pointsTo64_entails_memRegion (sp' + 8#64) sw8)
      (sepConj_mono hm1
        (sepConj_mono_right (sepConj_mono hm4 (sepConj_mono_left hm2)))))

theorem memRegion72_split_ok (r : BitVec 64) :
    memRegion r 72 ⊢
      ∃∗ sb0 : BitVec 8, ∃∗ sw1 : BitVec 32, ∃∗ sh5 : BitVec 16, ∃∗ sh7 : BitVec 16,
      ∃∗ sw9 : BitVec 32, ∃∗ sh13 : BitVec 16, ∃∗ sw15 : BitVec 64, ∃∗ sw23 : BitVec 64,
      ∃∗ sb31 : BitVec 8,
      ∃∗ dw0 : BitVec 64, ∃∗ db8 : BitVec 8, ∃∗ dw9 : BitVec 32, ∃∗ dh13 : BitVec 16,
      ∃∗ dw15 : BitVec 64, ∃∗ dw23 : BitVec 64, ∃∗ db31 : BitVec 8,
      ∃∗ b_tag : BitVec 8,
        (r ↦₈ b_tag) ∗
        pkCells dw0 db8 dw9 dh13 dw15 dw23 db31 (r + 1#64) ∗
        skCells sb0 sw1 sh5 sh7 sw9 sh13 sw15 sw23 sb31 (r + 0x21#64) ∗
        memRegion (r + 0x41#64) 7 := by
  have hm32_pk : memRegion (r + 1#64) 32 ⊢
      ∃∗ dw0 : BitVec 64, ∃∗ db8 : BitVec 8, ∃∗ dw9 : BitVec 32, ∃∗ dh13 : BitVec 16,
      ∃∗ dw15 : BitVec 64, ∃∗ dw23 : BitVec 64, ∃∗ db31 : BitVec 8,
        pkCells dw0 db8 dw9 dh13 dw15 dw23 db31 (r + 1#64) := by
    rw [memRegion_eq_exists_bytes (r + 1#64) 32 (by decide)]
    refine Entails.sepExists_elim fun bs => Entails.pure_left fun hlen => ?_
    obtain ⟨dw0', db8', dw9', dh13', dw15', dw23', db31', heq⟩ := pointsToBytes32_exists_pkCells bs hlen
    rw [heq (r + 1#64)]
    refine Entails.trans ?_ (sepExists_intro _ dw0')
    refine Entails.trans ?_ (sepExists_intro _ db8')
    refine Entails.trans ?_ (sepExists_intro _ dw9')
    refine Entails.trans ?_ (sepExists_intro _ dh13')
    refine Entails.trans ?_ (sepExists_intro _ dw15')
    refine Entails.trans ?_ (sepExists_intro _ dw23')
    exact sepExists_intro (fun db31 => pkCells dw0' db8' dw9' dh13' dw15' dw23' db31 (r + 1#64)) db31'
  have hm32_sk : memRegion (r + 0x21#64) 32 ⊢
      ∃∗ sb0 : BitVec 8, ∃∗ sw1 : BitVec 32, ∃∗ sh5 : BitVec 16, ∃∗ sh7 : BitVec 16,
      ∃∗ sw9 : BitVec 32, ∃∗ sh13 : BitVec 16, ∃∗ sw15 : BitVec 64, ∃∗ sw23 : BitVec 64,
      ∃∗ sb31 : BitVec 8,
        skCells sb0 sw1 sh5 sh7 sw9 sh13 sw15 sw23 sb31 (r + 0x21#64) := by
    rw [memRegion_eq_exists_bytes (r + 0x21#64) 32 (by decide)]
    refine Entails.sepExists_elim fun bs => Entails.pure_left fun hlen => ?_
    obtain ⟨sb0', sw1', sh5', sh7', sw9', sh13', sw15', sw23', sb31', hsrc, _⟩ :=
      vector32_exists_skCells ⟨bs, hlen⟩
    rw [hsrc (r + 0x21#64)]
    refine Entails.trans ?_ (sepExists_intro _ sb0')
    refine Entails.trans ?_ (sepExists_intro _ sw1')
    refine Entails.trans ?_ (sepExists_intro _ sh5')
    refine Entails.trans ?_ (sepExists_intro _ sh7')
    refine Entails.trans ?_ (sepExists_intro _ sw9')
    refine Entails.trans ?_ (sepExists_intro _ sh13')
    refine Entails.trans ?_ (sepExists_intro _ sw15')
    refine Entails.trans ?_ (sepExists_intro _ sw23')
    exact sepExists_intro
      (fun sb31 => skCells sb0' sw1' sh5' sh7' sw9' sh13' sw15' sw23' sb31 (r + 0x21#64)) sb31'
  rw [Prost.memRegion_split r 1 71 (by decide),
    Prost.memRegion_split (r + 1#64) 32 39 (by decide),
    Prost.memRegion_split (r + 1#64 + 32#64) 32 7 (by decide),
    memRegion_one]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono hm32_pk (sepConj_mono_left hm32_sk))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

/-! ## Error tail `+760 .. +772 -> +812` and post-PK `Ok(pk)` path `+396 .. +568 -> +812` -/

private theorem clamp_b0_post (b : BitVec 8) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 b &&& 1065151889656#64) = b &&& 248#8 := by
  revert b; decide

private theorem clamp_b31_post (b : BitVec 8) :
    BitVec.zeroExtend 8 (64#64 ||| BitVec.zeroExtend 64 b >>> 0 &&& 63#64) =
      (b &&& 127#8) ||| 64#8 := by
  revert b; decide

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IkpTryFrom
