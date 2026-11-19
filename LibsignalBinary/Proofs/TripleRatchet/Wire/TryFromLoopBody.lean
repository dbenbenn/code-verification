/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoop -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromHooks
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.Sep
meta import Lean
import ProofLib.SepLogic.WPp

public section

namespace CryptoVerification.LibsignalTripleRatchet.Wire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace TryFromLoopStateSimp

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

end TryFromLoopStateSimp

run_meta do
  let env ← Lean.getEnv
  for (h, ks) in #[(``RustAlloc.live, #[1]), (``stackAt, #[0]), (``vecHeader, #[0]), (``optU32At, #[0]), (``speAt, #[2]), (``errResultAt, #[3]), (``signalMessageResultAt, #[2])] do
    let n := Lean.mkPrivateName env (((ks.foldl Lean.Name.mkNum ProofLib.Sep.sepKeyMarker).str "_TARGET_") ++ h)
    unless env.contains n do
      Lean.withExporting (isExporting := false) do
        Lean.addDecl <| .defnDecl { name := n, levelParams := [], type := .const ``Unit [], value := .const ``Unit.unit [], hints := .abbrev, safety := .safe }

private theorem trans_sub {P Sub Out F Q : SepProp} (hsub : Sub ⊢ Out)
    (hpre : P ⊢ Sub ∗ F := by first | sep_accu | bi_frame)
    (hpost : Out ∗ F ⊢ Q := by first | sep_accu | sep_interval | bi_entail) : P ⊢ Q :=
  Entails.trans hpre (Entails.trans (sepConj_mono_left hsub) hpost)

/-!
# `<SignalMessage>::try_from` Protobuf Decode Loop Body (`+0x0d0 .. +0x3b0`)

Proves the inlined varint/key decoder, per-tag field merge branches (`int32::merge`, `bytes::merge`,
and `skip_field`), tag dispatch, and fuel-inductive decode loop (`decodeLoop_e0_wp`,
`decodeLoop_f0_wp`, and relocatable `[LibsignalPlacement]` variants) for
`<SignalMessage as TryFrom<&[u8]>>::try_from` (`0x25868`, Block `85`).
-/

/-! ## Loop-invariant `WireSignalMessageGhost` capacity bound (`BytesMergeCapOk`) -/

structure WireGhostCapOk (g : WireSignalMessageGhost) (n : ℕ) : Prop where
  rk : BytesMergeCapOk g.rk.cap n
  ct : BytesMergeCapOk g.ct.cap n
  pq : BytesMergeCapOk g.pq.cap n
  addr : BytesMergeCapOk g.addr.cap n

theorem WireGhostCapOk.mono {g : WireSignalMessageGhost} {m n : ℕ}
    (hg : WireGhostCapOk g n) (hle : m ≤ n) :
    WireGhostCapOk g m :=
  ⟨bytesMergeCapOk_mono hg.rk hle,
   bytesMergeCapOk_mono hg.ct hle,
   bytesMergeCapOk_mono hg.pq hle,
   bytesMergeCapOk_mono hg.addr hle⟩

@[expose] def wireSignalMessageLoopOf (A : RustAlloc) (a : BitVec 64) (n : ℕ)
    (m : ProtoSignalMessage) : SepProp :=
  ∃∗ g : WireSignalMessageGhost, ⌜WireGhostCapOk g n⌝ ∗ wireSignalMessageAt A g a m

theorem wireSignalMessageAt_entails_loopOf (A : RustAlloc) (g : WireSignalMessageGhost)
    (a : BitVec 64) (n : ℕ) (m : ProtoSignalMessage) (hg : WireGhostCapOk g n) :
    wireSignalMessageAt A g a m ⊢ wireSignalMessageLoopOf A a n m := by
  unfold wireSignalMessageLoopOf
  refine Entails.trans ?_ (sepExists_intro _ g)
  rw [pure_true_emp hg, emp_sepConj]
  exact Entails.refl _

theorem wireSignalMessageLoopOf_entails_of (A : RustAlloc) (a : BitVec 64) (n : ℕ)
    (m : ProtoSignalMessage) :
    wireSignalMessageLoopOf A a n m ⊢ wireSignalMessageOf A a m :=
  Entails.sepExists_elim fun g =>
    Entails.pure_left fun _ => wireSignalMessageAt_entails_of A g a m

theorem wireSignalMessageLoopOf_mono (A : RustAlloc) (a : BitVec 64) {m n : ℕ}
    (msg : ProtoSignalMessage) (hle : m ≤ n) :
    wireSignalMessageLoopOf A a n msg ⊢ wireSignalMessageLoopOf A a m msg :=
  Entails.sepExists_elim fun g =>
    Entails.pure_left fun hg =>
      wireSignalMessageAt_entails_loopOf A g a m msg (hg.mono hle)

theorem wireSignalMessageOf_emptyMsg_entails_loopOf (A : RustAlloc) (a : BitVec 64) (n : ℕ) :
    wireSignalMessageOf A a emptyProtoSignalMessage ⊢ wireSignalMessageLoopOf A a n emptyProtoSignalMessage := by
  refine Entails.sepExists_elim fun g => ?_
  have h0 : WireGhostCapOk ⟨⟨0#64, 0#64⟩, ⟨0#64, 0#64⟩, ⟨0#64, 0#64⟩, ⟨0#64, 0#64⟩⟩ n :=
    ⟨bytesMergeCapOk_zero, bytesMergeCapOk_zero, bytesMergeCapOk_zero, bytesMergeCapOk_zero⟩
  have heq : wireSignalMessageAt A g a emptyProtoSignalMessage =
      wireSignalMessageAt A ⟨⟨0#64, 0#64⟩, ⟨0#64, 0#64⟩, ⟨0#64, 0#64⟩, ⟨0#64, 0#64⟩⟩ a emptyProtoSignalMessage :=
    rfl
  rw [heq]
  exact wireSignalMessageAt_entails_loopOf A _ a n emptyProtoSignalMessage h0

private theorem wireSignalMessageLoopOf_def (A : RustAlloc) (a : BitVec 64) (n : ℕ)
    (m : ProtoSignalMessage) :
    wireSignalMessageLoopOf A a n m =
      ∃∗ g : WireSignalMessageGhost, ⌜WireGhostCapOk g n⌝ ∗ wireSignalMessageAt A g a m := rfl

section LoopBodyOpaqueErr
attribute [local irreducible] decodeErrorAtStackLen decodeErrorAt wireSignalMessageOf wireSignalMessageLoopOf

theorem loopExitMem_err_loop_intro (A : RustAlloc) (sp' ptr : BitVec 64) (bs : List (BitVec 8))
    (x24 : BitVec 64) (hx24 : x24 ≠ 0#64) (n k : ℕ) (mErr : ProtoSignalMessage) :
    memRegion (sp' + 160#64) 16 ∗ (ptr ↦ₛ bs) ∗
      ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗ memRegion (sp' + 296#64) 48 ∗
      A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
      decodeErrorAtStackLen A x24 n ∗ wireSignalMessageLoopOf A (sp' + 176#64) k mErr ⊢
      loopExitMem A sp' ptr bs x24 none := by
  refine Entails.trans ?_ (loopExitMem_err_intro A sp' ptr bs x24 hx24 n mErr)
  exact trans_sub (wireSignalMessageLoopOf_entails_of A (sp' + 176#64) k mErr)

/-! ## Negative-offset callee helpers for `try_from` (`0x25868`) -/

theorem memRegion48_split24 (sp' : BitVec 64) :
    memRegion (sp' + 296#64) 48 =
      memRegion (sp' + 296#64) 24 ∗ memRegion (sp' + 320#64) 24 := by
  sep_interval_eq

theorem pointsTo64_zero_split32 (a : BitVec 64) :
    (a ↦₆₄ 0#64) = (a ↦₃₂ 0#32) ∗ ((a + 4#64) ↦₃₂ 0#32) := by
  sep_interval_eq

theorem pointsTo64_one_split32 (a : BitVec 64) :
    (a ↦₆₄ 1#64) = (a ↦₃₂ 1#32) ∗ ((a + 4#64) ↦₃₂ 0#32) := by
  sep_interval_eq

theorem scratch24_ok_entails_memRegion48 (sp' v w : BitVec 64) :
    ((sp' + 296#64) ↦₃₂ 0#32) ∗ ((sp' + 300#64) ↦₃₂ 0#32) ∗
      ((sp' + 304#64) ↦₆₄ v) ∗ ((sp' + 312#64) ↦₆₄ w) ∗
      memRegion (sp' + 320#64) 24 ⊢
      memRegion (sp' + 296#64) 48 := by
  sep_interval

theorem scratch24_err_entails_memRegion48 (sp' e : BitVec 64) :
    ((sp' + 296#64) ↦₃₂ 1#32) ∗ ((sp' + 300#64) ↦₃₂ 0#32) ∗
      ((sp' + 304#64) ↦₆₄ e) ∗ memRegion (sp' + 312#64) 8 ∗
      memRegion (sp' + 320#64) 24 ⊢
      memRegion (sp' + 296#64) 48 := by
  sep_interval

theorem memRegion48_split_296_304_312 (sp' : BitVec 64) :
    memRegion (sp' + 296#64) 48 =
      (∃∗ w0 : BitVec 64, (sp' + 296#64) ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (sp' + 304#64) ↦₆₄ w1) ∗
      memRegion (sp' + 312#64) 32 := by
  sep_interval_eq

theorem pointsTo64_304_memRegion32_entails_memRegion40 (sp' v : BitVec 64) :
    ((sp' + 304#64) ↦₆₄ v) ∗ memRegion (sp' + 312#64) 32 ⊢ memRegion (sp' + 304#64) 40 := by
  sep_interval

/-! ## Pure arithmetic helpers for `decodeVarint` and `decodeKey` -/

theorem signExtend64_bit63_eq_false_iff (b0 : BitVec 8) :
    ((b0.signExtend 64).getLsbD 63 == true) = false ↔ b0.toNat ≤ 0x7F := by
  revert b0; decide

theorem signExtend64_bit63_eq_true_iff (b0 : BitVec 8) :
    ((b0.signExtend 64).getLsbD 63 == true) = true ↔ 0x7F < b0.toNat := by
  revert b0; decide

theorem signExtend64_eq_zeroExtend64_of_le (b0 : BitVec 8) (h : b0.toNat ≤ 0x7F) :
    b0.signExtend 64 = b0.zeroExtend 64 := by
  revert b0 h; decide

theorem signExtend32_bit31_eq_false_iff (b : BitVec 8) :
    (b.getLsbD 7 == true) = false ↔ b.toNat ≤ 0x7F := by
  revert b; decide

theorem signExtend32_bit31_eq_true_iff (b : BitVec 8) :
    (b.getLsbD 7 == true) = true ↔ 0x7F < b.toNat := by
  revert b; decide

/-! ## `decode_varint_slow` branch (`+0x284..+0x294`) -/

theorem key_lsr32_ne_zero_of_ge (key : BitVec 64) (h : 2 ^ 32 ≤ key.toNat) :
    (key >>> 32 != 0#64) = true := by
  simp only [bne_iff_ne, ne_eq]
  intro heq
  have hto := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow] at hto
  omega

theorem key_lsr32_eq_zero_of_lt (key : BitVec 64) (h : key.toNat < 2 ^ 32) :
    (key >>> 32 != 0#64) = false := by
  simp only [bne_eq_false_iff_eq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

theorem sliceCursorAfter_entails_memRegion (slot ptr : BitVec 64) (bs rest : List (BitVec 8)) :
    sliceCursorAfter slot ptr bs rest ⊢ memRegion slot 16 ∗ (ptr ↦ₛ bs) := by
  unfold sliceCursorAfter; sep_interval

theorem key_and7_toNat (key : BitVec 64) : (key &&& 7#64).toNat = key.toNat % 8 := by
  have h7 : (7#64).toNat = 2 ^ 3 - 1 := rfl
  rw [BitVec.toNat_and, h7, Nat.and_two_pow_sub_one_eq_mod]

theorem decodeKey_err_entails (A : RustAlloc) (sp' ptr w0 v : BitVec 64)
    (bs rest : List (BitVec 8)) (len : ℕ) (m : ProtoSignalMessage) :
    sliceCursorAfter (sp' + 160#64) ptr bs rest ∗
      ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
      ((sp' + 296#64) ↦₆₄ w0) ∗
      ((sp' + 304#64) ↦₆₄ v) ∗
      memRegion (sp' + 312#64) 32 ∗
      A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
      wireSignalMessageLoopOf A (sp' + 176#64) len m ⊢
    memRegion (sp' + 160#64) 16 ∗ (ptr ↦ₛ bs) ∗
      ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
      ((sp' + 296#64) ↦₆₄ w0) ∗ memRegion (sp' + 304#64) 40 ∗
      A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
      wireSignalMessageOf A (sp' + 176#64) m := by
  unfold sliceCursorAfter
  exact trans_sub (wireSignalMessageLoopOf_entails_of A (sp' + 176#64) len m)
    (hpost := by sep_interval)

theorem key_and7_ule6_of_ge (key : BitVec 64) (h : 6 ≤ key.toNat % 8) :
    (6#64).ule (key &&& 7#64) = true := by
  simp only [BitVec.ule, BitVec.toNat_ofNat, key_and7_toNat, decide_eq_true_eq]
  omega

theorem key_and7_ule6_of_lt (key : BitVec 64) (h : key.toNat % 8 < 6) :
    (6#64).ule (key &&& 7#64) = false := by
  simp only [BitVec.ule, BitVec.toNat_ofNat, key_and7_toNat, decide_eq_false_iff_not]
  omega

theorem WireType.ofNat?_eq_none_iff (n : ℕ) (hn : n < 8) :
    WireType.ofNat? n = none ↔ 6 ≤ n := by
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | n <;> simp [WireType.ofNat?]

theorem WireType.toNat_of_ofNat?_eq_some {n : ℕ} {wt : WireType}
    (h : WireType.ofNat? n = some wt) :
    wt.toNat = n := by
  rcases n with _ | _ | _ | _ | _ | _ | n <;> simp [WireType.ofNat?] at h
  all_goals (subst h; rfl)

theorem WireType.lt_six_of_ofNat?_eq_some {n : ℕ} {wt : WireType}
    (h : WireType.ofNat? n = some wt) :
    n < 6 := by
  have hto := WireType.toNat_of_ofNat?_eq_some h
  cases wt <;> simp [WireType.toNat] at hto <;> omega

theorem key_tag32_zeroExtend64_eq (key : BitVec 64) (hk : key.toNat < 2 ^ 32) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 key) >>> 3)) =
      BitVec.ofNat 64 (key.toNat / 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hk, BitVec.toNat_ofNat]
  omega

theorem key_tag32_eq_zero_of_lt1 (key : BitVec 64) (hk : key.toNat < 2 ^ 32)
    (h : key.toNat / 8 < 1) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 key) >>> 3)) == 0#64) = true := by
  rw [key_tag32_zeroExtend64_eq key hk]
  have h0 : key.toNat / 8 = 0 := by omega
  rw [h0]
  rfl

theorem key_tag32_ne_zero_of_ge1 (key : BitVec 64) (hk : key.toNat < 2 ^ 32)
    (h : ¬ key.toNat / 8 < 1) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 key) >>> 3)) == 0#64) = false := by
  rw [key_tag32_zeroExtend64_eq key hk]
  simp only [beq_eq_false_iff_ne, ne_eq]
  intro heq
  have hto := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hto
  omega

theorem key_and7_eq_wt (key : BitVec 64) {wt : WireType}
    (hwt : WireType.ofNat? (key.toNat % 8) = some wt) :
    (key &&& 7#64) = BitVec.ofNat 64 wt.toNat := by
  apply BitVec.eq_of_toNat_eq
  have hto := WireType.toNat_of_ofNat?_eq_some hwt
  have hlt : wt.toNat < 2 ^ 64 := by omega
  rw [key_and7_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, hto]

theorem setWidth8_ofNat64 (n : ℕ) :
    (BitVec.ofNat 64 n).setWidth 8 = BitVec.ofNat 8 n :=
  BitVec.setWidth_ofNat_of_le (by decide) n

theorem setWidth32_ofNat64 (n : ℕ) :
    (BitVec.ofNat 64 n).setWidth 32 = BitVec.ofNat 32 n :=
  BitVec.setWidth_ofNat_of_le (by decide) n

theorem pointsTo32_memRegion4_entails_exists_pointsTo64 (a : BitVec 64) (w0 : BitVec 32) :
    (a ↦₃₂ w0) ∗ memRegion (a + 4#64) 4 ⊢ ∃∗ w : BitVec 64, a ↦₆₄ w := by
  sep_interval

theorem pointsTo64_one_entails_pointsTo32_memRegion4 (a : BitVec 64) :
    (a ↦₆₄ 1#64) ⊢ (a ↦₃₂ 1#32) ∗ memRegion (a + 4#64) 4 := by
  rw [pointsTo64_one_split32]; sep_interval

section SplitOpaque
attribute [local irreducible] optVecU8At optU32At

theorem wireSignalMessageAt_split_prevCounter (A : RustAlloc) (g : WireSignalMessageGhost)
    (sp' : BitVec 64) (m : ProtoSignalMessage) :
    wireSignalMessageAt A g (sp' + 176#64) m =
      optU32At (sp' + 280#64) m.previousCounter ∗
      (optVecU8At A g.rk (sp' + 176#64) m.ratchetKey ∗
       optVecU8At A g.ct (sp' + 200#64) m.ciphertext ∗
       optVecU8At A g.pq (sp' + 224#64) m.pqRatchet ∗
       optVecU8At A g.addr (sp' + 248#64) m.addresses ∗
       optU32At (sp' + 272#64) m.counter) := by
  unfold wireSignalMessageAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  apply Entails.antisymm <;> bi_entail

theorem wireSignalMessageAt_split_counter (A : RustAlloc) (g : WireSignalMessageGhost)
    (sp' : BitVec 64) (m : ProtoSignalMessage) :
    wireSignalMessageAt A g (sp' + 176#64) m =
      optU32At (sp' + 272#64) m.counter ∗
      (optVecU8At A g.rk (sp' + 176#64) m.ratchetKey ∗
       optVecU8At A g.ct (sp' + 200#64) m.ciphertext ∗
       optVecU8At A g.pq (sp' + 224#64) m.pqRatchet ∗
       optVecU8At A g.addr (sp' + 248#64) m.addresses ∗
       optU32At (sp' + 280#64) m.previousCounter) := by
  unfold wireSignalMessageAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  apply Entails.antisymm <;> bi_entail

end SplitOpaque

theorem optU32At_some_eq (sp' off off4 : BitVec 64) (v : BitVec 32)
    (ha : sp' + off + 4#64 = sp' + off4 := by bv_omega) :
    ((sp' + off) ↦₃₂ 1#32) ∗ ((sp' + off4) ↦₃₂ v) =
      optU32At (sp' + off) (some v) := by
  unfold optU32At; rw [ha]

section SplitOpaque2
attribute [local irreducible] optVecU8At optU32At

theorem wireSignalMessageAt_split_addr (A : RustAlloc) (g : WireSignalMessageGhost)
    (sp' : BitVec 64) (m : ProtoSignalMessage) :
    wireSignalMessageAt A g (sp' + 176#64) m =
      optVecU8At A g.addr (sp' + 248#64) m.addresses ∗
      (optVecU8At A g.rk (sp' + 176#64) m.ratchetKey ∗
       optVecU8At A g.ct (sp' + 200#64) m.ciphertext ∗
       optVecU8At A g.pq (sp' + 224#64) m.pqRatchet ∗
       optU32At (sp' + 272#64) m.counter ∗
       optU32At (sp' + 280#64) m.previousCounter) := by
  unfold wireSignalMessageAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc, sepConj_comm, sepConj_left_comm]

theorem wireSignalMessageAt_split_rk (A : RustAlloc) (g : WireSignalMessageGhost)
    (sp' : BitVec 64) (m : ProtoSignalMessage) :
    wireSignalMessageAt A g (sp' + 176#64) m =
      optVecU8At A g.rk (sp' + 176#64) m.ratchetKey ∗
      (optVecU8At A g.ct (sp' + 200#64) m.ciphertext ∗
       optVecU8At A g.pq (sp' + 224#64) m.pqRatchet ∗
       optVecU8At A g.addr (sp' + 248#64) m.addresses ∗
       optU32At (sp' + 272#64) m.counter ∗
       optU32At (sp' + 280#64) m.previousCounter) := by
  unfold wireSignalMessageAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem wireSignalMessageAt_split_ct (A : RustAlloc) (g : WireSignalMessageGhost)
    (sp' : BitVec 64) (m : ProtoSignalMessage) :
    wireSignalMessageAt A g (sp' + 176#64) m =
      optVecU8At A g.ct (sp' + 200#64) m.ciphertext ∗
      (optVecU8At A g.rk (sp' + 176#64) m.ratchetKey ∗
       optVecU8At A g.pq (sp' + 224#64) m.pqRatchet ∗
       optVecU8At A g.addr (sp' + 248#64) m.addresses ∗
       optU32At (sp' + 272#64) m.counter ∗
       optU32At (sp' + 280#64) m.previousCounter) := by
  unfold wireSignalMessageAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc, sepConj_comm, sepConj_left_comm]

theorem wireSignalMessageAt_split_pq (A : RustAlloc) (g : WireSignalMessageGhost)
    (sp' : BitVec 64) (m : ProtoSignalMessage) :
    wireSignalMessageAt A g (sp' + 176#64) m =
      optVecU8At A g.pq (sp' + 224#64) m.pqRatchet ∗
      (optVecU8At A g.rk (sp' + 176#64) m.ratchetKey ∗
       optVecU8At A g.ct (sp' + 200#64) m.ciphertext ∗
       optVecU8At A g.addr (sp' + 248#64) m.addresses ∗
       optU32At (sp' + 272#64) m.counter ∗
       optU32At (sp' + 280#64) m.previousCounter) := by
  unfold wireSignalMessageAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc, sepConj_comm, sepConj_left_comm]

end SplitOpaque2

theorem optVecU8At_none_split (A : RustAlloc) (pin : VecPin) (sp' off off8 off16 : BitVec 64)
    (ha8 : sp' + off + 8#64 = sp' + off8 := by bv_omega)
    (ha16 : sp' + off8 + 8#64 = sp' + off16 := by bv_omega) :
    optVecU8At A pin (sp' + off) none =
      ((sp' + off) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
      (∃∗ w1 : BitVec 64, (sp' + off8) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (sp' + off16) ↦₆₄ w2) := by
  have hn : noneCap = 0xFFFFFFFFFFFFFFFF#64 := rfl
  rw [← ha16, ← ha8]; unfold optVecU8At; rw [hn]
  generalize sp' + off = base
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  sep_interval_eq

theorem pointsTo64_emptyVec_eq_vecU8At (A : RustAlloc) (sp' off off8 off16 : BitVec 64)
    (ha8 : sp' + off + 8#64 = sp' + off8 := by bv_omega)
    (ha16 : sp' + off + 16#64 = sp' + off16 := by bv_omega) :
    ((sp' + off) ↦₆₄ 0#64) ∗ ((sp' + off8) ↦₆₄ 1#64) ∗ ((sp' + off16) ↦₆₄ 0#64) =
      vecU8At A (sp' + off) 0#64 1#64 [] := by
  apply Entails.antisymm <;> (unfold vecU8At vecHeader; rw [← ha8, ← ha16]; bi_entail)

theorem optVecU8At_some_unfold (A : RustAlloc) (pin : VecPin) (a : BitVec 64)
    (v0 : List (BitVec 8)) :
    optVecU8At A pin a (some v0) =
      ⌜v0.length ≤ pin.cap.toNat ∧ pin.cap.toNat < 2 ^ 63 ∧ pin.ptr ≠ 0⌝ ∗
      (a ↦₆₄ pin.cap) ∗
      (((a + 8#64) ↦₆₄ pin.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 v0.length) ∗
        (if pin.cap = 0 then emp
         else A.live pin.ptr pin.cap.toNat 1 ∗ (pin.ptr ↦ₛ v0) ∗
           memRegion (pin.ptr + BitVec.ofNat 64 v0.length) (pin.cap.toNat - v0.length))) := by
  dsimp only [optVecU8At, vecU8At, vecHeader]
  generalize (if pin.cap = 0 then emp
    else A.live pin.ptr pin.cap.toNat 1 ∗ (pin.ptr ↦ₛ v0) ∗
      memRegion (pin.ptr + BitVec.ofNat 64 v0.length) (pin.cap.toNat - v0.length)) = buf
  apply Entails.antisymm <;> bi_entail

theorem vecU8At_fold_of_pure (A : RustAlloc) (pin : VecPin) (a : BitVec 64)
    (v0 : List (BitVec 8))
    (hp : v0.length ≤ pin.cap.toNat ∧ pin.cap.toNat < 2 ^ 63 ∧ pin.ptr ≠ 0) :
    (a ↦₆₄ pin.cap) ∗
      (((a + 8#64) ↦₆₄ pin.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 v0.length) ∗
        (if pin.cap = 0 then emp
         else A.live pin.ptr pin.cap.toNat 1 ∗ (pin.ptr ↦ₛ v0) ∗
           memRegion (pin.ptr + BitVec.ofNat 64 v0.length) (pin.cap.toNat - v0.length))) =
      vecU8At A a pin.cap pin.ptr v0 := by
  unfold vecU8At vecHeader
  generalize (if pin.cap = 0 then emp
    else A.live pin.ptr pin.cap.toNat 1 ∗ (pin.ptr ↦ₛ v0) ∗
      memRegion (pin.ptr + BitVec.ofNat 64 v0.length) (pin.cap.toNat - v0.length)) = buf
  apply Entails.antisymm <;> bi_entail

theorem cmn_one_ne_of_lt (cap : BitVec 64) (h : cap.toNat < 2 ^ 63) :
    ((cap + 1#64 == 0#64) = false) ∧ ((cap + 1#64 != 0#64) = true) := by
  have hne : cap + 1#64 ≠ 0#64 := by bv_omega
  exact ⟨beq_eq_false_iff_ne.mpr hne, bne_iff_ne.mpr hne⟩

theorem vecU8At_addr_entails_wireSignalMessageOf (A : RustAlloc) (g : WireSignalMessageGhost)
    (sp' cap0 ptr0 : BitVec 64) (m : ProtoSignalMessage) (v0 : List (BitVec 8)) :
    vecU8At A (sp' + 248#64) cap0 ptr0 v0 ∗
      (optVecU8At A g.rk (sp' + 176#64) m.ratchetKey ∗
       optVecU8At A g.ct (sp' + 200#64) m.ciphertext ∗
       optVecU8At A g.pq (sp' + 224#64) m.pqRatchet ∗
       optU32At (sp' + 272#64) m.counter ∗
       optU32At (sp' + 280#64) m.previousCounter) ⊢
      wireSignalMessageOf A (sp' + 176#64) { m with addresses := some v0 } :=
  (wireSignalMessageAt_split_addr A { g with addr := ⟨cap0, ptr0⟩ } sp'
    { m with addresses := some v0 }) ▸
    wireSignalMessageAt_entails_of A { g with addr := ⟨cap0, ptr0⟩ } (sp' + 176#64)
      { m with addresses := some v0 }

theorem vecU8At_addr_entails_wireSignalMessageLoopOf (A : RustAlloc) (g : WireSignalMessageGhost)
    (sp' cap' ptr' : BitVec 64) (len : ℕ) (m : ProtoSignalMessage) (v : List (BitVec 8))
    (hg : WireGhostCapOk g len) (hcap' : BytesMergeCapOk cap' len) :
    vecU8At A (sp' + 248#64) cap' ptr' v ∗
      (optVecU8At A g.rk (sp' + 176#64) m.ratchetKey ∗
       optVecU8At A g.ct (sp' + 200#64) m.ciphertext ∗
       optVecU8At A g.pq (sp' + 224#64) m.pqRatchet ∗
       optU32At (sp' + 272#64) m.counter ∗
       optU32At (sp' + 280#64) m.previousCounter) ⊢
      wireSignalMessageLoopOf A (sp' + 176#64) len { m with addresses := some v } :=
  (wireSignalMessageAt_split_addr A { g with addr := ⟨cap', ptr'⟩ } sp'
    { m with addresses := some v }) ▸
    wireSignalMessageAt_entails_loopOf A { g with addr := ⟨cap', ptr'⟩ } (sp' + 176#64) len
      { m with addresses := some v } ⟨hg.rk, hg.ct, hg.pq, hcap'⟩

theorem vecU8At_rk_entails_wireSignalMessageOf (A : RustAlloc) (g : WireSignalMessageGhost)
    (sp' cap0 ptr0 : BitVec 64) (m : ProtoSignalMessage) (v0 : List (BitVec 8)) :
    vecU8At A (sp' + 176#64) cap0 ptr0 v0 ∗
      (optVecU8At A g.ct (sp' + 200#64) m.ciphertext ∗
       optVecU8At A g.pq (sp' + 224#64) m.pqRatchet ∗
       optVecU8At A g.addr (sp' + 248#64) m.addresses ∗
       optU32At (sp' + 272#64) m.counter ∗
       optU32At (sp' + 280#64) m.previousCounter) ⊢
      wireSignalMessageOf A (sp' + 176#64) { m with ratchetKey := some v0 } :=
  (wireSignalMessageAt_split_rk A { g with rk := ⟨cap0, ptr0⟩ } sp'
    { m with ratchetKey := some v0 }) ▸
    wireSignalMessageAt_entails_of A { g with rk := ⟨cap0, ptr0⟩ } (sp' + 176#64)
      { m with ratchetKey := some v0 }

theorem vecU8At_rk_entails_wireSignalMessageLoopOf (A : RustAlloc) (g : WireSignalMessageGhost)
    (sp' cap' ptr' : BitVec 64) (len : ℕ) (m : ProtoSignalMessage) (v : List (BitVec 8))
    (hg : WireGhostCapOk g len) (hcap' : BytesMergeCapOk cap' len) :
    vecU8At A (sp' + 176#64) cap' ptr' v ∗
      (optVecU8At A g.ct (sp' + 200#64) m.ciphertext ∗
       optVecU8At A g.pq (sp' + 224#64) m.pqRatchet ∗
       optVecU8At A g.addr (sp' + 248#64) m.addresses ∗
       optU32At (sp' + 272#64) m.counter ∗
       optU32At (sp' + 280#64) m.previousCounter) ⊢
      wireSignalMessageLoopOf A (sp' + 176#64) len { m with ratchetKey := some v } :=
  (wireSignalMessageAt_split_rk A { g with rk := ⟨cap', ptr'⟩ } sp'
    { m with ratchetKey := some v }) ▸
    wireSignalMessageAt_entails_loopOf A { g with rk := ⟨cap', ptr'⟩ } (sp' + 176#64) len
      { m with ratchetKey := some v } ⟨hcap', hg.ct, hg.pq, hg.addr⟩

theorem vecU8At_ct_entails_wireSignalMessageOf (A : RustAlloc) (g : WireSignalMessageGhost)
    (sp' cap0 ptr0 : BitVec 64) (m : ProtoSignalMessage) (v0 : List (BitVec 8)) :
    vecU8At A (sp' + 200#64) cap0 ptr0 v0 ∗
      (optVecU8At A g.rk (sp' + 176#64) m.ratchetKey ∗
       optVecU8At A g.pq (sp' + 224#64) m.pqRatchet ∗
       optVecU8At A g.addr (sp' + 248#64) m.addresses ∗
       optU32At (sp' + 272#64) m.counter ∗
       optU32At (sp' + 280#64) m.previousCounter) ⊢
      wireSignalMessageOf A (sp' + 176#64) { m with ciphertext := some v0 } :=
  (wireSignalMessageAt_split_ct A { g with ct := ⟨cap0, ptr0⟩ } sp'
    { m with ciphertext := some v0 }) ▸
    wireSignalMessageAt_entails_of A { g with ct := ⟨cap0, ptr0⟩ } (sp' + 176#64)
      { m with ciphertext := some v0 }

theorem vecU8At_ct_entails_wireSignalMessageLoopOf (A : RustAlloc) (g : WireSignalMessageGhost)
    (sp' cap' ptr' : BitVec 64) (len : ℕ) (m : ProtoSignalMessage) (v : List (BitVec 8))
    (hg : WireGhostCapOk g len) (hcap' : BytesMergeCapOk cap' len) :
    vecU8At A (sp' + 200#64) cap' ptr' v ∗
      (optVecU8At A g.rk (sp' + 176#64) m.ratchetKey ∗
       optVecU8At A g.pq (sp' + 224#64) m.pqRatchet ∗
       optVecU8At A g.addr (sp' + 248#64) m.addresses ∗
       optU32At (sp' + 272#64) m.counter ∗
       optU32At (sp' + 280#64) m.previousCounter) ⊢
      wireSignalMessageLoopOf A (sp' + 176#64) len { m with ciphertext := some v } :=
  (wireSignalMessageAt_split_ct A { g with ct := ⟨cap', ptr'⟩ } sp'
    { m with ciphertext := some v }) ▸
    wireSignalMessageAt_entails_loopOf A { g with ct := ⟨cap', ptr'⟩ } (sp' + 176#64) len
      { m with ciphertext := some v } ⟨hg.rk, hcap', hg.pq, hg.addr⟩

theorem vecU8At_pq_entails_wireSignalMessageOf (A : RustAlloc) (g : WireSignalMessageGhost)
    (sp' cap0 ptr0 : BitVec 64) (m : ProtoSignalMessage) (v0 : List (BitVec 8)) :
    vecU8At A (sp' + 224#64) cap0 ptr0 v0 ∗
      (optVecU8At A g.rk (sp' + 176#64) m.ratchetKey ∗
       optVecU8At A g.ct (sp' + 200#64) m.ciphertext ∗
       optVecU8At A g.addr (sp' + 248#64) m.addresses ∗
       optU32At (sp' + 272#64) m.counter ∗
       optU32At (sp' + 280#64) m.previousCounter) ⊢
      wireSignalMessageOf A (sp' + 176#64) { m with pqRatchet := some v0 } :=
  (wireSignalMessageAt_split_pq A { g with pq := ⟨cap0, ptr0⟩ } sp'
    { m with pqRatchet := some v0 }) ▸
    wireSignalMessageAt_entails_of A { g with pq := ⟨cap0, ptr0⟩ } (sp' + 176#64)
      { m with pqRatchet := some v0 }

theorem vecU8At_pq_entails_wireSignalMessageLoopOf (A : RustAlloc) (g : WireSignalMessageGhost)
    (sp' cap' ptr' : BitVec 64) (len : ℕ) (m : ProtoSignalMessage) (v : List (BitVec 8))
    (hg : WireGhostCapOk g len) (hcap' : BytesMergeCapOk cap' len) :
    vecU8At A (sp' + 224#64) cap' ptr' v ∗
      (optVecU8At A g.rk (sp' + 176#64) m.ratchetKey ∗
       optVecU8At A g.ct (sp' + 200#64) m.ciphertext ∗
       optVecU8At A g.addr (sp' + 248#64) m.addresses ∗
       optU32At (sp' + 272#64) m.counter ∗
       optU32At (sp' + 280#64) m.previousCounter) ⊢
      wireSignalMessageLoopOf A (sp' + 176#64) len { m with pqRatchet := some v } :=
  (wireSignalMessageAt_split_pq A { g with pq := ⟨cap', ptr'⟩ } sp'
    { m with pqRatchet := some v }) ▸
    wireSignalMessageAt_entails_loopOf A { g with pq := ⟨cap', ptr'⟩ } (sp' + 176#64) len
      { m with pqRatchet := some v } ⟨hg.rk, hg.ct, hcap', hg.addr⟩

private theorem optU32At_none_def (a : BitVec 64) :
    optU32At a none = (a ↦₃₂ 0#32) ∗ memRegion (a + 4#64) 4 := rfl

private theorem optU32At_some_def (a : BitVec 64) (v : BitVec 32) :
    optU32At a (some v) = (a ↦₃₂ 1#32) ∗ ((a + 4#64) ↦₃₂ v) := rfl

section LoopBodyOpaqueFields
attribute [local irreducible] vecU8At optVecU8At optU32At wireSignalMessageAt

theorem tag_ge7_conds (tag : ℕ) (hge : 7 ≤ tag) (hlt : tag < 2 ^ 32) :
    let w1 := (BitVec.ofNat 64 tag).setWidth 32
    ((w1 == 1#32) = false) ∧ ((w1 == 2#32) = false) ∧
    ((w1 == 3#32) = false) ∧ ((w1 != 3#32) = true) ∧
    ((w1 == 4#32) = false) ∧ ((w1 == 5#32) = false) ∧
    ((w1 == 6#32) = false) ∧ ((w1 != 6#32) = true) := by
  dsimp only
  rw [setWidth32_ofNat64]
  have h1 : BitVec.ofNat 32 tag ≠ 1#32 := by bv_omega
  have h2 : BitVec.ofNat 32 tag ≠ 2#32 := by bv_omega
  have h3 : BitVec.ofNat 32 tag ≠ 3#32 := by bv_omega
  have h4 : BitVec.ofNat 32 tag ≠ 4#32 := by bv_omega
  have h5 : BitVec.ofNat 32 tag ≠ 5#32 := by bv_omega
  have h6 : BitVec.ofNat 32 tag ≠ 6#32 := by bv_omega
  exact ⟨beq_eq_false_iff_ne.mpr h1, beq_eq_false_iff_ne.mpr h2,
    beq_eq_false_iff_ne.mpr h3, bne_iff_ne.mpr h3,
    beq_eq_false_iff_ne.mpr h4, beq_eq_false_iff_ne.mpr h5,
    beq_eq_false_iff_ne.mpr h6, bne_iff_ne.mpr h6⟩

theorem loopExitMem_ok_intro (A : RustAlloc) (sp' ptr : BitVec 64) (bs : List (BitVec 8))
    (m : ProtoSignalMessage) :
    sliceCursorAt (sp' + 160#64) ptr bs ∗
      ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗ memRegion (sp' + 296#64) 48 ∗
      A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
      wireSignalMessageOf A (sp' + 176#64) m ⊢
      loopExitMem A sp' ptr bs 0#64 (some m) := by
  unfold loopExitMem sliceCursorAt; dsimp only
  rw [pure_true_emp rfl, emp_sepConj]
  sep_interval

theorem cons_len_bv64_ne_zero (b0 : BitVec 8) (bs1 : List (BitVec 8))
    (hlen : (b0 :: bs1).length < 2 ^ 63) :
    ((BitVec.ofNat 64 (b0 :: bs1).length == 0#64) = false) ∧
    ((BitVec.ofNat 64 (b0 :: bs1).length != 0#64) = true) := by
  have hpos : 0 < (b0 :: bs1).length := by simp
  have hne : BitVec.ofNat 64 (b0 :: bs1).length ≠ 0#64 := by bv_omega
  exact ⟨beq_eq_false_iff_ne.mpr hne, bne_iff_ne.mpr hne⟩

theorem decodeVarintSlow_tail_cps_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : ProtoSignalMessage} {res : Option ProtoSignalMessage}
    (hpc : s.pc = (blkPl_85).base + 0x284#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint bs = some (key, rest) →
      s1.pc = (blkPl_85).base + 0x150#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      s1.readReg64 .x24 = key →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (sliceCursorAfter (sp' + 160#64) ptr bs rest ∗
          ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
          memRegion (sp' + 296#64) 48 ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
          wireSignalMessageLoopOf A (sp' + 176#64) bs.length m)
        (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr bs res)
        (tryFromQp s0))
    (hnone : decodeVarint bs = none → res = none) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr bs ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopOf A (sp' + 176#64) bs.length m)
      (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr bs res)
      (tryFromQp s0) := by
  have hcall := hS.decodeVarintSlow
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs.x29
  have hstack := stackAt_sub_split sp' (64 + 2 * extHookStack) (skipFieldStackX 100)
  unfold sliceCursorAt
  simp only [hstack, sepConj_assoc]
  refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ varintSlowName) ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hcl1
  refine SepWPp.call_tryFrom_placed (sp' + 288#64, sp' + 160#64, ptr, bs) hcall
    (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
    (ret_pc := (blkPl_85).base + 652#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗ ((sp' + 160#64) ↦₆₄ ptr) ∗
      ((sp' + 160#64 + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (ptr ↦ₛ bs) ∗
      A.pool ∗ stackAt sp' (64 + 2 * extHookStack))
    (φ := bs.length < 18446744073709551616)
    (by simp only [decodeVarintSlowSpecWithStack, hsp_eq, arm64_norm])
    (by omega)
    (by sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  have hregs2 : LoopRegs sp' x19 x20 x21 x23 s2 :=
    LoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
       by simpa [arm64_norm] using hregs.x19_eq⟩
      hsp2 hcs2
  dsimp only [decodeVarintSlowSpecWithStack]
  rw [VarintBridge.decodeVarint_eq_varintSlow bs]
  cases hd : decodeVarint bs with
  | some p =>
    rcases p with ⟨key, rest⟩
    dsimp only [Option.map]
    obtain ⟨k, _, hkl, hrest⟩ := decodeVarint_suffix hd
    have hlen_sub : bs.length - (bs.length - rest.length) = rest.length := by
      rw [hrest, List.length_drop]; omega
    rw [hlen_sub, sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun ⟨hx0_2, hx1_2⟩ => ?_)
    have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    have hx1_2' : s2.readReg64 (Reg.gpr 1#5) = key := hx1_2
    refine SepWPp.of_sepWP_placed hcl2 (mid := (blkPl_85).base + 336#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
    intro hcl3
    refine SepWPp.mono_pre ?_
      (hcont key rest _ hd
        (by simp only [arm64_norm])
        (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
         by simpa [arm64_norm] using hregs2.x19_eq⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl3
        (by simpa [arm64_norm] using htr2.trans htr)
        (by simp only [arm64_norm]))
    unfold sliceCursorAfter
    simp only [hstack, hsp_eq, arm64_norm]
    bi_entail
  | none =>
    dsimp only [Option.map]
    rw [hnone hd, sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun ⟨hx0_1, hx1_ne⟩ => ?_)
    have hx0_1' : s2.readReg64 (Reg.gpr 0#5) = 1#64 := hx0_1
    refine SepWPp.of_sepWP_end_placed hcl2 ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
    intro hcl3
    refine ⟨⟨⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
      by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
      by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
      by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
      by simpa [arm64_norm] using hregs2.x19_eq⟩,
      by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
      hcl3, by simpa [arm64_norm] using htr2.trans htr⟩, ?_⟩
    simp only [hsp_eq, arm64_norm]
    exact Entails.trans (by sep_interval)
      (loopExitMem_err_loop_intro A sp' ptr bs (s2.readReg64 (Reg.gpr 1#5)) hx1_ne 0 bs.length m)

theorem decodeVarintSlice_tail_cps_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hvarint : DecodeVarintSliceOkWPlaced A H)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : ProtoSignalMessage} {res : Option ProtoSignalMessage}
    (hpc : s.pc = (blkPl_85).base + 0x11c#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hx28 : s.readReg64 .x28 = sp' + 160#64)
    (hx27 : s.readReg64 .x27 = sp' + 168#64)
    (hx1 : s.readReg64 .x1 = ptr)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hpre_slice : VarintSlicePre bs)
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint bs = some (key, rest) →
      s1.pc = (blkPl_85).base + 0x150#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      s1.readReg64 .x24 = key →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (sliceCursorAfter (sp' + 160#64) ptr bs rest ∗
          ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
          memRegion (sp' + 296#64) 48 ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
          wireSignalMessageLoopOf A (sp' + 176#64) bs.length m)
        (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr bs res)
        (tryFromQp s0))
    (hnone : decodeVarint bs = none → res = none) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr bs ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopOf A (sp' + 176#64) bs.length m)
      (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr bs res)
      (tryFromQp s0) := by
  have hcall := hvarint
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs.x29
  have h28 : s.readReg64 (Reg.gpr 28#5) = sp' + 160#64 := hx28
  have h27 : s.readReg64 (Reg.gpr 27#5) = sp' + 168#64 := hx27
  have h1 : s.readReg64 (Reg.gpr 1#5) = ptr := hx1
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 bs.length := hx2
  have hx2_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hstack := stackAt_sub_split sp' decodeVarintSliceStackX (skipFieldStackX 100)
  unfold sliceCursorAt
  simp only [hstack, memRegion48_split24 sp', sepConj_assoc]
  refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ decodeVarintSliceName) ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hcl1
  refine SepWPp.call_tryFrom_placed ⟨sp' + 296#64, ptr, bs⟩ hcall
    (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
    (ret_pc := (blkPl_85).base + 292#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := memRegion (sp' + 296#64) 24 ∗ (ptr ↦ₛ bs) ∗
      A.pool ∗ stackAt sp' decodeVarintSliceStackX)
    (φ := bs.length < 9223372036854775808 ∧ VarintSlicePre bs)
    (by simp only [decodeVarintSliceSpecX, hsp_eq, h1, h2, hx2_nat, arm64_norm])
    ⟨hlen, hpre_slice⟩
    (by sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  have hregs2 : LoopRegs sp' x19 x20 x21 x23 s2 :=
    LoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
       by simpa [arm64_norm] using hregs.x19_eq⟩
      hsp2 hcs2
  have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs2.x29
  have h28_2 : s2.readReg64 (Reg.gpr 28#5) = sp' + 160#64 := by
    simpa [arm64_norm, h28] using hcs2.2.2.2.2.2.2.2.2.2.1
  have h27_2 : s2.readReg64 (Reg.gpr 27#5) = sp' + 168#64 := by
    simpa [arm64_norm, h27] using hcs2.2.2.2.2.2.2.2.2.1
  dsimp only [decodeVarintSliceSpecX]
  cases hd : decodeVarint bs with
  | some p =>
    rcases p with ⟨key, rest⟩
    dsimp only [varintSliceResultAt]
    obtain ⟨k, _, hkl, hrest⟩ := decodeVarint_suffix hd
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    have hlen64 : bs.length < 2 ^ 64 := by omega
    have hrest64 : rest.length < 2 ^ 64 := by omega
    have hsub64 : bs.length - rest.length < 2 ^ 64 := by omega
    have hsub_bv :
        BitVec.ofNat 64 bs.length - BitVec.ofNat 64 (bs.length - rest.length) =
          BitVec.ofNat 64 rest.length := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hlen64, Nat.mod_eq_of_lt hsub64, Nat.mod_eq_of_lt hrest64]
      omega
    have hult_false :
        (BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 (bs.length - rest.length)) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64, Nat.mod_eq_of_lt hsub64,
        decide_eq_false_iff_not]
      omega
    rw [pointsTo64_zero_split32 (sp' + 296#64)]
    simp only [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    refine SepWPp.of_sepWP_placed hcl2 (mid := (blkPl_85).base + 336#64) ?_
    wp_steps
    wp_if hcc
    · exfalso
      rw [← hrest] at hcc
      exact Bool.false_ne_true (hult_false.symm.trans hcc)
    · wp_steps
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
      intro hcl3
      refine SepWPp.mono_pre ?_
        (hcont key rest _ hd
          (by simp only [arm64_norm])
          (by simp only [hrun2, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
           by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
           by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
           by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
           by simpa [arm64_norm] using hregs2.x19_eq⟩
          (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
          hcl3
          (by simpa [arm64_norm] using htr2.trans htr)
          (by simp only [arm64_norm]))
      unfold sliceCursorAfter
      simp only [← hrest, hsub_bv, hstack, hsp_eq, arm64_norm]
      sep_interval
  | none =>
    dsimp only [varintSliceResultAt]
    rw [hnone hd, pointsTo64_one_split32 (sp' + 296#64), sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      sepConj_pure_left_comm]
    refine SepWPp.exists_pre (fun e => SepWPp.pure_pre (fun he_ne => ?_))
    refine SepWPp.of_sepWP_end_placed hcl2 ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
    intro hcl3
    refine ⟨⟨⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
      by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
      by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
      by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
      by simpa [arm64_norm] using hregs2.x19_eq⟩,
      by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
      hcl3, by simpa [arm64_norm] using htr2.trans htr⟩, ?_⟩
    simp only [hsp_eq, arm64_norm]
    exact Entails.trans (by sep_interval)
      (loopExitMem_err_loop_intro A sp' ptr bs e he_ne 0 bs.length m)

theorem decodeVarintMulti_cps_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hvarint : DecodeVarintSliceOkWPlaced A H)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : ProtoSignalMessage} {res : Option ProtoSignalMessage}
    (hpc : s.pc = (blkPl_85).base + 0x108#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hx28 : s.readReg64 .x28 = sp' + 160#64)
    (hx27 : s.readReg64 .x27 = sp' + 168#64)
    (hx1 : s.readReg64 .x1 = ptr)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hne : bs ≠ [])
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint bs = some (key, rest) →
      s1.pc = (blkPl_85).base + 0x150#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      s1.readReg64 .x24 = key →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (sliceCursorAfter (sp' + 160#64) ptr bs rest ∗
          ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
          memRegion (sp' + 296#64) 48 ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
          wireSignalMessageLoopOf A (sp' + 176#64) bs.length m)
        (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr bs res)
        (tryFromQp s0))
    (hnone : decodeVarint bs = none → res = none) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr bs ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopOf A (sp' + 176#64) bs.length m)
      (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr bs res)
      (tryFromQp s0) := by
  have hslice := @decodeVarintSlice_tail_cps_placed _ A H hvarint s0
  have hslow := @decodeVarintSlow_tail_cps_placed _ A H hS s0
  have h1 : s.readReg64 (Reg.gpr 1#5) = ptr := hx1
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 bs.length := hx2
  have hlen_pos : 1 ≤ bs.length := List.length_pos_of_ne_nil hne
  have hlen64 : bs.length < 2 ^ 64 := by omega
  by_cases hlen11 : 11 ≤ bs.length
  · have hhi : (10#64).ult (BitVec.ofNat 64 bs.length) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64, decide_eq_true_eq]
      omega
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 284#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hcl1
    exact hslice
      (by simp only [arm64_norm])
      (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
       by simpa [arm64_norm] using hregs.x19_eq⟩
      (by simpa [arm64_norm] using hx28)
      (by simpa [arm64_norm] using hx27)
      (by simpa [arm64_norm] using hx1)
      (by simpa [arm64_norm] using hx2)
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
      hcl1
      (by simpa [arm64_norm] using htr)
      hlen
      (Or.inl hlen11)
      hcont hnone
  · have hhi : (10#64).ult (BitVec.ofNat 64 bs.length) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64, decide_eq_false_iff_not]
      omega
    have hlast_addr :
        ptr + BitVec.ofNat 64 bs.length + bv% (2 ^ 64 - 1) =
          ptr + BitVec.ofNat 64 (bs.length - 1) := by
      have heq : bs.length = (bs.length - 1) + 1 := by omega
      have h1_eq : BitVec.ofNat 64 bs.length = BitVec.ofNat 64 (bs.length - 1) + 1#64 := by
        conv_lhs => rw [heq]
        exact BitVec.ofNat_add (bs.length - 1) 1
      rw [h1_eq]
      bv_omega
    by_cases hlast : (bs.getLast hne).toNat ≤ 0x7F
    · have hbit31 := (signExtend32_bit31_eq_false_iff (bs.getLast hne)).mpr hlast
      unfold sliceCursorAt
      rw [pointsToBytes_split_last ptr bs hne, ← hlast_addr]
      simp only [sepConj_assoc]
      refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 284#64) ?_
      wp_steps
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
      intro hcl1
      refine SepWPp.mono_pre ?_
        (hslice
          (by simp only [arm64_norm])
          (by simp only [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
           by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
           by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
           by simpa [arm64_norm] using hregs.x19_eq⟩
          (by simpa [arm64_norm] using hx28)
          (by simpa [arm64_norm] using hx27)
          (by simpa [arm64_norm] using hx1)
          (by simpa [arm64_norm] using hx2)
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hcl1
          (by simpa [arm64_norm] using htr)
          hlen
          (Or.inr ⟨hne, hlast⟩)
          hcont hnone)
      apply entails_of_eq
      unfold sliceCursorAt
      rw [pointsToBytes_split_last ptr bs hne, ← hlast_addr]
      simp only [arm64_norm]
    · have hbit31 := (signExtend32_bit31_eq_true_iff (bs.getLast hne)).mpr (by omega)
      unfold sliceCursorAt
      rw [pointsToBytes_split_last ptr bs hne, ← hlast_addr]
      simp only [sepConj_assoc]
      refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 644#64) ?_
      wp_steps
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
      intro hcl1
      refine SepWPp.mono_pre ?_
        (hslow
          (by simp only [arm64_norm])
          (by simp only [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
           by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
           by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
           by simpa [arm64_norm] using hregs.x19_eq⟩
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hcl1
          (by simpa [arm64_norm] using htr)
          hlen hcont hnone)
      apply entails_of_eq
      unfold sliceCursorAt
      rw [pointsToBytes_split_last ptr bs hne, ← hlast_addr]
      simp only [arm64_norm]

theorem decodeVarint_inlined_cps_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hvarint : DecodeVarintSliceOkWPlaced A H)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : ProtoSignalMessage} {res : Option ProtoSignalMessage}
    (hpc : s.pc = (blkPl_85).base + 0x0f0#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hx28 : s.readReg64 .x28 = sp' + 160#64)
    (hx27 : s.readReg64 .x27 = sp' + 168#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : (b0 :: bs1).length < 2 ^ 63)
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint (b0 :: bs1) = some (key, rest) →
      s1.pc = (blkPl_85).base + 0x150#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      s1.readReg64 .x24 = key →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (sliceCursorAfter (sp' + 160#64) ptr (b0 :: bs1) rest ∗
          ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
          memRegion (sp' + 296#64) 48 ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
          wireSignalMessageLoopOf A (sp' + 176#64) (b0 :: bs1).length m)
        (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr (b0 :: bs1) res)
        (tryFromQp s0))
    (hnone : decodeVarint (b0 :: bs1) = none → res = none) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr (b0 :: bs1) ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopOf A (sp' + 176#64) (b0 :: bs1).length m)
      (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr (b0 :: bs1) res)
      (tryFromQp s0) := by
  have hmulti := @decodeVarintMulti_cps_placed _ A H hS hvarint s0
  have h28 : s.readReg64 (Reg.gpr 28#5) = sp' + 160#64 := hx28
  have h27 : s.readReg64 (Reg.gpr 27#5) = sp' + 168#64 := hx27
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 (b0 :: bs1).length := hx2
  by_cases hb0 : b0.toNat ≤ 0x7F
  · have hbit63 := (signExtend64_bit63_eq_false_iff b0).mpr hb0
    have hd := decodeVarint_cons_of_le b0 bs1 hb0
    have hsub1 :
        BitVec.ofNat 64 (bs1.length + 1) - 1#64 =
          BitVec.ofNat 64 bs1.length := by
      have h1_eq : BitVec.ofNat 64 (bs1.length + 1) = BitVec.ofNat 64 bs1.length + 1#64 :=
        BitVec.ofNat_add bs1.length 1
      rw [h1_eq]
      bv_omega
    unfold sliceCursorAt
    rw [pointsToBytes_cons ptr b0 bs1]
    simp only [sepConj_assoc]
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 336#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hcl1
    have hse := signExtend64_eq_zeroExtend64_of_le b0 hb0
    refine SepWPp.mono_pre ?_
      (hcont (b0.zeroExtend 64) bs1 _ hd
        (by simp only [arm64_norm])
        (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
         by simpa [arm64_norm] using hregs.x19_eq⟩
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1
        (by simpa [arm64_norm] using htr)
        (by simp only [hse, arm64_norm]))
    apply entails_of_eq
    unfold sliceCursorAfter
    rw [pointsToBytes_cons ptr b0 bs1]
    simp only [List.length_cons, Nat.add_sub_cancel_left, hsub1, arm64_norm]
  · have hbit63 := (signExtend64_bit63_eq_true_iff b0).mpr (by omega)
    unfold sliceCursorAt
    rw [pointsToBytes_cons ptr b0 bs1]
    simp only [sepConj_assoc]
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 264#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hcl1
    refine SepWPp.mono_pre ?_
      (hmulti
        (by simp only [arm64_norm])
        (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
         by simpa [arm64_norm] using hregs.x19_eq⟩
        (by simpa [arm64_norm] using hx28)
        (by simpa [arm64_norm] using hx27)
        (by simp only [arm64_norm])
        (by simpa [arm64_norm] using hx2)
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1
        (by simpa [arm64_norm] using htr)
        (List.cons_ne_nil b0 bs1)
        hlen hcont hnone)
    apply entails_of_eq
    unfold sliceCursorAt
    rw [pointsToBytes_cons ptr b0 bs1]
    simp only [arm64_norm]

theorem decodeKey_tail_cps_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr key : BitVec 64}
    {bs rest : List (BitVec 8)} {m : ProtoSignalMessage} {res : Option ProtoSignalMessage}
    (hdv : decodeVarint bs = some (key, rest))
    (hpc : s.pc = (blkPl_85).base + 0x150#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hx24 : s.readReg64 .x24 = key)
    (hcont : ∀ (tag : ℕ) (wt : WireType) (s1 : State),
      decodeKey bs = some ((tag, wt), rest) →
      s1.pc = (blkPl_85).base + 0x16c#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      s1.readReg64 .x0 = BitVec.ofNat 64 wt.toNat →
      s1.readReg64 .x1 = BitVec.ofNat 64 tag →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (sliceCursorAfter (sp' + 160#64) ptr bs rest ∗
          ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
          memRegion (sp' + 296#64) 48 ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
          wireSignalMessageLoopOf A (sp' + 176#64) bs.length m)
        (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr bs res)
        (tryFromQp s0))
    (hnone : decodeKey bs = none → res = none) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAfter (sp' + 160#64) ptr bs rest ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopOf A (sp' + 176#64) bs.length m)
      (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr bs res)
      (tryFromQp s0) := by
  have herr := @decodeErrorFrom_tail_wp_placed _ A H hS s0
  have h24 : s.readReg64 (Reg.gpr 24#5) = key := hx24
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs.x29
  have h26 : s.readReg64 (Reg.gpr 26#5) = 0x8000000000000002#64 := hregs.x26
  by_cases hkey32 : 2 ^ 32 ≤ key.toNat
  · have hdk : decodeKey bs = none := by
      unfold decodeKey
      rw [hdv]
      simp only [hkey32, ↓reduceIte]
    have hres := hnone hdk
    subst hres
    have hcbnz := key_lsr32_ne_zero_of_ge key hkey32
    rw [memRegion48_split_296_304_312 sp']
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w1 => SepWPp.exists_pre (fun w0 => ?_))
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 700#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hcl1
    refine SepWPp.mono_pre ?_
      (herr (w0 := w0) (mErr := m)
        (by simp only [arm64_norm])
        (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
         by simpa [arm64_norm] using hregs.x19_eq⟩
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1
        (by simpa [arm64_norm] using htr)
        (by simp only [KindNoHeap, arm64_norm]))
    exact Entails.trans (by bi_entail) (decodeKey_err_entails A sp' ptr w0 key bs rest bs.length m)
  · have hkey_lt : key.toNat < 2 ^ 32 := by omega
    have hcbnz := key_lsr32_eq_zero_of_lt key hkey_lt
    cases hwt : WireType.ofNat? (key.toNat % 8) with
    | none =>
      have hdk : decodeKey bs = none := by
        unfold decodeKey
        rw [hdv]
        simp only [hkey32, ↓reduceIte, hwt]
      have hres := hnone hdk
      subst hres
      have hge6 : 6 ≤ key.toNat % 8 := (WireType.ofNat?_eq_none_iff (key.toNat % 8) (by omega)).mp hwt
      have hbcs := key_and7_ule6_of_ge key hge6
      rw [memRegion48_split_296_304_312 sp']
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_pre (fun w1 => SepWPp.exists_pre (fun w0 => ?_))
      refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 700#64) ?_
      wp_steps
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
      intro hcl1
      refine SepWPp.mono_pre ?_
        (herr (w0 := w0) (mErr := m)
          (by simp only [arm64_norm])
          (by simp only [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
           by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
           by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
           by simpa [arm64_norm] using hregs.x19_eq⟩
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hcl1
          (by simpa [arm64_norm] using htr)
          (by simp only [KindNoHeap, arm64_norm]))
      exact Entails.trans (by bi_entail) (decodeKey_err_entails A sp' ptr w0 (key &&& 7#64) bs rest bs.length m)
    | some wt =>
      have hlt6 : key.toNat % 8 < 6 := WireType.lt_six_of_ofNat?_eq_some hwt
      have hbcs := key_and7_ule6_of_lt key hlt6
      by_cases htag0 : key.toNat / 8 < 1
      · have hdk : decodeKey bs = none := by
          unfold decodeKey
          rw [hdv]
          simp only [hkey32, ↓reduceIte, hwt, htag0]
        have hres := hnone hdk
        subst hres
        have hcbz := key_tag32_eq_zero_of_lt1 key hkey_lt htag0
        rw [memRegion48_split8 sp', memRegion_eight (sp' + 296#64)]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        refine SepWPp.exists_pre (fun w0 => ?_)
        refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 700#64) ?_
        wp_steps
        refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
        intro hcl1
        refine SepWPp.mono_pre ?_
          (herr (w0 := w0) (mErr := m)
            (by simp only [arm64_norm])
            (by simp only [hrun, arm64_norm])
            ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
             by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
             by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
             by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
             by simpa [arm64_norm] using hregs.x19_eq⟩
            (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
            hcl1
            (by simpa [arm64_norm] using htr)
            (by simp only [KindNoHeap, arm64_norm]))
        unfold sliceCursorAfter
        simp only [arm64_norm]
        exact trans_sub (wireSignalMessageLoopOf_entails_of A (sp' + 176#64) bs.length m)
          (hpost := by sep_interval)
      · have hdk : decodeKey bs = some ((key.toNat / 8, wt), rest) := by
          unfold decodeKey
          rw [hdv]
          simp only [hkey32, ↓reduceIte, hwt, htag0]
        have hcbz := key_tag32_ne_zero_of_ge1 key hkey_lt htag0
        refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 364#64) ?_
        wp_steps
        refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
        intro hcl1
        have htag_eq := key_tag32_zeroExtend64_eq key hkey_lt
        have hand7_eq := key_and7_eq_wt key hwt
        exact hcont (key.toNat / 8) wt _ hdk
          (by simp only [arm64_norm])
          (by simp only [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
           by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
           by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
           by simpa [arm64_norm] using hregs.x19_eq⟩
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hcl1
          (by simpa [arm64_norm] using htr)
          (by simp only [arm64_norm]; exact hand7_eq)
          (by simp only [arm64_norm]; exact htag_eq)

theorem decodeKey_cps_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hvarint : DecodeVarintSliceOkWPlaced A H)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : ProtoSignalMessage} {res : Option ProtoSignalMessage}
    (hpc : s.pc = (blkPl_85).base + 0x0f0#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hx28 : s.readReg64 .x28 = sp' + 160#64)
    (hx27 : s.readReg64 .x27 = sp' + 168#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : (b0 :: bs1).length < 2 ^ 63)
    (hcont : ∀ (tag : ℕ) (wt : WireType) (rest : List (BitVec 8)) (s1 : State),
      decodeKey (b0 :: bs1) = some ((tag, wt), rest) →
      s1.pc = (blkPl_85).base + 0x16c#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      s1.readReg64 .x0 = BitVec.ofNat 64 wt.toNat →
      s1.readReg64 .x1 = BitVec.ofNat 64 tag →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (sliceCursorAfter (sp' + 160#64) ptr (b0 :: bs1) rest ∗
          ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
          memRegion (sp' + 296#64) 48 ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
          wireSignalMessageLoopOf A (sp' + 176#64) (b0 :: bs1).length m)
        (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr (b0 :: bs1) res)
        (tryFromQp s0))
    (hnone : decodeKey (b0 :: bs1) = none → res = none) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr (b0 :: bs1) ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopOf A (sp' + 176#64) (b0 :: bs1).length m)
      (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr (b0 :: bs1) res)
      (tryFromQp s0) := by
  refine decodeVarint_inlined_cps_placed hS hvarint hpc hrun hregs hx28 hx27 hx2 hsp hcl htr hlen
    (fun key rest s1 hdv hpc1 hrun1 hregs1 hsp1 hcl1 htr1 hx24_1 =>
      decodeKey_tail_cps_placed hS hdv hpc1 hrun1 hregs1 hsp1 hcl1 htr1 hx24_1
        (fun tag wt s2 hdk => hcont tag wt rest s2 hdk)
        hnone)
    (fun hdv_none => hnone (by simp [decodeKey, hdv_none]))

theorem mergeSkipField_cps_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hskip : SkipFieldOkWPlaced A H)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {tag : ℕ} {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoSignalMessage} {res : Option ProtoSignalMessage}
    (hpc : s.pc = (blkPl_85).base + 0x0d0#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (htag_lt : tag < 2 ^ 32)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (rest : List (BitVec 8)) (s1 : State),
      skipField (2 * bs.length + 2) 100 tag wt bs = some rest →
      s1.pc = (blkPl_85).base + 0x0e0#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (sliceCursorAfter (sp' + 160#64) ptr bs rest ∗
          ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
          memRegion (sp' + 296#64) 48 ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
          wireSignalMessageLoopOf A (sp' + 176#64) rest.length m)
        (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr bs res)
        (tryFromQp s0))
    (hnone : skipField (2 * bs.length + 2) 100 tag wt bs = none → res = none) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr bs ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopOf A (sp' + 176#64) bs.length m)
      (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr bs res)
      (tryFromQp s0) := by
  have hcall := hskip
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs.x29
  have h0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0
  have h1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 tag := hx1
  refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).ρ skipFieldName) ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hcl1
  refine SepWPp.call_tryFrom_placed ⟨wt, tag, 100, sp' + 288#64, sp' + 160#64, ptr, bs⟩ hcall
    (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
    (ret_pc := (blkPl_85).base + 220#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗ sliceCursorAt (sp' + 160#64) ptr bs ∗
      A.pool ∗ stackAt sp' (skipFieldStackX 100))
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      (BitVec.ofNat 64 tag).setWidth 32 = BitVec.ofNat 32 tag ∧ tag < 4294967296 ∧
      sp' + 352#64 - 64#64 = sp' + 288#64 ∧
      (100#64 : BitVec 64).setWidth 32 = 100#32 ∧ 100 < 4294967296 ∧ bs.length < 9223372036854775808)
    (by simp only [skipFieldSpecX, hsp_eq, h0, h1, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, setWidth32_ofNat64 tag, htag_lt, by bv_omega, rfl, by decide, hlen⟩
    (by sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  have hregs2 : LoopRegs sp' x19 x20 x21 x23 s2 :=
    LoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
       by simpa [arm64_norm] using hregs.x19_eq⟩
      hsp2 hcs2
  dsimp only [skipFieldSpecX]
  cases hs : skipField (2 * bs.length + 2) 100 tag wt bs with
  | some rest =>
    dsimp only
    obtain ⟨k, hkl, hrest⟩ := skipField_suffix hs
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_0 => ?_)
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine SepWPp.of_sepWP_placed hcl2 (mid := (blkPl_85).base + 224#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
    intro hcl3
    refine SepWPp.mono_pre ?_
      (hcont rest _ hs
        (by simp only [arm64_norm])
        (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
         by simpa [arm64_norm] using hregs2.x19_eq⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl3
        (by simpa [arm64_norm] using htr2.trans htr))
    simp only [hsp_eq, arm64_norm]
    exact trans_sub (wireSignalMessageLoopOf_mono A (sp' + 176#64) m hrest_le)
  | none =>
    dsimp only
    have hres := hnone hs
    subst hres
    rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_ne => ?_)
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    refine SepWPp.of_sepWP_end_placed hcl2 ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
    intro hcl3
    refine ⟨⟨⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
      by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
      by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
      by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
      by simpa [arm64_norm] using hregs2.x19_eq⟩,
      by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
      hcl3, by simpa [arm64_norm] using htr2.trans htr⟩, ?_⟩
    simp only [hsp_eq, arm64_norm]
    exact Entails.trans (by sep_interval)
      (loopExitMem_err_loop_intro A sp' ptr bs (s2.readReg64 (Reg.gpr 0#5)) hx0_ne 0 bs.length m)

theorem initOptU32_prevCounter_cps_placed [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State} {sp' x19 x20 x21 x23 : BitVec 64}
    {u : Option (BitVec 32)} {F : SepProp}
    {Q : State → SepProp → Prop} {Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_85).base + 0x18c#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hcont : ∀ (s1 : State),
      s1.pc = (blkPl_85).base + 0x198#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (((sp' + 280#64) ↦₃₂ 1#32) ∗ memRegion (sp' + 284#64) 4 ∗ F) Q Qp) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (optU32At (sp' + 280#64) u ∗ F) Q Qp := by
  have hsp_eq : s.sp = sp' := hregs.sp
  have h25 : s.readReg64 (Reg.gpr 25#5) = 1#64 := hregs.x25
  have ha : sp' + 280#64 + 4#64 = sp' + 284#64 := by bv_omega
  cases u with
  | none =>
    rw [optU32At_none_def, ha, sepConj_assoc]
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 404#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hcl1
    refine SepWPp.mono_pre (P' := (∃∗ w : BitVec 64, (sp' + 280#64) ↦₆₄ w) ∗ F) (by sep_interval) ?_
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_pre (fun w => ?_)
    refine SepWPp.of_sepWP_placed hcl1 (mid := (blkPl_85).base + 408#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hcl2
    refine SepWPp.mono_pre ?_
      (hcont _
        (by simp only [arm64_norm])
        (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
         by simpa [arm64_norm] using hregs.x19_eq⟩
        (by simp only [arm64_norm])
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl2 htr)
    rw [pointsTo64_one_split32]; sep_interval
  | some v0 =>
    rw [optU32At_some_def, ha, sepConj_assoc]
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 408#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hcl1
    refine SepWPp.mono_pre ?_
      (hcont _
        (by simp only [arm64_norm])
        (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
         by simpa [arm64_norm] using hregs.x19_eq⟩
        (by simp only [arm64_norm])
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr)
    sep_interval

theorem mergePrevCounter_cps_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hint32 : Int32MergeOkWPlaced A H)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoSignalMessage} {res : Option ProtoSignalMessage}
    (hpc : s.pc = (blkPl_85).base + 0x18c#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (v : BitVec 32) (rest : List (BitVec 8)) (s1 : State),
      mergeUint32 wt bs = some (v, rest) →
      s1.pc = (blkPl_85).base + 0x0e0#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (sliceCursorAfter (sp' + 160#64) ptr bs rest ∗
          ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
          memRegion (sp' + 296#64) 48 ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
          wireSignalMessageLoopOf A (sp' + 176#64) rest.length { m with previousCounter := some v })
        (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr bs res)
        (tryFromQp s0))
    (hnone : mergeUint32 wt bs = none → res = none) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr bs ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopOf A (sp' + 176#64) bs.length m)
      (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr bs res)
      (tryFromQp s0) := by
  rw [wireSignalMessageLoopOf_def]
  simp only [sepExists_sepConj_right, sepConj_pure_left_comm]
  refine SepWPp.exists_pre (fun g => SepWPp.pure_pre (fun hg => ?_))
  rw [wireSignalMessageAt_split_prevCounter A g sp' m]
  let F_msg := optVecU8At A g.rk (sp' + 176#64) m.ratchetKey ∗
    optVecU8At A g.ct (sp' + 200#64) m.ciphertext ∗
    optVecU8At A g.pq (sp' + 224#64) m.pqRatchet ∗
    optVecU8At A g.addr (sp' + 248#64) m.addresses ∗
    optU32At (sp' + 272#64) m.counter
  refine SepWPp.mono_pre
    (P' := optU32At (sp' + 280#64) m.previousCounter ∗
      (sliceCursorAt (sp' + 160#64) ptr bs ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗ F_msg))
    (by dsimp only [F_msg]; bi_entail) ?_
  refine initOptU32_prevCounter_cps_placed hpc hrun hregs hsp hcl htr ?_
  intro s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1
  have hcall := hint32
  have herr := @decodeErrorPush_tail_wp_placed _ A H hS s0
  have hsp_eq : s1.sp = sp' := hregs1.sp
  have h29 : s1.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs1.x29
  have h22 : s1.readReg64 (Reg.gpr 22#5) = sp' + 176#64 := hregs1.x22
  have h0 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0_1.trans hx0
  have hstack := stackAt_sub_split sp' int32MergeStackX (skipFieldStackX 100)
  simp only [hstack, sepConj_assoc]
  refine SepWPp.of_sepWP_placed hcl1 (mid := (blkPl_85).ρ int32MergeName) ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm]) ?_
  intro hcl2
  refine SepWPp.call_tryFrom_placed ⟨wt, sp' + 284#64, sp' + 288#64, sp' + 160#64, ptr, bs⟩ hcall
    (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp1 ⊢; exact hsp1) hcl2
    (ret_pc := (blkPl_85).base + 420#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr1)
    (T := memRegion (sp' + 284#64) 4 ∗ ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
      sliceCursorAt (sp' + 160#64) ptr bs ∗ A.pool ∗ stackAt sp' int32MergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 176#64 + 108#64 = sp' + 284#64 ∧
      sp' + 352#64 - 64#64 = sp' + 288#64 ∧ bs.length < 9223372036854775808)
    (by simp only [int32MergeSpecX, hsp_eq, h0, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, by bv_omega, by bv_omega, hlen⟩
    (by sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl3 hcs2
  have hregs2 : LoopRegs sp' x19 x20 x21 x23 s2 :=
    LoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs1.x26, by simpa [arm64_norm] using hregs1.x25,
       by simpa [arm64_norm] using hregs1.x23_eq, by simpa [arm64_norm] using h22,
       by simpa [arm64_norm] using hregs1.x21_eq, by simpa [arm64_norm] using hregs1.x20_eq,
       by simpa [arm64_norm] using hregs1.x19_eq⟩
      hsp2 hcs2
  dsimp only [int32MergeSpecX]
  cases hm : mergeUint32 wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩
    dsimp only
    obtain ⟨k, hkl, hrest⟩ := mergeUint32_suffix hm
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_0 => ?_)
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_85).base + 224#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
    intro hcl4
    refine SepWPp.mono_pre ?_
      (hcont v rest _ hm
        (by simp only [arm64_norm])
        (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
         by simpa [arm64_norm] using hregs2.x19_eq⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4
        (by simpa [arm64_norm] using htr2.trans htr1))
    have hmsg : ((sp' + 280#64) ↦₃₂ 1#32) ∗ ((sp' + 284#64) ↦₃₂ v) ∗ F_msg ⊢
        wireSignalMessageLoopOf A (sp' + 176#64) rest.length { m with previousCounter := some v } := by
      refine Entails.trans ?_
        (wireSignalMessageAt_entails_loopOf A g (sp' + 176#64) rest.length _ (hg.mono hrest_le))
      rw [wireSignalMessageAt_split_prevCounter A g sp' { m with previousCounter := some v }]
      rw [← sepConj_assoc, optU32At_some_eq sp' 280#64 284#64 v]
      exact Entails.refl _
    simp only [hstack, hsp_eq, arm64_norm]
    exact trans_sub hmsg
  | none =>
    dsimp only
    have hres := hnone hm
    subst hres
    rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_ne => ?_)
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs2.x29
    rw [memRegion48_split8 sp', memRegion_eight (sp' + 296#64), memRegion_four (sp' + 284#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w0 => SepWPp.exists_pre (fun vErr => ?_))
    refine SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_85).base + 936#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
    intro hcl4
    refine SepWPp.mono_pre ?_
      (herr (err := s2.readReg64 (Reg.gpr 0#5)) (n := 0)
        (mErr := { m with previousCounter := some vErr })
        (by simp only [arm64_norm])
        (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
         by simpa [arm64_norm] using hregs2.x19_eq⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4
        (by simpa [arm64_norm] using htr2.trans htr1)
        (by simp only [arm64_norm])
        hx0_ne (by decide))
    have hmsg : ((sp' + 280#64) ↦₃₂ 1#32) ∗ ((sp' + 284#64) ↦₃₂ vErr) ∗ F_msg ⊢
        wireSignalMessageOf A (sp' + 176#64) { m with previousCounter := some vErr } := by
      refine Entails.trans ?_ (wireSignalMessageAt_entails_of A g (sp' + 176#64) _)
      rw [wireSignalMessageAt_split_prevCounter A g sp' { m with previousCounter := some vErr }]
      rw [← sepConj_assoc, optU32At_some_eq sp' 280#64 284#64 vErr]
      exact Entails.refl _
    simp only [hstack, hsp_eq, arm64_norm]
    exact trans_sub hmsg

theorem initOptU32_counter_cps_placed [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State} {sp' x19 x20 x21 x23 : BitVec 64}
    {u : Option (BitVec 32)} {F : SepProp}
    {Q : State → SepProp → Prop} {Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_85).base + 0x23c#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hcont : ∀ (s1 : State),
      s1.pc = (blkPl_85).base + 0x248#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (((sp' + 272#64) ↦₃₂ 1#32) ∗ memRegion (sp' + 276#64) 4 ∗ F) Q Qp) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (optU32At (sp' + 272#64) u ∗ F) Q Qp := by
  have hsp_eq : s.sp = sp' := hregs.sp
  have h25 : s.readReg64 (Reg.gpr 25#5) = 1#64 := hregs.x25
  have ha : sp' + 272#64 + 4#64 = sp' + 276#64 := by bv_omega
  cases u with
  | none =>
    rw [optU32At_none_def, ha, sepConj_assoc]
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 580#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hcl1
    refine SepWPp.mono_pre (P' := (∃∗ w : BitVec 64, (sp' + 272#64) ↦₆₄ w) ∗ F) (by sep_interval) ?_
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_pre (fun w => ?_)
    refine SepWPp.of_sepWP_placed hcl1 (mid := (blkPl_85).base + 584#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hcl2
    refine SepWPp.mono_pre ?_
      (hcont _
        (by simp only [arm64_norm])
        (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
         by simpa [arm64_norm] using hregs.x19_eq⟩
        (by simp only [arm64_norm])
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl2 htr)
    rw [pointsTo64_one_split32]; sep_interval
  | some v0 =>
    rw [optU32At_some_def, ha, sepConj_assoc]
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 584#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hcl1
    refine SepWPp.mono_pre ?_
      (hcont _
        (by simp only [arm64_norm])
        (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
         by simpa [arm64_norm] using hregs.x19_eq⟩
        (by simp only [arm64_norm])
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr)
    sep_interval

theorem mergeCounter_cps_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hint32 : Int32MergeOkWPlaced A H)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoSignalMessage} {res : Option ProtoSignalMessage}
    (hpc : s.pc = (blkPl_85).base + 0x23c#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (v : BitVec 32) (rest : List (BitVec 8)) (s1 : State),
      mergeUint32 wt bs = some (v, rest) →
      s1.pc = (blkPl_85).base + 0x0e0#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (sliceCursorAfter (sp' + 160#64) ptr bs rest ∗
          ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
          memRegion (sp' + 296#64) 48 ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
          wireSignalMessageLoopOf A (sp' + 176#64) rest.length { m with counter := some v })
        (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr bs res)
        (tryFromQp s0))
    (hnone : mergeUint32 wt bs = none → res = none) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr bs ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopOf A (sp' + 176#64) bs.length m)
      (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr bs res)
      (tryFromQp s0) := by
  rw [wireSignalMessageLoopOf_def]
  simp only [sepExists_sepConj_right, sepConj_pure_left_comm]
  refine SepWPp.exists_pre (fun g => SepWPp.pure_pre (fun hg => ?_))
  rw [wireSignalMessageAt_split_counter A g sp' m]
  let F_msg := optVecU8At A g.rk (sp' + 176#64) m.ratchetKey ∗
    optVecU8At A g.ct (sp' + 200#64) m.ciphertext ∗
    optVecU8At A g.pq (sp' + 224#64) m.pqRatchet ∗
    optVecU8At A g.addr (sp' + 248#64) m.addresses ∗
    optU32At (sp' + 280#64) m.previousCounter
  refine SepWPp.mono_pre
    (P' := optU32At (sp' + 272#64) m.counter ∗
      (sliceCursorAt (sp' + 160#64) ptr bs ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗ F_msg))
    (by dsimp only [F_msg]; bi_entail) ?_
  refine initOptU32_counter_cps_placed hpc hrun hregs hsp hcl htr ?_
  intro s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1
  have hcall := hint32
  have herr := @decodeErrorPush_tail_wp_placed _ A H hS s0
  have hsp_eq : s1.sp = sp' := hregs1.sp
  have h29 : s1.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs1.x29
  have h22 : s1.readReg64 (Reg.gpr 22#5) = sp' + 176#64 := hregs1.x22
  have h0 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0_1.trans hx0
  have hstack := stackAt_sub_split sp' int32MergeStackX (skipFieldStackX 100)
  simp only [hstack, sepConj_assoc]
  refine SepWPp.of_sepWP_placed hcl1 (mid := (blkPl_85).ρ int32MergeName) ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm]) ?_
  intro hcl2
  refine SepWPp.call_tryFrom_placed ⟨wt, sp' + 276#64, sp' + 288#64, sp' + 160#64, ptr, bs⟩ hcall
    (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp1 ⊢; exact hsp1) hcl2
    (ret_pc := (blkPl_85).base + 596#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr1)
    (T := memRegion (sp' + 276#64) 4 ∗ ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
      sliceCursorAt (sp' + 160#64) ptr bs ∗ A.pool ∗ stackAt sp' int32MergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 176#64 + 100#64 = sp' + 276#64 ∧
      sp' + 352#64 - 64#64 = sp' + 288#64 ∧ bs.length < 9223372036854775808)
    (by simp only [int32MergeSpecX, hsp_eq, h0, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, by bv_omega, by bv_omega, hlen⟩
    (by sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl3 hcs2
  have hregs2 : LoopRegs sp' x19 x20 x21 x23 s2 :=
    LoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs1.x26, by simpa [arm64_norm] using hregs1.x25,
       by simpa [arm64_norm] using hregs1.x23_eq, by simpa [arm64_norm] using h22,
       by simpa [arm64_norm] using hregs1.x21_eq, by simpa [arm64_norm] using hregs1.x20_eq,
       by simpa [arm64_norm] using hregs1.x19_eq⟩
      hsp2 hcs2
  dsimp only [int32MergeSpecX]
  cases hm : mergeUint32 wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩
    dsimp only
    obtain ⟨k, hkl, hrest⟩ := mergeUint32_suffix hm
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_0 => ?_)
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_85).base + 224#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
    intro hcl4
    refine SepWPp.mono_pre ?_
      (hcont v rest _ hm
        (by simp only [arm64_norm])
        (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
         by simpa [arm64_norm] using hregs2.x19_eq⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4
        (by simpa [arm64_norm] using htr2.trans htr1))
    have hmsg : ((sp' + 272#64) ↦₃₂ 1#32) ∗ ((sp' + 276#64) ↦₃₂ v) ∗ F_msg ⊢
        wireSignalMessageLoopOf A (sp' + 176#64) rest.length { m with counter := some v } := by
      refine Entails.trans ?_
        (wireSignalMessageAt_entails_loopOf A g (sp' + 176#64) rest.length _ (hg.mono hrest_le))
      rw [wireSignalMessageAt_split_counter A g sp' { m with counter := some v }]
      rw [← sepConj_assoc, optU32At_some_eq sp' 272#64 276#64 v]
      exact Entails.refl _
    simp only [hstack, hsp_eq, arm64_norm]
    exact trans_sub hmsg
  | none =>
    dsimp only
    have hres := hnone hm
    subst hres
    rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_ne => ?_)
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs2.x29
    rw [memRegion48_split8 sp', memRegion_eight (sp' + 296#64), memRegion_four (sp' + 276#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w0 => SepWPp.exists_pre (fun vErr => ?_))
    refine SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_85).base + 936#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
    intro hcl4
    refine SepWPp.mono_pre ?_
      (herr (err := s2.readReg64 (Reg.gpr 0#5)) (n := 0)
        (mErr := { m with counter := some vErr })
        (by simp only [arm64_norm])
        (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
         by simpa [arm64_norm] using hregs2.x19_eq⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4
        (by simpa [arm64_norm] using htr2.trans htr1)
        (by simp only [arm64_norm])
        hx0_ne (by decide))
    have hmsg : ((sp' + 272#64) ↦₃₂ 1#32) ∗ ((sp' + 276#64) ↦₃₂ vErr) ∗ F_msg ⊢
        wireSignalMessageOf A (sp' + 176#64) { m with counter := some vErr } := by
      refine Entails.trans ?_ (wireSignalMessageAt_entails_of A g (sp' + 176#64) _)
      rw [wireSignalMessageAt_split_counter A g sp' { m with counter := some vErr }]
      rw [← sepConj_assoc, optU32At_some_eq sp' 272#64 276#64 vErr]
      exact Entails.refl _
    simp only [hstack, hsp_eq, arm64_norm]
    exact trans_sub hmsg

theorem initOptVecU8_addr_cps_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {s0 s : State} {sp' x19 x20 x21 x23 : BitVec 64}
    {pin : VecPin} {u : Option (List (BitVec 8))} {F : SepProp}
    {Q : State → SepProp → Prop} {Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_85).base + 0x1c4#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hcont : ∀ (cap0 ptr0 : BitVec 64) (v0 : List (BitVec 8)) (s1 : State),
      (cap0 = 0#64 ∨ cap0 = pin.cap) →
      s1.pc = (blkPl_85).base + 0x1d8#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (vecU8At A (sp' + 248#64) cap0 ptr0 v0 ∗ F) Q Qp) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (optVecU8At A pin (sp' + 248#64) u ∗ F) Q Qp := by
  have hsp_eq : s.sp = sp' := hregs.sp
  have h25 : s.readReg64 (Reg.gpr 25#5) = 1#64 := hregs.x25
  cases u with
  | none =>
    rw [optVecU8At_none_split A pin sp' 248#64 256#64 264#64]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w2 => SepWPp.exists_pre (fun w1 => ?_))
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 472#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hcl1
    refine SepWPp.mono_pre ?_
      (hcont 0#64 1#64 [] _ (Or.inl rfl)
        (by simp only [arm64_norm])
        (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
         by simpa [arm64_norm] using hregs.x19_eq⟩
        (by simp only [arm64_norm])
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr)
    rw [← pointsTo64_emptyVec_eq_vecU8At A sp' 248#64 256#64 264#64]
    bi_entail
  | some v0 =>
    rw [optVecU8At_some_unfold A pin (sp' + 248#64) v0, sepConj_assoc]
    refine SepWPp.pure_pre (fun hp => ?_)
    have ⟨hc1, hc2⟩ := cmn_one_ne_of_lt pin.cap hp.2.1
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 472#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hcl1
    refine SepWPp.mono_pre ?_
      (hcont pin.cap pin.ptr v0 _ (Or.inr rfl)
        (by simp only [arm64_norm])
        (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
         by simpa [arm64_norm] using hregs.x19_eq⟩
        (by simp only [arm64_norm])
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr)
    rw [← vecU8At_fold_of_pure A pin (sp' + 248#64) v0 hp]
    bi_entail

theorem mergeAddresses_cps_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hbytes : BytesMergeOkWPlaced A H)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoSignalMessage} {res : Option ProtoSignalMessage}
    (hpc : s.pc = (blkPl_85).base + 0x1c4#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (v rest : List (BitVec 8)) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      s1.pc = (blkPl_85).base + 0x0e0#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (sliceCursorAfter (sp' + 160#64) ptr bs rest ∗
          ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
          memRegion (sp' + 296#64) 48 ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
          wireSignalMessageLoopOf A (sp' + 176#64) rest.length { m with addresses := some v })
        (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr bs res)
        (tryFromQp s0))
    (hnone : mergeBytes wt bs = none → res = none) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr bs ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopOf A (sp' + 176#64) bs.length m)
      (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr bs res)
      (tryFromQp s0) := by
  rw [wireSignalMessageLoopOf_def]
  simp only [sepExists_sepConj_right, sepConj_pure_left_comm]
  refine SepWPp.exists_pre (fun g => SepWPp.pure_pre (fun hg => ?_))
  rw [wireSignalMessageAt_split_addr A g sp' m]
  let F_msg := optVecU8At A g.rk (sp' + 176#64) m.ratchetKey ∗
    optVecU8At A g.ct (sp' + 200#64) m.ciphertext ∗
    optVecU8At A g.pq (sp' + 224#64) m.pqRatchet ∗
    optU32At (sp' + 272#64) m.counter ∗
    optU32At (sp' + 280#64) m.previousCounter
  refine SepWPp.mono_pre
    (P' := optVecU8At A g.addr (sp' + 248#64) m.addresses ∗
      (sliceCursorAt (sp' + 160#64) ptr bs ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗ F_msg))
    (by dsimp only [F_msg]; bi_entail) ?_
  refine initOptVecU8_addr_cps_placed hpc hrun hregs hsp hcl htr ?_
  intro cap0 ptr0 v0 s1 hcap0 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1
  have hcap0_ok : BytesMergeCapOk cap0 bs.length := by
    rcases hcap0 with rfl | rfl
    · exact Or.inl (by decide)
    · exact hg.addr
  have hcall := hbytes
  have herr := @decodeErrorPush_tail_wp_placed _ A H hS s0
  have hsp_eq : s1.sp = sp' := hregs1.sp
  have h29 : s1.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs1.x29
  have h22 : s1.readReg64 (Reg.gpr 22#5) = sp' + 176#64 := hregs1.x22
  have h0 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0_1.trans hx0
  have hstack := stackAt_sub_split sp' bytesMergeStackX (skipFieldStackX 100)
  simp only [hstack, sepConj_assoc]
  refine SepWPp.of_sepWP_placed hcl1 (mid := (blkPl_85).ρ bytesMergeName) ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm]) ?_
  intro hcl2
  refine SepWPp.call_tryFrom_placed ⟨wt, sp' + 248#64, cap0, ptr0, v0, sp' + 288#64, sp' + 160#64, ptr, bs⟩ hcall
    (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp1 ⊢; exact hsp1) hcl2
    (ret_pc := (blkPl_85).base + 484#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr1)
    (T := vecU8At A (sp' + 248#64) cap0 ptr0 v0 ∗ ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
      sliceCursorAt (sp' + 160#64) ptr bs ∗ A.pool ∗ stackAt sp' bytesMergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 176#64 + 72#64 = sp' + 248#64 ∧
      sp' + 352#64 - 64#64 = sp' + 288#64 ∧ bs.length < 9223372036854775808 ∧
      BytesMergeCapOk cap0 bs.length)
    (by simp only [bytesMergeRawSpecX, hsp_eq, h0, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, by bv_omega, by bv_omega, hlen, hcap0_ok⟩
    (by sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl3 hcs2
  have hregs2 : LoopRegs sp' x19 x20 x21 x23 s2 :=
    LoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs1.x26, by simpa [arm64_norm] using hregs1.x25,
       by simpa [arm64_norm] using hregs1.x23_eq, by simpa [arm64_norm] using h22,
       by simpa [arm64_norm] using hregs1.x21_eq, by simpa [arm64_norm] using hregs1.x20_eq,
       by simpa [arm64_norm] using hregs1.x19_eq⟩
      hsp2 hcs2
  dsimp only [bytesMergeRawSpecX]
  cases hm : mergeBytes wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩
    dsimp only
    obtain ⟨k, hkl, hrest, _⟩ := mergeBytes_suffix hm
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_0 => ?_)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.exists_pre (fun cap' => SepWPp.exists_pre (fun ptr' => SepWPp.pure_pre (fun hcap' => ?_)))
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_85).base + 224#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
    intro hcl4
    refine SepWPp.mono_pre ?_
      (hcont v rest _ hm
        (by simp only [arm64_norm])
        (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
         by simpa [arm64_norm] using hregs2.x19_eq⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4
        (by simpa [arm64_norm] using htr2.trans htr1))
    simp only [hstack, hsp_eq, F_msg, arm64_norm]
    exact trans_sub (vecU8At_addr_entails_wireSignalMessageLoopOf A g sp' cap' ptr' rest.length m v (hg.mono hrest_le) hcap')
  | none =>
    dsimp only
    have hres := hnone hm
    subst hres
    rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_ne => ?_)
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs2.x29
    rw [memRegion48_split8 sp', memRegion_eight (sp' + 296#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w0 => ?_)
    refine SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_85).base + 936#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
    intro hcl4
    refine SepWPp.mono_pre ?_
      (herr (err := s2.readReg64 (Reg.gpr 0#5)) (n := 0)
        (mErr := { m with addresses := some v0 })
        (by simp only [arm64_norm])
        (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
         by simpa [arm64_norm] using hregs2.x19_eq⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4
        (by simpa [arm64_norm] using htr2.trans htr1)
        (by simp only [arm64_norm])
        hx0_ne (by decide))
    simp only [hstack, hsp_eq, F_msg, arm64_norm]
    exact trans_sub (vecU8At_addr_entails_wireSignalMessageOf A g sp' cap0 ptr0 m v0)

theorem initOptVecU8_rk_cps_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {s0 s : State} {sp' x19 x20 x21 x23 : BitVec 64}
    {pin : VecPin} {u : Option (List (BitVec 8))} {F : SepProp}
    {Q : State → SepProp → Prop} {Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_85).base + 0x1ec#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hcont : ∀ (cap0 ptr0 : BitVec 64) (v0 : List (BitVec 8)) (s1 : State),
      (cap0 = 0#64 ∨ cap0 = pin.cap) →
      s1.pc = (blkPl_85).base + 0x200#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (vecU8At A (sp' + 176#64) cap0 ptr0 v0 ∗ F) Q Qp) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (optVecU8At A pin (sp' + 176#64) u ∗ F) Q Qp := by
  have hsp_eq : s.sp = sp' := hregs.sp
  have h25 : s.readReg64 (Reg.gpr 25#5) = 1#64 := hregs.x25
  cases u with
  | none =>
    rw [optVecU8At_none_split A pin sp' 176#64 184#64 192#64]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w2 => SepWPp.exists_pre (fun w1 => ?_))
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 512#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hcl1
    refine SepWPp.mono_pre ?_
      (hcont 0#64 1#64 [] _ (Or.inl rfl)
        (by simp only [arm64_norm])
        (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
         by simpa [arm64_norm] using hregs.x19_eq⟩
        (by simp only [arm64_norm])
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr)
    rw [← pointsTo64_emptyVec_eq_vecU8At A sp' 176#64 184#64 192#64]
    bi_entail
  | some v0 =>
    rw [optVecU8At_some_unfold A pin (sp' + 176#64) v0, sepConj_assoc]
    refine SepWPp.pure_pre (fun hp => ?_)
    have ⟨hc1, hc2⟩ := cmn_one_ne_of_lt pin.cap hp.2.1
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 512#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hcl1
    refine SepWPp.mono_pre ?_
      (hcont pin.cap pin.ptr v0 _ (Or.inr rfl)
        (by simp only [arm64_norm])
        (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
         by simpa [arm64_norm] using hregs.x19_eq⟩
        (by simp only [arm64_norm])
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr)
    rw [← vecU8At_fold_of_pure A pin (sp' + 176#64) v0 hp]
    bi_entail

theorem mergeRatchetKey_cps_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hbytes : BytesMergeOkWPlaced A H)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoSignalMessage} {res : Option ProtoSignalMessage}
    (hpc : s.pc = (blkPl_85).base + 0x1ec#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (v rest : List (BitVec 8)) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      s1.pc = (blkPl_85).base + 0x0e0#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (sliceCursorAfter (sp' + 160#64) ptr bs rest ∗
          ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
          memRegion (sp' + 296#64) 48 ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
          wireSignalMessageLoopOf A (sp' + 176#64) rest.length { m with ratchetKey := some v })
        (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr bs res)
        (tryFromQp s0))
    (hnone : mergeBytes wt bs = none → res = none) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr bs ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopOf A (sp' + 176#64) bs.length m)
      (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr bs res)
      (tryFromQp s0) := by
  rw [wireSignalMessageLoopOf_def]
  simp only [sepExists_sepConj_right, sepConj_pure_left_comm]
  refine SepWPp.exists_pre (fun g => SepWPp.pure_pre (fun hg => ?_))
  rw [wireSignalMessageAt_split_rk A g sp' m]
  let F_msg := optVecU8At A g.ct (sp' + 200#64) m.ciphertext ∗
    optVecU8At A g.pq (sp' + 224#64) m.pqRatchet ∗
    optVecU8At A g.addr (sp' + 248#64) m.addresses ∗
    optU32At (sp' + 272#64) m.counter ∗
    optU32At (sp' + 280#64) m.previousCounter
  refine SepWPp.mono_pre
    (P' := optVecU8At A g.rk (sp' + 176#64) m.ratchetKey ∗
      (sliceCursorAt (sp' + 160#64) ptr bs ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗ F_msg))
    (by dsimp only [F_msg]; bi_entail) ?_
  refine initOptVecU8_rk_cps_placed hpc hrun hregs hsp hcl htr ?_
  intro cap0 ptr0 v0 s1 hcap0 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1
  have hcap0_ok : BytesMergeCapOk cap0 bs.length := by
    rcases hcap0 with rfl | rfl
    · exact Or.inl (by decide)
    · exact hg.rk
  have hcall := hbytes
  have herr := @decodeErrorPush_tail_wp_placed _ A H hS s0
  have hsp_eq : s1.sp = sp' := hregs1.sp
  have h29 : s1.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs1.x29
  have h22 : s1.readReg64 (Reg.gpr 22#5) = sp' + 176#64 := hregs1.x22
  have h0 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0_1.trans hx0
  have hstack := stackAt_sub_split sp' bytesMergeStackX (skipFieldStackX 100)
  simp only [hstack, sepConj_assoc]
  refine SepWPp.of_sepWP_placed hcl1 (mid := (blkPl_85).ρ bytesMergeName) ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm]) ?_
  intro hcl2
  refine SepWPp.call_tryFrom_placed ⟨wt, sp' + 176#64, cap0, ptr0, v0, sp' + 288#64, sp' + 160#64, ptr, bs⟩ hcall
    (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp1 ⊢; exact hsp1) hcl2
    (ret_pc := (blkPl_85).base + 524#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr1)
    (T := vecU8At A (sp' + 176#64) cap0 ptr0 v0 ∗ ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
      sliceCursorAt (sp' + 160#64) ptr bs ∗ A.pool ∗ stackAt sp' bytesMergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 352#64 - 64#64 = sp' + 288#64 ∧ bs.length < 9223372036854775808 ∧
      BytesMergeCapOk cap0 bs.length)
    (by simp only [bytesMergeRawSpecX, hsp_eq, h0, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, by bv_omega, hlen, hcap0_ok⟩
    (by sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl3 hcs2
  have hregs2 : LoopRegs sp' x19 x20 x21 x23 s2 :=
    LoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs1.x26, by simpa [arm64_norm] using hregs1.x25,
       by simpa [arm64_norm] using hregs1.x23_eq, by simpa [arm64_norm] using h22,
       by simpa [arm64_norm] using hregs1.x21_eq, by simpa [arm64_norm] using hregs1.x20_eq,
       by simpa [arm64_norm] using hregs1.x19_eq⟩
      hsp2 hcs2
  dsimp only [bytesMergeRawSpecX]
  cases hm : mergeBytes wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩
    dsimp only
    obtain ⟨k, hkl, hrest, _⟩ := mergeBytes_suffix hm
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_0 => ?_)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.exists_pre (fun cap' => SepWPp.exists_pre (fun ptr' => SepWPp.pure_pre (fun hcap' => ?_)))
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_85).base + 224#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
    intro hcl4
    refine SepWPp.mono_pre ?_
      (hcont v rest _ hm
        (by simp only [arm64_norm])
        (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
         by simpa [arm64_norm] using hregs2.x19_eq⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4
        (by simpa [arm64_norm] using htr2.trans htr1))
    simp only [hstack, hsp_eq, F_msg, arm64_norm]
    exact trans_sub (vecU8At_rk_entails_wireSignalMessageLoopOf A g sp' cap' ptr' rest.length m v (hg.mono hrest_le) hcap')
  | none =>
    dsimp only
    have hres := hnone hm
    subst hres
    rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_ne => ?_)
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs2.x29
    rw [memRegion48_split8 sp', memRegion_eight (sp' + 296#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w0 => ?_)
    refine SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_85).base + 936#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
    intro hcl4
    refine SepWPp.mono_pre ?_
      (herr (err := s2.readReg64 (Reg.gpr 0#5)) (n := 0)
        (mErr := { m with ratchetKey := some v0 })
        (by simp only [arm64_norm])
        (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
         by simpa [arm64_norm] using hregs2.x19_eq⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4
        (by simpa [arm64_norm] using htr2.trans htr1)
        (by simp only [arm64_norm])
        hx0_ne (by decide))
    simp only [hstack, hsp_eq, F_msg, arm64_norm]
    exact trans_sub (vecU8At_rk_entails_wireSignalMessageOf A g sp' cap0 ptr0 m v0)

theorem initOptVecU8_ct_cps_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {s0 s : State} {sp' x19 x20 x21 x23 : BitVec 64}
    {pin : VecPin} {u : Option (List (BitVec 8))} {F : SepProp}
    {Q : State → SepProp → Prop} {Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_85).base + 0x214#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hcont : ∀ (cap0 ptr0 : BitVec 64) (v0 : List (BitVec 8)) (s1 : State),
      (cap0 = 0#64 ∨ cap0 = pin.cap) →
      s1.pc = (blkPl_85).base + 0x228#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (vecU8At A (sp' + 200#64) cap0 ptr0 v0 ∗ F) Q Qp) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (optVecU8At A pin (sp' + 200#64) u ∗ F) Q Qp := by
  have hsp_eq : s.sp = sp' := hregs.sp
  have h25 : s.readReg64 (Reg.gpr 25#5) = 1#64 := hregs.x25
  cases u with
  | none =>
    rw [optVecU8At_none_split A pin sp' 200#64 208#64 216#64]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w2 => SepWPp.exists_pre (fun w1 => ?_))
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 552#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hcl1
    refine SepWPp.mono_pre ?_
      (hcont 0#64 1#64 [] _ (Or.inl rfl)
        (by simp only [arm64_norm])
        (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
         by simpa [arm64_norm] using hregs.x19_eq⟩
        (by simp only [arm64_norm])
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr)
    rw [← pointsTo64_emptyVec_eq_vecU8At A sp' 200#64 208#64 216#64]
    bi_entail
  | some v0 =>
    rw [optVecU8At_some_unfold A pin (sp' + 200#64) v0, sepConj_assoc]
    refine SepWPp.pure_pre (fun hp => ?_)
    have ⟨hc1, hc2⟩ := cmn_one_ne_of_lt pin.cap hp.2.1
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 552#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hcl1
    refine SepWPp.mono_pre ?_
      (hcont pin.cap pin.ptr v0 _ (Or.inr rfl)
        (by simp only [arm64_norm])
        (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
         by simpa [arm64_norm] using hregs.x19_eq⟩
        (by simp only [arm64_norm])
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr)
    rw [← vecU8At_fold_of_pure A pin (sp' + 200#64) v0 hp]
    bi_entail

theorem mergeCiphertext_cps_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hbytes : BytesMergeOkWPlaced A H)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoSignalMessage} {res : Option ProtoSignalMessage}
    (hpc : s.pc = (blkPl_85).base + 0x214#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (v rest : List (BitVec 8)) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      s1.pc = (blkPl_85).base + 0x0e0#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (sliceCursorAfter (sp' + 160#64) ptr bs rest ∗
          ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
          memRegion (sp' + 296#64) 48 ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
          wireSignalMessageLoopOf A (sp' + 176#64) rest.length { m with ciphertext := some v })
        (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr bs res)
        (tryFromQp s0))
    (hnone : mergeBytes wt bs = none → res = none) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr bs ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopOf A (sp' + 176#64) bs.length m)
      (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr bs res)
      (tryFromQp s0) := by
  rw [wireSignalMessageLoopOf_def]
  simp only [sepExists_sepConj_right, sepConj_pure_left_comm]
  refine SepWPp.exists_pre (fun g => SepWPp.pure_pre (fun hg => ?_))
  rw [wireSignalMessageAt_split_ct A g sp' m]
  let F_msg := optVecU8At A g.rk (sp' + 176#64) m.ratchetKey ∗
    optVecU8At A g.pq (sp' + 224#64) m.pqRatchet ∗
    optVecU8At A g.addr (sp' + 248#64) m.addresses ∗
    optU32At (sp' + 272#64) m.counter ∗
    optU32At (sp' + 280#64) m.previousCounter
  refine SepWPp.mono_pre
    (P' := optVecU8At A g.ct (sp' + 200#64) m.ciphertext ∗
      (sliceCursorAt (sp' + 160#64) ptr bs ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗ F_msg))
    (by dsimp only [F_msg]; bi_entail) ?_
  refine initOptVecU8_ct_cps_placed hpc hrun hregs hsp hcl htr ?_
  intro cap0 ptr0 v0 s1 hcap0 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1
  have hcap0_ok : BytesMergeCapOk cap0 bs.length := by
    rcases hcap0 with rfl | rfl
    · exact Or.inl (by decide)
    · exact hg.ct
  have hcall := hbytes
  have herr := @decodeErrorPush_tail_wp_placed _ A H hS s0
  have hsp_eq : s1.sp = sp' := hregs1.sp
  have h29 : s1.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs1.x29
  have h22 : s1.readReg64 (Reg.gpr 22#5) = sp' + 176#64 := hregs1.x22
  have h0 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0_1.trans hx0
  have hstack := stackAt_sub_split sp' bytesMergeStackX (skipFieldStackX 100)
  simp only [hstack, sepConj_assoc]
  refine SepWPp.of_sepWP_placed hcl1 (mid := (blkPl_85).ρ bytesMergeName) ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm]) ?_
  intro hcl2
  refine SepWPp.call_tryFrom_placed ⟨wt, sp' + 200#64, cap0, ptr0, v0, sp' + 288#64, sp' + 160#64, ptr, bs⟩ hcall
    (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp1 ⊢; exact hsp1) hcl2
    (ret_pc := (blkPl_85).base + 564#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr1)
    (T := vecU8At A (sp' + 200#64) cap0 ptr0 v0 ∗ ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
      sliceCursorAt (sp' + 160#64) ptr bs ∗ A.pool ∗ stackAt sp' bytesMergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 176#64 + 24#64 = sp' + 200#64 ∧
      sp' + 352#64 - 64#64 = sp' + 288#64 ∧ bs.length < 9223372036854775808 ∧
      BytesMergeCapOk cap0 bs.length)
    (by simp only [bytesMergeRawSpecX, hsp_eq, h0, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, by bv_omega, by bv_omega, hlen, hcap0_ok⟩
    (by sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl3 hcs2
  have hregs2 : LoopRegs sp' x19 x20 x21 x23 s2 :=
    LoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs1.x26, by simpa [arm64_norm] using hregs1.x25,
       by simpa [arm64_norm] using hregs1.x23_eq, by simpa [arm64_norm] using h22,
       by simpa [arm64_norm] using hregs1.x21_eq, by simpa [arm64_norm] using hregs1.x20_eq,
       by simpa [arm64_norm] using hregs1.x19_eq⟩
      hsp2 hcs2
  dsimp only [bytesMergeRawSpecX]
  cases hm : mergeBytes wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩
    dsimp only
    obtain ⟨k, hkl, hrest, _⟩ := mergeBytes_suffix hm
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_0 => ?_)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.exists_pre (fun cap' => SepWPp.exists_pre (fun ptr' => SepWPp.pure_pre (fun hcap' => ?_)))
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_85).base + 224#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
    intro hcl4
    refine SepWPp.mono_pre ?_
      (hcont v rest _ hm
        (by simp only [arm64_norm])
        (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
         by simpa [arm64_norm] using hregs2.x19_eq⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4
        (by simpa [arm64_norm] using htr2.trans htr1))
    simp only [hstack, hsp_eq, F_msg, arm64_norm]
    exact trans_sub (vecU8At_ct_entails_wireSignalMessageLoopOf A g sp' cap' ptr' rest.length m v (hg.mono hrest_le) hcap')
  | none =>
    dsimp only
    have hres := hnone hm
    subst hres
    rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_ne => ?_)
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs2.x29
    rw [memRegion48_split8 sp', memRegion_eight (sp' + 296#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w0 => ?_)
    refine SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_85).base + 936#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
    intro hcl4
    refine SepWPp.mono_pre ?_
      (herr (err := s2.readReg64 (Reg.gpr 0#5)) (n := 0)
        (mErr := { m with ciphertext := some v0 })
        (by simp only [arm64_norm])
        (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
         by simpa [arm64_norm] using hregs2.x19_eq⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4
        (by simpa [arm64_norm] using htr2.trans htr1)
        (by simp only [arm64_norm])
        hx0_ne (by decide))
    simp only [hstack, hsp_eq, F_msg, arm64_norm]
    exact trans_sub (vecU8At_ct_entails_wireSignalMessageOf A g sp' cap0 ptr0 m v0)

theorem initOptVecU8_pq_cps_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {s0 s : State} {sp' x19 x20 x21 x23 : BitVec 64}
    {pin : VecPin} {u : Option (List (BitVec 8))} {F : SepProp}
    {Q : State → SepProp → Prop} {Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_85).base + 0x25c#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hcont : ∀ (cap0 ptr0 : BitVec 64) (v0 : List (BitVec 8)) (s1 : State),
      (cap0 = 0#64 ∨ cap0 = pin.cap) →
      s1.pc = (blkPl_85).base + 0x270#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (vecU8At A (sp' + 224#64) cap0 ptr0 v0 ∗ F) Q Qp) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (optVecU8At A pin (sp' + 224#64) u ∗ F) Q Qp := by
  have hsp_eq : s.sp = sp' := hregs.sp
  have h25 : s.readReg64 (Reg.gpr 25#5) = 1#64 := hregs.x25
  cases u with
  | none =>
    rw [optVecU8At_none_split A pin sp' 224#64 232#64 240#64]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w2 => SepWPp.exists_pre (fun w1 => ?_))
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 624#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hcl1
    refine SepWPp.mono_pre ?_
      (hcont 0#64 1#64 [] _ (Or.inl rfl)
        (by simp only [arm64_norm])
        (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
         by simpa [arm64_norm] using hregs.x19_eq⟩
        (by simp only [arm64_norm])
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr)
    rw [← pointsTo64_emptyVec_eq_vecU8At A sp' 224#64 232#64 240#64]
    bi_entail
  | some v0 =>
    rw [optVecU8At_some_unfold A pin (sp' + 224#64) v0, sepConj_assoc]
    refine SepWPp.pure_pre (fun hp => ?_)
    have ⟨hc1, hc2⟩ := cmn_one_ne_of_lt pin.cap hp.2.1
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 624#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hcl1
    refine SepWPp.mono_pre ?_
      (hcont pin.cap pin.ptr v0 _ (Or.inr rfl)
        (by simp only [arm64_norm])
        (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
         by simpa [arm64_norm] using hregs.x19_eq⟩
        (by simp only [arm64_norm])
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcl1 htr)
    rw [← vecU8At_fold_of_pure A pin (sp' + 224#64) v0 hp]
    bi_entail

theorem mergePqRatchet_cps_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hbytes : BytesMergeOkWPlaced A H)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoSignalMessage} {res : Option ProtoSignalMessage}
    (hpc : s.pc = (blkPl_85).base + 0x25c#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (v rest : List (BitVec 8)) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      s1.pc = (blkPl_85).base + 0x0e0#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (sliceCursorAfter (sp' + 160#64) ptr bs rest ∗
          ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
          memRegion (sp' + 296#64) 48 ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
          wireSignalMessageLoopOf A (sp' + 176#64) rest.length { m with pqRatchet := some v })
        (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr bs res)
        (tryFromQp s0))
    (hnone : mergeBytes wt bs = none → res = none) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr bs ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopOf A (sp' + 176#64) bs.length m)
      (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr bs res)
      (tryFromQp s0) := by
  rw [wireSignalMessageLoopOf_def]
  simp only [sepExists_sepConj_right, sepConj_pure_left_comm]
  refine SepWPp.exists_pre (fun g => SepWPp.pure_pre (fun hg => ?_))
  rw [wireSignalMessageAt_split_pq A g sp' m]
  let F_msg := optVecU8At A g.rk (sp' + 176#64) m.ratchetKey ∗
    optVecU8At A g.ct (sp' + 200#64) m.ciphertext ∗
    optVecU8At A g.addr (sp' + 248#64) m.addresses ∗
    optU32At (sp' + 272#64) m.counter ∗
    optU32At (sp' + 280#64) m.previousCounter
  refine SepWPp.mono_pre
    (P' := optVecU8At A g.pq (sp' + 224#64) m.pqRatchet ∗
      (sliceCursorAt (sp' + 160#64) ptr bs ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗ F_msg))
    (by dsimp only [F_msg]; bi_entail) ?_
  refine initOptVecU8_pq_cps_placed hpc hrun hregs hsp hcl htr ?_
  intro cap0 ptr0 v0 s1 hcap0 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1
  have hcap0_ok : BytesMergeCapOk cap0 bs.length := by
    rcases hcap0 with rfl | rfl
    · exact Or.inl (by decide)
    · exact hg.pq
  have hcall := hbytes
  have herr := @decodeErrorPush_tail_wp_placed _ A H hS s0
  have hsp_eq : s1.sp = sp' := hregs1.sp
  have h29 : s1.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs1.x29
  have h22 : s1.readReg64 (Reg.gpr 22#5) = sp' + 176#64 := hregs1.x22
  have h0 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0_1.trans hx0
  have hstack := stackAt_sub_split sp' bytesMergeStackX (skipFieldStackX 100)
  simp only [hstack, sepConj_assoc]
  refine SepWPp.of_sepWP_placed hcl1 (mid := (blkPl_85).ρ bytesMergeName) ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm]) ?_
  intro hcl2
  refine SepWPp.call_tryFrom_placed ⟨wt, sp' + 224#64, cap0, ptr0, v0, sp' + 288#64, sp' + 160#64, ptr, bs⟩ hcall
    (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp1 ⊢; exact hsp1) hcl2
    (ret_pc := (blkPl_85).base + 636#64) (by simp only [arm64_norm])
    (by simpa [arm64_norm] using htr1)
    (T := vecU8At A (sp' + 224#64) cap0 ptr0 v0 ∗ ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
      sliceCursorAt (sp' + 160#64) ptr bs ∗ A.pool ∗ stackAt sp' bytesMergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 176#64 + 48#64 = sp' + 224#64 ∧
      sp' + 352#64 - 64#64 = sp' + 288#64 ∧ bs.length < 9223372036854775808 ∧
      BytesMergeCapOk cap0 bs.length)
    (by simp only [bytesMergeRawSpecX, hsp_eq, h0, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, by bv_omega, by bv_omega, hlen, hcap0_ok⟩
    (by sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl3 hcs2
  have hregs2 : LoopRegs sp' x19 x20 x21 x23 s2 :=
    LoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [arm64_norm] using hregs1.x26, by simpa [arm64_norm] using hregs1.x25,
       by simpa [arm64_norm] using hregs1.x23_eq, by simpa [arm64_norm] using h22,
       by simpa [arm64_norm] using hregs1.x21_eq, by simpa [arm64_norm] using hregs1.x20_eq,
       by simpa [arm64_norm] using hregs1.x19_eq⟩
      hsp2 hcs2
  dsimp only [bytesMergeRawSpecX]
  cases hm : mergeBytes wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩
    dsimp only
    obtain ⟨k, hkl, hrest, _⟩ := mergeBytes_suffix hm
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_0 => ?_)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.exists_pre (fun cap' => SepWPp.exists_pre (fun ptr' => SepWPp.pure_pre (fun hcap' => ?_)))
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_85).base + 224#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
    intro hcl4
    refine SepWPp.mono_pre ?_
      (hcont v rest _ hm
        (by simp only [arm64_norm])
        (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
         by simpa [arm64_norm] using hregs2.x19_eq⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4
        (by simpa [arm64_norm] using htr2.trans htr1))
    simp only [hstack, hsp_eq, F_msg, arm64_norm]
    exact trans_sub (vecU8At_pq_entails_wireSignalMessageLoopOf A g sp' cap' ptr' rest.length m v (hg.mono hrest_le) hcap')
  | none =>
    dsimp only
    have hres := hnone hm
    subst hres
    rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_ne => ?_)
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs2.x29
    rw [memRegion48_split8 sp', memRegion_eight (sp' + 296#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w0 => ?_)
    refine SepWPp.of_sepWP_placed hcl3 (mid := (blkPl_85).base + 936#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
    intro hcl4
    refine SepWPp.mono_pre ?_
      (herr (err := s2.readReg64 (Reg.gpr 0#5)) (n := 0)
        (mErr := { m with pqRatchet := some v0 })
        (by simp only [arm64_norm])
        (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x26, by simpa [arm64_norm] using hregs2.x25,
         by simpa [arm64_norm] using hregs2.x23_eq, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21_eq, by simpa [arm64_norm] using hregs2.x20_eq,
         by simpa [arm64_norm] using hregs2.x19_eq⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcl4
        (by simpa [arm64_norm] using htr2.trans htr1)
        (by simp only [arm64_norm])
        hx0_ne (by decide))
    simp only [hstack, hsp_eq, F_msg, arm64_norm]
    exact trans_sub (vecU8At_pq_entails_wireSignalMessageOf A g sp' cap0 ptr0 m v0)

theorem dispatch_tag_cps_placed [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State} {sp' x19 x20 x21 x23 : BitVec 64} {tag : ℕ}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_85).base + 0x16c#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (htag_ge : 1 ≤ tag) (htag_lt : tag < 2 ^ 32)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (h1 : tag = 1 → ∀ s1 : State,
      s1.pc = (blkPl_85).base + 0x1ec#64 →
      s1.status = .Running → LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1 P Q Qp)
    (h2 : tag = 2 → ∀ s1 : State,
      s1.pc = (blkPl_85).base + 0x23c#64 →
      s1.status = .Running → LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1 P Q Qp)
    (h3 : tag = 3 → ∀ s1 : State,
      s1.pc = (blkPl_85).base + 0x18c#64 →
      s1.status = .Running → LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1 P Q Qp)
    (h4 : tag = 4 → ∀ s1 : State,
      s1.pc = (blkPl_85).base + 0x214#64 →
      s1.status = .Running → LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1 P Q Qp)
    (h5 : tag = 5 → ∀ s1 : State,
      s1.pc = (blkPl_85).base + 0x25c#64 →
      s1.status = .Running → LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1 P Q Qp)
    (h6 : tag = 6 → ∀ s1 : State,
      s1.pc = (blkPl_85).base + 0x1c4#64 →
      s1.status = .Running → LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1 P Q Qp)
    (h7 : 7 ≤ tag → ∀ s1 : State,
      s1.pc = (blkPl_85).base + 0x0d0#64 →
      s1.status = .Running → LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.readReg64 .x1 = BitVec.ofNat 64 tag →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1 P Q Qp) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s P Q Qp := by
  rcases tag with _ | _ | _ | _ | _ | _ | _ | n
  · omega
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 1#64 := hx1
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 492#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hcl1
    exact h1 rfl _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
       by simpa [arm64_norm] using hregs.x19_eq⟩
      (by simp only [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 2#64 := hx1
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 572#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hcl1
    exact h2 rfl _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
       by simpa [arm64_norm] using hregs.x19_eq⟩
      (by simp only [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 3#64 := hx1
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 396#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hcl1
    exact h3 rfl _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
       by simpa [arm64_norm] using hregs.x19_eq⟩
      (by simp only [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 4#64 := hx1
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 532#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hcl1
    exact h4 rfl _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
       by simpa [arm64_norm] using hregs.x19_eq⟩
      (by simp only [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 5#64 := hx1
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 604#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hcl1
    exact h5 rfl _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
       by simpa [arm64_norm] using hregs.x19_eq⟩
      (by simp only [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 6#64 := hx1
    refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 452#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hcl1
    exact h6 rfl _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
       by simpa [arm64_norm] using hregs.x19_eq⟩
      (by simp only [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (n + 7) := hx1
    obtain ⟨hc1, hc2, hc3, hc3_ne, hc4, hc5, hc6, hc6_ne⟩ := tag_ge7_conds (n + 7) (by omega) htag_lt
    cases hgt : BitVec.slt 3#32 ((BitVec.ofNat 64 (n + 7)).setWidth 32)
    · refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 208#64) ?_
      wp_steps
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
      intro hcl1
      exact h7 (by omega) _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
         by simpa [arm64_norm] using hregs.x19_eq⟩
        (by simp only [arm64_norm]) (by simpa [arm64_norm] using hx1')
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1 htr
    · refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 208#64) ?_
      wp_steps
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
      intro hcl1
      exact h7 (by omega) _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
         by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
         by simpa [arm64_norm] using hregs.x19_eq⟩
        (by simp only [arm64_norm]) (by simpa [arm64_norm] using hx1')
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1 htr

theorem mergeField_cps_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hint32 : Int32MergeOkWPlaced A H)
    (hskip : SkipFieldOkWPlaced A H)
    (hbytes : BytesMergeOkWPlaced A H)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {tag : ℕ} {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoSignalMessage} {res : Option ProtoSignalMessage}
    (hpc : s.pc = (blkPl_85).base + 0x16c#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (htag_ge : 1 ≤ tag) (htag_lt : tag < 2 ^ 32)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (m' : ProtoSignalMessage) (rest : List (BitVec 8)) (s1 : State),
      mergeField m tag wt bs = some (m', rest) →
      s1.pc = (blkPl_85).base + 0x0e0#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (sliceCursorAfter (sp' + 160#64) ptr bs rest ∗
          ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
          memRegion (sp' + 296#64) 48 ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
          wireSignalMessageLoopOf A (sp' + 176#64) rest.length m')
        (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr bs res)
        (tryFromQp s0))
    (hnone : mergeField m tag wt bs = none → res = none) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr bs ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopOf A (sp' + 176#64) bs.length m)
      (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr bs res)
      (tryFromQp s0) := by
  refine dispatch_tag_cps_placed hpc hrun hregs hx1 htag_ge htag_lt hsp hcl htr
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hx1_1 hsp1 hcl1 htr1 => ?_)
  · subst htag
    exact mergeRatchetKey_cps_placed hS hbytes hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hcl1 htr1 hlen
      (fun v rest s2 hm => hcont { m with ratchetKey := some v } rest s2 (by simp [mergeField, hm]))
      (fun hm => hnone (by simp [mergeField, hm]))
  · subst htag
    exact mergeCounter_cps_placed hS hint32 hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hcl1 htr1 hlen
      (fun v rest s2 hm => hcont { m with counter := some v } rest s2 (by simp [mergeField, hm]))
      (fun hm => hnone (by simp [mergeField, hm]))
  · subst htag
    exact mergePrevCounter_cps_placed hS hint32 hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hcl1 htr1 hlen
      (fun v rest s2 hm => hcont { m with previousCounter := some v } rest s2 (by simp [mergeField, hm]))
      (fun hm => hnone (by simp [mergeField, hm]))
  · subst htag
    exact mergeCiphertext_cps_placed hS hbytes hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hcl1 htr1 hlen
      (fun v rest s2 hm => hcont { m with ciphertext := some v } rest s2 (by simp [mergeField, hm]))
      (fun hm => hnone (by simp [mergeField, hm]))
  · subst htag
    exact mergePqRatchet_cps_placed hS hbytes hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hcl1 htr1 hlen
      (fun v rest s2 hm => hcont { m with pqRatchet := some v } rest s2 (by simp [mergeField, hm]))
      (fun hm => hnone (by simp [mergeField, hm]))
  · subst htag
    exact mergeAddresses_cps_placed hS hbytes hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hcl1 htr1 hlen
      (fun v rest s2 hm => hcont { m with addresses := some v } rest s2 (by simp [mergeField, hm]))
      (fun hm => hnone (by simp [mergeField, hm]))
  · rcases Nat.exists_eq_add_of_le' htag with ⟨n, rfl⟩
    exact mergeSkipField_cps_placed hskip hpc1 hrun1 hregs1 (hx0_1.trans hx0) hx1_1 htag_lt
      hsp1 hcl1 htr1 hlen
      (fun rest s2 hs => hcont m rest s2 (by simp [mergeField, recursionLimit, hs]))
      (fun hs => hnone (by simp [mergeField, recursionLimit, hs]))

theorem SepWPp.advance_cursor_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {bs rest : List (BitVec 8)} {res : Option ProtoSignalMessage} {R : SepProp}
    (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k)
    (h : SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest ∗ R)
      (loopExitPostPlaced A s0 sp' x19 x20 x21 x23
        (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest res)
      (tryFromQp s0)) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAfter (sp' + 160#64) ptr bs rest ∗ R)
      (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr bs res)
      (tryFromQp s0) := by
  rw [sliceCursorAfter_eq_take_cursorAt (sp' + 160#64) ptr bs rest hsuf]
  rcases hsuf with ⟨k, hkl, rfl⟩
  have hk : bs.length - (bs.drop k).length = k := by simp; omega
  rw [hk] at h ⊢
  refine SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 160#64) (ptr + BitVec.ofNat 64 k) (bs.drop k) ∗ R) ∗
      (ptr ↦ₛ bs.take k))
    (by bi_entail) ?_
  exact SepWPp.frame_tryFrom h (fun _ _ hqm => loopExitPostPlaced_append_prefix hkl hqm)

theorem loopExitEmpty_298_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : ProtoSignalMessage} {res : Option ProtoSignalMessage}
    (hpc : s.pc = (blkPl_85).base + 0x298#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hres : res = some m) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr bs ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopOf A (sp' + 176#64) bs.length m)
      (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr bs res)
      (tryFromQp s0) := by
  subst hres
  refine SepWPp.of_sepWP_end_placed hcl ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hcl1
  refine ⟨⟨⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
    by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
    by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
    by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
    by simpa [arm64_norm] using hregs.x19_eq⟩,
    by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp, hcl1,
    by simpa [arm64_norm] using htr⟩, ?_⟩
  simp only [arm64_norm]
  exact Entails.trans
    (trans_sub (wireSignalMessageLoopOf_entails_of A (sp' + 176#64) bs.length m))
    (loopExitMem_ok_intro A sp' ptr bs m)

theorem loopCheck_e0_empty_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {m : ProtoSignalMessage} {res : Option ProtoSignalMessage}
    (hpc : s.pc = (blkPl_85).base + 0x0e0#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hres : res = some m) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr [] ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopOf A (sp' + 176#64) ([] : List (BitVec 8)).length m)
      (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr [] res)
      (tryFromQp s0) := by
  have hexit := @loopExitEmpty_298_wp_placed _ A H s0
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs.x29
  unfold sliceCursorAt
  simp only [sepConj_assoc]
  refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 664#64) ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hcl1
  refine SepWPp.mono_pre ?_
    (hexit (sp' := sp') (x19 := x19) (x20 := x20) (x21 := x21) (x23 := x23)
      (ptr := ptr) (bs := []) (m := m) (res := res)
      (by simp only [arm64_norm])
      (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
       by simpa [arm64_norm] using hregs.x19_eq⟩
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
      hcl1 htr hres)
  unfold sliceCursorAt; bi_entail

theorem loopCheck_e0_cons_cps_placed [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {b0 : BitVec 8} {bs1 : List (BitVec 8)} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_85).base + 0x0e0#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlen : (b0 :: bs1).length < 2 ^ 63)
    (hcont : ∀ s1 : State,
      s1.pc = (blkPl_85).base + 0x0f0#64 →
      s1.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s1 →
      s1.readReg64 .x28 = sp' + 160#64 →
      s1.readReg64 .x27 = sp' + 168#64 →
      s1.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s1
        (sliceCursorAt (sp' + 160#64) ptr (b0 :: bs1) ∗
          ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗ F) Q Qp) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr (b0 :: bs1) ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗ F) Q Qp := by
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 352#64 := hregs.x29
  obtain ⟨hc_eq, hc_ne⟩ := cons_len_bv64_ne_zero b0 bs1 hlen
  unfold sliceCursorAt
  simp only [sepConj_assoc]
  refine SepWPp.of_sepWP_placed hcl (mid := (blkPl_85).base + 240#64) ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  intro hcl1
  refine SepWPp.mono_pre ?_
    (hcont _
      (by simp only [arm64_norm])
      (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x26, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23_eq, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21_eq, by simpa [arm64_norm] using hregs.x20_eq,
       by simpa [arm64_norm] using hregs.x19_eq⟩
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
      hcl1 htr)
  unfold sliceCursorAt; bi_entail

theorem decodeLoop_f0_step_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hvarint : DecodeVarintSliceOkWPlaced A H)
    (hint32 : Int32MergeOkWPlaced A H)
    (hskip : SkipFieldOkWPlaced A H)
    (hbytes : BytesMergeOkWPlaced A H)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {fuel : ℕ} {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : ProtoSignalMessage}
    (ih : ∀ {s : State} {ptr : BitVec 64} {bs : List (BitVec 8)} {m : ProtoSignalMessage},
      s.pc = (blkPl_85).base + 0x0e0#64 →
      s.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s →
      s.spAligned = true → LibsignalCodeRoLoaded lsmpl s.mem →
      s.trace = s0.trace →
      bs.length ≤ fuel →
      bs.length < 2 ^ 63 →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s
        (sliceCursorAt (sp' + 160#64) ptr bs ∗
          ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
          memRegion (sp' + 296#64) 48 ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
          wireSignalMessageLoopOf A (sp' + 176#64) bs.length m)
        (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr bs (decodeLoop fuel m bs))
        (tryFromQp s0))
    (hpc : s.pc = (blkPl_85).base + 0x0f0#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hx28 : s.readReg64 .x28 = sp' + 160#64)
    (hx27 : s.readReg64 .x27 = sp' + 168#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hfuel : (b0 :: bs1).length ≤ fuel + 1)
    (hlen : (b0 :: bs1).length < 2 ^ 63) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr (b0 :: bs1) ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageLoopOf A (sp' + 176#64) (b0 :: bs1).length m)
      (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr (b0 :: bs1)
        (decodeLoop (fuel + 1) m (b0 :: bs1)))
      (tryFromQp s0) := by
  refine decodeKey_cps_placed hS hvarint hpc hrun hregs hx28 hx27 hx2 hsp hcl htr hlen
    (fun tag wt rest1 s1 hdk hpc1 hrun1 hregs1 hsp1 hcl1 htr1 hx0_1 hx1_1 => ?_)
    (fun hdk_none => by simp [decodeLoop, hdk_none])
  obtain ⟨k1, hk1_pos, hk1_le, hrest1_eq, htag_lt, htag_ge⟩ := decodeKey_suffix hdk
  have hrest1_len : rest1.length = (b0 :: bs1).length - k1 := by simp [hrest1_eq]
  refine SepWPp.advance_cursor_placed ⟨k1, hk1_le, hrest1_eq⟩ ?_
  refine SepWPp.mono_pre ?_
    (mergeField_cps_placed (m := m) hS hint32 hskip hbytes hpc1 hrun1 hregs1 hx0_1 hx1_1 htag_ge htag_lt
      hsp1 hcl1 htr1 (by omega)
      (fun m' rest2 s2 hmf hpc2 hrun2 hregs2 hsp2 hcl2 htr2 => ?_)
      (fun hmf_none => by simp [decodeLoop, hdk, hmf_none]))
  · exact trans_sub (wireSignalMessageLoopOf_mono A (sp' + 176#64) (m := rest1.length) (n := (b0 :: bs1).length) m (by omega))
  obtain ⟨k2, hk2_le, hrest2_eq⟩ := mergeField_suffix hmf
  have hrest2_len : rest2.length = rest1.length - k2 := by simp [hrest2_eq]
  refine SepWPp.advance_cursor_placed ⟨k2, hk2_le, hrest2_eq⟩ ?_
  have hloop_eq : decodeLoop (fuel + 1) m (b0 :: bs1) = decodeLoop fuel m' rest2 := by
    simp [decodeLoop, hdk, hmf]
  rw [hloop_eq]
  exact ih hpc2 hrun2 hregs2 hsp2 hcl2 htr2 (by omega) (by omega)

theorem decodeLoop_e0_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hvarint : DecodeVarintSliceOkWPlaced A H)
    (hint32 : Int32MergeOkWPlaced A H)
    (hskip : SkipFieldOkWPlaced A H)
    (hbytes : BytesMergeOkWPlaced A H)
    {s0 : State} {sp' x19 x20 x21 x23 : BitVec 64} :
    ∀ (fuel : ℕ) {s : State} {ptr : BitVec 64} {bs : List (BitVec 8)} {m : ProtoSignalMessage},
      s.pc = (blkPl_85).base + 0x0e0#64 →
      s.status = .Running →
      LoopRegs sp' x19 x20 x21 x23 s →
      s.spAligned = true → LibsignalCodeRoLoaded lsmpl s.mem →
      s.trace = s0.trace →
      bs.length ≤ fuel →
      bs.length < 2 ^ 63 →
      SepWPp (tryFromPlacedProg H)
        ((blkPl_85).base + 0x3b0#64) s
        (sliceCursorAt (sp' + 160#64) ptr bs ∗
          ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
          memRegion (sp' + 296#64) 48 ∗
          A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
          wireSignalMessageLoopOf A (sp' + 176#64) bs.length m)
        (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr bs (decodeLoop fuel m bs))
        (tryFromQp s0)
  | 0, s, ptr, bs, m, hpc, hrun, hregs, hsp, hcl, htr, hfuel, _ => by
    cases bs with
    | nil => exact loopCheck_e0_empty_wp_placed hpc hrun hregs hsp hcl htr rfl
    | cons b0 bs1 => simp at hfuel
  | fuel + 1, s, ptr, bs, m, hpc, hrun, hregs, hsp, hcl, htr, hfuel, hlen => by
    cases bs with
    | nil => exact loopCheck_e0_empty_wp_placed hpc hrun hregs hsp hcl htr rfl
    | cons b0 bs1 =>
      refine loopCheck_e0_cons_cps_placed hpc hrun hregs hsp hcl htr hlen ?_
      intro s1 hpc1 hrun1 hregs1 hx28_1 hx27_1 hx2_1 hsp1 hcl1 htr1
      exact decodeLoop_f0_step_wp_placed hS hvarint hint32 hskip hbytes
        (decodeLoop_e0_wp_placed hS hvarint hint32 hskip hbytes fuel)
        hpc1 hrun1 hregs1 hx28_1 hx27_1 hx2_1 hsp1 hcl1 htr1 hfuel hlen

theorem decodeLoop_f0_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H)
    (hvarint : DecodeVarintSliceOkWPlaced A H)
    (hint32 : Int32MergeOkWPlaced A H)
    (hskip : SkipFieldOkWPlaced A H)
    (hbytes : BytesMergeOkWPlaced A H)
    {s0 s : State} {sp' x19 x20 x21 x23 ptr : BitVec 64}
    {fuel : ℕ} {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : ProtoSignalMessage}
    (hpc : s.pc = (blkPl_85).base + 0x0f0#64)
    (hrun : s.status = .Running)
    (hregs : LoopRegs sp' x19 x20 x21 x23 s)
    (hx28 : s.readReg64 .x28 = sp' + 160#64)
    (hx27 : s.readReg64 .x27 = sp' + 168#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hfuel : (b0 :: bs1).length ≤ fuel + 1)
    (hlen : (b0 :: bs1).length < 2 ^ 63)
    (hm : m = emptyProtoSignalMessage := by rfl) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (sliceCursorAt (sp' + 160#64) ptr (b0 :: bs1) ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageOf A (sp' + 176#64) m)
      (loopExitPostPlaced A s0 sp' x19 x20 x21 x23 ptr (b0 :: bs1)
        (decodeLoop (fuel + 1) m (b0 :: bs1)))
      (tryFromQp s0) := by
  subst hm
  refine SepWPp.mono_pre ?_
    (decodeLoop_f0_step_wp_placed hS hvarint hint32 hskip hbytes
      (decodeLoop_e0_wp_placed hS hvarint hint32 hskip hbytes fuel)
      hpc hrun hregs hx28 hx27 hx2 hsp hcl htr hfuel hlen)
  exact trans_sub (wireSignalMessageOf_emptyMsg_entails_loopOf A (sp' + 176#64) (b0 :: bs1).length)

end LoopBodyOpaqueFields
end LoopBodyOpaqueErr

end CryptoVerification.LibsignalTripleRatchet.Wire

