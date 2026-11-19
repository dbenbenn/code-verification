/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefs
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.Defs
import LibsignalBinary.Proofs.FnOffEq
import ProofLib.Sep
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `decode_varint_slow` hook proof and full `PublicKey::deserialize` spec/proof
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.Wire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSession.FindReceiverChainIndex

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

attribute [local irreducible] Program.fetch Program.externAt?

/-! ## `decode_varint_slow::<&mut &[u8]>` hook proof -/

theorem varintSlow_take_min10 (bs : List (BitVec 8)) :
    varintSlow (bs.take (min 10 bs.length)) = varintSlow bs := by
  simp only [varintSlow, List.take_take]
  have hmin : min 10 (min 10 bs.length) = min 10 bs.length := by omega
  have h10 : (bs.take (min 10 bs.length)) = bs.take 10 := by
    rw [List.take_eq_take_iff]
    omega
  rw [hmin, h10]

theorem stackAt_varintSlow_split (sp : BitVec 64) :
    stackAt sp varintSlowStack =
      stackAt (sp - 64#64) decodeErrorHookStack ∗
      (∃∗ w0 : BitVec 64, (sp - 64#64) ↦₆₄ w0) ∗
      memRegion (sp - 64#64 + 8#64) 40 ∗
      memRegion (sp - 64#64 + 48#64) 16 := by
  dsimp only [stackAt, varintSlowStack, decodeErrorHookStack, allocHookStack]
  sep_interval_eq

theorem stackAt_varintSlow_fold (sp : BitVec 64) :
    stackAt (sp - 64#64) decodeErrorHookStack ∗
      (memRegion (sp - 64#64) 48 ∗
      memRegion (sp - 64#64 + 48#64) 16) =
    stackAt sp varintSlowStack := by
  dsimp only [stackAt, varintSlowStack, decodeErrorHookStack, allocHookStack]
  sep_interval_eq

theorem keepsFrozen_write64_of_pointsTo64 {m : Memory} {a v₀ : BitVec 64} {R : SepProp}
    (v : BitVec 64) (h : m ⊨ (a ↦₆₄ v₀) ∗ R) :
    m.KeepsFrozen (m.write64 a v) :=
  Memory.keepsFrozen_write64 ((IsBlock.pointsTo64 a v₀).canWrite (by decide) h) v

theorem satisfies_write64_of_pointsTo64 {m : Memory} {a v₀ : BitVec 64} {R : SepProp}
    (v : BitVec 64) (h : m ⊨ (a ↦₆₄ v₀) ∗ R) :
    m.write64 a v ⊨ (a ↦₆₄ v) ∗ R :=
  IsBlock.write64 (IsBlock.pointsTo64 a v₀) h v

theorem varintSlow_ok_ret_regs (s0 : State) (m' : Memory) (v : BitVec 64) :
    let sf := retHook (fun s => ((s.setMem m').writeReg64 .x0 0#64).writeReg64 .x1 v) s0
    sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = v ∧ sf.trace = s0.trace :=
  ⟨rfl, rfl, rfl⟩

theorem decodeVarintSlow_hookOk {A : RustAlloc} {fromHook : State → State}
    (hFrom : HookOk fromHook (decodeErrorFromSpec A)) :
    HookOk (decodeVarintSlowHook fromHook) (decodeVarintSlowSpec A) := by
  intro ⟨slotA, slot, ptr, bs⟩ R s0 hrun hpre hsp
  simp only [decodeVarintSlowSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hlen_lt⟩, hmem⟩
  have hread_slotA := (IsBlock.pointsTo64 slotA slot).read hmem
  have hmem_slot : s0.mem ⊨ (slot ↦₆₄ ptr) ∗
      ((slotA ↦₆₄ slot) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt s0.sp varintSlowStack ∗ R) :=
    Satisfies.mono (by bi_entail) hmem
  have hread_slot := (IsBlock.pointsTo64 slot ptr).read hmem_slot
  have hmem_len : s0.mem ⊨ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((slot ↦₆₄ ptr) ∗ (slotA ↦₆₄ slot) ∗
        (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt s0.sp varintSlowStack ∗ R) :=
    Satisfies.mono (by bi_entail) hmem
  have hread_len := (IsBlock.pointsTo64 (slot + 8#64) (BitVec.ofNat 64 bs.length)).read hmem_len
  have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen_lt]
  have hbs_split : (ptr ↦ₛ bs) =
      (ptr ↦ₛ bs.take (min 10 bs.length)) ∗
      ((ptr + BitVec.ofNat 64 (bs.take (min 10 bs.length)).length) ↦ₛ bs.drop (min 10 bs.length)) := by
    conv_lhs => rw [← List.take_append_drop (min 10 bs.length) bs]
    exact pointsToBytes_append ptr _ _
  have hmem_bs : s0.mem ⊨ (ptr ↦ₛ bs.take (min 10 bs.length)) ∗
      (((ptr + BitVec.ofNat 64 (bs.take (min 10 bs.length)).length) ↦ₛ bs.drop (min 10 bs.length)) ∗
        (slotA ↦₆₄ slot) ∗ (slot ↦₆₄ ptr) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.pool ∗ stackAt s0.sp varintSlowStack ∗ R) :=
    Satisfies.mono (by rw [hbs_split]; bi_entail) hmem
  obtain ⟨_, hread_bs⟩ := (IsBlock.pointsToBytes ptr (bs.take (min 10 bs.length))).read hmem_bs
  have htake_len : (bs.take (min 10 bs.length)).length = min 10 bs.length := by simp
  rw [htake_len] at hread_bs
  dsimp only [decodeVarintSlowHook]
  rw [hx0, hread_slotA, hread_slot, hread_len, hlen_toNat, hread_bs, varintSlow_take_min10]
  cases hvs : varintSlow bs with
  | some vk =>
    rcases vk with ⟨v, k⟩
    dsimp only
    have hkf1 := keepsFrozen_write64_of_pointsTo64 (ptr + BitVec.ofNat 64 k) hmem_slot
    have hw1 := satisfies_write64_of_pointsTo64 (ptr + BitVec.ofNat 64 k) hmem_slot
    have hmem1 : (s0.mem.write64 slot (ptr + BitVec.ofNat 64 k)) ⊨
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗ (slotA ↦₆₄ slot) ∗
          (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt s0.sp varintSlowStack ∗ R) :=
      Satisfies.mono (by bi_entail) hw1
    have hkf2 := hkf1.trans (keepsFrozen_write64_of_pointsTo64 (BitVec.ofNat 64 (bs.length - k)) hmem1)
    have hw2 := satisfies_write64_of_pointsTo64 (BitVec.ofNat 64 (bs.length - k)) hmem1
    refine ⟨hkf2, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
    have ⟨hr0, hr1, htr⟩ := varintSlow_ok_ret_regs s0
      ((s0.mem.write64 slot (ptr + BitVec.ofNat 64 k)).write64
        (slot + 8#64) (BitVec.ofNat 64 (bs.length - k))) v
    dsimp only [decodeVarintSlowSpec]
    rw [hvs, hr0, hr1, htr]
    simp only [sepConj_assoc, sepConj_pure_left_comm, satisfies_pure_sepConj, true_and]
    exact Satisfies.mono (by bi_entail) hw2
  | none =>
    dsimp only
    set k := min 10 bs.length
    set kindA := s0.sp - 64#64
    have hmem_stk := hmem
    rw [stackAt_varintSlow_split s0.sp] at hmem_stk
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      satisfies_sepExists] at hmem_stk
    rcases hmem_stk with ⟨w0, hmem_stk⟩
    have hmem_slot1 : s0.mem ⊨ (slot ↦₆₄ ptr) ∗
        (((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (kindA ↦₆₄ w0) ∗
          (slotA ↦₆₄ slot) ∗ (ptr ↦ₛ bs) ∗ A.pool ∗
          stackAt kindA decodeErrorHookStack ∗
          memRegion (kindA + 8#64) 40 ∗ memRegion (kindA + 48#64) 16 ∗ R) :=
      Satisfies.mono (by dsimp only [kindA]; bi_entail) hmem_stk
    have hkf1 := keepsFrozen_write64_of_pointsTo64 (ptr + BitVec.ofNat 64 k) hmem_slot1
    have hw1 := satisfies_write64_of_pointsTo64 (ptr + BitVec.ofNat 64 k) hmem_slot1
    have hmem_slot2 : (s0.mem.write64 slot (ptr + BitVec.ofNat 64 k)) ⊨
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((kindA ↦₆₄ w0) ∗ (slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗
          (slotA ↦₆₄ slot) ∗ (ptr ↦ₛ bs) ∗ A.pool ∗
          stackAt kindA decodeErrorHookStack ∗
          memRegion (kindA + 8#64) 40 ∗ memRegion (kindA + 48#64) 16 ∗ R) :=
      Satisfies.mono (by bi_entail) hw1
    have hkf2 := hkf1.trans (keepsFrozen_write64_of_pointsTo64 (BitVec.ofNat 64 (bs.length - k)) hmem_slot2)
    have hw2 := satisfies_write64_of_pointsTo64 (BitVec.ofNat 64 (bs.length - k)) hmem_slot2
    have hmem_kind : ((s0.mem.write64 slot (ptr + BitVec.ofNat 64 k)).write64
        (slot + 8#64) (BitVec.ofNat 64 (bs.length - k))) ⊨
        (kindA ↦₆₄ w0) ∗
        (((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k)) ∗
          (slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗
          (slotA ↦₆₄ slot) ∗ (ptr ↦ₛ bs) ∗ A.pool ∗
          stackAt kindA decodeErrorHookStack ∗
          memRegion (kindA + 8#64) 40 ∗ memRegion (kindA + 48#64) 16 ∗ R) :=
      Satisfies.mono (by bi_entail) hw2
    have hkf3 := hkf2.trans (keepsFrozen_write64_of_pointsTo64 invalidVarintWord hmem_kind)
    have hw3 := satisfies_write64_of_pointsTo64 invalidVarintWord hmem_kind
    set s1 : State :=
      ({ s0 with
          sp := kindA,
          mem := ((s0.mem.write64 slot (ptr + BitVec.ofNat 64 k)).write64
            (slot + 8#64) (BitVec.ofNat 64 (bs.length - k))).write64 kindA invalidVarintWord }).writeReg64
        .x0 kindA
    have hs1_run : s1.status = .Running := hrun
    have hs1_sp : s1.spAligned = true := s0.spAligned_sub 64#64 hsp
    have hkind_noHeap : KindNoHeap invalidVarintWord := by decide +kernel
    set R_from : SepProp :=
      (slotA ↦₆₄ slot) ∗ (ptr ↦ₛ bs) ∗
      (slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k)) ∗
      memRegion (kindA + 48#64) 16 ∗ R
    have hs1_x0 : s1.readReg64 .x0 = kindA := rfl
    have hs1_sp_eq : s1.sp = kindA := rfl
    have hs1_tr_eq : s1.trace = s0.trace := rfl
    have hw3' : s1.mem ⊨
        (kindA ↦₆₄ invalidVarintWord) ∗ memRegion (kindA + 8#64) 40 ∗
        A.pool ∗ stackAt kindA decodeErrorHookStack ∗ R_from :=
      Satisfies.mono (by dsimp only [R_from]; bi_entail) hw3
    have hs1_pre : s1.mem ⊨ (decodeErrorFromSpec A).pre (kindA, invalidVarintWord) s1 ∗ R_from := by
      simp only [decodeErrorFromSpec, hs1_sp_eq, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hs1_x0, hkind_noHeap⟩, hw3'⟩
    have ⟨hkf_s2, hsym_s2, hout⟩ := hFrom (kindA, invalidVarintWord) R_from s1 hs1_run hs1_pre hs1_sp
    set s2 := fromHook s1
    rcases hout with ⟨⟨_, _, hst_s2⟩, hcs_s2, hpost_s2⟩ | ⟨hpan_s2, hpost_s2⟩ | ⟨code, hex_s2, hpost_s2⟩ | ⟨hoom_s2, hpost_s2⟩
    · rw [hst_s2]
      dsimp only
      rcases hcs_s2 with ⟨_, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hvregs⟩
      refine ⟨hkf3.trans hkf_s2, hsym_s2,
        Or.inl ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hvregs⟩, ?_⟩⟩
      dsimp only [decodeErrorFromSpec] at hpost_s2
      rw [hs1_sp_eq, hs1_tr_eq] at hpost_s2
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost_s2
      rcases hpost_s2 with ⟨⟨hx0_ne, htr⟩, hmem_s2⟩
      dsimp only [decodeVarintSlowSpec]
      rw [hvs]
      change s2.mem ⊨
        (⌜s2.trace = s0.trace⌝ ∗ (slotA ↦₆₄ slot) ∗ (ptr ↦ₛ bs) ∗ A.pool ∗
          stackAt s0.sp varintSlowStack ∗
          (⌜1#64 = 1#64 ∧ s2.readReg64 .x0 ≠ 0#64⌝ ∗
            decodeErrorAtStackLen A (s2.readReg64 .x0) 0 ∗
            (slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗
            ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k)))) ∗ R
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨htr, ?_⟩
      simp only [sepConj_assoc, sepConj_pure_left_comm, satisfies_pure_sepConj, true_and]
      refine ⟨hx0_ne, ?_⟩
      dsimp only [R_from, kindA, k] at hmem_s2 ⊢
      exact Satisfies.mono (by rw [← stackAt_varintSlow_fold s0.sp]; sep_interval) hmem_s2
    · rw [hpan_s2]
      dsimp only
      refine ⟨hkf3.trans hkf_s2, hsym_s2, Or.inr (Or.inl ⟨hpan_s2, ?_⟩)⟩
      have hpan_eq :
          (decodeErrorFromSpec A).onPanic (kindA, invalidVarintWord) s1 s2 =
          (decodeVarintSlowSpec A).onPanic (slotA, slot, ptr, bs) s0 s2 := rfl
      rw [hpan_eq] at hpost_s2
      dsimp only [decodeVarintSlowSpec] at hpost_s2 ⊢
      have hR_eq : R_from = ((slotA ↦₆₄ slot) ∗ (ptr ↦ₛ bs) ∗ (slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗
          ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k)) ∗ memRegion (kindA + 48#64) 16) ∗ R := by
        dsimp only [R_from]; simp only [sepConj_assoc]
      rw [hR_eq, ← sepConj_assoc] at hpost_s2
      exact Satisfies.mono
        (sepConj_mono_left (by rw [sepConj_assoc]; exact sepConj_mono_right (entails_anyHeap _)))
        hpost_s2
    · exfalso
      exact not_satisfies_false_sepConj hpost_s2
    · exfalso
      exact not_satisfies_false_sepConj hpost_s2

theorem pointsTo64_zero_byte0 (a : BitVec 64) :
    (a ↦₆₄ 0#64) = (a ↦₈ 0#8) ∗ ((a + 1#64) ↦ₛ List.replicate 7 0#8) := by
  rw [pointsTo64_eq_pointsToBytes]
  simp only [unpack64, List.replicate, pointsToBytes_cons, pointsToBytes_nil,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
  rfl

theorem pointsTo64_two_byte0 (a : BitVec 64) :
    (a ↦₆₄ 2#64) = (a ↦₈ 2#8) ∗ ((a + 1#64) ↦ₛ List.replicate 7 0#8) := by
  rw [pointsTo64_eq_pointsToBytes]
  simp only [unpack64, List.replicate, pointsToBytes_cons, pointsToBytes_nil,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
  rfl

/-- The 33-byte result written at `sret` by `PublicKey::deserialize` (`0x3db50`). -/
@[expose] def deserializeResult33At (sret : BitVec 64) : Except SignalProtocolError PublicKey → SepProp
  | .ok pk => (sret ↦₈ 0#8) ∗ ((sret + 1#64) ↦ₛ pk.bytes.toList)
  | .error .noKeyTypeIdentifier =>
    (sret ↦₈ 1#8) ∗ memRegion (sret + 1#64) 7 ∗
      ((sret + 8#64) ↦₈ 0#8) ∗ memRegion (sret + 9#64) 24
  | .error (.badKeyType t) =>
    (sret ↦₈ 1#8) ∗ memRegion (sret + 1#64) 7 ∗
      ((sret + 8#64) ↦₈ 1#8) ∗ ((sret + 9#64) ↦₈ t) ∗ memRegion (sret + 10#64) 23
  | .error (.badKeyLength n) =>
    (sret ↦₈ 1#8) ∗ memRegion (sret + 1#64) 7 ∗
      ((sret + 8#64) ↦₈ 2#8) ∗ memRegion (sret + 9#64) 7 ∗
      ((sret + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗ memRegion (sret + 24#64) 9
  | .error _ => ⌜False⌝

/-- Error-path specification of `PublicKey::deserialize` when `bs = []` (`.noKeyTypeIdentifier`). -/
private def deserializeEmptySpec (b : BitVec 64) :
    Spec (BitVec 64 × BitVec 64 × BitVec 8 × BitVec 64) where
  pre := fun (ptr, sret, tag0, w8) s =>
    ⌜s.readReg64 .x0 = ptr ∧ s.readReg64 .x1 = 0#64 ∧
      s.readReg64 .x8 = sret ∧ b &&& 0xfff#64 = 0#64⌝ ∗
    (sret ↦₈ tag0) ∗ ((sret + 8#64) ↦₆₄ w8)
  post := fun (_, sret, _, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (sret ↦₈ 1#8) ∗ ((sret + 8#64) ↦₆₄ 0#64)

/-- Error-path specification of `PublicKey::deserialize` when `bs = b0 :: b1` and `b0 ≠ 5#8`
(`.badKeyType b0`). -/
private def deserializeBadTypeSpec (b : BitVec 64) :
    Spec (BitVec 64 × BitVec 8 × Nat × BitVec 64 × BitVec 8 × BitVec 8 × BitVec 8) where
  pre := fun (ptr, b0, len1, sret, tag0, w8, w9) s =>
    ⌜s.readReg64 .x0 = ptr ∧ (s.readReg64 .x1).toNat = len1 + 1 ∧
      s.readReg64 .x8 = sret ∧ len1 + 1 < 2 ^ 63 ∧ b0 ≠ 5#8 ∧
      b &&& 0xfff#64 = 0#64⌝ ∗
    (ptr ↦₈ b0) ∗ (sret ↦₈ tag0) ∗ ((sret + 8#64) ↦₈ w8) ∗ ((sret + 9#64) ↦₈ w9)
  post := fun (ptr, b0, _, sret, _, _, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (ptr ↦₈ b0) ∗ (sret ↦₈ 1#8) ∗ ((sret + 8#64) ↦₈ 1#8) ∗ ((sret + 9#64) ↦₈ b0)

/-- Error-path specification of `PublicKey::deserialize` when `bs = 5#8 :: b1` and `b1.length < 32`
(`.badKeyLength (b1.length + 1)`). -/
private def deserializeBadLenSpec (b : BitVec 64) :
    Spec (BitVec 64 × Nat × BitVec 64 × BitVec 8 × BitVec 64 × BitVec 64) where
  pre := fun (ptr, len1, sret, tag0, w8, w16) s =>
    ⌜s.readReg64 .x0 = ptr ∧ (s.readReg64 .x1).toNat = len1 + 1 ∧
      s.readReg64 .x8 = sret ∧ len1 < 32 ∧
      b &&& 0xfff#64 = 0#64⌝ ∗
    (ptr ↦₈ 5#8) ∗ (sret ↦₈ tag0) ∗ ((sret + 8#64) ↦₆₄ w8) ∗ ((sret + 16#64) ↦₆₄ w16)
  post := fun (ptr, len1, sret, _, _, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (ptr ↦₈ 5#8) ∗ (sret ↦₈ 1#8) ∗ ((sret + 8#64) ↦₆₄ 2#64) ∗
    ((sret + 16#64) ↦₆₄ BitVec.ofNat 64 (len1 + 1))

@[expose] def deserializeFullPlacedSpec [LibsignalPlacement] : Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (ptr, bs, sret) s =>
    ⌜s.readReg64 .x0 = ptr ∧ (s.readReg64 .x1).toNat = bs.length ∧
      s.readReg64 .x8 = sret ∧ bs.length < 2 ^ 63⌝ ∗
    (ptr ↦ₛ bs) ∗
    memRegion sret 33 ∗
    (lsLogFilterAddr ↦₆₄ 0#64)
  post := fun (ptr, bs, sret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (ptr ↦ₛ bs) ∗
    deserializeResult33At sret (PublicKey.deserialize bs) ∗
    (lsLogFilterAddr ↦₆₄ 0#64)

private def deserializeEmptyPlacedSpec :
    Spec (BitVec 64 × BitVec 64 × BitVec 8 × BitVec 64) where
  pre := fun (ptr, sret, tag0, w8) s =>
    ⌜s.readReg64 .x0 = ptr ∧ s.readReg64 .x1 = 0#64 ∧
      s.readReg64 .x8 = sret⌝ ∗
    (sret ↦₈ tag0) ∗ ((sret + 8#64) ↦₆₄ w8)
  post := fun (_, sret, _, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (sret ↦₈ 1#8) ∗ ((sret + 8#64) ↦₆₄ 0#64)

private theorem deserializeEmpty_placed_ok [LibsignalPlacement] (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_201).rebase (blkPl_201).base H)
      (blkPl_201).base
      deserializeEmptyPlacedSpec := by
  simp only [deserializeEmptyPlacedSpec]
  wp_init g s0
  obtain ⟨ptr, sret, tag0, w8⟩ := g
  dsimp only at *
  subst h_1 h
  wp_steps
  wp_done

private def deserializeBadTypePlacedSpec :
    Spec (BitVec 64 × BitVec 8 × Nat × BitVec 64 × BitVec 8 × BitVec 8 × BitVec 8) where
  pre := fun (ptr, b0, len1, sret, tag0, w8, w9) s =>
    ⌜s.readReg64 .x0 = ptr ∧ (s.readReg64 .x1).toNat = len1 + 1 ∧
      s.readReg64 .x8 = sret ∧ len1 + 1 < 2 ^ 63 ∧ b0 ≠ 5#8⌝ ∗
    (ptr ↦₈ b0) ∗ (sret ↦₈ tag0) ∗ ((sret + 8#64) ↦₈ w8) ∗ ((sret + 9#64) ↦₈ w9)
  post := fun (ptr, b0, _, sret, _, _, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (ptr ↦₈ b0) ∗ (sret ↦₈ 1#8) ∗ ((sret + 8#64) ↦₈ 1#8) ∗ ((sret + 9#64) ↦₈ b0)

private theorem deserializeBadType_placed_ok [LibsignalPlacement] (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_201).rebase (blkPl_201).base H)
      (blkPl_201).base
      deserializeBadTypePlacedSpec := by
  simp only [deserializeBadTypePlacedSpec]
  wp_init g s0
  obtain ⟨ptr, b0, len1, sret, tag0, w8, w9⟩ := g
  dsimp only at *
  subst h_1 h_3
  have hx1_ne : s0.readReg64 (Reg.gpr 1#5) ≠ 0#64 := by
    intro hc; rw [hc] at h_2; simp at h_2
  wp_steps
  wp_done

private def deserializeBadLenPlacedSpec :
    Spec (BitVec 64 × Nat × BitVec 64 × BitVec 8 × BitVec 64 × BitVec 64) where
  pre := fun (ptr, len1, sret, tag0, w8, w16) s =>
    ⌜s.readReg64 .x0 = ptr ∧ (s.readReg64 .x1).toNat = len1 + 1 ∧
      s.readReg64 .x8 = sret ∧ len1 < 32⌝ ∗
    (ptr ↦₈ 5#8) ∗ (sret ↦₈ tag0) ∗ ((sret + 8#64) ↦₆₄ w8) ∗ ((sret + 16#64) ↦₆₄ w16)
  post := fun (ptr, len1, sret, _, _, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (ptr ↦₈ 5#8) ∗ (sret ↦₈ 1#8) ∗ ((sret + 8#64) ↦₆₄ 2#64) ∗
    ((sret + 16#64) ↦₆₄ BitVec.ofNat 64 (len1 + 1))

private theorem deserializeBadLen_placed_ok [LibsignalPlacement] (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_201).rebase (blkPl_201).base H)
      (blkPl_201).base
      deserializeBadLenPlacedSpec := by
  simp only [deserializeBadLenPlacedSpec]
  wp_init g s0
  obtain ⟨ptr, len1, sret, tag0, w8, w16⟩ := g
  dsimp only at *
  subst h_1 h_3
  have hx1_ne : s0.readReg64 (Reg.gpr 1#5) ≠ 0#64 := by
    intro hc; rw [hc] at h_2; simp at h_2
  have hx1_eq : s0.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (len1 + 1) := by
    rw [← h_2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  wp_steps
  wp_if hlo
  · wp_steps
    wp_done
  · exfalso
    simp only [BitVec.ult, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      decide_eq_true_eq] at hlo
    omega

theorem deserializeFull_placed_ok [LibsignalPlacement] (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_201).rebase (blkPl_201).base H)
      (blkPl_201).base
      deserializeFullPlacedSpec := by
  refine subroutine_ok_intro fun ⟨ptr, bs, sret⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [deserializeFullPlacedSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hlen⟩, hmem⟩
  rcases bs with _ | ⟨b0, b1⟩
  · -- bs = []
    have hsplit : memRegion sret 33 =
        (∃∗ tag0 : BitVec 8, sret ↦₈ tag0) ∗
        memRegion (sret + 1#64) 7 ∗
        (∃∗ w8 : BitVec 64, (sret + 8#64) ↦₆₄ w8) ∗
        memRegion (sret + 16#64) 17 := by sep_interval_eq
    rw [pointsToBytes_nil, emp_sepConj, hsplit] at hmem
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      satisfies_sepExists] at hmem
    rcases hmem with ⟨w8, tag0, hmem⟩
    have hx1_zero : s0.readReg64 .x1 = 0#64 := by
      apply BitVec.eq_of_toNat_eq; simpa using hx1
    set F := memRegion (sret + 1#64) 7 ∗ memRegion (sret + 16#64) 17 ∗
      (lsLogFilterAddr ↦₆₄ 0#64)
    have hpre' : s0.mem ⊨ deserializeEmptyPlacedSpec.pre (ptr, sret, tag0, w8) s0 ∗ (F ∗ R) := by
      dsimp only [deserializeEmptyPlacedSpec, F]
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1_zero, hx8⟩, Satisfies.mono (by bi_entail) hmem⟩
    refine reaches_of_ghost (deserializeEmpty_placed_ok H) (ptr, sret, tag0, w8) F hpc hrun hsp hpre' ?_
    intro sf _ hpost
    dsimp only [deserializeEmptyPlacedSpec, deserializeFullPlacedSpec, deserializeResult33At,
      PublicKey.deserialize, F] at hpost ⊢
    simp only [pointsToBytes_nil, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    refine ⟨htr, ?_⟩
    rw [pointsTo64_zero_byte0 (sret + 8#64)] at hpost
    have hrep7 : (List.replicate 7 0#8).length = 7 := rfl
    have h24 : ((sret + 8#64 + 1#64) ↦ₛ List.replicate 7 0#8) ∗ memRegion (sret + 16#64) 17 ⊢
        memRegion (sret + 9#64) 24 := by sep_interval
    exact Satisfies.mono (by
      refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left h24))))
      bi_entail) hpost
  · -- bs = b0 :: b1
    by_cases hb0 : b0 = 5#8
    · subst hb0
      by_cases hlen32 : b1.length < 32
      · -- bs = 5#8 :: b1, b1.length < 32 (.badKeyLength)
        have hsplit : memRegion sret 33 =
            (∃∗ tag0 : BitVec 8, sret ↦₈ tag0) ∗
            memRegion (sret + 1#64) 7 ∗
            (∃∗ w8 : BitVec 64, (sret + 8#64) ↦₆₄ w8) ∗
            (∃∗ w16 : BitVec 64, (sret + 16#64) ↦₆₄ w16) ∗
            memRegion (sret + 24#64) 9 := by sep_interval_eq
        rw [pointsToBytes_cons, hsplit] at hmem
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
          satisfies_sepExists] at hmem
        rcases hmem with ⟨w16, w8, tag0, hmem⟩
        set F := ((ptr + 1#64) ↦ₛ b1) ∗ memRegion (sret + 1#64) 7 ∗
          memRegion (sret + 24#64) 9 ∗ (lsLogFilterAddr ↦₆₄ 0#64)
        have hpre' : s0.mem ⊨ deserializeBadLenPlacedSpec.pre (ptr, b1.length, sret, tag0, w8, w16) s0 ∗ (F ∗ R) := by
          dsimp only [deserializeBadLenPlacedSpec, F]
          simp only [sepConj_assoc, satisfies_pure_sepConj]
          exact ⟨⟨hx0, hx1, hx8, hlen32⟩, Satisfies.mono (by bi_entail) hmem⟩
        refine reaches_of_ghost (deserializeBadLen_placed_ok H) (ptr, b1.length, sret, tag0, w8, w16) F hpc hrun hsp hpre' ?_
        intro sf _ hpost
        have hdes : PublicKey.deserialize (5#8 :: b1) = .error (.badKeyLength (b1.length + 1)) := by
          simp [PublicKey.deserialize, djbType, hlen32]
        dsimp only [deserializeBadLenPlacedSpec, deserializeFullPlacedSpec, F] at hpost ⊢
        rw [hdes]
        simp only [deserializeResult33At, pointsToBytes_cons, sepConj_assoc,
          satisfies_pure_sepConj] at hpost ⊢
        rcases hpost with ⟨htr, hpost⟩
        refine ⟨htr, ?_⟩
        rw [pointsTo64_two_byte0 (sret + 8#64)] at hpost
        have hrep7 : (List.replicate 7 0#8).length = 7 := rfl
        have h7 : ((sret + 8#64 + 1#64) ↦ₛ List.replicate 7 0#8) ⊢ memRegion (sret + 9#64) 7 := by
          sep_interval
        exact Satisfies.mono (by
          refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h7))))))
          bi_entail) hpost
      · -- bs = 5#8 :: b1, 32 ≤ b1.length (.ok pk)
        have hge32 : 32 ≤ b1.length := Nat.le_of_not_lt hlen32
        set pk : PublicKey := ⟨⟨b1.take 32, by simp [hge32]⟩⟩
        have hdes : PublicKey.deserialize (5#8 :: b1) = .ok pk := by
          simp [PublicKey.deserialize, djbType, hge32, pk]
        have hsplit : memRegion sret 33 =
            (∃∗ tag0 : BitVec 8, sret ↦₈ tag0) ∗
            (∃∗ out32 : List (BitVec 8), ⌜out32.length = 32⌝ ∗ ((sret + 1#64) ↦ₛ out32)) := by
          rw [show (33 : Nat) = 1 + 32 by decide, memRegion_split sret 1 32 (by decide),
            memRegion_one, memRegion_eq_exists_bytes (sret + 1#64) 32 (by decide)]
        rw [hsplit] at hmem
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
          satisfies_sepExists, sepConj_pure_left_comm, satisfies_pure_sepConj] at hmem
        rcases hmem with ⟨out32, tag0, hout32, hmem⟩
        have hpre' : s0.mem ⊨ deserializePlacedSpec.pre (ptr, 5#8 :: b1, pk, sret, tag0, out32) s0 ∗ (emp ∗ R) := by
          dsimp only [deserializePlacedSpec]
          simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj]
          exact ⟨⟨hx0, hx1, hx8, hlen, hdes, hout32⟩, Satisfies.mono (by bi_entail) hmem⟩
        refine reaches_of_ghost (deserialize_placed_ok H) (ptr, 5#8 :: b1, pk, sret, tag0, out32) emp hpc hrun hsp hpre' ?_
        intro sf _ hpost
        dsimp only [deserializePlacedSpec, deserializeFullPlacedSpec] at hpost ⊢
        rw [hdes]
        simpa only [deserializeResult33At, emp_sepConj, sepConj_assoc] using hpost
    · -- bs = b0 :: b1, b0 ≠ 5#8 (.badKeyType b0)
      have hsplit : memRegion sret 33 =
          (∃∗ tag0 : BitVec 8, sret ↦₈ tag0) ∗
          memRegion (sret + 1#64) 7 ∗
          (∃∗ w8 : BitVec 8, (sret + 8#64) ↦₈ w8) ∗
          (∃∗ w9 : BitVec 8, (sret + 9#64) ↦₈ w9) ∗
          memRegion (sret + 10#64) 23 := by sep_interval_eq
      rw [pointsToBytes_cons, hsplit] at hmem
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
        satisfies_sepExists] at hmem
      rcases hmem with ⟨w9, w8, tag0, hmem⟩
      set F := ((ptr + 1#64) ↦ₛ b1) ∗ memRegion (sret + 1#64) 7 ∗
        memRegion (sret + 10#64) 23 ∗ (lsLogFilterAddr ↦₆₄ 0#64)
      have hpre' : s0.mem ⊨ deserializeBadTypePlacedSpec.pre (ptr, b0, b1.length, sret, tag0, w8, w9) s0 ∗ (F ∗ R) := by
        dsimp only [deserializeBadTypePlacedSpec, F]
        simp only [sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨⟨hx0, hx1, hx8, hlen, hb0⟩, Satisfies.mono (by bi_entail) hmem⟩
      refine reaches_of_ghost (deserializeBadType_placed_ok H) (ptr, b0, b1.length, sret, tag0, w8, w9) F hpc hrun hsp hpre' ?_
      intro sf _ hpost
      have hdes : PublicKey.deserialize (b0 :: b1) = .error (.badKeyType b0) := by
        simp [PublicKey.deserialize, djbType, hb0]
      dsimp only [deserializeBadTypePlacedSpec, deserializeFullPlacedSpec, F] at hpost ⊢
      rw [hdes]
      simp only [deserializeResult33At, pointsToBytes_cons, sepConj_assoc,
        satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨htr, hpost⟩
      exact ⟨htr, Satisfies.mono (by bi_entail) hpost⟩

theorem deserializeFull_ok_at_placed [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok (tryFromPlacedProg H)
      ((blkPl_85).ρ deserializeName)
      (withLsCodeRoLoaded lsmpl deserializeFullPlacedSpec) := by
  have h1 := keys_ls_subroutine_ok_of_block_cro (callerProg := tryFromPlacedProg H)
    (subroutine_ok_withLsCodeRoLoaded_of_plain (deserializeFull_placed_ok H))
  simp only [deserializeName, arm64_norm]
  exact h1

end CryptoVerification.LibsignalTripleRatchet.Wire
