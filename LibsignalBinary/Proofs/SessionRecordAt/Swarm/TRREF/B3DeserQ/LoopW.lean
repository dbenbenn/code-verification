/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Defs
public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.LoopIter -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Adapters -- proof-setup: allow-public-import
import ProofLib
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Fields
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.DeserLoopExitG
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Deser.DeserTransportX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserLoopEntryGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserLoopExitGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserLoopIterGExt
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Fields
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.ReprMove
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
public import LibsignalBinary.Proofs.CodeLayout -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers

/-!
# W-Stack `SessionRecord::deserialize` Loop Entry, Iteration, Exit, and `.base` Framing

Verifies `.base` field framing (`mergeFieldQOkAtWA_base`), loop entry (`deserLoopEntryQ_ok_atW`),
loop iteration (`deserLoopIterQ_ok_atWA`), loop exit (`deserLoopExitQ_ok_of_memcpyA`), and full loop
assembly (`deserializeExactQWA_ok`, `recordDeserializeOpen_of_exactQA`) on `SP2Ext` with slice length
`< 2 ^ 62`.
-/

public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.B3DeserQ

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization (CanonRecord CanonSession allocPanic)
open CryptoVerification.E2E.RecordX (DeserializeScopeP SessionScopeP)
open CryptoVerification.E2E.Bin (BinCanonSession recordDeserializeStack)
open CryptoVerification.E2E.Record.L1GX
open Symbolic.Swarm.TRREF.B3Defs
open Proofs.libsignal.Hooks2
open Proofs.libsignal.Hooks2.DeserLoopEntryGExt

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
open CryptoVerification.E2E.Record.DeserializeSeed.LoopIterStateSimp
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.DeserLoopIterG
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero ofNat_succ_sub_one_loopIter
@[local arm64_norm ↓, local wp_norm ↓] private theorem sp_setPC_pre_loopW (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem sp_setMem_setPC_pre_loopW (s : State) (pc : BitVec 64) (m : Memory) : ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem readReg64_setPC_pre_loopW (s : State) (pc : BitVec 64) (r : Reg) : (s.setPC pc).readReg64 r = s.readReg64 r := State.readReg64_setPC s pc r
@[local arm64_norm ↓, local wp_norm ↓] private theorem readReg64_setMem_setPC_pre_loopW (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) : ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem readReg32_setPC_pre_loopW (s : State) (pc : BitVec 64) (r : Reg) : (s.setPC pc).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem readReg32_setMem_setPC_pre_loopW (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) : ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem readReg_setPC_pre_loopW (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) : (s.setPC pc).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem readReg_setMem_setPC_pre_loopW (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) : ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by cases w <;> cases r <;> rfl
@[local simp, local arm64_norm] private theorem int64_toBitVec_mk_loopW (u : UInt64) : ({ toUInt64 := u } : Int64).toBitVec = u.toBitVec := rfl
@[local simp, local arm64_norm] private theorem uint64_toBitVec_mk_loopW (v : BitVec 64) : ({ toBitVec := v } : UInt64).toBitVec = v := rfl
@[local simp, local arm64_norm] private theorem bitVec_toFin_mk_64_loopW (n : Nat) (h : n < 18446744073709551616 := by decide) : ({ toFin := ⟨n, h⟩ } : BitVec 64) = BitVec.ofNat 64 n := BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt h).symm

theorem L1_B3DeserQ_LoopW : True := trivial

local elab "d0_fetch_range_q " codeId:ident b:term:max H:term:max hfn:term:max off:term:max k0:num len:num : tactic => do
  let off ← CryptoVerification.CodeLayout.evalNat off "d0_fetch_range_q"
  let k0 := k0.getNat; let len := len.getNat; let codeBase := codeId.getId.eraseMacroScopes
  let fetchEntry := Lean.mkIdent (codeBase.appendAfter "_fetch_fnAddr_entry")
  let fetchAdd := Lean.mkIdent (codeBase.appendAfter "_fetch_fnAddr")
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let dec := Lean.mkIdent (Lean.Name.str `Proofs.libsignal.Hooks2.DeserLoopEntryGExt s!"d0_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Lean.Syntax.mkNumLit (toString k)
    if k == 0 then Lean.Elab.Tactic.evalTactic (← `(tactic| have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else Lean.Elab.Tactic.evalTactic (← `(tactic| have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

private theorem encodeKey_1_ld_loopW : encodeKey 1 .lengthDelimited = [0x0a#8] := rfl
private theorem encodeVarint_length_pos_loopW (v : BitVec 64) : 0 < (encodeVarint v).length := List.length_pos_iff.mpr (encodeVarint_ne_nil v)
private theorem encodeVarint_of_lt_128_loopW {n : Nat} (hn : n < 128) : encodeVarint (BitVec.ofNat 64 n) = [BitVec.ofNat 8 n] := by
  have h1 : (BitVec.ofNat 64 n).toNat < 0x80 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  unfold encodeVarint encodeVarintAux; simp only [h1, ↓reduceIte]; congr 1; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
private theorem encodeVarint_cons_of_ge_128_loopW {n : Nat} (hge : 128 ≤ n) (hlt : n < 2 ^ 33) :
    encodeVarint (BitVec.ofNat 64 n) = BitVec.ofNat 8 (n % 128 + 128) :: encodeVarintAux 9 (BitVec.ofNat 64 n >>> 7) := by
  have hn : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 : ¬ ((BitVec.ofNat 64 n).toNat < 0x80) := by omega
  unfold encodeVarint encodeVarintAux; simp only [h1, ↓reduceIte]; congr 1; apply BitVec.eq_of_toNat_eq
  have hor := Nat.two_pow_add_eq_or_of_lt (i := 7) (b := n % 128) (by omega) 1; simp only [Nat.reducePow, Nat.reduceMul] at hor
  rw [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_and, hn, show (0x7F : BitVec 64).toNat = 127 from rfl,
    Nat.and_two_pow_sub_one_eq_mod n 7, show (0x80 : BitVec 64).toNat = 128 from rfl, Nat.or_comm, ← hor, BitVec.toNat_ofNat]; omega
private theorem signExtend64_bit63_eq_false_iff_loopW (b0 : BitVec 8) : ((b0.signExtend 64).getLsbD 63 == true) = false ↔ b0.toNat ≤ 0x7F := by revert b0; decide
private theorem signExtend64_bit63_eq_true_iff_loopW (b0 : BitVec 8) : ((b0.signExtend 64).getLsbD 63 == true) = true ↔ 0x7F < b0.toNat := by revert b0; decide
private theorem signExtend64_eq_zeroExtend64_of_le_loopW (b0 : BitVec 8) (h : b0.toNat ≤ 0x7F) : b0.signExtend 64 = b0.zeroExtend 64 := by revert b0 h; decide
private theorem signExtend64_ofNat8_lt_128_loopW {n : Nat} (hn : n < 128) : (BitVec.ofNat 8 n).signExtend 64 = BitVec.ofNat 64 n := by
  have hle : (BitVec.ofNat 8 n).toNat ≤ 0x7F := by rw [BitVec.toNat_ofNat]; omega
  rw [signExtend64_eq_zeroExtend64_of_le_loopW _ hle]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
private theorem sp_sub_1904_aligned_loopW {sp0 : BitVec 64} (h : sp0 &&& 15#64 = 0#64) :
    (sp0 - 0x770#64) &&& 15#64 = 0#64 ∧ (sp0 - 0x770#64 + 1808#64) &&& 15#64 = 0#64 := by
  have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by simp only [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  have h' := congrArg BitVec.toNat h; rw [e] at h'; have hlt := sp0.isLt; have hsub : sp0 - 0x770#64 + 1808#64 = sp0 - 96#64 := by bv_omega
  refine ⟨by apply BitVec.eq_of_toNat_eq; rw [e]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢; omega,
    by rw [hsub]; apply BitVec.eq_of_toNat_eq; rw [e]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢; omega⟩
private theorem empty_vecU8_intro_loopW (A : RustAlloc) (v : BitVec 64) : (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢ vecU8 A v [] := by
  dsimp only [vecU8, vecU8At, vecHeader]; simp only [List.length_nil, BitVec.ofNat_eq_ofNat]
  refine Entails.trans ?_ (Entails.sepExists_intro 0#64); refine Entails.trans ?_ (Entails.sepExists_intro 1#64)
  simp only [↓reduceIte, sepConj_emp, sepConj_assoc]
  have hp : 0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64 := by decide
  have heq : (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ∗ ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64⌝ =
    ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64⌝ ∗ ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) := by ac_rfl
  rw [heq]; exact Entails.pure_right hp (Entails.refl _)
private theorem empty_vecChainG_intro_loopW (A : RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 8#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢ vecOf A 104 8 (fun c a => prostChainGAt A a c) v [] := by
  dsimp only [vecOf, vecAt, vecHeader, vecBuf]
  refine Entails.trans ?_ (Entails.sepExists_intro 0#64); refine Entails.trans ?_ (Entails.sepExists_intro 8#64)
  have hite : (if (0#64 : BitVec 64) = 0 then emp else A.live (8#64) ((0#64 : BitVec 64).toNat * 104) 8 ∗
    arrayAt (fun c a => prostChainGAt A a c) 104 8#64 [] ∗
    memRegion (8#64 + BitVec.ofNat 64 (([] : List ChainG).length * 104)) (((0#64 : BitVec 64).toNat - ([] : List ChainG).length) * 104)) = emp := rfl
  rw [hite]; simp only [List.length_nil, BitVec.ofNat_eq_ofNat, sepConj_assoc, sepConj_emp]
  have hp : 0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 104 < 2 ^ 63 ∧ (8#64 : BitVec 64) ≠ 0#64 := by decide
  have heq : (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 8#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ∗ ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 104 < 2 ^ 63 ∧ (8#64 : BitVec 64) ≠ 0#64⌝ =
    ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 104 < 2 ^ 63 ∧ (8#64 : BitVec 64) ≠ 0#64⌝ ∗ ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 8#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) := by ac_rfl
  rw [heq]; exact Entails.pure_right hp (Entails.refl _)
private theorem pointsTo64_zero_split32_loopW (a : BitVec 64) : (a ↦₆₄ 0#64) = (a ↦₃₂ 0#32) ∗ ((a + 4#64) ↦₃₂ 0#32) := by simpa using pointsTo64_split32 a 0#64

private def ssRawCells_loopW (L : BitVec 64) : SepProp :=
  (((L + 0x420#64) ↦₆₄ 0#64) ∗ ((L + 0x428#64) ↦₆₄ 1#64) ∗ ((L + 0x430#64) ↦₆₄ 0#64)) ∗ (((L + 0x438#64) ↦₆₄ 0#64) ∗ ((L + 0x440#64) ↦₆₄ 1#64) ∗ ((L + 0x448#64) ↦₆₄ 0#64)) ∗
  (((L + 0x450#64) ↦₆₄ 0#64) ∗ ((L + 0x458#64) ↦₆₄ 1#64) ∗ ((L + 0x460#64) ↦₆₄ 0#64)) ∗ (((L + 0x468#64) ↦₆₄ 0#64) ∗ ((L + 0x470#64) ↦₆₄ 8#64) ∗ ((L + 0x478#64) ↦₆₄ 0#64)) ∗
  (((L + 0x480#64) ↦₆₄ 0#64) ∗ ((L + 0x488#64) ↦₆₄ 1#64) ∗ ((L + 0x490#64) ↦₆₄ 0#64)) ∗ (((L + 0x498#64) ↦₆₄ 0#64) ∗ ((L + 0x4a0#64) ↦₆₄ 1#64) ∗ ((L + 0x4a8#64) ↦₆₄ 0#64)) ∗
  ((L + 0x4b0#64) ↦₆₄ noneCap) ∗ ((L + 0x518#64) ↦₆₄ noneCap) ∗ ((L + 0x548#64) ↦₆₄ noneCap) ∗ ((L + 0x568#64) ↦₆₄ 0#64) ∗ ((L + 0x570#64) ↦₆₄ 0#64)

private theorem prostSSGAt_empty_intro_loopW (A : RustAlloc) (L : BitVec 64) :
    ssRawCells_loopW L ∗ memRegion (L + 0x4b8#64) 96 ∗ memRegion (L + 0x520#64) 40 ∗ memRegion (L + 0x550#64) 24 ⊢ prostSSGAt A (L + 0x420#64) SSG.empty := by
  unfold ssRawCells_loopW prostSSGAt SSG.empty; dsimp only
  have h1 := empty_vecU8_intro_loopW A (L + 0x420#64); have h2 := empty_vecU8_intro_loopW A (L + 0x420#64 + 0x18#64); have h3 := empty_vecU8_intro_loopW A (L + 0x420#64 + 0x30#64)
  have h4 := empty_vecChainG_intro_loopW A (L + 0x420#64 + 0x48#64); have h5 := empty_vecU8_intro_loopW A (L + 0x420#64 + 0x60#64); have h6 := empty_vecU8_intro_loopW A (L + 0x420#64 + 0x78#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1 h2 h3 h4 h5 h6 ⊢; rw [pointsTo64_zero_split32_loopW (L + 0x568#64)]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (sepConj_mono h4 (sepConj_mono h5 (sepConj_mono h6 (Entails.refl _)))))))

@[local arm64_norm ↓, local wp_norm ↓] private theorem add_1904_sub_96_loopW (L : BitVec 64) : L + 1904#64 + bv% (2 ^ 64 - 96) = L + 1808#64 := by rw [BitVec.add_assoc]; rfl
@[local arm64_norm ↓, local wp_norm ↓] private theorem add_1808_sub_1808_loopW (L : BitVec 64) : L + 1808#64 - 1808#64 = L := by bv_omega
@[local arm64_norm ↓, local wp_norm ↓] private theorem add_1808_sub_40_loopW (L : BitVec 64) : L + 1808#64 + bv% (2 ^ 64 - 40) = L + 1768#64 := by rw [BitVec.add_assoc]; rfl

private def deserSavedAt_loopW (L : BitVec 64) (s0 : State) : SepProp :=
  ((L + 1808#64) ↦₆₄ s0.readReg64 .x29) ∗ ((L + 1816#64) ↦₆₄ s0.readReg64 .x30) ∗ ((L + 1824#64) ↦₆₄ s0.readReg64 .x28) ∗ ((L + 1832#64) ↦₆₄ s0.readReg64 .x27) ∗ ((L + 1840#64) ↦₆₄ s0.readReg64 .x26) ∗ ((L + 1848#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((L + 1856#64) ↦₆₄ s0.readReg64 .x24) ∗ ((L + 1864#64) ↦₆₄ s0.readReg64 .x23) ∗ ((L + 1872#64) ↦₆₄ s0.readReg64 .x22) ∗ ((L + 1880#64) ↦₆₄ s0.readReg64 .x21) ∗ ((L + 1888#64) ↦₆₄ s0.readReg64 .x20) ∗ ((L + 1896#64) ↦₆₄ s0.readReg64 .x19)
private theorem deserSavedAt_eq_loopW (s0 : State) : deserSavedAt_loopW (deserSpL s0.sp) s0 = deserSaved s0 := by
  unfold deserSavedAt_loopW deserSaved deserSpL; dsimp only; simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
private def ssUninitCells_loopW (L : BitVec 64) (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 : BitVec 64) : SepProp :=
  ((L + 1056#64) ↦₆₄ noneCap) ∗ ((L + 1064#64) ↦₆₄ c1) ∗ ((L + 1072#64) ↦₆₄ c2) ∗ ((L + 1080#64) ↦₆₄ c3) ∗ ((L + 1088#64) ↦₆₄ c4) ∗ ((L + 1096#64) ↦₆₄ c5) ∗ ((L + 1104#64) ↦₆₄ c6) ∗ ((L + 1112#64) ↦₆₄ c7) ∗ ((L + 1120#64) ↦₆₄ c8) ∗ ((L + 1128#64) ↦₆₄ c9) ∗ ((L + 1136#64) ↦₆₄ c10) ∗ ((L + 1144#64) ↦₆₄ c11) ∗
  ((L + 1152#64) ↦₆₄ c12) ∗ ((L + 1160#64) ↦₆₄ c13) ∗ ((L + 1168#64) ↦₆₄ c14) ∗ ((L + 1176#64) ↦₆₄ c15) ∗ ((L + 1184#64) ↦₆₄ c16) ∗ ((L + 1192#64) ↦₆₄ c17) ∗ ((L + 1200#64) ↦₆₄ c18) ∗ ((L + 1304#64) ↦₆₄ c19) ∗ ((L + 1352#64) ↦₆₄ c20) ∗ ((L + 1384#64) ↦₆₄ c21) ∗ ((L + 1392#64) ↦₆₄ c22)
private def step1aPre_loopW (L p : BitVec 64) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7 : BitVec 64) : SepProp :=
  ((L + 1808#64) ↦₆₄ w0) ∗ ((L + 1816#64) ↦₆₄ w1) ∗ ((L + 1824#64) ↦₆₄ w2) ∗ ((L + 1832#64) ↦₆₄ w3) ∗ ((L + 1840#64) ↦₆₄ w4) ∗ ((L + 1848#64) ↦₆₄ w5) ∗ ((L + 1856#64) ↦₆₄ w6) ∗ ((L + 1864#64) ↦₆₄ w7) ∗ ((L + 1872#64) ↦₆₄ w8) ∗ ((L + 1880#64) ↦₆₄ w9) ∗ ((L + 1888#64) ↦₆₄ w10) ∗ ((L + 1896#64) ↦₆₄ w11) ∗
  (L ↦₆₄ u0) ∗ ((L + 1016#64) ↦₆₄ u1) ∗ ((L + 1024#64) ↦₆₄ u2) ∗ ((L + 1032#64) ↦₆₄ u3) ∗ ((L + 1040#64) ↦₆₄ u4) ∗ ((L + 1048#64) ↦₆₄ u5) ∗ ((L + 1056#64) ↦₆₄ u6) ∗ ((L + 1768#64) ↦₆₄ u7) ∗ (p ↦₈ 10#8)
private def step1aPost_loopW (L p : BitVec 64) (len1 : Nat) (s0 : State) : SepProp :=
  deserSavedAt_loopW L s0 ∗ (L ↦₆₄ 0#64) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 len1) ∗ ((L + 1032#64) ↦₆₄ 0#64) ∗ ((L + 1040#64) ↦₆₄ 8#64) ∗ ((L + 1048#64) ↦₆₄ 0#64) ∗ ((L + 1056#64) ↦₆₄ noneCap) ∗ ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ (p ↦₈ 10#8)
private def step2aPre_loopW (L p : BitVec 64) (N : Nat) : SepProp := ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 (1 + N)) ∗ ((p + 1#64) ↦₈ BitVec.ofNat 8 N)
private def step2aPost_loopW (L p : BitVec 64) (N : Nat) : SepProp := ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 2#64)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 N) ∗ ((p + 1#64) ↦₈ BitVec.ofNat 8 N)
private def step2bPre_loopW (L p : BitVec 64) (vlen N : Nat) : SepProp := ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 (vlen + N)) ∗ ((p + 1#64) ↦₈ BitVec.ofNat 8 (N % 128 + 128))
private def step2bPostPre_loopW (L p : BitVec 64) (vlen N : Nat) : SepProp := ((L + 1400#64) ↦₃₂ 0#32) ∗ ((L + 1404#64) ↦₃₂ 0#32) ∗ ((L + 1408#64) ↦₆₄ BitVec.ofNat 64 N) ∗ ((L + 1416#64) ↦₆₄ BitVec.ofNat 64 vlen) ∗ ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 (vlen + N))
private def step2bPostPost_loopW (L p : BitVec 64) (vlen N : Nat) : SepProp := ((L + 1400#64) ↦₃₂ 0#32) ∗ ((L + 1404#64) ↦₃₂ 0#32) ∗ ((L + 1408#64) ↦₆₄ BitVec.ofNat 64 N) ∗ ((L + 1416#64) ↦₆₄ BitVec.ofNat 64 vlen) ∗ ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64 + BitVec.ofNat 64 vlen)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 N)
private theorem memRegion_succ8_loopW (a : BitVec 64) (n : Nat) (hn : n < 2000) :
    memRegion a (n + 8) = (∃∗ w : BitVec 64, a ↦₆₄ w) ∗ memRegion (a + 8#64) n := by
  rw [Nat.add_comm n 8, memRegion_split a 8 n (by omega), ProofLib.memRegion_eight]

private theorem memRegion_1064_336_cells_loopW (L : BitVec 64) :
    ((L + 1056#64) ↦₆₄ noneCap) ∗ memRegion (L + 1064#64) 336 =
      ∃∗ c22 : BitVec 64, ∃∗ c21 : BitVec 64, ∃∗ c20 : BitVec 64, ∃∗ c19 : BitVec 64, ∃∗ c18 : BitVec 64, ∃∗ c17 : BitVec 64, ∃∗ c16 : BitVec 64, ∃∗ c15 : BitVec 64,
      ∃∗ c14 : BitVec 64, ∃∗ c13 : BitVec 64, ∃∗ c12 : BitVec 64, ∃∗ c11 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c8 : BitVec 64, ∃∗ c7 : BitVec 64,
      ∃∗ c6 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c4 : BitVec 64, ∃∗ c3 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c1 : BitVec 64,
        ssUninitCells_loopW L c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 ∗
        memRegion (L + 1208#64) 96 ∗ memRegion (L + 1312#64) 40 ∗ memRegion (L + 1360#64) 24 := by
  rw [memRegion_split (L + 1064#64) 144 192 (by decide), memRegion_split (L + 1064#64 + 144#64) 96 96 (by decide),
    memRegion_split (L + 1064#64 + 144#64 + 96#64) 8 88 (by decide), memRegion_split (L + 1064#64 + 144#64 + 96#64 + 8#64) 40 48 (by decide),
    memRegion_split (L + 1064#64 + 144#64 + 96#64 + 8#64 + 40#64) 8 40 (by decide), memRegion_split (L + 1064#64 + 144#64 + 96#64 + 8#64 + 40#64 + 8#64) 24 16 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  conv_lhs => arg 2; arg 1; simp (discharger := decide) only [memRegion_succ8_loopW, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  rw [ProofLib.memRegion_eight (L + 1304#64), ProofLib.memRegion_eight (L + 1352#64)]
  conv_lhs => arg 2; arg 2; arg 2; arg 2; arg 2; arg 2; arg 2; simp (discharger := decide) only [memRegion_succ8_loopW, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  unfold ssUninitCells_loopW; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; repeat' (apply congrArg sepExists; funext _)
  ac_rfl

private theorem memRegion_1904_split_loopW (L p : BitVec 64) :
    memRegion L 1904 ∗ (p ↦₈ 0x0a#8) =
      ∃∗ w11 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64, ∃∗ u7 : BitVec 64, ∃∗ u6 : BitVec 64, ∃∗ u5 : BitVec 64, ∃∗ u4 : BitVec 64,
      ∃∗ u3 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        step1aPre_loopW L p w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 u0 u1 u2 u3 u4 u5 u6 u7 ∗
        memRegion (L + 8#64) 1008 ∗ memRegion (L + 1064#64) 336 ∗ memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32 := by
  rw [memRegion_split L 8 1896 (by decide), memRegion_split (L + 8#64) 1008 888 (by decide),
    memRegion_split (L + 8#64 + 1008#64) 48 840 (by decide), memRegion_split (L + 8#64 + 1008#64 + 48#64) 336 504 (by decide),
    memRegion_split (L + 8#64 + 1008#64 + 48#64 + 336#64) 368 136 (by decide), memRegion_split (L + 8#64 + 1008#64 + 48#64 + 336#64 + 368#64) 8 128 (by decide),
    memRegion_split (L + 8#64 + 1008#64 + 48#64 + 336#64 + 368#64 + 8#64) 32 96 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  conv_lhs => arg 1; arg 1; simp (discharger := decide) only [memRegion_succ8_loopW, ProofLib.memRegion_zero, sepConj_emp]
  conv_lhs => arg 1; arg 2; arg 2; arg 1; simp (discharger := decide) only [memRegion_succ8_loopW, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  conv_lhs => arg 1; arg 2; arg 2; arg 2; arg 2; arg 2; arg 1; simp (discharger := decide) only [memRegion_succ8_loopW, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  conv_lhs => arg 1; arg 2; arg 2; arg 2; arg 2; arg 2; arg 2; arg 2; simp (discharger := decide) only [memRegion_succ8_loopW, ProofLib.memRegion_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  unfold step1aPre_loopW; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; repeat' (apply congrArg sepExists; funext _)
  ac_rfl

private theorem stackAt_recDeserialize_split_loopW (sp0 : BitVec 64) :
    stackAt sp0 recDeserializeStack = stackAt (deserSpL sp0) deserCalleeStack ∗ memRegion (deserSpL sp0) 1904 := by
  change memRegion (sp0 - 65536#64) 65536 = memRegion (sp0 - 0x770#64 - 63632#64) 63632 ∗ memRegion (sp0 - 0x770#64) 1904
  rw [memRegion_split (sp0 - 65536#64) 63632 1904 (by decide)]
  have h1 : sp0 - 65536#64 = sp0 - 0x770#64 - 63632#64 := by bv_omega
  have h2 : sp0 - 65536#64 + 63632#64 = sp0 - 0x770#64 := by bv_omega
  rw [h2, h1]

private theorem memRegion_0_1016_intro_loopW (L : BitVec 64) : (L ↦₆₄ 0#64) ∗ memRegion (L + 8#64) 1008 ⊢ memRegion L 0x3f8 := by
  rw [show (0x3f8 : Nat) = 1016 by decide, memRegion_split L 8 1008 (by decide)]; exact sepConj_mono_left (pointsTo64_entails_memRegion L 0#64)

private def deserFixedLocalsG_loopW (A : RustAlloc) (L : BitVec 64) : SepProp :=
  memRegion L 0x3f8 ∗ ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗ prostSSGAt A (L + 0x420#64) SSG.empty ∗ memRegion (L + 0x6f0#64) 0x20

private theorem step1b_post_entails_loopW (A : RustAlloc) (L p : BitVec 64) (len1 : Nat) (s0 : State) (hL : L = deserSpL s0.sp) :
    ssRawCells_loopW L ∗ memRegion (L + 1208#64) 96 ∗ memRegion (L + 1312#64) 40 ∗ memRegion (L + 1360#64) 24 ∗ deserSavedAt_loopW L s0 ∗ (L ↦₆₄ 0#64) ∗
      ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 len1) ∗ ((L + 1032#64) ↦₆₄ 0#64) ∗ ((L + 1040#64) ↦₆₄ 8#64) ∗ ((L + 1048#64) ↦₆₄ 0#64) ∗
      ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ (p ↦₈ 0x0a#8) ∗ memRegion (L + 8#64) 1008 ∗ memRegion (L + 1400#64) 368 ∗ memRegion (L + 1776#64) 32 ⊢
    ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 len1) ∗ (p ↦₈ 0x0a#8) ∗
      memRegion (L + 1400#64) 368 ∗ deserFixedLocalsG_loopW A L ∗ deserSaved s0 := by
  have hss := prostSSGAt_empty_intro_loopW A L; have hm0 := memRegion_0_1016_intro_loopW L
  have hds : deserSavedAt_loopW L s0 = deserSaved s0 := hL ▸ deserSavedAt_eq_loopW s0
  unfold deserFixedLocalsG_loopW; rw [hds, show (0x408#64 : BitVec 64) = 1032#64 from rfl, show (0x410#64 : BitVec 64) = 1040#64 from rfl,
    show (0x418#64 : BitVec 64) = 1048#64 from rfl, show (0x6f0#64 : BitVec 64) = 1776#64 from rfl, show (0x20 : Nat) = 32 from rfl]
  exact Entails.trans (Entails.of_eq (by ac_rfl)) (Entails.trans (sepConj_mono (sepConj_mono hss hm0)
    (Entails.refl (((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 len1) ∗ (p ↦₈ 0x0a#8) ∗
      memRegion (L + 1400#64) 368 ∗ ((L + 1032#64) ↦₆₄ 0#64) ∗ ((L + 1040#64) ↦₆₄ 8#64) ∗ ((L + 1048#64) ↦₆₄ 0#64) ∗ memRegion (L + 1776#64) 32 ∗ deserSaved s0))) (Entails.of_eq (by ac_rfl)))

private theorem scratch24_368_fold_loopW (L v w : BitVec 64) :
    ((L + 1400#64) ↦₃₂ 0#32) ∗ ((L + 1404#64) ↦₃₂ 0#32) ∗ ((L + 1408#64) ↦₆₄ v) ∗ ((L + 1416#64) ↦₆₄ w) ∗ memRegion (L + 1424#64) 344 ⊢ memRegion (L + 1400#64) 368 := by
  have h0 : ((L + 1400#64) ↦₃₂ 0#32) ∗ ((L + 1404#64) ↦₃₂ 0#32) = ((L + 1400#64) ↦₆₄ 0#64) := by
    have hs := (pointsTo64_zero_split32_loopW (L + 1400#64)).symm; rw [show L + 1400#64 + 4#64 = L + 1404#64 by bv_omega] at hs; exact hs
  rw [← sepConj_assoc, h0, memRegion_split (L + 1400#64) 24 344 (by decide), memRegion_split (L + 1400#64) 8 16 (by decide), memRegion_split (L + 1400#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono (sepConj_mono (pointsTo64_entails_memRegion (L + 1400#64) 0#64)
    (sepConj_mono (pointsTo64_entails_memRegion (L + 1408#64) v) (pointsTo64_entails_memRegion (L + 1416#64) w))) (Entails.refl _))

private theorem deserLocalsG_of_2a_loopW (A : RustAlloc) (L p : BitVec 64) (r : SessionRecord (List (BitVec 8)))
    (heq : encodeRecord r = encodeKey 1 .lengthDelimited ++ encodeVarint (BitVec.ofNat 64 ((recFieldsQ r).flatMap GenFieldQ.enc).length) ++ (recFieldsQ r).flatMap GenFieldQ.enc)
    (hN : ((recFieldsQ r).flatMap GenFieldQ.enc).length < 128) :
    let body := (recFieldsQ r).flatMap GenFieldQ.enc
    step2aPost_loopW L p body.length ∗ ((p + 1#64 + 1#64) ↦ₛ body) ∗ (p ↦₈ 0x0a#8) ∗ memRegion (L + 1400#64) 368 ∗ deserFixedLocalsG_loopW A L = deserLocalsGA A L p (encodeRecord r) body SSG.empty := by
  intro body
  have hpfx : encodeRecord r = 0x0a#8 :: BitVec.ofNat 8 body.length :: body := by rw [heq, encodeKey_1_ld_loopW, encodeVarint_of_lt_128_loopW hN]; rfl
  have hsub : (encodeRecord r).length - body.length = 2 := by rw [hpfx, List.length_cons, List.length_cons]; omega
  have hbytes : (p ↦ₛ encodeRecord r) = (p ↦₈ 0x0a#8) ∗ ((p + 1#64) ↦₈ BitVec.ofNat 8 body.length) ∗ ((p + 1#64 + 1#64) ↦ₛ body) := by rw [hpfx, pointsToBytes_cons, pointsToBytes_cons]
  unfold deserLocalsGA Prost.sliceCursorAfter deserFixedLocalsG_loopW step2aPost_loopW
  rw [hsub, hbytes, show (0x3f8#64 : BitVec 64) = 1016#64 from rfl, show L + 1016#64 + 8#64 = L + 1024#64 by bv_omega,
    show (BitVec.ofNat 64 2 : BitVec 64) = 2#64 from rfl, show (0x578#64 : BitVec 64) = 1400#64 from rfl, show (0x170 : Nat) = 368 from rfl, show (0x6e8#64 : BitVec 64) = 1768#64 from rfl]; ac_rfl

private theorem step2bPostPost_entails_loopW (L p : BitVec 64) (vlen N : Nat) :
    step2bPostPost_loopW L p vlen N ∗ memRegion (L + 1424#64) 344 ⊢
      memRegion (L + 1400#64) 368 ∗ ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗ ((L + 1016#64) ↦₆₄ (p + 1#64 + BitVec.ofNat 64 vlen)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 N) := by
  unfold step2bPostPost_loopW
  exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left (Q := ((L + 1768#64) ↦₆₄ (L + 1016#64)) ∗
    ((L + 1016#64) ↦₆₄ (p + 1#64 + BitVec.ofNat 64 vlen)) ∗ ((L + 1024#64) ↦₆₄ BitVec.ofNat 64 N)) (scratch24_368_fold_loopW L (BitVec.ofNat 64 N) (BitVec.ofNat 64 vlen)))

private theorem deserLocalsG_of_2b_loopW (A : RustAlloc) (L p : BitVec 64) (r : SessionRecord (List (BitVec 8)))
    (heq : encodeRecord r = encodeKey 1 .lengthDelimited ++ encodeVarint (BitVec.ofNat 64 ((recFieldsQ r).flatMap GenFieldQ.enc).length) ++ (recFieldsQ r).flatMap GenFieldQ.enc) :
    let body := (recFieldsQ r).flatMap GenFieldQ.enc; let vlen := (encodeVarint (BitVec.ofNat 64 body.length)).length
    (step2bPostPost_loopW L p vlen body.length ∗ memRegion (L + 1424#64) 344) ∗ ((p + 1#64) ↦ₛ (encodeVarint (BitVec.ofNat 64 body.length) ++ body)) ∗ (p ↦₈ 0x0a#8) ∗ deserFixedLocalsG_loopW A L ⊢
    deserLocalsGA A L p (encodeRecord r) body SSG.empty := by
  intro body vlen; refine Entails.trans (sepConj_mono_left (step2bPostPost_entails_loopW L p vlen body.length)) ?_
  have hpfx : encodeRecord r = 0x0a#8 :: (encodeVarint (BitVec.ofNat 64 body.length) ++ body) := by rw [heq, encodeKey_1_ld_loopW]; rfl
  have hsub : (encodeRecord r).length - body.length = 1 + vlen := by rw [hpfx, List.length_cons, List.length_append]; omega
  have hptr : p + 1#64 + BitVec.ofNat 64 vlen = p + BitVec.ofNat 64 (1 + vlen) := by rw [BitVec.ofNat_add, BitVec.add_assoc]
  have hbytes : (p ↦ₛ encodeRecord r) = (p ↦₈ 0x0a#8) ∗ ((p + 1#64) ↦ₛ (encodeVarint (BitVec.ofNat 64 body.length) ++ body)) := by rw [hpfx, pointsToBytes_cons]
  unfold deserLocalsGA Prost.sliceCursorAfter deserFixedLocalsG_loopW
  rw [hsub, hptr, hbytes, show (0x3f8#64 : BitVec 64) = 1016#64 from rfl, show L + 1016#64 + 8#64 = L + 1024#64 by bv_omega,
    show (0x578#64 : BitVec 64) = 1400#64 from rfl, show (0x170 : Nat) = 368 from rfl, show (0x6e8#64 : BitVec 64) = 1768#64 from rfl]
  exact Entails.of_eq (by ac_rfl)

private theorem stackAt_deserCallee_split_varint_loopW (L : BitVec 64) :
    stackAt L deserCalleeStack = stackAt L Prost.X.decodeVarintSliceStackW ∗ memRegion (L - 63632#64) 38976 := by
  change memRegion (L - 63632#64) 63632 = memRegion (L - 24656#64) 24656 ∗ memRegion (L - 63632#64) 38976
  rw [memRegion_split (L - 63632#64) 38976 24656 (by decide), show L - 63632#64 + 38976#64 = L - 24656#64 by bv_omega, sepConj_comm]

private theorem allocFailedIn_of_trace_eq_loopW {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) : allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by unfold allocFailedIn at h ⊢; rwa [htr] at h
private theorem allowPanic_frame_trace_loopW {s0 sm sf : State} {F R : SepProp} (htr : sm.trace = s0.trace)
    (h : sf.mem ⊨ ((⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) : sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R :=
  allowPanic_frame (allocFailedIn_of_trace_eq_loopW htr) h

private theorem deserOutRawQA_A0 : deserOutRawQA A0 = deserOutRawQ := by
  funext x s0 sf; have hp : A0.pool = emp := rfl; unfold deserOutRawQA deserOutRawQ; simp only [deserOutRecordQA_A0, hp, emp_sepConj]
private theorem DeserRetQAtWA_A0 : DeserRetQAtWA A0 = DeserRetQAtW := by
  funext x R s0 sf; unfold DeserRetQAtWA DeserRetQAtW; rw [deserOutRawQA_A0]

def keyByte_diterQ (fl : GenFieldQ) : BitVec 8 := BitVec.ofNat 8 (fl.tag * 8 + if fl.wt = .varint then 0 else 2)
theorem enc_eq_keyByte_cons_diterQ (fl : GenFieldQ) : fl.enc = keyByte_diterQ fl :: fl.payload := by rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> rfl
theorem drop_flatMap_enc_diterQ {r : SessionRecord (List (BitVec 8))} {k : Nat} (hk : k < (recFieldsQ r).length) :
    ((recFieldsQ r).drop k).flatMap GenFieldQ.enc = (recFieldsQ r)[k].enc ++ ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc := by rw [List.drop_eq_getElem_cons hk, List.flatMap_cons]
theorem ssgqAfter_succ_diterQ {r : SessionRecord (List (BitVec 8))} {k : Nat} (hk : k < (recFieldsQ r).length) :
    ssgqAfter r (k + 1) = (ssgqAfter r k).apply (recFieldsQ r)[k] := by simp only [ssgqAfter, List.take_succ_eq_append_getElem hk, List.foldl_append, List.foldl_cons, List.foldl_nil]
def preBytes_diterQ (r : SessionRecord (List (BitVec 8))) (k : Nat) : List (BitVec 8) :=
  encodeKey 1 .lengthDelimited ++ encodeVarint (BitVec.ofNat 64 ((recFieldsQ r).flatMap GenFieldQ.enc).length) ++ ((recFieldsQ r).take k).flatMap GenFieldQ.enc
def curPtr_diterQ (p : BitVec 64) (r : SessionRecord (List (BitVec 8))) (k : Nat) : BitVec 64 := p + BitVec.ofNat 64 (preBytes_diterQ r k).length
theorem encodeRecord_eq_preBytes_append_diterQ {r : SessionRecord (List (BitVec 8))} (hr : DeserializeScopeP_Q NonEmptyV1Q r) (k : Nat) :
    encodeRecord r = preBytes_diterQ r k ++ ((recFieldsQ r).drop k).flatMap GenFieldQ.enc := by
  have hs : (recFieldsQ r).flatMap GenFieldQ.enc = ((recFieldsQ r).take k).flatMap GenFieldQ.enc ++ ((recFieldsQ r).drop k).flatMap GenFieldQ.enc := by rw [← List.flatMap_append, List.take_append_drop]
  rw [encodeRecord_eq_recFieldsQ r hr, preBytes_diterQ, List.append_assoc, List.append_assoc, ← hs, ← List.append_assoc]
theorem rem_length_lt_diterQ {r : SessionRecord (List (BitVec 8))} (hr : DeserializeScopeP_Q NonEmptyV1Q r) (k : Nat) :
    (((recFieldsQ r).drop k).flatMap GenFieldQ.enc).length < 2 ^ 33 := by have h1 := encodeRecord_length_ltQ hr; rw [encodeRecord_eq_preBytes_append_diterQ hr k, List.length_append] at h1; omega
theorem payload_rest_length_lt_diterQ {r : SessionRecord (List (BitVec 8))} (hr : DeserializeScopeP_Q NonEmptyV1Q r) {k : Nat} (hk : k < (recFieldsQ r).length) :
    ((recFieldsQ r)[k].payload ++ ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc).length < 2 ^ 33 := by
  have h := rem_length_lt_diterQ hr k; rw [drop_flatMap_enc_diterQ hk, enc_eq_keyByte_cons_diterQ, List.cons_append, List.length_cons] at h; omega
theorem encodeRecord_sub_rem_length_diterQ {r : SessionRecord (List (BitVec 8))} (hr : DeserializeScopeP_Q NonEmptyV1Q r) (k : Nat) :
    (encodeRecord r).length - (((recFieldsQ r).drop k).flatMap GenFieldQ.enc).length = (preBytes_diterQ r k).length := by rw [encodeRecord_eq_preBytes_append_diterQ hr k, List.length_append]; omega

theorem sliceCursorAfter_split_key_diterQ (L p : BitVec 64) {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScopeP_Q NonEmptyV1Q r) {k : Nat} (hk : k < (recFieldsQ r).length) :
    Prost.sliceCursorAfter (L + 0x3f8#64) p (encodeRecord r) (((recFieldsQ r).drop k).flatMap GenFieldQ.enc) =
      ((L + 0x3f8#64) ↦₆₄ curPtr_diterQ p r k) ∗ ((L + 0x400#64) ↦₆₄ BitVec.ofNat 64 (((recFieldsQ r)[k].payload ++ ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc).length + 1)) ∗
        (curPtr_diterQ p r k ↦₈ keyByte_diterQ (recFieldsQ r)[k]) ∗ ((curPtr_diterQ p r k + 1#64) ↦ₛ ((recFieldsQ r)[k].payload ++ ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc)) ∗ (p ↦ₛ preBytes_diterQ r k) := by
  unfold Prost.sliceCursorAfter; have hsub := encodeRecord_sub_rem_length_diterQ hr k
  have hrem : ((recFieldsQ r).drop k).flatMap GenFieldQ.enc = keyByte_diterQ (recFieldsQ r)[k] :: ((recFieldsQ r)[k].payload ++ ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc) := by
    rw [drop_flatMap_enc_diterQ hk, enc_eq_keyByte_cons_diterQ, List.cons_append]
  have hbs_split : (p ↦ₛ encodeRecord r) = (p ↦ₛ preBytes_diterQ r k) ∗ (curPtr_diterQ p r k ↦₈ keyByte_diterQ (recFieldsQ r)[k]) ∗
      ((curPtr_diterQ p r k + 1#64) ↦ₛ ((recFieldsQ r)[k].payload ++ ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc)) := by
    conv_lhs => rw [encodeRecord_eq_preBytes_append_diterQ hr k, hrem]
    rw [pointsToBytes_append, ← curPtr_diterQ, pointsToBytes_cons]
  rw [hsub, ← curPtr_diterQ, show L + 0x3f8#64 + 8#64 = L + 0x400#64 by bv_omega, hbs_split, hrem, List.length_cons]; ac_rfl

theorem sliceCursorAfter_unsplit_key_diterQ (L p : BitVec 64) {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScopeP_Q NonEmptyV1Q r) {k : Nat} (hk : k < (recFieldsQ r).length) :
    Prost.sliceCursorAfter (L + 0x3f8#64) (curPtr_diterQ p r k + 1#64) ((recFieldsQ r)[k].payload ++ ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc) (((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc) ∗
      (curPtr_diterQ p r k ↦₈ keyByte_diterQ (recFieldsQ r)[k]) ∗ (p ↦ₛ preBytes_diterQ r k) =
    Prost.sliceCursorAfter (L + 0x3f8#64) p (encodeRecord r) (((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc) := by
  let fl := (recFieldsQ r)[k]; let rest := ((recFieldsQ r).drop (k + 1)).flatMap GenFieldQ.enc
  have hrem : ((recFieldsQ r).drop k).flatMap GenFieldQ.enc = keyByte_diterQ fl :: (fl.payload ++ rest) := by rw [drop_flatMap_enc_diterQ hk, enc_eq_keyByte_cons_diterQ, List.cons_append]
  have hbs_eq : encodeRecord r = preBytes_diterQ r k ++ (keyByte_diterQ fl :: (fl.payload ++ rest)) := by rw [encodeRecord_eq_preBytes_append_diterQ hr k, hrem]
  have hpay_sub : (fl.payload ++ rest).length - rest.length = fl.payload.length := by rw [List.length_append]; omega
  have hbs_sub : (encodeRecord r).length - rest.length = (preBytes_diterQ r k).length + 1 + fl.payload.length := by rw [hbs_eq, List.length_append, List.length_cons, List.length_append]; omega
  have hptr : curPtr_diterQ p r k + 1#64 + BitVec.ofNat 64 ((fl.payload ++ rest).length - rest.length) = p + BitVec.ofNat 64 ((encodeRecord r).length - rest.length) := by
    rw [hpay_sub, hbs_sub, curPtr_diterQ, BitVec.ofNat_add, BitVec.ofNat_add]; bv_omega
  have hbs_pts : (p ↦ₛ encodeRecord r) = (p ↦ₛ preBytes_diterQ r k) ∗ (curPtr_diterQ p r k ↦₈ keyByte_diterQ fl) ∗ ((curPtr_diterQ p r k + 1#64) ↦ₛ (fl.payload ++ rest)) := by
    conv_lhs => rw [hbs_eq]
    rw [pointsToBytes_append, ← curPtr_diterQ, pointsToBytes_cons]
  unfold Prost.sliceCursorAfter; rw [hptr, hbs_pts]; ac_rfl

theorem deserLocalsQA_decomp_diterQ (A : RustAlloc) (L p : BitVec 64) (bs rest : List (BitVec 8)) (v : SSGQ) :
    deserLocalsQA A L p bs rest v = Prost.sliceCursorAfter (L + 0x3f8#64) p bs rest ∗ prostSSGQAt A (L + 0x420#64) v ∗ ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗ deserFixed_loopIter L := by
  unfold deserLocalsQA deserFixed_loopIter
  generalize memRegion L 0x3f8 = m1; generalize memRegion (L + 0x578#64) 0x170 = m2; generalize memRegion (L + 0x6f0#64) 0x20 = m3; ac_rfl

theorem deserLocalsQ_decomp_diterQ (L p : BitVec 64) (bs rest : List (BitVec 8)) (v : SSGQ) :
    deserLocalsQ L p bs rest v = Prost.sliceCursorAfter (L + 0x3f8#64) p bs rest ∗ prostSSGQAt A0 (L + 0x420#64) v ∗ ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗ deserFixed_loopIter L :=
  deserLocalsQA_decomp_diterQ A0 L p bs rest v

private theorem ule_zero_ofNat_succ_diterQ {n : Nat} (hn : n < 2 ^ 33) : (BitVec.ofNat 64 (n + 1)).ule 0#64 = false := by
  rw [BitVec.ule_eq_decide, decide_eq_false_iff_not, BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.mod_eq_of_lt (by omega : n + 1 < 2 ^ 64)]; omega
@[local arm64_norm] private theorem keyByte_signExtend_lsb63_diterQ (fl : GenFieldQ) : (BitVec.signExtend 64 (keyByte_diterQ fl)).getLsbD 63 = false := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> simp [keyByte_diterQ, GenFieldQ.tag, GenFieldQ.wt, GenField.tag, GenField.wt]
@[local arm64_norm] private theorem keyByte_signExtend_lsr32_diterQ (fl : GenFieldQ) : (BitVec.signExtend 64 (keyByte_diterQ fl)) >>> 32 = 0#64 := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> simp [keyByte_diterQ, GenFieldQ.tag, GenFieldQ.wt, GenField.tag, GenField.wt]
@[local arm64_norm] private theorem keyByte_signExtend_and7_ule6_diterQ (fl : GenFieldQ) : (6#64).ule (BitVec.signExtend 64 (keyByte_diterQ fl) &&& 7#64) = false := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> simp [keyByte_diterQ, GenFieldQ.tag, GenFieldQ.wt, GenField.tag, GenField.wt]
@[local arm64_norm] private theorem keyByte_signExtend_tag_w1_diterQ (fl : GenFieldQ) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 (keyByte_diterQ fl))) >>> 3)) = BitVec.ofNat 64 fl.tag := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> simp [keyByte_diterQ, GenFieldQ.tag, GenFieldQ.wt, GenField.tag, GenField.wt]
@[local arm64_norm] private theorem tag_zeroExtend_ofNat32_diterQ (fl : GenFieldQ) : BitVec.zeroExtend 64 (BitVec.ofNat 32 fl.tag) = BitVec.ofNat 64 fl.tag := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> simp [GenFieldQ.tag, GenField.tag]
@[local arm64_norm] private theorem tag_ofNat64_beq0_diterQ (fl : GenFieldQ) : (BitVec.ofNat 64 fl.tag == 0#64) = false := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> simp [GenFieldQ.tag, GenField.tag]
@[local arm64_norm] private theorem tag_ofNat64_setWidth32_diterQ (fl : GenFieldQ) : (BitVec.ofNat 64 fl.tag).setWidth 32 = BitVec.ofNat 32 fl.tag := by
  rcases fl with f | _ | _ | _ | _ | _ | _ | _ <;> (try cases f) <;> simp [GenFieldQ.tag, GenField.tag]

@[expose] def ProstSSGQMovePropA (A : RustAlloc) : Prop :=
  ∀ {m : Memory} {L : BitVec 64} {v : SSGQ} {R : SepProp}, (m ⊨ prostSSGQAt A (L + 0x420#64) v ∗ R) →
    ∃ w0 : BitVec 64, ∃ rest : List (BitVec 8), ∃ H : SepProp,
      w0 ≠ noneCap ∧ rest.length = 336 ∧ (∀ b : BitVec 64, ((b ↦₆₄ w0) ∗ ((b + 8#64) ↦ₛ rest) ∗ H) ⊢ prostSSGQAt A b v) ∧
      (m ⊨ (((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗ H) ∗ R)

abbrev ProstSSGQMoveProp : Prop := ProstSSGQMovePropA A0

local elab "dexit_code_fetches_from_q " codeId:ident b:term:max H:term:max hfn:term:max off:term:max k0:num len:num : tactic => do
  let off ← CryptoVerification.CodeLayout.evalNat off "dexit_code_fetches_from_q"
  let k0 := k0.getNat; let len := len.getNat; let codeBase := codeId.getId.eraseMacroScopes
  let fetchEntry := Lean.mkIdent (codeBase.appendAfter "_fetch_fnAddr_entry")
  let fetchAdd := Lean.mkIdent (codeBase.appendAfter "_fetch_fnAddr")
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let dec := Lean.mkIdent (Lean.Name.str `CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.DeserLoopExitG s!"loopExit_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Lean.Syntax.mkNumLit (toString k)
    if k == 0 then Lean.Elab.Tactic.evalTactic (← `(tactic| have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else Lean.Elab.Tactic.evalTactic (← `(tactic| have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

@[local arm64_norm] private theorem int64_raw_toBitVec_dexitQ (n : Nat) (h : n < 18446744073709551616) :
    ({ toUInt64 := { toBitVec := { toFin := ⟨n, h⟩ } } } : Int64).toBitVec = BitVec.ofNat 64 n := BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt h).symm
private theorem w0_add_one_ne_zero_dexitQ {w0 : BitVec 64} (h : w0 ≠ noneCap) : w0 + 1#64 ≠ 0#64 := by unfold noneCap at h; bv_omega
private theorem w0_add_one_beq_zero_dexitQ {w0 : BitVec 64} (h : w0 ≠ noneCap) : (w0 + 1#64 == 0#64) = false := by rw [beq_eq_false_iff_ne]; exact w0_add_one_ne_zero_dexitQ h

private def deserSavedAtL_dexitQ (L : BitVec 64) (s0 : State) : SepProp :=
  ((L + 0x710#64) ↦₆₄ s0.readReg64 .x29) ∗ ((L + 0x718#64) ↦₆₄ s0.readReg64 .x30) ∗ ((L + 0x720#64) ↦₆₄ s0.readReg64 .x28) ∗ ((L + 0x728#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((L + 0x730#64) ↦₆₄ s0.readReg64 .x26) ∗ ((L + 0x738#64) ↦₆₄ s0.readReg64 .x25) ∗ ((L + 0x740#64) ↦₆₄ s0.readReg64 .x24) ∗ ((L + 0x748#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((L + 0x750#64) ↦₆₄ s0.readReg64 .x22) ∗ ((L + 0x758#64) ↦₆₄ s0.readReg64 .x21) ∗ ((L + 0x760#64) ↦₆₄ s0.readReg64 .x20) ∗ ((L + 0x768#64) ↦₆₄ s0.readReg64 .x19)
private theorem deserSaved_eq_atL_dexitQ (s0 : State) : deserSaved s0 = deserSavedAtL_dexitQ (deserSpL s0.sp) s0 := by
  unfold deserSaved deserSavedAtL_dexitQ deserSpL; rw [show s0.sp - 0x60#64 = s0.sp - 0x770#64 + 0x710#64 by bv_omega]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
private theorem sliceCursorAfter_nil_dexitQ (L p : BitVec 64) (bs : List (BitVec 8)) :
    Prost.sliceCursorAfter (L + 0x3f8#64) p bs [] = ((L + 0x3f8#64) ↦₆₄ (p + BitVec.ofNat 64 bs.length)) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗ (p ↦ₛ bs) := by
  unfold Prost.sliceCursorAfter; rw [show L + 0x3f8#64 + 8#64 = L + 0x400#64 by bv_omega, List.length_nil, Nat.sub_zero]
private theorem memRegion_3f8_split_dexitQ (L : BitVec 64) :
    memRegion L 0x3f8 = memRegion L 8 ∗ (memRegion (L + 8#64) 336 ∗ memRegion (L + 0x158#64) 336 ∗ memRegion (L + 0x2a8#64) 336) := by
  rw [memRegion_split' (b := L) (b' := L + 8#64) (N := 0x3f8) (n := 8) (k := 1008) (by decide) rfl (by decide),
    memRegion_split' (b := L + 8#64) (b' := L + 0x158#64) (N := 1008) (n := 336) (k := 672) (by decide) (by bv_omega) (by decide),
    memRegion_split' (b := L + 0x158#64) (b' := L + 0x2a8#64) (N := 672) (n := 336) (k := 336) (by decide) (by bv_omega) (by decide)]
private theorem memRegion_out_split_dexitQ (out : BitVec 64) :
    memRegion out 368 = ∃∗ u3 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
      (out ↦₆₄ u0) ∗ ((out + 8#64) ↦₆₄ u1) ∗ ((out + 0x10#64) ↦₆₄ u2) ∗ ((out + 0x18#64) ↦₆₄ u3) ∗ memRegion (out + 0x20#64) 336 := by
  rw [memRegion_split' (b := out) (b' := out + 8#64) (N := 368) (n := 8) (k := 360) (by decide) rfl (by decide),
    memRegion_split' (b := out + 8#64) (b' := out + 0x10#64) (N := 360) (n := 8) (k := 352) (by decide) (by bv_omega) (by decide),
    memRegion_split' (b := out + 0x10#64) (b' := out + 0x18#64) (N := 352) (n := 8) (k := 344) (by decide) (by bv_omega) (by decide),
    memRegion_split' (b := out + 0x18#64) (b' := out + 0x20#64) (N := 344) (n := 8) (k := 336) (by decide) (by bv_omega) (by decide),
    ProofLib.memRegion_eight out, ProofLib.memRegion_eight (out + 8#64), ProofLib.memRegion_eight (out + 0x10#64), ProofLib.memRegion_eight (out + 0x18#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
private theorem satisfies_memRegion_out_split_dexitQ {m : Memory} {out : BitVec 64} {R : SepProp} (h : m ⊨ memRegion out 368 ∗ R) :
    ∃ u0 u1 u2 u3 : BitVec 64, m ⊨ ((out ↦₆₄ u0) ∗ ((out + 8#64) ↦₆₄ u1) ∗ ((out + 0x10#64) ↦₆₄ u2) ∗ ((out + 0x18#64) ↦₆₄ u3) ∗ memRegion (out + 0x20#64) 336) ∗ R := by
  rw [memRegion_out_split_dexitQ out] at h; simp only [sepExists_sepConj_left, satisfies_sepExists] at h
  rcases h with ⟨u3, u2, u1, u0, h⟩; exact ⟨u0, u1, u2, u3, by simpa only [sepConj_assoc] using h⟩

private theorem deserSavedAtL_entails_memRegion_dexitQ (L : BitVec 64) (s0 : State) : deserSavedAtL_dexitQ L s0 ⊢ memRegion (L + 0x710#64) 0x60 := by
  unfold deserSavedAtL_dexitQ
  refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)))))))))))) ?_
  have join (n : Nat) (h : n + 8 ≤ 2 ^ 64) : memRegion (L + 0x710#64) n ∗ memRegion (L + BitVec.ofNat 64 (0x710 + n)) 8 = memRegion (L + 0x710#64) (n + 8) :=
    (memRegion_split' (b := L + 0x710#64) (b' := L + BitVec.ofNat 64 (0x710 + n)) (n := n) (k := 8) rfl (by bv_omega) h).symm
  simp only [← sepConj_assoc]
  rw [join 8 (by decide), join 16 (by decide), join 24 (by decide), join 32 (by decide), join 40 (by decide),
    join 48 (by decide), join 56 (by decide), join 64 (by decide), join 72 (by decide), join 80 (by decide), join 88 (by decide)]
  exact Entails.refl _

private theorem dexit_locals_entails_memRegion_dexitQ (L c0 w0 : BitVec 64) (s0 : State) (rest : List (BitVec 8)) (hrest : rest.length = 336) :
    memRegion L 8 ∗ ((L + 8#64) ↦ₛ rest) ∗ ((L + 0x158#64) ↦ₛ rest) ∗ ((L + 0x2a8#64) ↦ₛ rest) ∗ ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗
      ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗ ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗
      memRegion (L + 0x578#64) 0x170 ∗ ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗ memRegion (L + 0x6f0#64) 0x20 ∗ deserSavedAtL_dexitQ L s0 ⊢ memRegion L 0x770 := by
  have hb (a : BitVec 64) : (a ↦ₛ rest) ⊢ memRegion a 336 := by rw [← hrest]; exact ProofLib.pointsToBytes_entails_memRegion a rest
  refine Entails.trans (sepConj_mono_right (sepConj_mono (hb (L + 8#64)) (sepConj_mono (hb (L + 0x158#64)) (sepConj_mono (hb (L + 0x2a8#64))
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (hb (L + 0x428#64)) (sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono_right (deserSavedAtL_entails_memRegion_dexitQ L s0))))))))))))))) ?_
  have join (n k : Nat) (h : n + k ≤ 2 ^ 64) : memRegion L n ∗ memRegion (L + BitVec.ofNat 64 n) k = memRegion L (n + k) :=
    (memRegion_split' (b := L) (b' := L + BitVec.ofNat 64 n) (n := n) (k := k) rfl rfl h).symm
  simp only [← sepConj_assoc]
  rw [join 8 336 (by decide), join 344 336 (by decide), join 680 336 (by decide), join 1016 8 (by decide), join 1024 8 (by decide),
    join 1032 8 (by decide), join 1040 8 (by decide), join 1048 8 (by decide), join 1056 8 (by decide), join 1064 336 (by decide),
    join 1400 0x170 (by decide), join 1768 8 (by decide), join 1776 0x20 (by decide), join 1808 0x60 (by decide)]
  exact Entails.refl _

private theorem dexit_frame_entails_stackAt_dexitQ (s0 : State) (c0 w0 : BitVec 64) (rest : List (BitVec 8)) (hrest : rest.length = 336) :
    let L := deserSpL s0.sp
    stackAt L deserCalleeStack ∗ (memRegion L 8 ∗ ((L + 8#64) ↦ₛ rest) ∗ ((L + 0x158#64) ↦ₛ rest) ∗ ((L + 0x2a8#64) ↦ₛ rest) ∗
      ((L + 0x3f8#64) ↦₆₄ c0) ∗ ((L + 0x400#64) ↦₆₄ 0#64) ∗ ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
      ((L + 0x420#64) ↦₆₄ w0) ∗ ((L + 0x428#64) ↦ₛ rest) ∗ memRegion (L + 0x578#64) 0x170 ∗ ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗
      memRegion (L + 0x6f0#64) 0x20 ∗ deserSavedAtL_dexitQ L s0) ⊢ stackAt s0.sp recDeserializeStack := by
  intro L; refine Entails.trans (sepConj_mono_right (dexit_locals_entails_memRegion_dexitQ L c0 w0 s0 rest hrest)) ?_; unfold stackAt
  have h1 : s0.sp - BitVec.ofNat 64 recDeserializeStack = L - BitVec.ofNat 64 deserCalleeStack := by dsimp [L, deserSpL, recDeserializeStack, deserCalleeStack]; bv_omega
  rw [h1, memRegion_split' (b := L - BitVec.ofNat 64 deserCalleeStack) (b' := L) (N := recDeserializeStack) (n := deserCalleeStack) (k := 0x770) (by decide)
    (by dsimp [deserCalleeStack, recDeserializeStack]; bv_omega) (by decide)]
  exact Entails.refl _

@[local simp, local wp_norm, local arm64_norm] private theorem symtab_setPState_dexitQ (s : State) (ps : PState) : (s.setPState ps).symtab = s.symtab := rfl

end Symbolic.Swarm.TRREF.B3DeserQ
