/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Mac.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Mac.MacCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContracts -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.CodeLayout -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Calls
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ParseServiceId
import ProofLib.SepLogic.WPp
import ProofLib.Sep
meta import Lean
public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.InImageLift

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace AddressesStateSimp

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

end AddressesStateSimp

open AddressesStateSimp

run_meta do
  let env ← Lean.getEnv
  for (h, ks) in #[(``RustAlloc.live, #[1]), (``stackAt, #[0]), (``protocolAddressAt, #[2]), (``optSerializeAddressesAt, #[1])] do
    let n := Lean.mkPrivateName env (((ks.foldl Lean.Name.mkNum ProofLib.Sep.sepKeyMarker).str "_TARGET_") ++ h)
    unless env.contains n do
      Lean.withExporting (isExporting := false) do
        Lean.addDecl <| .defnDecl { name := n, levelParams := [], type := .const ``Unit [], value := .const ``Unit.unit [], hints := .abbrev, safety := .safe }

/-! ## 16-byte UUID word unpacking -/

/-- Low 64-bit little-endian word of a 16-byte UUID (`bytes[0..8]`). -/
@[expose] def uuidWord0 (u : List.Vector (BitVec 8) 16) : BitVec 64 :=
  pack64 (u.toList.getD 0 0#8) (u.toList.getD 1 0#8) (u.toList.getD 2 0#8) (u.toList.getD 3 0#8)
    (u.toList.getD 4 0#8) (u.toList.getD 5 0#8) (u.toList.getD 6 0#8) (u.toList.getD 7 0#8)

/-- High 64-bit little-endian word of a 16-byte UUID (`bytes[8..16]`). -/
@[expose] def uuidWord1 (u : List.Vector (BitVec 8) 16) : BitVec 64 :=
  pack64 (u.toList.getD 8 0#8) (u.toList.getD 9 0#8) (u.toList.getD 10 0#8) (u.toList.getD 11 0#8)
    (u.toList.getD 12 0#8) (u.toList.getD 13 0#8) (u.toList.getD 14 0#8) (u.toList.getD 15 0#8)

theorem pointsToBytes_uuid (a : BitVec 64) (u : List.Vector (BitVec 8) 16) :
    (a ↦ₛ u.toList) = ((a ↦₆₄ uuidWord0 u) ∗ ((a + 8#64) ↦₆₄ uuidWord1 u)) := by
  have hlen : u.toList.length = 16 := u.toList_length
  have hsplit : u.toList = (u.toList.drop 0).take 8 ++ (u.toList.drop 8).take 8 := by
    have hd : (u.toList.drop 8).length ≤ 8 := by simp [hlen]
    simp only [List.drop_zero, List.take_of_length_le hd, List.take_append_drop]
  conv => lhs; rw [hsplit]
  rw [pointsToBytes_append]
  have ht8 : ((u.toList.drop 0).take 8).length = 8 := by simp [hlen]
  rw [ht8, pointsToBytes_take8_eq_pointsTo64 a u.toList 0 (by omega),
    pointsToBytes_take8_eq_pointsTo64 (a + 8#64) u.toList 8 (by omega)]
  rfl

@[local simp, local arm64_norm]
theorem kindByte_beq_two (pni : Bool) : (kindByte pni == 2#8) = false := by
  cases pni <;> decide

@[local simp, local arm64_norm]
theorem kindByte_zext32_beq_two (pni : Bool) :
    ((kindByte pni).zeroExtend 32 == 2#32) = false := by
  cases pni <;> decide

@[local simp, local arm64_norm]
theorem kindByte_zext64_beq_two (pni : Bool) :
    ((kindByte pni).zeroExtend 64 == 2#64) = false := by
  cases pni <;> decide

@[local simp, local arm64_norm]
theorem kindByte_bne_two (pni : Bool) : (kindByte pni != 2#8) = true := by
  cases pni <;> decide

@[local simp, local arm64_norm]
theorem kindByte_zext32_bne_two (pni : Bool) :
    ((kindByte pni).zeroExtend 32 != 2#32) = true := by
  cases pni <;> decide

@[local simp, local arm64_norm]
theorem kindByte_zext64_bne_two (pni : Bool) :
    ((kindByte pni).zeroExtend 64 != 2#64) = true := by
  cases pni <;> decide

/-! ## `parseSidCodeSpec` with 64-bit word cells -/

theorem memRegion_17_eq (a : BitVec 64) :
    memRegion a 17 =
      ∃∗ b0 : BitVec 8, ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        (a ↦₈ b0) ∗ ((a + 1#64) ↦₆₄ w0) ∗ ((a + 9#64) ↦₆₄ w1) := by
  sep_interval_eq

theorem pointsTo_17_entails_memRegion (a : BitVec 64) (b0 : BitVec 8) (w0 w1 : BitVec 64) :
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦₆₄ w0) ∗ ((a + 9#64) ↦₆₄ w1)) ⊢ memRegion a 17 := by
  sep_interval

/-- Ghost arguments of `parseSidCellsSpecAt`: `(p, bs, out, b0, w0, w1)`. -/
abbrev ParseSidCellsGhost :=
  BitVec 64 × List (BitVec 8) × BitVec 64 × BitVec 8 × BitVec 64 × BitVec 64

theorem memRegion_16_out_split (a : BitVec 64) :
    memRegion (a + 1#64) 16 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ((a + 1#64) ↦₆₄ w0) ∗ ((a + 9#64) ↦₆₄ w1) := by
  sep_interval_eq

@[expose] def parseSidCellsResultAt (out : BitVec 64) :
    Option (Bool × List.Vector (BitVec 8) 16) → SepProp
  | some (pni, uuid) =>
    (out ↦₈ kindByte pni) ∗ ((out + 1#64) ↦₆₄ uuidWord0 uuid) ∗ ((out + 9#64) ↦₆₄ uuidWord1 uuid)
  | none =>
    (out ↦₈ 2#8) ∗ ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
      ((out + 1#64) ↦₆₄ w0) ∗ ((out + 9#64) ↦₆₄ w1)

theorem parseSidResultAt_eq_cells (out : BitVec 64)
    (res : Option (Bool × List.Vector (BitVec 8) 16)) :
    parseSidResultAt out res = parseSidCellsResultAt out res := by
  cases res with
  | none =>
    simp only [parseSidResultAt, parseSidCellsResultAt, memRegion_16_out_split]
  | some val =>
    rcases val with ⟨pni, uuid⟩
    simp only [parseSidResultAt, parseSidCellsResultAt, pointsToBytes_uuid (out + 1#64) uuid]
    have h9 : out + 1#64 + 8#64 = out + 9#64 := by bv_arith
    rw [h9]

private theorem stackAt_allocHookStack_eq_parseSid (sp : BitVec 64) :
    stackAt sp allocHookStack =
      stackAt sp parseSidStack ∗ memRegion (sp - 4096#64) 3824 := by
  show stackAt sp (parseSidStack + 3824) = _
  rw [ProofLib.stackAt_split_bottom sp parseSidStack 3824 (by decide)]
  exact sepConj_comm _ _

/-- Stack-parameterized `parseSidCellsSpec` at arbitrary callee stack `callStack`. -/
@[expose] def parseSidCellsSpecAt (parse : UuidParser) (callStack : Nat) : Spec ParseSidCellsGhost where
  pre := fun (p, bs, out, b0, w0, w1) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ s.readReg64 .x8 = out⌝ ∗
      (p ↦ₛ bs) ∗ (out ↦₈ b0) ∗ ((out + 1#64) ↦₆₄ w0) ∗ ((out + 9#64) ↦₆₄ w1) ∗
      stackAt s.sp callStack
  post := fun (p, bs, out, _, _, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (p ↦ₛ bs) ∗ parseSidCellsResultAt out (serviceIdParse parse bs) ∗
      stackAt s0.sp callStack

/-- `parseSidStack + extHookStack` as the uuid hook's `extHookStack` below the own frame
`parseSidFrameStack`, plus the unused bottom `uuidTryParseStack` bytes. -/
private theorem stackAt_parseSid_add_extHook (sp : BitVec 64) :
    stackAt sp (parseSidStack + extHookStack) =
      memRegion (sp - BitVec.ofNat 64 (parseSidStack + extHookStack)) uuidTryParseStack ∗
        stackAt (sp - 80#64) extHookStack ∗ stackAt sp parseSidFrameStack := by
  have h1 : parseSidStack + extHookStack = (0x50 + extHookStack) + uuidTryParseStack := rfl
  rw [h1, ProofLib.stackAt_split_bottom sp (0x50 + extHookStack) uuidTryParseStack (by decide),
    ProofLib.stackAt_split_bottom sp 0x50 extHookStack (by decide)]
  have hbot : sp - BitVec.ofNat 64 (0x50 + extHookStack) =
      sp - 80#64 - BitVec.ofNat 64 extHookStack := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add]
  rw [hbot]

@[expose] def vecU8BufRest (A : RustAlloc) (cap ptr : BitVec 64) (n : Nat) : SepProp :=
  if cap = 0 then emp
  else A.live ptr cap.toNat 1 ∗ memRegion (ptr + BitVec.ofNat 64 n) (cap.toNat - n)

theorem vecU8At_buf_eq (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length ≤ cap.toNat) :
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
      (ptr ↦ₛ bs) ∗ vecU8BufRest A cap ptr bs.length := by
  unfold vecU8BufRest
  by_cases hcap : cap = 0
  · subst hcap
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hle)
    subst hbs
    simp [pointsToBytes_nil]
  · simp only [hcap, ite_false]
    apply Entails.antisymm <;> bi_entail

theorem vecU8At_expose (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ vecU8BufRest A cap ptr bs.length := by
  unfold vecU8At vecHeader
  trans (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      if cap = 0 then emp
      else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)))
  · by_cases hcap : cap = 0 <;> simp only [hcap, ite_true, ite_false] <;>
      (apply Entails.antisymm <;> bi_entail)
  · simp only [pure_sepConj]
    ext h
    refine and_congr_right fun ⟨hle, _, _⟩ => ?_
    rw [vecU8At_buf_eq A cap ptr bs hle]

@[expose] def addrRest (A : RustAlloc) (g : AddrGhost) (a : BitVec 64) : SepProp :=
  (a ↦₆₄ g.name.cap) ∗ vecU8BufRest A g.name.cap g.name.ptr g.name.bytes.length ∗
    memRegion (a + 0x19#64) 7

theorem protocolAddressAt_expose (A : RustAlloc) (g : AddrGhost) (a : BitVec 64) :
    protocolAddressAt A g a =
      ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
        ((a + 8#64) ↦₆₄ g.name.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
        (g.name.ptr ↦ₛ g.name.bytes) ∗
        ((a + 24#64) ↦₈ g.device) ∗
        addrRest A g a := by
  unfold protocolAddressAt vecGhostAt addrRest
  rw [vecU8At_expose]
  unfold vecU8BufRest
  by_cases hcap : g.name.cap = 0 <;> simp only [hcap, ite_true, ite_false] <;>
    (apply Entails.antisymm <;> bi_entail)

theorem memRegion_18_eq (a : BitVec 64) :
    memRegion a 18 =
      ∃∗ b0 : BitVec 8, ∃∗ w1 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ b17 : BitVec 8,
        (a ↦₈ b0) ∗ ((a + 1#64) ↦₆₄ w1) ∗ ((a + 9#64) ↦₆₄ w9) ∗ ((a + 17#64) ↦₈ b17) := by
  sep_interval_eq

theorem memRegion_36_addr_split (p : BitVec 64) :
    memRegion p 36 =
      ∃∗ b0 : BitVec 8, ∃∗ w1 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ b17 : BitVec 8,
      ∃∗ b18 : BitVec 8, ∃∗ w19 : BitVec 64, ∃∗ w27 : BitVec 64, ∃∗ b35 : BitVec 8,
        (p ↦₈ b0) ∗ ((p + 1#64) ↦₆₄ w1) ∗ ((p + 9#64) ↦₆₄ w9) ∗ ((p + 17#64) ↦₈ b17) ∗
        ((p + 18#64) ↦₈ b18) ∗ ((p + 19#64) ↦₆₄ w19) ∗ ((p + 27#64) ↦₆₄ w27) ∗ ((p + 35#64) ↦₈ b35) := by
  sep_interval_eq

theorem pointsToBytes_addrBytes_append (p : BitVec 64)
    (s : Bool × List.Vector (BitVec 8) 16) (dev : BitVec 8) (rest : List (BitVec 8)) :
    (p ↦ₛ (addrBytes s dev ++ rest)) =
      (p ↦₈ kindByte s.1) ∗ ((p + 1#64) ↦₆₄ uuidWord0 s.2) ∗
      ((p + 9#64) ↦₆₄ uuidWord1 s.2) ∗ ((p + 17#64) ↦₈ dev) ∗ ((p + 18#64) ↦ₛ rest) := by
  unfold addrBytes
  rw [List.cons_append, List.append_assoc, List.singleton_append,
    pointsToBytes_cons, pointsToBytes_append, s.2.toList_length, pointsToBytes_cons,
    pointsToBytes_uuid (p + 1#64) s.2]
  have h9 : p + 1#64 + 8#64 = p + 9#64 := by bv_arith
  have h17 : p + 1#64 + 16#64 = p + 17#64 := by bv_arith
  have h18 : p + 17#64 + 1#64 = p + 18#64 := by bv_arith
  rw [h9, h17, h18]
  apply Entails.antisymm <;> bi_entail

theorem pointsToBytes_addrBytes_pair (p : BitVec 64)
    (s r : Bool × List.Vector (BitVec 8) 16) (sDev rDev : BitVec 8) :
    (p ↦ₛ (addrBytes s sDev ++ addrBytes r rDev)) =
      (p ↦₈ kindByte s.1) ∗ ((p + 1#64) ↦₆₄ uuidWord0 s.2) ∗ ((p + 9#64) ↦₆₄ uuidWord1 s.2) ∗
      ((p + 17#64) ↦₈ sDev) ∗ ((p + 18#64) ↦₈ kindByte r.1) ∗
      ((p + 19#64) ↦₆₄ uuidWord0 r.2) ∗ ((p + 27#64) ↦₆₄ uuidWord1 r.2) ∗ ((p + 35#64) ↦₈ rDev) := by
  rw [pointsToBytes_addrBytes_append p s sDev,
    ← List.append_nil (addrBytes r rDev),
    pointsToBytes_addrBytes_append (p + 18#64) r rDev [],
    pointsToBytes_nil, sepConj_emp]
  have h19 : p + 18#64 + 1#64 = p + 19#64 := by bv_arith
  have h27 : p + 18#64 + 9#64 = p + 27#64 := by bv_arith
  have h35 : p + 18#64 + 17#64 = p + 35#64 := by bv_arith
  rw [h19, h27, h35]

theorem addrBytes_pair_length (s r : Bool × List.Vector (BitVec 8) 16) (sDev rDev : BitVec 8) :
    (addrBytes s sDev ++ addrBytes r rDev).length = 36 := by
  simp [addrBytes, s.2.toList_length, r.2.toList_length]

theorem optSerializeAddressesAt_some_36_eq (A : RustAlloc) (ret : BitVec 64)
    (s r : Bool × List.Vector (BitVec 8) 16) (sDev rDev : BitVec 8) :
    optSerializeAddressesAt A ret (some (addrBytes s sDev ++ addrBytes r rDev)) =
      ∃∗ p : BitVec 64,
        ⌜p ≠ 0⌝ ∗
        (ret ↦₆₄ 36#64) ∗ ((ret + 8#64) ↦₆₄ p) ∗ ((ret + 16#64) ↦₆₄ 36#64) ∗
        A.live p 36 1 ∗
        (p ↦₈ kindByte s.1) ∗ ((p + 1#64) ↦₆₄ uuidWord0 s.2) ∗ ((p + 9#64) ↦₆₄ uuidWord1 s.2) ∗
        ((p + 17#64) ↦₈ sDev) ∗ ((p + 18#64) ↦₈ kindByte r.1) ∗
        ((p + 19#64) ↦₆₄ uuidWord0 r.2) ∗ ((p + 27#64) ↦₆₄ uuidWord1 r.2) ∗ ((p + 35#64) ↦₈ rDev) := by
  dsimp only [optSerializeAddressesAt]
  refine congrArg sepExists (funext fun p => ?_)
  rw [vecU8At_expose, addrBytes_pair_length, pointsToBytes_addrBytes_pair]
  unfold vecU8BufRest
  have h36 : (36#64 : BitVec 64).toNat = 36 := rfl
  have hne : (36#64 : BitVec 64) ≠ 0 := by decide
  simp only [hne, ite_false, h36, Nat.sub_self, memRegion_zero, sepConj_emp]
  have hpure : (36 ≤ 36 ∧ 36 < 2 ^ 63 ∧ p ≠ 0) ↔ (p ≠ 0) :=
    ⟨fun ⟨_, _, hp⟩ => hp, fun hp => ⟨by decide, by decide, hp⟩⟩
  simp only [hpure]
  apply Entails.antisymm <;> bi_entail

/-- Stack-parameterized `serializeAddressesSpec` (`= serializeAddressesSpec` at `allocHookStack`,
`= serializeAddressesSpecX` at `parseSidStack + extHookStack`). -/
@[expose] def serializeAddressesSpecAt (A : RustAlloc) (parse : UuidParser) (callStack : Nat) :
    Spec SerializeAddressesGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.senderA ∧ s.readReg64 .x2 = x.recipientA⌝ ∗
      protocolAddressAt A x.sender x.senderA ∗ protocolAddressAt A x.recipient x.recipientA ∗
      memRegion x.ret 24 ∗ A.pool ∗ stackAt s.sp (callStack + 128)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      protocolAddressAt A x.sender x.senderA ∗ protocolAddressAt A x.recipient x.recipientA ∗
      optSerializeAddressesAt A x.ret (serializeAddresses (serviceIdParse parse) x.sender x.recipient) ∗
      A.pool ∗ stackAt s0.sp (callStack + 128)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private def serializeAddressesFrameRest (sp : BitVec 64) : SepProp :=
  memRegion (sp - 96#64) 12 ∗ memRegion (sp - 67#64) 3

private theorem stackAt_serializeAddresses_at {callStack : Nat}
    (hbound : callStack + 128 ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (callStack + 128) =
      stackAt (sp - 128#64) callStack ∗
      serializeAddressesFrameRest sp ∗
      (∃∗ q0 : BitVec 64, ∃∗ q1 : BitVec 64, ∃∗ q2 : BitVec 64, ∃∗ q3 : BitVec 64,
        ((sp - 128#64) ↦₆₄ q0) ∗ ((sp - 120#64) ↦₆₄ q1) ∗
        ((sp - 112#64) ↦₆₄ q2) ∗ ((sp - 104#64) ↦₆₄ q3)) ∗
      (∃∗ b0 : BitVec 8, ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        ((sp - 84#64) ↦₈ b0) ∗ ((sp - 83#64) ↦₆₄ w0) ∗ ((sp - 75#64) ↦₆₄ w1)) ∗
      (∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64, ∃∗ s3 : BitVec 64,
       ∃∗ s4 : BitVec 64, ∃∗ s5 : BitVec 64, ∃∗ s6 : BitVec 64, ∃∗ s7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ s0) ∗ ((sp - 56#64) ↦₆₄ s1) ∗
        ((sp - 48#64) ↦₆₄ s2) ∗ ((sp - 40#64) ↦₆₄ s3) ∗
        ((sp - 32#64) ↦₆₄ s4) ∗ ((sp - 24#64) ↦₆₄ s5) ∗
        ((sp - 16#64) ↦₆₄ s6) ∗ ((sp - 8#64) ↦₆₄ s7)) := by
  have htop : stackAt sp (callStack + 128) =
      stackAt (sp - 128#64) callStack ∗ memRegion (sp - 128#64) 128 := by
    simp only [stackAt]
    rw [memRegion_split _ callStack 128 hbound]
    have e1 : sp - BitVec.ofNat 64 (callStack + 128) =
        sp - 128#64 - BitVec.ofNat 64 callStack := by
      rw [BitVec.sub_sub, ← BitVec.ofNat_add, Nat.add_comm]
    have e2 : sp - 128#64 - BitVec.ofNat 64 callStack + BitVec.ofNat 64 callStack =
        sp - 128#64 := BitVec.sub_add_cancel _ _
    rw [e1, e2]
  have hm128 : memRegion (sp - 128#64) 128 =
      serializeAddressesFrameRest sp ∗
      (∃∗ q0 : BitVec 64, ∃∗ q1 : BitVec 64, ∃∗ q2 : BitVec 64, ∃∗ q3 : BitVec 64,
        ((sp - 128#64) ↦₆₄ q0) ∗ ((sp - 120#64) ↦₆₄ q1) ∗
        ((sp - 112#64) ↦₆₄ q2) ∗ ((sp - 104#64) ↦₆₄ q3)) ∗
      (∃∗ b0 : BitVec 8, ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        ((sp - 84#64) ↦₈ b0) ∗ ((sp - 83#64) ↦₆₄ w0) ∗ ((sp - 75#64) ↦₆₄ w1)) ∗
      (∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64, ∃∗ s3 : BitVec 64,
       ∃∗ s4 : BitVec 64, ∃∗ s5 : BitVec 64, ∃∗ s6 : BitVec 64, ∃∗ s7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ s0) ∗ ((sp - 56#64) ↦₆₄ s1) ∗
        ((sp - 48#64) ↦₆₄ s2) ∗ ((sp - 40#64) ↦₆₄ s3) ∗
        ((sp - 32#64) ↦₆₄ s4) ∗ ((sp - 24#64) ↦₆₄ s5) ∗
        ((sp - 16#64) ↦₆₄ s6) ∗ ((sp - 8#64) ↦₆₄ s7)) := by
    unfold serializeAddressesFrameRest
    sep_interval_eq
  rw [htop, hm128]

theorem memRegion_24_ret_split (r : BitVec 64) :
    memRegion r 24 = (∃∗ v0 : BitVec 64, r ↦₆₄ v0) ∗ memRegion (r + 8#64) 16 := by
  sep_interval_eq

theorem memRegion_16_ret_split (r : BitVec 64) :
    memRegion (r + 8#64) 16 =
      ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ((r + 8#64) ↦₆₄ v1) ∗ ((r + 16#64) ↦₆₄ v2) := by
  sep_interval_eq

attribute [local irreducible] Program.fnOff

private theorem shimWithStack_of_noAllocShim {prog : Program} {addr : BitVec 64} (hookStack : Nat)
    (h : subroutine_ok prog addr noAllocShimSpec) :
    subroutine_ok prog addr (shimSpecWithStack hookStack) := by
  have h' := subroutine_ok_withStack_of_subroutine_ok h hookStack
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withStack noAllocShimSpec hookStack).pre x s0 ∗ R := by
    dsimp only [withStack, noAllocShimSpec, shimSpecWithStack] at hpre ⊢
    simpa only [emp_sepConj, sepConj_assoc] using hpre
  refine h'.mono_outcome x R s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hpan | hex | hoom)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, noAllocShimSpec, shimSpecWithStack] at hpost ⊢
    simpa only [emp_sepConj, sepConj_assoc] using hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

theorem shimSpecWithStack_widen {P : Program} {addr : BitVec 64}
    {s1 extra : Nat} (hbound : s1 + extra ≤ 2 ^ 64)
    (h : subroutine_ok P addr (shimSpecWithStack s1)) :
    subroutine_ok P addr (shimSpecWithStack (extra + s1)) := by
  have hsplit : ∀ sp : BitVec 64,
      stackAt sp (extra + s1) =
        stackAt sp s1 ∗ memRegion (sp - BitVec.ofNat 64 (extra + s1)) extra := by
    intro sp
    rw [Nat.add_comm extra s1, ProofLib.stackAt_split_bottom sp s1 extra hbound, sepConj_comm]
  refine subroutine_ok_map h ?_
  rintro ⟨⟩ R s0 hpre
  refine ⟨(), memRegion (s0.sp - BitVec.ofNat 64 (extra + s1)) extra ∗ R, ?_, fun sf hpost => ?_⟩
  · simp only [shimSpecWithStack, hsplit] at hpre ⊢
    exact Satisfies.mono (by bi_entail) hpre
  · simp only [shimSpecWithStack, hsplit] at hpost ⊢
    exact Satisfies.mono (by bi_entail) hpost

theorem rustAllocSpecWithStack_widen {A : RustAlloc} {P : Program}
    {addr : BitVec 64} {s1 extra : Nat} (hbound : s1 + extra ≤ 2 ^ 64)
    (h : subroutine_ok P addr (rustAllocSpecWithStack A s1)) :
    subroutine_ok P addr (rustAllocSpecWithStack A (extra + s1)) := by
  have hsplit : ∀ sp : BitVec 64,
      stackAt sp (extra + s1) =
        stackAt sp s1 ∗ memRegion (sp - BitVec.ofNat 64 (extra + s1)) extra := by
    intro sp
    rw [Nat.add_comm extra s1, ProofLib.stackAt_split_bottom sp s1 extra hbound, sepConj_comm]
  refine subroutine_ok_map h ?_
  rintro ⟨size, align⟩ R s0 hpre
  refine ⟨(size, align),
    memRegion (s0.sp - BitVec.ofNat 64 (extra + s1)) extra ∗ R,
    ?_, fun sf hpost => ?_⟩
  · simp only [rustAllocSpecWithStack, hsplit] at hpre ⊢
    exact Satisfies.mono (by bi_entail) hpre
  · simp only [rustAllocSpecWithStack, hsplit] at hpost ⊢
    by_cases h0 : sf.readReg64 (Reg.gpr 0#5) = 0 <;>
      simp only [h0, ite_true, ite_false] at hpost ⊢ <;>
      exact Satisfies.mono (by bi_entail) hpost

theorem parseSidCells_of_parseSidCode [LibsignalPlacement] {P : Program} {addr : BitVec 64}
    {parse : UuidParser}
    (h : subroutine_ok P addr (withLsCodeLoaded lsmpl (parseSidCodeSpec parse))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (parseSidCellsSpecAt parse allocHookStack)) := by
  refine subroutine_ok_map h ?_
  rintro ⟨p, bs, out, b0, w0, w1⟩ R s0 hpre
  refine ⟨(p, bs, out), memRegion (s0.sp - 4096#64) 3824 ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [withLsCodeLoaded, parseSidCellsSpecAt, parseSidCodeSpec, parseSidSpec] at hpre ⊢
    rw [stackAt_allocHookStack_eq_parseSid] at hpre
    rw [memRegion_17_eq out]
    exact Satisfies.mono (by bi_entail) hpre
  · dsimp only [withLsCodeLoaded, parseSidCodeSpec, parseSidSpec, parseSidCellsSpecAt] at hpost ⊢
    rw [parseSidResultAt_eq_cells] at hpost
    rw [stackAt_allocHookStack_eq_parseSid]
    rcases hres : serviceIdParse parse bs with _ | ⟨pni, uuid⟩ <;>
      (simp only [hres, parseSidCellsResultAt] at hpost ⊢; exact Satisfies.mono (by bi_entail) hpost)

theorem parseSidCells_of_parseSidStack [LibsignalPlacement] {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr (withLsCodeLoaded lsmpl (parseSidCodeStackSpec extHookStack))) :
    subroutine_ok P addr
      (withLsCodeLoaded lsmpl (parseSidCellsSpecAt uuidTryParse (parseSidStack + extHookStack))) := by
  refine subroutine_ok_map h ?_
  rintro ⟨p, bs, out, b0, w0, w1⟩ R s0 hpre
  refine ⟨(p, bs, out),
    memRegion (s0.sp - BitVec.ofNat 64 (parseSidStack + extHookStack)) uuidTryParseStack ∗ R,
    ?_, fun sf hpost => ?_⟩
  · dsimp only [withLsCodeLoaded, parseSidCellsSpecAt, parseSidCodeStackSpec, parseSidSpec] at hpre ⊢
    rw [stackAt_parseSid_add_extHook] at hpre
    rw [memRegion_17_eq out]
    exact Satisfies.mono (by bi_entail) hpre
  · dsimp only [withLsCodeLoaded, parseSidCodeStackSpec, parseSidSpec, parseSidCellsSpecAt] at hpost ⊢
    rw [parseSidResultAt_eq_cells] at hpost
    rw [stackAt_parseSid_add_extHook]
    rcases hres : serviceIdParse uuidTryParse bs with _ | ⟨pni, uuid⟩ <;>
      (simp only [hres, parseSidCellsResultAt] at hpost ⊢; exact Satisfies.mono (by bi_entail) hpost)

private theorem parseSidCells_placed_ok_at_state [LibsignalPlacement] {prog : Program}
    {parse : UuidParser} {callStack : Nat} {addr : BitVec 64} {s : State}
    (hparse : subroutine_ok prog addr (withLsCodeLoaded lsmpl (parseSidCellsSpecAt parse callStack)))
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    subroutine_ok prog addr
      { pre := fun (p, bs, out, b0, w0, w1) s' =>
          ⌜s'.mem = s.mem ∧
            s'.readReg64 .x0 = p ∧ (s'.readReg64 .x1).toNat = bs.length ∧ s'.readReg64 .x8 = out⌝ ∗
            (p ↦ₛ bs) ∗ (out ↦₈ b0) ∗ ((out + 1#64) ↦₆₄ w0) ∗ ((out + 9#64) ↦₆₄ w1) ∗
            stackAt s'.sp callStack
        post := (parseSidCellsSpecAt parse callStack).post } := by
  refine subroutine_ok_outcome_intro fun ⟨p, bs, out, b0, w0, w1⟩ R s0 hpc hrun hm hsp => ?_
  refine hparse.mono_outcome (p, bs, out, b0, w0, w1) R s0 hpc hrun ?_ hsp (fun _ ho => ho)
  dsimp only [withLsCodeLoaded, parseSidCellsSpecAt] at hm ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hmem, hrest⟩, hspatial⟩
  refine ⟨hmem ▸ hcl, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hrest, hspatial⟩

/-- Relocatable `[LibsignalPlacement]` proof of `<SignalMessage>::serialize_addresses` (Block `61`)
from `parseSid`, `shim`, and `alloc` contracts at `callStack`. -/
theorem serialize_addresses_placed_ok_of_hooks [LibsignalPlacement]
    {A : RustAlloc} {parse : UuidParser} {H : String → Option (State → State)}
    {callStack : Nat} (hbound : callStack + 128 ≤ 2 ^ 64 := by decide)
    (hparse_in : subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCellsSpecAt parse callStack)))
    (hshim : subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (lsρ lsMacRustNoAllocShimSym)
      (shimSpecWithStack callStack))
    (halloc : subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (lsρ lsMacRustAllocSym)
      (rustAllocSpecWithStack A callStack))
    (hpanic_in : H lsMacHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (blkPl_61).base
      (withLsCodeLoaded lsmpl (serializeAddressesSpecAt A parse callStack)) := by
  have hpanic : ((blkPC_61).rebase (blkPl_61).base H).externAt? (lsρ lsMacHandleErrorSym) =
      some Rust.panicked :=
    (mac_ls_externAt?_of_mem).trans hpanic_in
  unfold withLsCodeLoaded
  simp only [serializeAddressesSpecAt, protocolAddressAt_expose, stackAt_serializeAddresses_at hbound,
    memRegion_24_ret_split, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wpp_init x s0
  obtain ⟨ret, senderA, sender, recipientA, recipient⟩ := x
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hlen_s : (BitVec.ofNat 64 sender.name.bytes.length).toNat = sender.name.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlen_r : (BitVec.ofNat 64 recipient.name.bytes.length).toNat = recipient.name.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply sepWPp_seq_lscl (mid := lsmpl.base 206) hcl0
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl1
  have hparse1 := parseSidCells_placed_ok_at_state hparse_in hcl1
  apply sepWPp_seq_lscl (mid := (blkPl_61).base + 52#64) hcl1
  wp_call hparse1 (sender.name.ptr, sender.name.bytes, s0.sp - 84#64, v_stk_8, v_stk_9, v_stk_10)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl2
  have ha83 : s0.sp - 84#64 + 1#64 = s0.sp - 83#64 := by bv_arith
  have ha75 : s0.sp - 84#64 + 9#64 = s0.sp - 75#64 := by bv_arith
  cases hs : serviceIdParse parse sender.name.bytes with
  | none =>
    simp only [parseSidCellsResultAt, serializeAddresses, hs, Option.bind_eq_bind, Option.bind,
      optSerializeAddressesAt, noneCap, ha83, ha75, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc]
    refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done
  | some sval =>
    rcases sval with ⟨sPni, sUuid⟩
    simp only [parseSidCellsResultAt, ha83, ha75, sepConj_assoc]
    apply sepWPp_seq_lscl (mid := lsmpl.base 206) hcl2
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcl3
    have hparse2 := parseSidCells_placed_ok_at_state hparse_in hcl3
    apply sepWPp_seq_lscl (mid := (blkPl_61).base + 84#64) hcl3
    wp_call hparse2 (recipient.name.ptr, recipient.name.bytes, s0.sp - 84#64,
      kindByte sPni, uuidWord0 sUuid, uuidWord1 sUuid)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro _hcl4
    cases hr : serviceIdParse parse recipient.name.bytes with
    | none =>
      simp only [parseSidCellsResultAt, serializeAddresses, hs, hr, Option.bind_eq_bind,
        Option.bind, optSerializeAddressesAt, noneCap, ha83, ha75, sepExists_sepConj_left,
        sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 => ?_
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done
    | some rval =>
      rcases rval with ⟨rPni, rUuid⟩
      simp only [parseSidCellsResultAt, ha83, ha75, sepConj_assoc]
      have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      have hlay : LayoutOk 36 1 := ⟨by decide, hpow1, by decide⟩
      apply SepWPp.of_sepWP (mid := lsρ lsMacRustNoAllocShimSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      apply SepWPp.of_sepWP (mid := lsρ lsMacRustAllocSym)
      wp_call hshim ()
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      apply SepWPp.of_sepWP (mid := (blkPl_61).base + 152#64)
      wp_call halloc (36, 1)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      have hsp2 : sf_2.sp = s0.sp - 128#64 := by simp only [wp_norm, arm64_norm, *]
      rw [hsp2]
      by_cases hoom : sf_3.readReg64 (Reg.gpr 0#5) = 0
      · simp only [hoom, ite_true]
        rw [sepConj_left_comm (stackAt (s0.sp - 128#64) callStack), sepConj_left_comm A.pool]
        refine SepWPp.pure_elim fun htrace => ?_
        apply SepWPp.of_sepWP (mid := lsρ lsMacHandleErrorSym)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by simpa using hpanic) fun hm => ?_
        simpa only [sepConj_assoc] using
          allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
      · have hoom' : sf_3.readReg64 (Reg.gpr 0#5) ≠ 0 := hoom
        simp only [hoom, ite_false, sepConj_assoc]
        rw [sepConj_left_comm (stackAt (s0.sp - 128#64) callStack), sepConj_left_comm A.pool]
        refine SepWPp.pure_elim fun ⟨_, htrace⟩ => ?_
        rw [memRegion_36_addr_split (sf_3.readReg64 (Reg.gpr 0#5))]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        refine SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun w1 =>
          SepWPp.exists_elim fun w9 => SepWPp.exists_elim fun b17 =>
          SepWPp.exists_elim fun b18 => SepWPp.exists_elim fun w19 =>
          SepWPp.exists_elim fun w27 => SepWPp.exists_elim fun b35 => ?_
        rw [memRegion_16_ret_split ret]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        refine SepWPp.exists_elim fun rv1 => SepWPp.exists_elim fun rv2 => ?_
        simp only [serializeAddresses, hs, hr, Option.bind_eq_bind, Option.bind, pure,
          optSerializeAddressesAt_some_36_eq, sepExists_sepConj_left, sepExists_sepConj_right,
          sepConj_assoc]
        apply SepWPp.of_sepWP_ret
        wp_steps
        wp_done

theorem serialize_addresses_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {parse : UuidParser} {H : String → Option (State → State)}
    (hparse : subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeSpec parse)))
    (hshim : HookSat H lsMacRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsMacRustAllocSym (rustAllocSpec A))
    (hpanic : H lsMacHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (blkPl_61).base
      (withLsCodeLoaded lsmpl (serializeAddressesSpec A parse)) :=
  serialize_addresses_placed_ok_of_hooks (callStack := allocHookStack) (by decide)
    (parseSidCells_of_parseSidCode hparse)
    (shimWithStack_of_noAllocShim allocHookStack (mac_ls_hook_ok_of_mem hshim))
    (mac_ls_hook_ok_of_mem (rustAllocSpecWithStack_eq_rustAllocSpec A ▸ halloc))
    hpanic

theorem serialize_addresses_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (hparse : subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeStackSpec extHookStack)))
    (hshim : HookSat H lsMacRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsMacRustAllocSym (rustAllocSpec A))
    (hpanic : H lsMacHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (blkPl_61).base
      (withLsCodeLoaded lsmpl (serializeAddressesSpecX A uuidTryParse)) :=
  serialize_addresses_placed_ok_of_hooks (callStack := parseSidStack + extHookStack) (by decide)
    (parseSidCells_of_parseSidStack hparse)
    (shimSpecWithStack_widen (by decide) (shimWithStack_of_noAllocShim extHookStack (mac_ls_hook_ok_of_mem hshim)))
    (rustAllocSpecWithStack_widen (by decide)
      (rustAllocWithStack_of_rustAlloc (mac_ls_hook_ok_of_mem halloc) (by decide) (by decide)))
    hpanic

end CryptoVerification.LibsignalTripleRatchet
