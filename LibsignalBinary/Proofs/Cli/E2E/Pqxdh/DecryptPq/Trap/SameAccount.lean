/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccount -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Defs
public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.S0Sym -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegFront.S0B
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.S0A
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.S0B
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Instances
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Defs
import LibsignalBinary.Proofs.TripleRatchet.TrapRng
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244

/-!
# `_trap` twins for `isSameAccountEqDistinct_ok` and weak-`pre` `S0` (`*_pq_distinct_trap`)

Proved directly on `trTrapProgAt` with all byte-packing facts discharged by `bv_slice` / `bv_omega`.
-/

public section

namespace CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames
open CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
open CryptoVerification.E2E.Pqxdh.WireEntries

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 800000

section SameAccountTrap

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem stackAt_parseSidStack_eq_publicKeyEq_sa (sp : BitVec 64) :
    stackAt sp parseSidStack =
      memRegion (sp - 16#64) 16 ∗
      memRegion (sp - 16#64 - 48#64) 48 ∗
      memRegion (sp - 272#64) 208 := by
  simp only [stackAt, parseSidStack, uuidTryParseStack]
  have h64 : sp - 16#64 - 48#64 = sp - 64#64 := by bv_omega
  rw [h64,
      show (80 + 192 : Nat) = 272 from rfl,
      show BitVec.ofNat 64 272 = 272#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 272#64) (b' := sp - 64#64) (N := 272) (n := 208) (k := 64)
        (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 64#64) (b' := sp - 16#64) (N := 64) (n := 48) (k := 16)
        (by decide) (by bv_omega) (by decide)]
  ac_rfl

private def publicKeyEqMem80Spec_sa :
    Spec (BitVec 64 × PublicKey × BitVec 64 × PublicKey × BitVec 64) where
  pre := fun (p1, pk1, p2, pk2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp⌝ ∗
    (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
    stackAt sp parseSidStack
  post := fun (p1, pk1, p2, pk2, sp) s0 sf =>
    ⌜sf.readReg64 .x0 = (if pk1 == pk2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
    (p1 ↦ₛ pk1.bytes.toList) ∗ (p2 ↦ₛ pk2.bytes.toList) ∗
    stackAt sp parseSidStack

private theorem memRegion_17_eq_cells_sa (a : BitVec 64) :
    memRegion a 17 =
      ∃∗ b0 : BitVec 8, ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        (a ↦₈ b0) ∗ ((a + 1#64) ↦₆₄ w0) ∗ ((a + 9#64) ↦₆₄ w1) := by
  rw [show (17 : Nat) = 1 + (8 + 8) by decide,
    memRegion_split a 1 (8 + 8) (by decide),
    memRegion_split (a + 1#64) 8 8 (by decide),
    memRegion_one a, ProofLib.memRegion_eight (a + 1#64),
      ProofLib.memRegion_eight (a + 1#64 + 8#64)]
  have h9 : a + 1#64 + 8#64 = a + 9#64 := by bv_arith
  rw [h9, sepExists_sepConj_left]
  refine congrArg sepExists (funext fun b0 => ?_)
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine congrArg sepExists (funext fun w0 => ?_)
  rw [sepExists_sepConj_right, sepExists_sepConj_right]

private theorem pointsTo_17_entails_memRegion_sa (a : BitVec 64) (b0 : BitVec 8) (w0 w1 : BitVec 64) :
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦₆₄ w0) ∗ ((a + 9#64) ↦₆₄ w1)) ⊢ memRegion a 17 := by
  rw [memRegion_17_eq_cells_sa a]
  exact Entails.sepExists_right b0 (Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.refl _)))

private theorem memRegion_16_out_split_sa (a : BitVec 64) :
    memRegion (a + 1#64) 16 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ((a + 1#64) ↦₆₄ w0) ∗ ((a + 9#64) ↦₆₄ w1) := by
  rw [show (16 : Nat) = 8 + 8 by decide, memRegion_split (a + 1#64) 8 8 (by decide)]
  have h9 : a + 1#64 + BitVec.ofNat 64 8 = a + 9#64 := by bv_arith
  rw [h9, ProofLib.memRegion_eight (a + 1#64), ProofLib.memRegion_eight (a + 9#64),
    sepExists_sepConj_left]
  refine congrArg sepExists (funext fun w0 => ?_)
  rw [sepExists_sepConj_right]

private theorem parseSidResultAt_entails_rel_cells (out : BitVec 64)
    (res : Option (Bool × List.Vector (BitVec 8) 16)) :
    parseSidResultAt out res ⊢
      ∃∗ b0 : BitVec 8, ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        ⌜SidCellsRel res b0 w0 w1⌝ ∗
        (out ↦₈ b0) ∗ ((out + 1#64) ↦₆₄ w0) ∗ ((out + 9#64) ↦₆₄ w1) := by
  cases res with
  | none =>
    simp only [parseSidResultAt, SidCellsRel, memRegion_16_out_split_sa,
      sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro w0
    apply Entails.sepExists_elim; intro w1
    refine Entails.sepExists_right 2#8 (Entails.sepExists_right w0 (Entails.sepExists_right w1 ?_))
    exact Entails.pure_right rfl (Entails.of_eq (by ac_rfl))
  | some val =>
    rcases val with ⟨pni, uuid⟩
    rw [ParseServiceId.parseSidResultAt_some_eq out pni uuid]
    exact Entails.sepExists_right (kindByte pni)
      (Entails.sepExists_right (ParseServiceId.uuidWord0 uuid)
        (Entails.sepExists_right (ParseServiceId.uuidWord1 uuid)
          (Entails.pure_right ⟨rfl, rfl, rfl⟩ (Entails.refl _))))

private abbrev ParseSidRelGhost :=
  BitVec 64 × List (BitVec 8) × BitVec 64 × BitVec 8 × BitVec 64 × BitVec 64

private def parseSidRelSpec (parse : UuidParser) : Spec ParseSidRelGhost where
  pre := fun (p, bs, out, b0, w0, w1) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ s.readReg64 .x8 = out⌝ ∗
      (p ↦ₛ bs) ∗ (out ↦₈ b0) ∗ ((out + 1#64) ↦₆₄ w0) ∗ ((out + 9#64) ↦₆₄ w1) ∗
      stackAt s.sp parseSidStack
  post := fun (p, bs, out, _, _, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (p ↦ₛ bs) ∗
      (∃∗ b0' : BitVec 8, ∃∗ w0' : BitVec 64, ∃∗ w1' : BitVec 64,
        ⌜SidCellsRel (serviceIdParse parse bs) b0' w0' w1'⌝ ∗
        (out ↦₈ b0') ∗ ((out + 1#64) ↦₆₄ w0') ∗ ((out + 9#64) ↦₆₄ w1')) ∗
      stackAt s0.sp parseSidStack

private theorem stackAt_isSameAccountDistinct_split (sp : BitVec 64) :
    stackAt sp isSameAccountDistinctStack =
      stackAt (sp - 80#64) parseSidStack ∗
      memRegion (sp - 80#64) 12 ∗
      (∃∗ b0 : BitVec 8, ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        ((sp - 68#64) ↦₈ b0) ∗ ((sp - 67#64) ↦₆₄ w0) ∗ ((sp - 59#64) ↦₆₄ w1)) ∗
      memRegion (sp - 51#64) 3 ∗
      ProofLib.cells (sp - 48#64) 6 := by
  simp only [stackAt, isSameAccountDistinctStack, parseSidStack, uuidTryParseStack]
  rw [show (80 + (80 + 192) : Nat) = 352 from rfl,
      show (80 + 192 : Nat) = 272 from rfl,
      show BitVec.ofNat 64 352 = 352#64 from rfl,
      show BitVec.ofNat 64 272 = 272#64 from rfl,
      show sp - 80#64 - 272#64 = sp - 352#64 by bv_arith,
      show (352 : Nat) = 272 + (12 + (17 + (3 + 8 * 6))) by decide,
      memRegion_split (sp - 352#64) 272 (12 + (17 + (3 + 8 * 6))) (by decide),
      memRegion_split (sp - 352#64 + 272#64) 12 (17 + (3 + 8 * 6)) (by decide),
      memRegion_split (sp - 352#64 + 272#64 + 12#64) 17 (3 + 8 * 6) (by decide),
      memRegion_split (sp - 352#64 + 272#64 + 12#64 + 17#64) 3 (8 * 6) (by decide),
      ProofLib.memRegion_cells _ 6 (by decide),
      memRegion_17_eq_cells_sa]
  have h1 : sp - 352#64 + 272#64 = sp - 80#64 := by bv_arith
  have h2 : sp - 80#64 + 12#64 = sp - 68#64 := by bv_arith
  have h3 : sp - 68#64 + 1#64 = sp - 67#64 := by bv_arith
  have h4 : sp - 68#64 + 9#64 = sp - 59#64 := by bv_arith
  have h5 : sp - 68#64 + 17#64 = sp - 51#64 := by bv_arith
  have h6 : sp - 51#64 + 3#64 = sp - 48#64 := by bv_arith
  rw [h1, h2, h3, h4, h5, h6]

private theorem pack64_inj_bv (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (h : pack64 a0 a1 a2 a3 a4 a5 a6 a7 = pack64 b0 b1 b2 b3 b4 b5 b6 b7) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4 ∧ a5 = b5 ∧ a6 = b6 ∧ a7 = b7 := by
  have h0 := congrArg (BitVec.extractLsb' 0 8) h
  have h1 := congrArg (BitVec.extractLsb' 8 8) h
  have h2 := congrArg (BitVec.extractLsb' 16 8) h
  have h3 := congrArg (BitVec.extractLsb' 24 8) h
  have h4 := congrArg (BitVec.extractLsb' 32 8) h
  have h5 := congrArg (BitVec.extractLsb' 40 8) h
  have h6 := congrArg (BitVec.extractLsb' 48 8) h
  have h7 := congrArg (BitVec.extractLsb' 56 8) h
  unfold pack64 at h0 h1 h2 h3 h4 h5 h6 h7
  exact ⟨by clear * - h0; bv_slice, by clear * - h1; bv_slice,
    by clear * - h2; bv_slice, by clear * - h3; bv_slice,
    by clear * - h4; bv_slice, by clear * - h5; bv_slice,
    by clear * - h6; bv_slice, by clear * - h7; bv_slice⟩

private theorem uuid_eq_of_uuidWords_eq_bv {u1 u2 : List.Vector (BitVec 8) 16}
    (hw0 : ParseServiceId.uuidWord0 u1 = ParseServiceId.uuidWord0 u2)
    (hw1 : ParseServiceId.uuidWord1 u1 = ParseServiceId.uuidWord1 u2) :
    u1 = u2 := by
  rcases u1 with ⟨l1, hl1⟩
  rcases u2 with ⟨l2, hl2⟩
  rcases l1 with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7,
    _ | ⟨a8, _ | ⟨a9, _ | ⟨a10, _ | ⟨a11, _ | ⟨a12, _ | ⟨a13, _ | ⟨a14, _ | ⟨a15,
      _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try cases hl1
  rcases l2 with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
      _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try cases hl2
  simp only [ParseServiceId.uuidWord0, ParseServiceId.uuidWord1, List.Vector.toList, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hw0 hw1
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := pack64_inj_bv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw0
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := pack64_inj_bv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw1
  rfl

private theorem kindByte_inj_bv {p1 p2 : Bool} (h : kindByte p1 = kindByte p2) : p1 = p2 := by
  cases p1 <;> cases p2 <;> revert h <;> decide

private theorem sidCellsRel_ne_of_distinct_bv {parse : UuidParser} {bs1 bs2 : List (BitVec 8)}
    {b0_1 b0_2 : BitVec 8} {w0_1 w1_1 w0_2 w1_2 : BitVec 64}
    (hDist : DistinctSid parse bs1 bs2)
    (hrel1 : SidCellsRel (serviceIdParse parse bs1) b0_1 w0_1 w1_1)
    (hrel2 : SidCellsRel (serviceIdParse parse bs2) b0_2 w0_2 w1_2)
    (hb1 : b0_1 ≠ 2#8) (hb2 : b0_2 ≠ 2#8) (hkind : b0_1 = b0_2) :
    w0_1 = w0_2 ∧ w1_1 = w1_2 → False := by
  rintro ⟨hw0, hw1⟩
  cases hs1 : serviceIdParse parse bs1 with
  | none => rw [hs1, SidCellsRel] at hrel1; exact hb1 hrel1
  | some v1 =>
    rcases v1 with ⟨p1, u1⟩
    rw [hs1, SidCellsRel] at hrel1
    rcases hrel1 with ⟨hb0_1, hw0_1, hw1_1⟩
    cases hs2 : serviceIdParse parse bs2 with
    | none => rw [hs2, SidCellsRel] at hrel2; exact hb2 hrel2
    | some v2 =>
      rcases v2 with ⟨p2, u2⟩
      rw [hs2, SidCellsRel] at hrel2
      rcases hrel2 with ⟨hb0_2, hw0_2, hw1_2⟩
      have hp : p1 = p2 := kindByte_inj_bv (hb0_1.symm.trans (hkind.trans hb0_2))
      have hu : u1 = u2 := uuid_eq_of_uuidWords_eq_bv
        (hw0_1.symm.trans (hw0.trans hw0_2))
        (hw1_1.symm.trans (hw1.trans hw1_2))
      subst hp hu
      exact hDist (p1, u1) hs1 hs2

private theorem cond_uuid_words_ne_bv {w0_1 w1_1 w0_2 w1_2 : BitVec 64}
    (hne : w0_1 = w0_2 ∧ w1_1 = w1_2 → False) :
    (if (w0_1 == w0_2) = true then w1_1 != w1_2 else true) = true := by
  by_cases h0 : (w0_1 == w0_2) = true
  · simp only [h0, ↓reduceIte, bne_iff_ne]
    intro h1
    exact hne ⟨of_decide_eq_true h0, h1⟩
  · simp only [h0, Bool.false_eq_true, ↓reduceIte]

private def vecU8BufRest_sa (A : RustAlloc) (cap ptr : BitVec 64) (n : Nat) : SepProp :=
  if cap = 0 then emp
  else A.live ptr cap.toNat 1 ∗ memRegion (ptr + BitVec.ofNat 64 n) (cap.toNat - n)

private theorem vecU8At_buf_eq_sa (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length ≤ cap.toNat) :
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
      (ptr ↦ₛ bs) ∗ vecU8BufRest_sa A cap ptr bs.length := by
  unfold vecU8BufRest_sa
  by_cases hcap : cap = 0
  · subst hcap
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hle)
    subst hbs
    simp [pointsToBytes_nil]
  · simp only [hcap, ite_false]
    ac_rfl

private theorem vecU8At_expose_sa (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ vecU8BufRest_sa A cap ptr bs.length := by
  unfold vecU8At vecHeader
  trans (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      if cap = 0 then emp
      else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)))
  · ac_rfl
  · simp only [pure_sepConj]
    congr 1
    funext h
    apply propext
    refine and_congr_right fun ⟨hle, _, _⟩ => ?_
    rw [vecU8At_buf_eq_sa A cap ptr bs hle]

private def addrRest_sa (A : RustAlloc) (g : AddrGhost) (a : BitVec 64) : SepProp :=
  (a ↦₆₄ g.name.cap) ∗ vecU8BufRest_sa A g.name.cap g.name.ptr g.name.bytes.length ∗
    ((a + 24#64) ↦₈ g.device) ∗ memRegion (a + 0x19#64) 7

private theorem protocolAddressAt_expose_sa (A : RustAlloc) (g : AddrGhost) (a : BitVec 64) :
    protocolAddressAt A g a =
      ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
        ((a + 8#64) ↦₆₄ g.name.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
        (g.name.ptr ↦ₛ g.name.bytes) ∗
        addrRest_sa A g a := by
  unfold protocolAddressAt vecGhostAt addrRest_sa
  rw [vecU8At_expose_sa]
  ac_rfl

end SameAccountTrap

section SameAccountExt32

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Stack budget (`80 + publicKeyEqStackExt = 16528` B) for `<IdentityKey>::is_same_account`
under `DistinctSid` with 32-bit stacked `CliExt.blackBoxSpec` (`extHookStack = 16384`). -/
abbrev isSameAccountDistinctStackExt : Nat := 80 + Getters.publicKeyEqStackExt

/-- Raw byte-level contract for `<IdentityKey>::is_same_account` under `DistinctSid` at `isSameAccountDistinctStackExt`. -/
@[expose] def isSameAccountDistinctRawSpecExt (parse : UuidParser) :
    Spec (BitVec 64 × IdentityKey × BitVec 64 × BitVec 64 × List (BitVec 8) ×
      BitVec 64 × IdentityKey × BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (lIkA, lIk, lAd, lPtr, lBs, rIkA, rIk, rAd, rPtr, rBs) s =>
    ⌜s.readReg64 .x0 = lIkA ∧ s.readReg64 .x1 = lAd ∧ s.readReg64 .x2 = rIkA ∧
      s.readReg64 .x3 = rAd ∧ lBs.length < 2 ^ 64 ∧ rBs.length < 2 ^ 64 ∧
      (lIk ≠ rIk ∨ DistinctSid parse lBs rBs)⌝ ∗
      (lIkA ↦ₛ lIk.publicKey.bytes.toList) ∗ ((lAd + 8#64) ↦₆₄ lPtr) ∗
      ((lAd + 16#64) ↦₆₄ BitVec.ofNat 64 lBs.length) ∗ (lPtr ↦ₛ lBs) ∗
      (rIkA ↦ₛ rIk.publicKey.bytes.toList) ∗ ((rAd + 8#64) ↦₆₄ rPtr) ∗
      ((rAd + 16#64) ↦₆₄ BitVec.ofNat 64 rBs.length) ∗ (rPtr ↦ₛ rBs) ∗
      stackAt s.sp isSameAccountDistinctStackExt
  post := fun (lIkA, lIk, lAd, lPtr, lBs, rIkA, rIk, rAd, rPtr, rBs) s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ sf.trace = s0.trace⌝ ∗
      (lIkA ↦ₛ lIk.publicKey.bytes.toList) ∗ ((lAd + 8#64) ↦₆₄ lPtr) ∗
      ((lAd + 16#64) ↦₆₄ BitVec.ofNat 64 lBs.length) ∗ (lPtr ↦ₛ lBs) ∗
      (rIkA ↦ₛ rIk.publicKey.bytes.toList) ∗ ((rAd + 8#64) ↦₆₄ rPtr) ∗
      ((rAd + 16#64) ↦₆₄ BitVec.ofNat 64 rBs.length) ∗ (rPtr ↦ₛ rBs) ∗
      stackAt s0.sp isSameAccountDistinctStackExt

/-- `protocolAddressAt`-level contract for `<IdentityKey>::is_same_account` under `DistinctSid` at `isSameAccountDistinctStackExt`. -/
@[expose] def isSameAccountDistinctSpecExt (A : RustAlloc) (parse : UuidParser) :
    Spec (BitVec 64 × IdentityKey × BitVec 64 × AddrGhost ×
      BitVec 64 × IdentityKey × BitVec 64 × AddrGhost) where
  pre := fun (lIkA, lIk, locA, loc, rIkA, rIk, remA, rem) s =>
    ⌜s.readReg64 .x0 = lIkA ∧ s.readReg64 .x1 = locA ∧ s.readReg64 .x2 = rIkA ∧
      s.readReg64 .x3 = remA ∧ (lIk ≠ rIk ∨ DistinctSid parse loc.name.bytes rem.name.bytes)⌝ ∗
      (lIkA ↦ₛ lIk.publicKey.bytes.toList) ∗ protocolAddressAt A loc locA ∗
      (rIkA ↦ₛ rIk.publicKey.bytes.toList) ∗ protocolAddressAt A rem remA ∗
      stackAt s.sp isSameAccountDistinctStackExt
  post := fun (lIkA, lIk, locA, loc, rIkA, rIk, remA, rem) s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ sf.trace = s0.trace⌝ ∗
      (lIkA ↦ₛ lIk.publicKey.bytes.toList) ∗ protocolAddressAt A loc locA ∗
      (rIkA ↦ₛ rIk.publicKey.bytes.toList) ∗ protocolAddressAt A rem remA ∗
      stackAt s0.sp isSameAccountDistinctStackExt

private theorem stackAt_isSameAccountDistinctExt_split (sp : BitVec 64) :
    stackAt sp isSameAccountDistinctStackExt =
      stackAt (sp - 80#64) Getters.publicKeyEqStackExt ∗ memRegion (sp - 80#64) 12 ∗
      (∃∗ b0 : BitVec 8, ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        ((sp - 68#64) ↦₈ b0) ∗ ((sp - 67#64) ↦₆₄ w0) ∗ ((sp - 59#64) ↦₆₄ w1)) ∗
      memRegion (sp - 51#64) 3 ∗ ProofLib.cells (sp - 48#64) 6 := by
  simp only [stackAt, isSameAccountDistinctStackExt, Getters.publicKeyEqStackExt, extHookStack]
  rw [show (80 + (64 + 2 ^ 14) : Nat) = 16528 by decide,
      show (64 + 2 ^ 14 : Nat) = 16448 by decide,
      show BitVec.ofNat 64 16528 = 16528#64 from rfl, show BitVec.ofNat 64 16448 = 16448#64 from rfl,
      show sp - 80#64 - 16448#64 = sp - 16528#64 by bv_omega,
      show (16528 : Nat) = 16448 + (12 + (17 + (3 + 8 * 6))) by decide,
      memRegion_split (sp - 16528#64) 16448 (12 + (17 + (3 + 8 * 6))) (by decide),
      memRegion_split (sp - 16528#64 + 16448#64) 12 (17 + (3 + 8 * 6)) (by decide),
      memRegion_split (sp - 16528#64 + 16448#64 + 12#64) 17 (3 + 8 * 6) (by decide),
      memRegion_split (sp - 16528#64 + 16448#64 + 12#64 + 17#64) 3 (8 * 6) (by decide),
      ProofLib.memRegion_cells _ 6 (by decide), memRegion_17_eq_cells_sa]
  have h1 : sp - 16528#64 + 16448#64 = sp - 80#64 := by bv_omega
  have h2 : sp - 80#64 + 12#64 = sp - 68#64 := by bv_omega
  have h3 : sp - 68#64 + 1#64 = sp - 67#64 := by bv_omega
  have h4 : sp - 68#64 + 9#64 = sp - 59#64 := by bv_omega
  have h5 : sp - 68#64 + 17#64 = sp - 51#64 := by bv_omega
  have h6 : sp - 51#64 + 3#64 = sp - 48#64 := by bv_omega
  rw [h1, h2, h3, h4, h5, h6]

private theorem stackAt_publicKeyEqStackExt_eq_parseSid (sp80 : BitVec 64) :
    stackAt sp80 Getters.publicKeyEqStackExt =
      memRegion (sp80 - 16448#64) 16176 ∗ stackAt sp80 parseSidStack := by
  simp only [stackAt, Getters.publicKeyEqStackExt, extHookStack, parseSidStack, uuidTryParseStack]
  rw [show (64 + 2 ^ 14 : Nat) = 16448 by decide, show (80 + 192 : Nat) = 272 by decide,
      show BitVec.ofNat 64 16448 = 16448#64 from rfl, show BitVec.ofNat 64 272 = 272#64 from rfl]
  exact ProofLib.memRegion_split' (b := sp80 - 16448#64) (b' := sp80 - 272#64)
    (N := 16448) (n := 16176) (k := 272) (by decide) (by bv_omega) (by decide)

end SameAccountExt32

end CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.LibsignalTripleRatchet.DecryptPq
open CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

end CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
