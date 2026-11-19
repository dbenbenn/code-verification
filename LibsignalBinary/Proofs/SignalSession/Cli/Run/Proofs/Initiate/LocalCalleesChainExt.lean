/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ContractsExt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccount -- proof-setup: allow-public-import
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Stage2ContractsExt
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.CtEqRO
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Extract
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Defs
import LibsignalBinary.Proofs.TripleRatchet.TrapRng
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244

/-!
# Extern-Parameterized Account and Chain Callee Contracts for `initiate`

Shared specifications and stack-layout lemmas for `<IdentityKey>::is_same_account`,
`<PrivateKey>::calculate_agreement`, and `<RootKey>::create_chain`.
-/

public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HKDF CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.E2E
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli

abbrev isSameAccountSym : String :=
  "<libsignal_protocol::identity_key::IdentityKey>::is_same_account"

/-- Stack-parameterized `<IdentityKey>::is_same_account` distinct-account specification. -/
@[expose] def isSameAccountDistinctAtSpec (A : RustAlloc) (parse : UuidParser) (isaStk : Nat) :
    Spec Pqxdh.WireEntries.IsSameAccountDistinctGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.localIkA ∧
      s.readReg64 .x1 = g.locA ∧
      s.readReg64 .x2 = g.remoteIkA ∧
      s.readReg64 .x3 = g.remA ∧
      (g.localIk ≠ g.remoteIk ∨
        Pqxdh.WireEntries.DistinctSid parse g.loc.name.bytes g.rem.name.bytes)⌝ ∗
    (g.localIkA ↦ₛ g.localIk.publicKey.bytes.toList) ∗
    protocolAddressAt A g.loc g.locA ∗
    (g.remoteIkA ↦ₛ g.remoteIk.publicKey.bytes.toList) ∗
    protocolAddressAt A g.rem g.remA ∗
    stackAt s.sp isaStk
  post := fun g s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ sf.trace = s0.trace⌝ ∗
    (g.localIkA ↦ₛ g.localIk.publicKey.bytes.toList) ∗
    protocolAddressAt A g.loc g.locA ∗
    (g.remoteIkA ↦ₛ g.remoteIk.publicKey.bytes.toList) ∗
    protocolAddressAt A g.rem g.remA ∗
    stackAt s0.sp isaStk

/-! ## `<IdentityKey>::is_same_account` -/

section IsSameAccountExt

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Stack budget for `<IdentityKey>::is_same_account` under `CliExternsOk` (`80 + publicKeyEqStackExt = 16528` bytes). -/
abbrev isSameAccountExtStack : Nat := 80 + Getters.publicKeyEqStackExt

private theorem stackAt_16368_split_uuid (sp : BitVec 64) :
    stackAt sp 16368 = memRegion (sp - 16368#64) 16176 ∗ stackAt sp uuidTryParseStack := by
  simp only [stackAt, uuidTryParseStack]
  rw [show BitVec.ofNat 64 16368 = 16368#64 from rfl,
      show BitVec.ofNat 64 0xC0 = 192#64 from rfl]
  exact ProofLib.memRegion_split' (b := sp - 16368#64) (n := 16176) (k := 192)
    (b' := sp - 192#64) (by decide) (by bv_omega) (by decide)

private theorem stackAt_publicKeyEqStackExt_eq_parseSid16368 (sp : BitVec 64) :
    stackAt sp Getters.publicKeyEqStackExt =
      stackAt (sp - 80#64) 16368 ∗ stackAt sp parseSidFrameStack := by
  simp only [stackAt, Getters.publicKeyEqStackExt, extHookStack, parseSidFrameStack]
  have hsub : sp - 80#64 - BitVec.ofNat 64 16368 = sp - 16448#64 := by bv_omega
  rw [hsub, show (64 + 2 ^ 14 : Nat) = 16448 from rfl,
      show BitVec.ofNat 64 16448 = 16448#64 from rfl,
      show BitVec.ofNat 64 0x50 = 80#64 from rfl]
  exact ProofLib.memRegion_split' (b := sp - 16448#64) (n := 16368) (k := 80)
    (b' := sp - 80#64) (by decide) (by bv_omega) (by decide)

private theorem memRegion_17_eq_cells_ext (a : BitVec 64) :
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
  refine congrArg sepExists (funext fun _ => ?_)
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine congrArg sepExists (funext fun _ => ?_)
  rw [sepExists_sepConj_right, sepExists_sepConj_right]

private theorem pointsTo_17_entails_memRegion_ext (a : BitVec 64) (b0 : BitVec 8) (w0 w1 : BitVec 64) :
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦₆₄ w0) ∗ ((a + 9#64) ↦₆₄ w1)) ⊢ memRegion a 17 := by
  rw [memRegion_17_eq_cells_ext a]
  exact Entails.sepExists_right b0 (Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.refl _)))

private theorem memRegion_16_out_split_ext (a : BitVec 64) :
    memRegion (a + 1#64) 16 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ((a + 1#64) ↦₆₄ w0) ∗ ((a + 9#64) ↦₆₄ w1) := by
  rw [show (16 : Nat) = 8 + 8 by decide, memRegion_split (a + 1#64) 8 8 (by decide)]
  have h9 : a + 1#64 + BitVec.ofNat 64 8 = a + 9#64 := by bv_arith
  rw [h9, ProofLib.memRegion_eight (a + 1#64), ProofLib.memRegion_eight (a + 9#64),
      sepExists_sepConj_left]
  refine congrArg sepExists (funext fun _ => ?_)
  rw [sepExists_sepConj_right]

private theorem parseSidResultAt_entails_rel_cells_ext (out : BitVec 64)
    (res : Option (Bool × List.Vector (BitVec 8) 16)) :
    parseSidResultAt out res ⊢
      ∃∗ b0 : BitVec 8, ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        ⌜Pqxdh.WireEntries.SidCellsRel res b0 w0 w1⌝ ∗
        (out ↦₈ b0) ∗ ((out + 1#64) ↦₆₄ w0) ∗ ((out + 9#64) ↦₆₄ w1) := by
  cases res with
  | none =>
    simp only [parseSidResultAt, Pqxdh.WireEntries.SidCellsRel, memRegion_16_out_split_ext,
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

private def parseSidRelExtSpec (parse : UuidParser) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × BitVec 8 × BitVec 64 × BitVec 64) where
  pre := fun (p, bs, out, b0, w0, w1) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ s.readReg64 .x8 = out⌝ ∗
      (p ↦ₛ bs) ∗ (out ↦₈ b0) ∗ ((out + 1#64) ↦₆₄ w0) ∗ ((out + 9#64) ↦₆₄ w1) ∗
      stackAt s.sp Getters.publicKeyEqStackExt
  post := fun (p, bs, out, _, _, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (p ↦ₛ bs) ∗
      (∃∗ b0' : BitVec 8, ∃∗ w0' : BitVec 64, ∃∗ w1' : BitVec 64,
        ⌜Pqxdh.WireEntries.SidCellsRel (serviceIdParse parse bs) b0' w0' w1'⌝ ∗
        (out ↦₈ b0') ∗ ((out + 1#64) ↦₆₄ w0') ∗ ((out + 9#64) ↦₆₄ w1')) ∗
      stackAt s0.sp Getters.publicKeyEqStackExt

private theorem stackAt_isSameAccountExt_split (sp : BitVec 64) :
    stackAt sp isSameAccountExtStack =
      stackAt (sp - 80#64) Getters.publicKeyEqStackExt ∗
      memRegion (sp - 80#64) 12 ∗
      (∃∗ b0 : BitVec 8, ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        ((sp - 68#64) ↦₈ b0) ∗ ((sp - 67#64) ↦₆₄ w0) ∗ ((sp - 59#64) ↦₆₄ w1)) ∗
      memRegion (sp - 51#64) 3 ∗
      ProofLib.cells (sp - 48#64) 6 := by
  simp only [stackAt, isSameAccountExtStack, Getters.publicKeyEqStackExt, extHookStack]
  rw [show (80 + (64 + 2 ^ 14) : Nat) = 16528 from rfl,
      show (64 + 2 ^ 14 : Nat) = 16448 from rfl,
      show BitVec.ofNat 64 16528 = 16528#64 from rfl,
      show BitVec.ofNat 64 16448 = 16448#64 from rfl,
      show sp - 80#64 - 16448#64 = sp - 16528#64 by bv_arith,
      show (16528 : Nat) = 16448 + (12 + (17 + (3 + 8 * 6))) by decide,
      memRegion_split (sp - 16528#64) 16448 (12 + (17 + (3 + 8 * 6))) (by decide),
      memRegion_split (sp - 16528#64 + 16448#64) 12 (17 + (3 + 8 * 6)) (by decide),
      memRegion_split (sp - 16528#64 + 16448#64 + 12#64) 17 (3 + 8 * 6) (by decide),
      memRegion_split (sp - 16528#64 + 16448#64 + 12#64 + 17#64) 3 (8 * 6) (by decide),
      ProofLib.memRegion_cells _ 6 (by decide),
      memRegion_17_eq_cells_ext]
  have h1 : sp - 16528#64 + 16448#64 = sp - 80#64 := by bv_arith
  have h2 : sp - 80#64 + 12#64 = sp - 68#64 := by bv_arith
  have h3 : sp - 68#64 + 1#64 = sp - 67#64 := by bv_arith
  have h4 : sp - 68#64 + 9#64 = sp - 59#64 := by bv_arith
  have h5 : sp - 68#64 + 17#64 = sp - 51#64 := by bv_arith
  have h6 : sp - 51#64 + 3#64 = sp - 48#64 := by bv_arith
  rw [h1, h2, h3, h4, h5, h6]

private theorem pack64_inj_ext (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (h : pack64 a0 a1 a2 a3 a4 a5 a6 a7 = pack64 b0 b1 b2 b3 b4 b5 b6 b7) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4 ∧ a5 = b5 ∧ a6 = b6 ∧ a7 = b7 := by
  exact ⟨
    calc a0 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 0 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 0 8 := congrArg _ h
      _ = b0 := by unfold pack64; bv_bits,
    calc a1 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 8 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 8 8 := congrArg _ h
      _ = b1 := by unfold pack64; bv_bits,
    calc a2 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 16 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 16 8 := congrArg _ h
      _ = b2 := by unfold pack64; bv_bits,
    calc a3 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 24 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 24 8 := congrArg _ h
      _ = b3 := by unfold pack64; bv_bits,
    calc a4 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 32 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 32 8 := congrArg _ h
      _ = b4 := by unfold pack64; bv_bits,
    calc a5 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 40 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 40 8 := congrArg _ h
      _ = b5 := by unfold pack64; bv_bits,
    calc a6 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 48 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 48 8 := congrArg _ h
      _ = b6 := by unfold pack64; bv_bits,
    calc a7 = (pack64 a0 a1 a2 a3 a4 a5 a6 a7).extractLsb' 56 8 := by unfold pack64; bv_bits
      _ = (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 56 8 := congrArg _ h
      _ = b7 := by unfold pack64; bv_bits⟩

private theorem uuid_eq_of_uuidWords_eq_ext {u1 u2 : List.Vector (BitVec 8) 16}
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
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := pack64_inj_ext _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw0
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := pack64_inj_ext _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw1
  rfl

private theorem kindByte_inj_ext {p1 p2 : Bool} (h : kindByte p1 = kindByte p2) : p1 = p2 := by
  cases p1 <;> cases p2 <;> revert h <;> decide

private theorem sidCellsRel_ne_of_distinct_ext {parse : UuidParser} {bs1 bs2 : List (BitVec 8)}
    {b0_1 b0_2 : BitVec 8} {w0_1 w1_1 w0_2 w1_2 : BitVec 64}
    (hDist : Pqxdh.WireEntries.DistinctSid parse bs1 bs2)
    (hrel1 : Pqxdh.WireEntries.SidCellsRel (serviceIdParse parse bs1) b0_1 w0_1 w1_1)
    (hrel2 : Pqxdh.WireEntries.SidCellsRel (serviceIdParse parse bs2) b0_2 w0_2 w1_2)
    (hb1 : b0_1 ≠ 2#8) (hb2 : b0_2 ≠ 2#8) (hkind : b0_1 = b0_2) :
    w0_1 = w0_2 ∧ w1_1 = w1_2 → False := by
  rintro ⟨hw0, hw1⟩
  cases hs1 : serviceIdParse parse bs1 with
  | none => rw [hs1, Pqxdh.WireEntries.SidCellsRel] at hrel1; exact hb1 hrel1
  | some v1 =>
    rcases v1 with ⟨p1, u1⟩
    rw [hs1, Pqxdh.WireEntries.SidCellsRel] at hrel1
    rcases hrel1 with ⟨hb0_1, hw0_1, hw1_1⟩
    cases hs2 : serviceIdParse parse bs2 with
    | none => rw [hs2, Pqxdh.WireEntries.SidCellsRel] at hrel2; exact hb2 hrel2
    | some v2 =>
      rcases v2 with ⟨p2, u2⟩
      rw [hs2, Pqxdh.WireEntries.SidCellsRel] at hrel2
      rcases hrel2 with ⟨hb0_2, hw0_2, hw1_2⟩
      have hp : p1 = p2 := kindByte_inj_ext (hb0_1.symm.trans (hkind.trans hb0_2))
      have hu : u1 = u2 := uuid_eq_of_uuidWords_eq_ext
        (hw0_1.symm.trans (hw0.trans hw0_2))
        (hw1_1.symm.trans (hw1.trans hw1_2))
      subst hp hu
      exact hDist (p1, u1) hs1 hs2

private theorem cond_uuid_words_ne_ext {w0_1 w1_1 w0_2 w1_2 : BitVec 64}
    (hne : w0_1 = w0_2 ∧ w1_1 = w1_2 → False) :
    (if (w0_1 == w0_2) = true then w1_1 != w1_2 else true) = true := by
  by_cases h0 : (w0_1 == w0_2) = true
  · simp only [h0, ↓reduceIte, bne_iff_ne]
    intro h1
    exact hne ⟨of_decide_eq_true h0, h1⟩
  · simp only [h0, Bool.false_eq_true, ↓reduceIte]

private theorem sidCellsRel_b0_cases_ext {o : Option (Bool × List.Vector (BitVec 8) 16)}
    {b0 : BitVec 8} {w0 w1 : BitVec 64} (h : Pqxdh.WireEntries.SidCellsRel o b0 w0 w1) :
    b0 = 0#8 ∨ b0 = 1#8 ∨ b0 = 2#8 := by
  cases o with
  | none => right; right; exact h
  | some v => rcases v with ⟨p, _⟩; rcases h with ⟨rfl, _, _⟩; cases p <;> simp [kindByte]

private def isSameAccountDistinctRawExtSpec (parse : UuidParser) :
    Spec Pqxdh.WireEntries.IsSameAccountDistinctRawGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.localIkA ∧
      s.readReg64 .x1 = g.localAddr ∧
      s.readReg64 .x2 = g.remoteIkA ∧
      s.readReg64 .x3 = g.remoteAddr ∧
      g.localNameBytes.length < 2 ^ 64 ∧
      g.remoteNameBytes.length < 2 ^ 64 ∧
      (g.localIk ≠ g.remoteIk ∨ Pqxdh.WireEntries.DistinctSid parse g.localNameBytes g.remoteNameBytes)⌝ ∗
    (g.localIkA ↦ₛ g.localIk.publicKey.bytes.toList) ∗
    ((g.localAddr + 8#64) ↦₆₄ g.localNamePtr) ∗
    ((g.localAddr + 16#64) ↦₆₄ BitVec.ofNat 64 g.localNameBytes.length) ∗
    (g.localNamePtr ↦ₛ g.localNameBytes) ∗
    (g.remoteIkA ↦ₛ g.remoteIk.publicKey.bytes.toList) ∗
    ((g.remoteAddr + 8#64) ↦₆₄ g.remoteNamePtr) ∗
    ((g.remoteAddr + 16#64) ↦₆₄ BitVec.ofNat 64 g.remoteNameBytes.length) ∗
    (g.remoteNamePtr ↦ₛ g.remoteNameBytes) ∗
    stackAt s.sp isSameAccountExtStack
  post := fun g s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ sf.trace = s0.trace⌝ ∗
    (g.localIkA ↦ₛ g.localIk.publicKey.bytes.toList) ∗
    ((g.localAddr + 8#64) ↦₆₄ g.localNamePtr) ∗
    ((g.localAddr + 16#64) ↦₆₄ BitVec.ofNat 64 g.localNameBytes.length) ∗
    (g.localNamePtr ↦ₛ g.localNameBytes) ∗
    (g.remoteIkA ↦ₛ g.remoteIk.publicKey.bytes.toList) ∗
    ((g.remoteAddr + 8#64) ↦₆₄ g.remoteNamePtr) ∗
    ((g.remoteAddr + 16#64) ↦₆₄ BitVec.ofNat 64 g.remoteNameBytes.length) ∗
    (g.remoteNamePtr ↦ₛ g.remoteNameBytes) ∗
    stackAt s0.sp isSameAccountExtStack

private def vecU8BufRest_ext (A : RustAlloc) (cap ptr : BitVec 64) (n : Nat) : SepProp :=
  if cap = 0 then emp
  else A.live ptr cap.toNat 1 ∗ memRegion (ptr + BitVec.ofNat 64 n) (cap.toNat - n)

private theorem vecU8At_buf_eq_ext (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length ≤ cap.toNat) :
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
      (ptr ↦ₛ bs) ∗ vecU8BufRest_ext A cap ptr bs.length := by
  unfold vecU8BufRest_ext
  by_cases hcap : cap = 0
  · subst hcap
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hle)
    subst hbs
    simp [pointsToBytes_nil]
  · simp only [hcap, ite_false]
    ac_rfl

private theorem vecU8At_expose_ext (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ vecU8BufRest_ext A cap ptr bs.length := by
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
    rw [vecU8At_buf_eq_ext A cap ptr bs hle]

private def addrRest_ext (A : RustAlloc) (g : AddrGhost) (a : BitVec 64) : SepProp :=
  (a ↦₆₄ g.name.cap) ∗ vecU8BufRest_ext A g.name.cap g.name.ptr g.name.bytes.length ∗
    ((a + 24#64) ↦₈ g.device) ∗ memRegion (a + 0x19#64) 7

private theorem protocolAddressAt_expose_ext (A : RustAlloc) (g : AddrGhost) (a : BitVec 64) :
    protocolAddressAt A g a =
      ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
        ((a + 8#64) ↦₆₄ g.name.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
        (g.name.ptr ↦ₛ g.name.bytes) ∗
        addrRest_ext A g a := by
  unfold protocolAddressAt vecGhostAt addrRest_ext
  rw [vecU8At_expose_ext]
  ac_rfl

end IsSameAccountExt

/-! ## `<PrivateKey>::calculate_agreement` and `<RootKey>::create_chain` -/

section CreateChainExt

private theorem stackAt_calcSub_split_ext (sp : BitVec 64) :
    stackAt sp (48 + extHookStack) =
      memRegion (sp - 16432#64) 48 ∗ stackAt sp extHookStack := by
  change memRegion (sp - 16432#64) 16432 =
    memRegion (sp - 16432#64) 48 ∗ memRegion (sp - 16384#64) 16384
  exact ProofLib.memRegion_split' (b := sp - 16432#64) (n := 48) (k := 16384)
    (b' := sp - 16384#64) (by decide) (by bv_omega) (by decide)

section CtEqWrap

end CtEqWrap

private theorem stackAt_extract_split_calc (sp : BitVec 64) :
    stackAt sp extractStackExt =
      memRegion (sp - 17360#64) 768 ∗ stackAt sp (160 + (48 + extHookStack)) := by
  change memRegion (sp - 17360#64) 17360 =
    memRegion (sp - 17360#64) 768 ∗ memRegion (sp - 16592#64) 16592
  exact ProofLib.memRegion_split' (b := sp - 17360#64) (n := 768) (k := 16592)
    (b' := sp - 16592#64) (by decide) (by bv_omega) (by decide)

private theorem stackAt_extract_split_expand (sp : BitVec 64) :
    stackAt sp extractStackExt =
      memRegion (sp - 17360#64) 336 ∗ stackAt sp expandMultiInfoStackExt := by
  change memRegion (sp - 17360#64) 17360 =
    memRegion (sp - 17360#64) 336 ∗ memRegion (sp - 17024#64) 17024
  exact ProofLib.memRegion_split' (b := sp - 17360#64) (n := 336) (k := 17024)
    (b' := sp - 17024#64) (by decide) (by bv_omega) (by decide)

private theorem stackAt_extract_split_dealloc (sp : BitVec 64) :
    stackAt sp extractStackExt =
      memRegion (sp - 17360#64) 976 ∗ stackAt sp extHookStack := by
  change memRegion (sp - 17360#64) 17360 =
    memRegion (sp - 17360#64) 976 ∗ memRegion (sp - 16384#64) 16384
  exact ProofLib.memRegion_split' (b := sp - 17360#64) (n := 976) (k := 16384)
    (b' := sp - 16384#64) (by decide) (by bv_omega) (by decide)

end CreateChainExt

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate
