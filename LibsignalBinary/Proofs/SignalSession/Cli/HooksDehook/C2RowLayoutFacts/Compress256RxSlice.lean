/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress256 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Compress256GhostReplays
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Code
import LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.TieSpec
import ProofLib.BV.ReflectROBDD
import ProofLib.GenPlacedFetches
import ProofLib.Placed.Fetch
import ProofLib.ProgramReflection

/-!
# Isolated `WordTree` Byte-Subslice Witness for `sha2::sha256::compress256` (`C2RowLayoutFacts.Compress256RxSlice`)

**Checked by Lean. Untrusted (`Role::Proof`, `CliElfLib`).**

Proves `c2_rxSlice_compress256_ok` by comparing `f3TrialRxWordTree` directly against
`compress256Tree` (`1,907` unrelocated words) and the two relocated words at byte offsets
`0xd0` (`4 * 52`) and `0xd4` (`4 * 53`), so the Lean kernel never unfolds `compress256CodeBytes`
(`7,636` bytes) or `f3TrialElf` / `cliElfBytes`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress256RxSlice

open Arm64 ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Heap.Fine (f3RxWordCount)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Code
  (compress256Block compress256Lib compress256Tree compress256_code_eq compress256_tree_size
   sha2K32Sym)
open LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.TieSpec (f3ByteBeq f3ByteBeq_true_iff)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
  (checkProgCodeSubslice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress256
  (c2Compress256Pl)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Compress256GhostReplays
  (compress256Placement compress256SubProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
  (f3RxSegBase f3TrialRxProg f3TrialRxProg_base f3TrialRxWordTree f3TrialRxWordTree_eq
   f3TrialRxWordTree_size)

private def r52 : Obj.RelocEntry :=
  { off := 0xd0, kind := .adrpHi21, sym := sha2K32Sym, addend := 0 }

private def r53 : Obj.RelocEntry :=
  { off := 0xd4, kind := .addLo12, sym := sha2K32Sym, addend := 0 }

private theorem rxProg_code_len_eq :
    f3TrialRxProg.code.length = 4 * f3RxWordCount := by
  rw [f3TrialRxWordTree_eq, WordTree.length_toBytes_of_checkSize? f3TrialRxWordTree_size]

private theorem compress256Block_code_len :
    compress256Block.code.length = 7636 := by
  have h : compress256Lib.text.code.length = 4 * 1909 := by
    rw [compress256_code_eq, WordTree.length_toBytes_of_checkSize? compress256_tree_size]
  exact h

set_option maxRecDepth 400000 in
private theorem compress256SubProg_code (pl : Obj.Placement) :
    (compress256SubProg pl).code = compress256Block.patched pl := rfl

private theorem compress256SubProg_code_len :
    (compress256SubProg c2Compress256Pl).code.length = 7636 := by
  rw [compress256SubProg_code, Obj.CodeBlock.length_patched_of_aligned c2Compress256Pl
    (by rw [compress256Block_code_len])]
  exact compress256Block_code_len

private theorem bytesOfWordLE_wordOfBytesLE4 (b0 b1 b2 b3 : BitVec 8) :
    Obj.bytesOfWordLE (Obj.wordOfBytesLE [b0, b1, b2, b3] 0) = [b0, b1, b2, b3] := by
  rw [Obj.wordOfBytesLE_cons4_zero b0 b1 b2 b3 []]
  simp only [Obj.bytesOfWordLE, Obj.bytesLE, List.range_succ, List.range_zero, List.map_append,
    List.map_cons, List.map_nil, List.nil_append]
  exact congrArg₂ List.cons (by bv_bits) (congrArg₂ List.cons (by bv_bits)
    (congrArg₂ List.cons (by bv_bits) (congrArg₂ List.cons (by bv_bits) rfl)))

private def checkQuadEqBytes4 (q? : Option (BitVec 8 × BitVec 8 × BitVec 8 × BitVec 8))
    (bs : List (BitVec 8)) : Bool :=
  match q?, bs with
  | some (a0, a1, a2, a3), [b0, b1, b2, b3] =>
    f3ByteBeq a0 b0 && f3ByteBeq a1 b1 && f3ByteBeq a2 b2 && f3ByteBeq a3 b3
  | _, _ => false

private def checkQuadsEq (q1? q2? : Option (BitVec 8 × BitVec 8 × BitVec 8 × BitVec 8)) : Bool :=
  match q1?, q2? with
  | some (a0, a1, a2, a3), some (b0, b1, b2, b3) =>
    f3ByteBeq a0 b0 && f3ByteBeq a1 b1 && f3ByteBeq a2 b2 && f3ByteBeq a3 b3
  | _, _ => false

private theorem take4_rx_of_getQuad? {q : Nat} {a0 a1 a2 a3 : BitVec 8}
    (hg : f3TrialRxWordTree.getQuad? q = some (a0, a1, a2, a3)) :
    (f3TrialRxWordTree.toBytes.drop (4 * q)).take 4 = [a0, a1, a2, a3] := by
  obtain ⟨rest, hdrop⟩ := WordTree.toBytes_drop_of_getQuad? f3TrialRxWordTree_size hg
  rw [hdrop]; rfl

private theorem take4_rx_of_checkQuadEqBytes4 {q : Nat} {bs : List (BitVec 8)}
    (hok : checkQuadEqBytes4 (f3TrialRxWordTree.getQuad? q) bs = true) :
    (f3TrialRxWordTree.toBytes.drop (4 * q)).take 4 = bs := by
  unfold checkQuadEqBytes4 at hok
  cases hg : f3TrialRxWordTree.getQuad? q with
  | none => rw [hg] at hok; simp at hok
  | some quad =>
    rcases quad with ⟨a0, a1, a2, a3⟩
    rw [hg] at hok
    match bs with
    | [b0, b1, b2, b3] =>
      simp only [Bool.and_eq_true, f3ByteBeq_true_iff] at hok
      rcases hok with ⟨⟨⟨e0, e1⟩, e2⟩, e3⟩
      subst e0; subst e1; subst e2; subst e3
      exact take4_rx_of_getQuad? hg
    | [] | [_] | [_, _] | [_, _, _] | _ :: _ :: _ :: _ :: _ :: _ =>
      simp at hok

private def checkCompress256WordsFrom (rxStart : Nat) : Nat → Nat → Bool
  | _, 0 => true
  | j, rem + 1 =>
    let okJ :=
      if j == 52 then
        match compress256Tree.getQuad? 52 with
        | some (b0, b1, b2, b3) =>
          let w := Obj.patchRelocWord .adrpHi21 (Obj.wordOfBytesLE [b0, b1, b2, b3] 0)
            (c2Compress256Pl.base + BitVec.ofNat 64 (4 * 52))
            (compress256Block.target c2Compress256Pl r52)
          checkQuadEqBytes4 (f3TrialRxWordTree.getQuad? (rxStart + 52)) (Obj.bytesOfWordLE w)
        | none => false
      else if j == 53 then
        match compress256Tree.getQuad? 53 with
        | some (b0, b1, b2, b3) =>
          let w := Obj.patchRelocWord .addLo12 (Obj.wordOfBytesLE [b0, b1, b2, b3] 0)
            (c2Compress256Pl.base + BitVec.ofNat 64 (4 * 53))
            (compress256Block.target c2Compress256Pl r53)
          checkQuadEqBytes4 (f3TrialRxWordTree.getQuad? (rxStart + 53)) (Obj.bytesOfWordLE w)
        | none => false
      else
        checkQuadsEq (f3TrialRxWordTree.getQuad? (rxStart + j)) (compress256Tree.getQuad? j)
    okJ && checkCompress256WordsFrom rxStart (j + 1) rem

private theorem compress256_relaxedAt_false (off : Nat) :
    compress256Block.relaxedAt c2Compress256Pl off = false :=
  Obj.CodeBlock.relaxedAt_of_relax_false (off := off) rfl

private theorem compress256_relocAt?_52 :
    compress256Block.relocAt? (4 * 52) = some r52 := rfl

private theorem compress256_relocAt?_53 :
    compress256Block.relocAt? (4 * 53) = some r53 := rfl

private theorem compress256_relocAt?_other {j : Nat} (h52 : j ≠ 52) (h53 : j ≠ 53) :
    compress256Block.relocAt? (4 * j) = none := by
  have ne0 : (0xd0 == 4 * j) = false := beq_eq_false_iff_ne.mpr (by omega)
  have ne1 : (0xd4 == 4 * j) = false := beq_eq_false_iff_ne.mpr (by omega)
  simp only [Obj.CodeBlock.relocAt?, compress256Block, List.find?_cons, List.find?_nil, ne0, ne1]

private theorem compress256_quad_eq_one {rxStart j : Nat} (hj : j < 1909)
    (hok :
      (if j == 52 then
        match compress256Tree.getQuad? 52 with
        | some (b0, b1, b2, b3) =>
          let w := Obj.patchRelocWord .adrpHi21 (Obj.wordOfBytesLE [b0, b1, b2, b3] 0)
            (c2Compress256Pl.base + BitVec.ofNat 64 (4 * 52))
            (compress256Block.target c2Compress256Pl r52)
          checkQuadEqBytes4 (f3TrialRxWordTree.getQuad? (rxStart + 52)) (Obj.bytesOfWordLE w)
        | none => false
      else if j == 53 then
        match compress256Tree.getQuad? 53 with
        | some (b0, b1, b2, b3) =>
          let w := Obj.patchRelocWord .addLo12 (Obj.wordOfBytesLE [b0, b1, b2, b3] 0)
            (c2Compress256Pl.base + BitVec.ofNat 64 (4 * 53))
            (compress256Block.target c2Compress256Pl r53)
          checkQuadEqBytes4 (f3TrialRxWordTree.getQuad? (rxStart + 53)) (Obj.bytesOfWordLE w)
        | none => false
      else
        checkQuadsEq (f3TrialRxWordTree.getQuad? (rxStart + j)) (compress256Tree.getQuad? j)) =
      true) :
    (f3TrialRxWordTree.toBytes.drop (4 * (rxStart + j))).take 4 =
      ((compress256Block.patched c2Compress256Pl).drop (4 * j)).take 4 := by
  have hlen : 4 * j + 4 ≤ compress256Block.code.length := by
    rw [compress256Block_code_len]; omega
  rw [Obj.CodeBlock.take4_drop_patched (by omega) hlen]
  by_cases h52 : j = 52
  · subst h52
    simp only [beq_self_eq_true, ↓reduceIte] at hok
    cases hg : compress256Tree.getQuad? 52 with
    | none => rw [hg] at hok; simp at hok
    | some quad =>
      rcases quad with ⟨b0, b1, b2, b3⟩
      rw [hg] at hok
      have hw : compress256Block.wordAt (4 * 52) = Obj.wordOfBytesLE [b0, b1, b2, b3] 0 :=
        GenPlacedFetches.wordAt_of_getQuad? compress256_code_eq compress256_tree_size hg
      have hpw : compress256Block.patchedWord c2Compress256Pl (4 * 52) =
          Obj.patchRelocWord .adrpHi21 (Obj.wordOfBytesLE [b0, b1, b2, b3] 0)
            (c2Compress256Pl.base + BitVec.ofNat 64 (4 * 52))
            (compress256Block.target c2Compress256Pl r52) := by
        rw [Obj.CodeBlock.patchedWord_of_notRelaxed compress256_relocAt?_52
          (compress256_relaxedAt_false _) (.inr (compress256_relaxedAt_false _)) rfl rfl, hw]
        rfl
      rw [hpw]
      exact take4_rx_of_checkQuadEqBytes4 hok
  · have hb52 : (j == 52) = false := beq_eq_false_iff_ne.mpr h52
    rw [hb52] at hok
    simp only [Bool.false_eq_true, ↓reduceIte] at hok
    by_cases h53 : j = 53
    · subst h53
      simp only [beq_self_eq_true, ↓reduceIte] at hok
      cases hg : compress256Tree.getQuad? 53 with
      | none => rw [hg] at hok; simp at hok
      | some quad =>
        rcases quad with ⟨b0, b1, b2, b3⟩
        rw [hg] at hok
        have hw : compress256Block.wordAt (4 * 53) = Obj.wordOfBytesLE [b0, b1, b2, b3] 0 :=
          GenPlacedFetches.wordAt_of_getQuad? compress256_code_eq compress256_tree_size hg
        have hpw : compress256Block.patchedWord c2Compress256Pl (4 * 53) =
            Obj.patchRelocWord .addLo12 (Obj.wordOfBytesLE [b0, b1, b2, b3] 0)
              (c2Compress256Pl.base + BitVec.ofNat 64 (4 * 53))
              (compress256Block.target c2Compress256Pl r53) := by
          rw [Obj.CodeBlock.patchedWord_of_notRelaxed compress256_relocAt?_53
            (compress256_relaxedAt_false _) (.inr (compress256_relaxedAt_false _)) rfl rfl, hw]
          rfl
        rw [hpw]
        exact take4_rx_of_checkQuadEqBytes4 hok
    · have hb53 : (j == 53) = false := beq_eq_false_iff_ne.mpr h53
      rw [hb53] at hok
      simp only [Bool.false_eq_true, ↓reduceIte, checkQuadsEq] at hok
      cases hgrx : f3TrialRxWordTree.getQuad? (rxStart + j) with
      | none => rw [hgrx] at hok; simp at hok
      | some qrx =>
        rcases qrx with ⟨a0, a1, a2, a3⟩
        rw [hgrx] at hok
        cases hglib : compress256Tree.getQuad? j with
        | none => rw [hglib] at hok; simp at hok
        | some qlib =>
          rcases qlib with ⟨b0, b1, b2, b3⟩
          rw [hglib] at hok
          simp only [Bool.and_eq_true, f3ByteBeq_true_iff] at hok
          rcases hok with ⟨⟨⟨e0, e1⟩, e2⟩, e3⟩
          subst e0; subst e1; subst e2; subst e3
          have hw : compress256Block.wordAt (4 * j) = Obj.wordOfBytesLE [a0, a1, a2, a3] 0 :=
            GenPlacedFetches.wordAt_of_getQuad? compress256_code_eq compress256_tree_size hglib
          rw [Obj.CodeBlock.patchedWord_of_relocAt_none (compress256_relocAt?_other h52 h53), hw,
            bytesOfWordLE_wordOfBytesLE4]
          exact take4_rx_of_getQuad? hgrx

private theorem compress256_quad_eq_of_check {rxStart : Nat} :
    ∀ (j rem : Nat),
      j + rem = 1909 →
      checkCompress256WordsFrom rxStart j rem = true →
      ∀ (q : Nat), j ≤ q → q < 1909 →
        (f3TrialRxWordTree.toBytes.drop (4 * (rxStart + q))).take 4 =
          ((compress256Block.patched c2Compress256Pl).drop (4 * q)).take 4
  | j, 0, hjrem, _, q, hjq, hq => by omega
  | j, rem + 1, hjrem, hok, q, hjq, hq => by
    unfold checkCompress256WordsFrom at hok
    dsimp only at hok
    rw [Bool.and_eq_true] at hok
    by_cases heq : q = j
    · subst heq
      exact compress256_quad_eq_one hq hok.1
    · exact compress256_quad_eq_of_check (j + 1) rem (by omega) hok.2 q (by omega) hq

private def c2Compress256RxWordStart : Nat :=
  (c2Compress256Pl.base.toNat - f3RxSegBase.toNat) / 4

set_option maxRecDepth 400000 in
private theorem c2_rxSlice_compress256_words_ok :
    checkCompress256WordsFrom c2Compress256RxWordStart 0 1909 = true := by
  rfl_kernel

theorem c2_rxSlice_compress256_ok :
    checkProgCodeSubslice f3TrialRxProg (compress256SubProg c2Compress256Pl) = true := by
  have hbase_rx : f3TrialRxProg.base = f3RxSegBase := f3TrialRxProg_base
  have hbase_sub : (compress256SubProg c2Compress256Pl).base = c2Compress256Pl.base := rfl
  have hrx_len : f3TrialRxProg.code.length = 0x58000 := by
    rw [rxProg_code_len_eq]; decide
  have hsub_len : (compress256SubProg c2Compress256Pl).code.length = 7636 :=
    compress256SubProg_code_len
  have hpl_val : c2Compress256Pl.base.toNat =
      (LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen.c2Compress256Addr).toNat := rfl
  have hbound :
      f3RxSegBase.toNat ≤ c2Compress256Pl.base.toNat ∧
      c2Compress256Pl.base.toNat % 4 = 0 ∧
      f3RxSegBase.toNat % 4 = 0 ∧
      (c2Compress256Pl.base - f3RxSegBase).toNat + 7636 ≤ 0x58000 ∧
      c2Compress256Pl.base.toNat + 7636 ≤ 2 ^ 64 ∧
      f3RxSegBase + BitVec.ofNat 64 (c2Compress256Pl.base - f3RxSegBase).toNat =
        c2Compress256Pl.base ∧
      (c2Compress256Pl.base - f3RxSegBase).toNat = 4 * c2Compress256RxWordStart := by
    unfold c2Compress256RxWordStart
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  rcases hbound with ⟨hle_base, hal_sub, hal_rx, hfit, hnw, hbase_add, hoff_eq⟩
  unfold checkProgCodeSubslice
  dsimp only
  rw [hbase_rx, hbase_sub, hrx_len, hsub_len]
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨⟨⟨hal_sub, hnw⟩, hbase_add⟩, hfit⟩, ?_⟩
  apply List.ext_getElem
  · rw [List.length_take, List.length_drop, hrx_len, hsub_len]; omega
  · intro i hi1 hi2
    rw [List.getElem_take, List.getElem_drop]
    have hi : i < 7636 := by omega
    let q := i / 4
    let k := i % 4
    have hq : q < 1909 := by omega
    have hk : k < 4 := by omega
    have hquad :=
      compress256_quad_eq_of_check 0 1909 rfl c2_rxSlice_compress256_words_ok q (Nat.zero_le q) hq
    have hget4 := congrArg (fun l => l[k]?) hquad
    rw [List.getElem?_take_of_lt hk, List.getElem?_take_of_lt hk,
      List.getElem?_drop, List.getElem?_drop] at hget4
    have hidx_rx_t : 4 * (c2Compress256RxWordStart + q) + k =
        (c2Compress256Pl.base - f3RxSegBase).toNat + i := by omega
    have hidx_sub : 4 * q + k = i := by omega
    rw [hidx_rx_t, hidx_sub, ← f3TrialRxWordTree_eq] at hget4
    have hi_rx : (c2Compress256Pl.base - f3RxSegBase).toNat + i < f3TrialRxProg.code.length := by
      omega
    rw [← compress256SubProg_code c2Compress256Pl, List.getElem?_eq_getElem hi_rx,
      List.getElem?_eq_getElem hi1] at hget4
    exact (Option.some.inj hget4).symm

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress256RxSlice
