/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymDefs

/-!
# `encapsulate1_serialized` (`B03`) — Relocation-Free Fetch & `TreeMem` Algebra (`Seg2Mem`)

1. Relocation-free fetch (`fetch_blk03_noReloc`, `fetch_blk03_seg2a`, `fetch_blk03_seg2b`,
   `fetchesInstrsAt_blk03_seg2b`) across `Seg2` (`[+0x026c, +0x0524)` and `[+0x0528, +0x3294)`).
2. `TreeMem` (`len ≤ 512` 64-bit `↦₆₄` cells backed by `BTree (BitVec 64) 9`) with `O(log N)`
   `SepLoad64` / `SepStore64` / `SepLoad128` / `SepStore128` focus, split/join, `↦ₛ` byte-slice
   equivalence, `memRegion` bridges, and `Seg2SeedConsts` embedding.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Mem

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open ProofLib.GenPlacedFetches (hookAtOff?_rebase_of_placeable fetch_rebase_of_noReloc)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemPlacement)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs
  (FetchesInstrsAt pcAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
  (Vec128At SepLoad128 SepStore128)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
  (blkLib03 blkPl03 blkPlaceable03 blkPC03 blkTree03 blk03_code_eq blk03_tree_size)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a
  (Seg2SeedConsts)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2SymDefs
  (BTree fetchWordTree03)

/-! ## 1. Relocation-Free Fetch Helpers for `B03` -/

theorem fetch_blk03_noReloc [MlKemPlacement] {loOff hiOff : Nat}
    (hrel : blkLib03.text.relocs.all (fun r => decide (r.off < loOff ∨ hiOff ≤ r.off)) = true)
    {b : BitVec 64} {j : Nat} {inst : Instr}
    (hlo : loOff ≤ 4 * j) (hhi : 4 * j < hiOff) (hbound : 4 * j + 4 ≤ 4 * 7114)
    (hfw : fetchWordTree03 j = some inst) :
    (blkPC03.rebase b (fun _ => none)).fetch (b + BitVec.ofNat 64 (4 * j)) = some inst := by
  have hnrel : (blkLib03.text.relocAt? (4 * j)).isNone = true := by
    cases hr : blkLib03.text.relocAt? (4 * j) with
    | none => rfl
    | some r =>
      have hmem := CodeBlock.relocAt?_mem hr
      have hoff := CodeBlock.relocAt?_off hr
      have hall := (List.all_eq_true.mp hrel) r hmem
      simp only [decide_eq_true_eq] at hall
      omega
  have hdec : blkTree03.fetchDecodeAt (4 * j) = some inst := by
    unfold WordTree.fetchDecodeAt
    have hdiv : 4 * j / 4 = j := by omega
    rw [hdiv]
    unfold fetchWordTree03 at hfw
    cases hq : blkTree03.getQuad? j with
    | none => simp [hq] at hfw
    | some q =>
      rcases q with ⟨b0, b1, b2, b3⟩
      simp [hq] at hfw ⊢
      exact hfw
  have hnh := hookAtOff?_rebase_of_placeable (pl := blkPl03) (b := b)
    (X := fun _ => none) blk03_code_eq blk03_tree_size blkPlaceable03 (off := 4 * j) (by omega)
  exact fetch_rebase_of_noReloc blk03_code_eq blk03_tree_size
    (by omega) hbound (by omega) hdec hnrel hnh

private theorem blk03_relocs_outside_seg2a :
    blkLib03.text.relocs.all (fun r => decide (r.off < 620 ∨ 1316 ≤ r.off)) = true := by
  decide +kernel

private theorem blk03_relocs_outside_seg2b :
    blkLib03.text.relocs.all (fun r => decide (r.off < 1320 ∨ 12948 ≤ r.off)) = true := by
  decide +kernel

theorem fetch_blk03_seg2a [MlKemPlacement] {b : BitVec 64} {j : Nat} {inst : Instr}
    (hlo : 155 ≤ j) (hhi : j < 329) (hfw : fetchWordTree03 j = some inst) :
    (blkPC03.rebase b (fun _ => none)).fetch (b + BitVec.ofNat 64 (4 * j)) = some inst :=
  fetch_blk03_noReloc blk03_relocs_outside_seg2a (by omega) (by omega) (by omega) hfw

theorem fetch_blk03_seg2b [MlKemPlacement] {b : BitVec 64} {j : Nat} {inst : Instr}
    (hlo : 330 ≤ j) (hhi : j < 3237) (hfw : fetchWordTree03 j = some inst) :
    (blkPC03.rebase b (fun _ => none)).fetch (b + BitVec.ofNat 64 (4 * j)) = some inst :=
  fetch_blk03_noReloc blk03_relocs_outside_seg2b (by omega) (by omega) (by omega) hfw

@[expose] def checkInstrsAt03 (w0 : Nat) : List Instr → Bool
  | [] => true
  | i :: is => (fetchWordTree03 w0 == some i) && checkInstrsAt03 (w0 + 1) is

theorem fetchesInstrsAt_blk03_seg2b [MlKemPlacement] {b pcBase : BitVec 64}
    {w0 idx : Nat} {instrs : List Instr}
    (hlo : 330 ≤ w0) (hhi : w0 + instrs.length ≤ 3237)
    (hbase : pcBase + BitVec.ofNat 64 (4 * idx) = b + BitVec.ofNat 64 (4 * w0))
    (hchk : checkInstrsAt03 w0 instrs = true) :
    FetchesInstrsAt (blkPC03.rebase b (fun _ => none)) pcBase idx instrs := by
  induction instrs generalizing w0 idx with
  | nil =>
      intro k inst hget
      simp at hget
  | cons i is ih =>
      simp only [checkInstrsAt03, Bool.and_eq_true, beq_iff_eq] at hchk
      simp only [List.length_cons] at hhi
      intro k inst hget
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst hget
          have npc : pcAt pcBase (idx + 0) = b + BitVec.ofNat 64 (4 * w0) := by
            unfold pcAt; simpa using hbase
          rw [npc]
          exact fetch_blk03_seg2b hlo (by omega) hchk.1
      | succ k' =>
          simp only [List.getElem?_cons_succ] at hget
          have hadj : pcBase + BitVec.ofNat 64 (4 * (idx + 1)) =
              b + BitVec.ofNat 64 (4 * (w0 + 1)) := by
            have h1 : BitVec.ofNat 64 (4 * (idx + 1)) = BitVec.ofNat 64 (4 * idx) + 4#64 :=
              BitVec.ofNat_add (4 * idx) 4
            have h2 : BitVec.ofNat 64 (4 * (w0 + 1)) = BitVec.ofNat 64 (4 * w0) + 4#64 :=
              BitVec.ofNat_add (4 * w0) 4
            rw [h1, h2, ← BitVec.add_assoc, hbase, BitVec.add_assoc]
          have hstep := ih (w0 := w0 + 1) (idx := idx + 1) (by omega) (by omega) hadj hchk.2 k' inst hget
          have hpc_eq : pcAt pcBase (idx + (k' + 1)) = pcAt pcBase ((idx + 1) + k') := by
            unfold pcAt; congr 2; omega
          simpa [hpc_eq] using hstep

/-! ## 2. `TreeMem` Definition, Focus, & 64/128-Bit Load/Store Lemmas -/

@[expose] def zeroTree9 : BTree (BitVec 64) 9 :=
  BTree.ofFn 9 (fun _ => 0#64)

theorem zeroTree9_get (i : Nat) (hi : i < 512) : zeroTree9.get i = 0#64 :=
  BTree.get_ofFn 9 (fun _ => 0#64) i (Nat.lt_of_lt_of_eq hi (by decide))

@[expose] def TreeMemFrom (ptr : BitVec 64) (start : Nat) :
    Nat → BTree (BitVec 64) 9 → SepProp
  | 0, _ => emp
  | n + 1, t =>
      ((ptr + BitVec.ofNat 64 (8 * start)) ↦₆₄ t.get start) ∗
        TreeMemFrom ptr (start + 1) n t

@[expose] def TreeMem (ptr : BitVec 64) (len : Nat) (t : BTree (BitVec 64) 9) : SepProp :=
  TreeMemFrom ptr 0 len t

theorem TreeMemFrom.congr {ptr : BitVec 64} {start len : Nat}
    {t1 t2 : BTree (BitVec 64) 9}
    (h : ∀ i, start ≤ i → i < start + len → t1.get i = t2.get i) :
    TreeMemFrom ptr start len t1 = TreeMemFrom ptr start len t2 := by
  induction len generalizing start with
  | zero => rfl
  | succ n ih =>
      simp only [TreeMemFrom]
      rw [h start (Nat.le_refl _) (by omega),
          ih (start := start + 1) fun i _ _ => h i (by omega) (by omega)]

theorem TreeMem.congr {ptr : BitVec 64} {len : Nat} {t1 t2 : BTree (BitVec 64) 9}
    (h : ∀ i, i < len → t1.get i = t2.get i) :
    TreeMem ptr len t1 = TreeMem ptr len t2 :=
  TreeMemFrom.congr fun i _ hi => h i (by omega)

private theorem TreeMemFrom.focus {ptr : BitVec 64} {start len idx : Nat}
    (hlo : start ≤ idx) (hhi : idx < start + len) (hmax : start + len ≤ 512)
    (t : BTree (BitVec 64) 9) :
    ∃ Frame : SepProp,
      TreeMemFrom ptr start len t =
        ((ptr + BitVec.ofNat 64 (8 * idx)) ↦₆₄ t.get idx) ∗ Frame ∧
      ∀ v : BitVec 64,
        ((ptr + BitVec.ofNat 64 (8 * idx)) ↦₆₄ v) ∗ Frame =
          TreeMemFrom ptr start len (t.set idx v) := by
  have h512 : (2 ^ 9 : Nat) = 512 := by decide
  induction len generalizing start with
  | zero => exact absurd hhi (by omega)
  | succ n ih =>
      by_cases hk : idx = start
      · subst hk
        refine ⟨TreeMemFrom ptr (idx + 1) n t, rfl, fun v => ?_⟩
        simp only [TreeMemFrom]
        rw [BTree.get_set t idx v (by omega) idx (by omega)]
        simp only [↓reduceIte]
        congr 1
        exact TreeMemFrom.congr fun i hi1 hi2 => by
          rw [BTree.get_set t idx v (by omega) i (by omega)]
          simp [show i ≠ idx by omega]
      · rcases ih (start := start + 1) (by omega) (by omega) (by omega) with ⟨F, hF, hUpd⟩
        refine ⟨((ptr + BitVec.ofNat 64 (8 * start)) ↦₆₄ t.get start) ∗ F, ?_, fun v => ?_⟩
        · simp only [TreeMemFrom, hF]
          rw [← sepConj_assoc,
              sepConj_comm ((ptr + BitVec.ofNat 64 (8 * start)) ↦₆₄ t.get start),
              sepConj_assoc]
        · rw [← sepConj_assoc,
              sepConj_comm ((ptr + BitVec.ofNat 64 (8 * idx)) ↦₆₄ v),
              sepConj_assoc, hUpd v]
          simp only [TreeMemFrom]
          rw [BTree.get_set t idx v (by omega) start (by omega)]
          simp [show start ≠ idx by omega]

theorem TreeMem.focus {ptr : BitVec 64} {len idx : Nat}
    (hidx : idx < len) (hlen : len ≤ 512) (t : BTree (BitVec 64) 9) :
    ∃ Frame : SepProp,
      TreeMem ptr len t =
        ((ptr + BitVec.ofNat 64 (8 * idx)) ↦₆₄ t.get idx) ∗ Frame ∧
      ∀ v : BitVec 64,
        ((ptr + BitVec.ofNat 64 (8 * idx)) ↦₆₄ v) ∗ Frame =
          TreeMem ptr len (t.set idx v) :=
  TreeMemFrom.focus (Nat.zero_le idx) (by omega) (by omega) t

theorem sepLoad64_treeMem {ea ptr : BitVec 64} {len idx : Nat} {t : BTree (BitVec 64) 9}
    {P F : SepProp} (hidx : idx < len) (hlen : len ≤ 512)
    (hP : P = TreeMem ptr len t ∗ F)
    (hea : ptr + BitVec.ofNat 64 (8 * idx) = ea) :
    SepLoad64 ea P (t.get idx) := by
  rcases TreeMem.focus hidx hlen t with ⟨Fm, hFm, _⟩
  exact SepLoad64.of_eq_addr (by rw [hP, hFm, sepConj_assoc]) hea

theorem sepStore64_treeMem {ea ptr : BitVec 64} {len idx : Nat} {v : BitVec 64}
    {t : BTree (BitVec 64) 9} {P P' F : SepProp}
    (hidx : idx < len) (hlen : len ≤ 512)
    (hP : P = TreeMem ptr len t ∗ F)
    (hP' : P' = TreeMem ptr len (t.set idx v) ∗ F)
    (hea : ptr + BitVec.ofNat 64 (8 * idx) = ea) :
    SepStore64 ea v P P' := by
  rcases TreeMem.focus hidx hlen t with ⟨Fm, hFm, hUpd⟩
  exact SepStore64.of_eq_addr (by rw [hP, hFm, sepConj_assoc])
    (by rw [hP', ← hUpd v, sepConj_assoc]) hea

private theorem lo64_append (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 0 64 = lo := by bv_bits
private theorem hi64_append (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 64 64 = hi := by bv_bits

theorem sepLoad128_treeMem {ea ptr : BitVec 64} {len idx : Nat} {t : BTree (BitVec 64) 9}
    {P F : SepProp} (hidx : idx + 1 < len) (hlen : len ≤ 512)
    (hP : P = TreeMem ptr len t ∗ F)
    (hea : ptr + BitVec.ofNat 64 (8 * idx) = ea) :
    SepLoad128 ea P (t.get (idx + 1) ++ t.get idx) := by
  have hea8 : ptr + BitVec.ofNat 64 (8 * (idx + 1)) = ea + 8#64 := by
    rw [← hea, BitVec.add_assoc]
    exact congrArg (ptr + ·) (BitVec.ofNat_add (8 * idx) 8)
  refine ⟨?_, ?_⟩
  · rw [lo64_append]; exact sepLoad64_treeMem (by omega) hlen hP hea
  · rw [hi64_append]; exact sepLoad64_treeMem hidx hlen hP hea8

theorem sepStore128_treeMem {ea ptr : BitVec 64} {len idx : Nat} {vhi vlo : BitVec 64}
    {t : BTree (BitVec 64) 9} {P P' F : SepProp}
    (hidx : idx + 1 < len) (hlen : len ≤ 512)
    (hP : P = TreeMem ptr len t ∗ F)
    (hP' : P' = TreeMem ptr len ((t.set idx vlo).set (idx + 1) vhi) ∗ F)
    (hea : ptr + BitVec.ofNat 64 (8 * idx) = ea) :
    SepStore128 ea (vhi ++ vlo) P P' := by
  have hea8 : ptr + BitVec.ofNat 64 (8 * (idx + 1)) = ea + 8#64 := by
    rw [← hea, BitVec.add_assoc]
    exact congrArg (ptr + ·) (BitVec.ofNat_add (8 * idx) 8)
  refine ⟨TreeMem ptr len (t.set idx vlo) ∗ F, ?_, ?_⟩
  · rw [lo64_append]; exact sepStore64_treeMem (by omega) hlen hP rfl hea
  · rw [hi64_append]; exact sepStore64_treeMem hidx hlen rfl hP' hea8


/-! ## 3. Split/Join, Word-List, `↦ₛ` Byte-Slice, and `memRegion` Bridges -/

theorem TreeMemFrom_split (ptr : BitVec 64) (start n1 n2 : Nat)
    (t : BTree (BitVec 64) 9) :
    TreeMemFrom ptr start (n1 + n2) t =
      TreeMemFrom ptr start n1 t ∗ TreeMemFrom ptr (start + n1) n2 t := by
  induction n1 generalizing start with
  | zero => simp [TreeMemFrom]
  | succ m ih =>
      rw [Nat.succ_add, TreeMemFrom, TreeMemFrom, ih (start + 1), sepConj_assoc]
      rw [show start + (m + 1) = start + 1 + m by omega]

theorem TreeMemFrom_shift (ptr : BitVec 64) (off start len : Nat)
    (t1 t2 : BTree (BitVec 64) 9)
    (ht : ∀ i, i < len → t2.get (start + i) = t1.get (off + start + i)) :
    TreeMemFrom ptr (off + start) len t1 =
      TreeMemFrom (ptr + BitVec.ofNat 64 (8 * off)) start len t2 := by
  induction len generalizing start with
  | zero => rfl
  | succ m ih =>
      simp only [TreeMemFrom]
      have h0 := ht 0 (Nat.zero_lt_succ m)
      simp only [Nat.add_zero] at h0
      have haddr : ptr + BitVec.ofNat 64 (8 * (off + start)) =
          ptr + BitVec.ofNat 64 (8 * off) + BitVec.ofNat 64 (8 * start) := by
        rw [BitVec.add_assoc]
        congr 1
        rw [← BitVec.ofNat_add]
        congr 1; omega
      rw [haddr, ← h0, show off + start + 1 = off + (start + 1) by omega]
      rw [ih (start + 1) fun i hi => by
        have hi' := ht (i + 1) (Nat.succ_lt_succ hi)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using hi']

theorem treeMem_split {ptr : BitVec 64} {n1 n2 : Nat} {t t2 : BTree (BitVec 64) 9}
    (ht2 : ∀ i, i < n2 → t2.get i = t.get (n1 + i)) :
    TreeMem ptr (n1 + n2) t =
      TreeMem ptr n1 t ∗ TreeMem (ptr + BitVec.ofNat 64 (8 * n1)) n2 t2 := by
  simp only [TreeMem, TreeMemFrom_split ptr 0 n1 n2 t, Nat.zero_add]
  change TreeMemFrom ptr 0 n1 t ∗ TreeMemFrom ptr (n1 + 0) n2 t = _
  rw [TreeMemFrom_shift ptr n1 0 n2 t t2 fun i hi => by simpa using ht2 i hi]

theorem treeMem_join {ptr : BitVec 64} {n1 n2 : Nat} {t1 t2 t : BTree (BitVec 64) 9}
    (ht1 : ∀ i, i < n1 → t.get i = t1.get i)
    (ht2 : ∀ i, i < n2 → t.get (n1 + i) = t2.get i) :
    TreeMem ptr n1 t1 ∗ TreeMem (ptr + BitVec.ofNat 64 (8 * n1)) n2 t2 =
      TreeMem ptr (n1 + n2) t := by
  rw [treeMem_split (t := t) (t2 := t2) (fun i hi => (ht2 i hi).symm),
      TreeMem.congr (t1 := t1) (t2 := t) (fun i hi => (ht1 i hi).symm)]

@[expose] def btreeWords (start : Nat) : Nat → BTree (BitVec 64) 9 → List (BitVec 64)
  | 0, _ => []
  | len + 1, t => t.get start :: btreeWords (start + 1) len t

theorem btreeWords_length (start len : Nat) (t : BTree (BitVec 64) 9) :
    (btreeWords start len t).length = len := by
  induction len generalizing start <;> simp [btreeWords, *]

theorem btreeWords_eq_of_get {start len : Nat} {t : BTree (BitVec 64) 9} {ws : List (BitVec 64)}
    (hlen : ws.length = len) (h : ∀ i, i < len → t.get (start + i) = ws.getD i 0#64) :
    btreeWords start len t = ws := by
  subst hlen
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih =>
      dsimp only [List.length_cons, btreeWords]
      have h0 : t.get start = w := by simpa using h 0 (Nat.zero_lt_succ ws.length)
      rw [h0, ih (start := start + 1) fun i hi => by
        have hi' := h (i + 1) (Nat.succ_lt_succ hi)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using hi']

@[expose] def btreeOfWords : Nat → List (BitVec 64) → BTree (BitVec 64) 9 → BTree (BitVec 64) 9
  | _, [], t => t
  | idx, w :: ws, t => btreeOfWords (idx + 1) ws (t.set idx w)

private theorem btreeOfWords_get_lt (idx : Nat) (ws : List (BitVec 64))
    (t : BTree (BitVec 64) 9) (j : Nat) (hj : j < idx) (hmax : idx + ws.length ≤ 512) :
    (btreeOfWords idx ws t).get j = t.get j := by
  have h512 : (2 ^ 9 : Nat) = 512 := by decide
  induction ws generalizing idx t with
  | nil => rfl
  | cons w ws ih =>
      simp only [List.length_cons] at hmax
      simp only [btreeOfWords]
      rw [ih (idx := idx + 1) (t := t.set idx w) (by omega) (by omega),
          BTree.get_set t idx w (by omega) j (by omega)]
      simp [show j ≠ idx by omega]

theorem btreeOfWords_get (idx : Nat) (ws : List (BitVec 64))
    (t : BTree (BitVec 64) 9) (i : Nat) (hi : i < ws.length) (hmax : idx + ws.length ≤ 512) :
    (btreeOfWords idx ws t).get (idx + i) = ws.getD i 0#64 := by
  have h512 : (2 ^ 9 : Nat) = 512 := by decide
  induction ws generalizing idx i t with
  | nil => exact absurd hi (by simp)
  | cons w ws ih =>
      simp only [List.length_cons] at hi hmax
      cases i with
      | zero =>
          simp only [Nat.add_zero, btreeOfWords, List.getD_cons_zero]
          rw [btreeOfWords_get_lt (idx + 1) ws (t.set idx w) idx (by omega) (by omega),
              BTree.get_set t idx w (by omega) idx (by omega)]
          simp
      | succ j =>
          simp only [btreeOfWords, List.getD_cons_succ]
          rw [show idx + (j + 1) = (idx + 1) + j by omega]
          exact ih (idx := idx + 1) (i := j) (t := t.set idx w) (by omega) (by omega)

theorem TreeMemFrom_eq_pointsToWords64 (ptr : BitVec 64) (start len : Nat)
    (t : BTree (BitVec 64) 9) :
    TreeMemFrom ptr start len t =
      ((ptr + BitVec.ofNat 64 (8 * start)) ↦₆₄* btreeWords start len t) := by
  induction len generalizing start with
  | zero => simp [TreeMemFrom, btreeWords]
  | succ n ih =>
      simp only [TreeMemFrom, btreeWords, pointsToWords64_cons, ih (start + 1)]
      congr 2
      rw [BitVec.add_assoc]
      exact congrArg (ptr + ·) (BitVec.ofNat_add (8 * start) 8)

theorem TreeMem_eq_pointsToWords64 (ptr : BitVec 64) (len : Nat) (t : BTree (BitVec 64) 9) :
    TreeMem ptr len t = (ptr ↦₆₄* btreeWords 0 len t) := by
  simpa [TreeMem] using TreeMemFrom_eq_pointsToWords64 ptr 0 len t

@[expose] def wordsToBytes : List (BitVec 64) → List (BitVec 8)
  | [] => []
  | w :: ws => unpack64 w ++ wordsToBytes ws

theorem wordsToBytes_length (ws : List (BitVec 64)) :
    (wordsToBytes ws).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons _ _ ih => simp [wordsToBytes, ih]; omega

theorem pointsToWords64_eq_pointsToBytes (ptr : BitVec 64) (ws : List (BitVec 64)) :
    (ptr ↦₆₄* ws) = (ptr ↦ₛ wordsToBytes ws) := by
  induction ws generalizing ptr with
  | nil => simp [wordsToBytes]
  | cons w ws ih =>
      rw [pointsToWords64_cons, pointsTo64_eq_pointsToBytes, ih (ptr + 8#64)]
      simp only [wordsToBytes, pointsToBytes_append, unpack64_length]

theorem treeMem_eq_pointsToBytes {ptr : BitVec 64} {len : Nat} {t : BTree (BitVec 64) 9}
    {bs : List (BitVec 8)} (hbs : wordsToBytes (btreeWords 0 len t) = bs) :
    TreeMem ptr len t = (ptr ↦ₛ bs) := by
  rw [TreeMem_eq_pointsToWords64, pointsToWords64_eq_pointsToBytes, hbs]

@[expose] def packWordAt (bs : List (BitVec 8)) (off : Nat) : BitVec 64 :=
  bs.getD (off + 7) 0#8 ++ bs.getD (off + 6) 0#8 ++ bs.getD (off + 5) 0#8 ++ bs.getD (off + 4) 0#8 ++
  bs.getD (off + 3) 0#8 ++ bs.getD (off + 2) 0#8 ++ bs.getD (off + 1) 0#8 ++ bs.getD off 0#8

@[expose] def bytesToWords : Nat → List (BitVec 8) → List (BitVec 64)
  | 0, _ => []
  | n + 1, bs => packWordAt bs 0 :: bytesToWords n (bs.drop 8)

theorem bytesToWords_length (n : Nat) (bs : List (BitVec 8)) :
    (bytesToWords n bs).length = n := by
  induction n generalizing bs <;> simp [bytesToWords, *]

private theorem getD_drop (bs : List (BitVec 8)) (k i : Nat) (d : BitVec 8) :
    (bs.drop k).getD i d = bs.getD (k + i) d := by
  induction k generalizing bs with
  | zero => simp
  | succ k ih =>
      cases bs with
      | nil => simp
      | cons b bs' =>
          simp only [List.drop_succ_cons]
          rw [ih bs', show k + 1 + i = (k + i) + 1 by omega, List.getD_cons_succ]

theorem bytesToWords_getD (n : Nat) (bs : List (BitVec 8)) (i : Nat) (hi : i < n) :
    (bytesToWords n bs).getD i 0#64 = packWordAt bs (8 * i) := by
  induction n generalizing bs i with
  | zero => exact absurd hi (by omega)
  | succ _ ih =>
      cases i with
      | zero => simp [bytesToWords]
      | succ j =>
          simp only [bytesToWords, List.getD_cons_succ]
          rw [ih (bs.drop 8) j (by omega)]
          simp only [packWordAt, getD_drop]
          rw [show 8 + 8 * j = 8 * (j + 1) by omega,
              show 8 + (8 * j + 1) = 8 * (j + 1) + 1 by omega,
              show 8 + (8 * j + 2) = 8 * (j + 1) + 2 by omega,
              show 8 + (8 * j + 3) = 8 * (j + 1) + 3 by omega,
              show 8 + (8 * j + 4) = 8 * (j + 1) + 4 by omega,
              show 8 + (8 * j + 5) = 8 * (j + 1) + 5 by omega,
              show 8 + (8 * j + 6) = 8 * (j + 1) + 6 by omega,
              show 8 + (8 * j + 7) = 8 * (j + 1) + 7 by omega]

private theorem peel_byte {bs : List (BitVec 8)} (h : 0 < bs.length) :
    ∃ b rest, bs = b :: rest ∧ rest.length + 1 = bs.length := by
  cases bs with
  | nil => simp at h
  | cons b rest => exact ⟨b, rest, rfl, rfl⟩

theorem wordsToBytes_bytesToWords (n : Nat) (bs : List (BitVec 8)) (hbs : bs.length = 8 * n) :
    wordsToBytes (bytesToWords n bs) = bs := by
  induction n generalizing bs with
  | zero =>
      cases bs with
      | nil => rfl
      | cons _ _ => simp at hbs
  | succ m ih =>
      obtain ⟨b0, bs1, rfl, h1⟩ := peel_byte (bs := bs) (by omega)
      obtain ⟨b1, bs2, rfl, h2⟩ := peel_byte (bs := bs1) (by omega)
      obtain ⟨b2, bs3, rfl, h3⟩ := peel_byte (bs := bs2) (by omega)
      obtain ⟨b3, bs4, rfl, h4⟩ := peel_byte (bs := bs3) (by omega)
      obtain ⟨b4, bs5, rfl, h5⟩ := peel_byte (bs := bs4) (by omega)
      obtain ⟨b5, bs6, rfl, h6⟩ := peel_byte (bs := bs5) (by omega)
      obtain ⟨b6, bs7, rfl, h7⟩ := peel_byte (bs := bs6) (by omega)
      obtain ⟨b7, rest, rfl, h8⟩ := peel_byte (bs := bs7) (by omega)
      have hrest : rest.length = 8 * m := by omega
      have hdrop : (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest).drop 8 = rest := rfl
      simp only [bytesToWords, wordsToBytes, packWordAt, Nat.zero_add,
        List.getD_cons_zero, List.getD_cons_succ, unpack64_pack64, hdrop]
      rw [ih rest hrest]
      rfl

theorem pointsToBytes_eq_treeMem {ptr : BitVec 64} {n : Nat} {bs : List (BitVec 8)}
    (hbs : bs.length = 8 * n) (hn : n ≤ 512) :
    (ptr ↦ₛ bs) = TreeMem ptr n (btreeOfWords 0 (bytesToWords n bs) zeroTree9) := by
  symm
  apply treeMem_eq_pointsToBytes
  rw [btreeWords_eq_of_get (ws := bytesToWords n bs) (bytesToWords_length n bs) fun i hi => by
    simpa using btreeOfWords_get 0 (bytesToWords n bs) zeroTree9 i
      (by rw [bytesToWords_length]; exact hi) (by rw [bytesToWords_length]; omega)]
  exact wordsToBytes_bytesToWords n bs hbs

theorem pointsToBytes_zero_eq_treeMem {ptr : BitVec 64} {n : Nat} (hn : n ≤ 512) :
    (ptr ↦ₛ List.replicate (8 * n) 0#8) = TreeMem ptr n zeroTree9 := by
  rw [pointsToBytes_eq_treeMem (n := n) (by simp) hn]
  apply TreeMem.congr
  intro i hi
  have hg := btreeOfWords_get 0 (bytesToWords n (List.replicate (8 * n) 0#8))
    zeroTree9 i (by rw [bytesToWords_length]; exact hi) (by rw [bytesToWords_length]; omega)
  rw [Nat.zero_add] at hg
  rw [hg, bytesToWords_getD _ _ _ hi, zeroTree9_get i (by omega)]
  have hrep : ∀ k, k < 8 * n → (List.replicate (8 * n) 0#8).getD k 0#8 = 0#8 := by
    intro k hk; simp [List.getD_eq_getElem?_getD, hk]
  simp only [packWordAt, hrep (8 * i) (by omega), hrep (8 * i + 1) (by omega),
    hrep (8 * i + 2) (by omega), hrep (8 * i + 3) (by omega),
    hrep (8 * i + 4) (by omega), hrep (8 * i + 5) (by omega),
    hrep (8 * i + 6) (by omega), hrep (8 * i + 7) (by omega)]
  rfl

theorem treeMem_entails_memRegion {ptr : BitVec 64} {len : Nat} (t : BTree (BitVec 64) 9)
    (hlen : len ≤ 512) :
    TreeMem ptr len t ⊢ memRegion ptr (8 * len) := by
  rw [TreeMem_eq_pointsToWords64]
  have h := pointsToWords64_entails_memRegion (btreeWords 0 len t) ptr
    (by rw [btreeWords_length]; omega)
  simpa [btreeWords_length] using h

theorem memRegion_entails_exists_treeMem {ptr : BitVec 64} {len : Nat} (hlen : len ≤ 512) :
    memRegion ptr (8 * len) ⊢ ∃∗ t : BTree (BitVec 64) 9, TreeMem ptr len t := by
  refine Entails.trans (memRegion_entails_pointsToWords64 len ptr (by omega)) ?_
  refine Entails.sepExists_elim fun ws => Entails.pure_left fun hws => ?_
  refine Entails.sepExists_right (btreeOfWords 0 ws zeroTree9) ?_
  rw [TreeMem_eq_pointsToWords64, btreeWords_eq_of_get hws fun i hi => by
    simpa using btreeOfWords_get 0 ws zeroTree9 i (by omega) (by omega)]
  exact Entails.refl _

theorem sepWP_elim_treeMem {prog : Program} {tgt : BitVec 64} {s : State}
    {ptr : BitVec 64} {len : Nat} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hlen : len ≤ 512)
    (h : ∀ t : BTree (BitVec 64) 9, SepWP prog tgt s (TreeMem ptr len t ∗ F) post oom) :
    SepWP prog tgt s (memRegion ptr (8 * len) ∗ F) post oom := by
  rw [memRegion_eq_exists_bytes ptr (8 * len) (by omega)]
  apply SepWP.of_sepExists_left
  intro bs
  rw [sepConj_assoc]
  apply SepWP.pure_elim
  intro hbs
  rw [pointsToBytes_eq_treeMem hbs hlen]
  exact h (btreeOfWords 0 (bytesToWords len bs) zeroTree9)

/-! ## 4. `Seg2SeedConsts` ↔ `TreeMem (sp + 96) 262` Embedding -/

@[expose] def seedConstsWords (rho : List (BitVec 8)) : List (BitVec 64) :=
  let s0w := ByteSlice.readLE rho 0 8
  let s1w := ByteSlice.readLE rho 8 8
  let s2w := ByteSlice.readLE rho 16 8
  let s3w := ByteSlice.readLE rho 24 8
  [0xffffffffff0000ff#64, 0xffffffffffffffff#64,
   s3w, s3w, s2w, s2w, s1w, s1w, s0w, s0w]

theorem seg2SeedConsts_eq_treeMem (sp : BitVec 64) (rho : List (BitVec 8))
    (t : BTree (BitVec 64) 9)
    (ht : ∀ i, i < 10 → t.get i = (seedConstsWords rho).getD i 0#64) :
    Seg2SeedConsts sp rho = TreeMem (sp + 336#64) 10 t := by
  rw [TreeMem_eq_pointsToWords64,
      btreeWords_eq_of_get (start := 0) (len := 10) (ws := seedConstsWords rho) rfl
        (fun i hi => by simpa using ht i hi)]
  unfold Seg2SeedConsts Vec128At seedConstsWords
  dsimp only
  rw [lo64_append, hi64_append, lo64_append, hi64_append,
      lo64_append, hi64_append, lo64_append, hi64_append,
      show (0xffffffffffffffffffffffffff0000ff#128).extractLsb' 0 64 = 0xffffffffff0000ff#64 by decide,
      show (0xffffffffffffffffffffffffff0000ff#128).extractLsb' 64 64 = 0xffffffffffffffff#64 by decide]
  simp only [pointsToWords64_cons, pointsToWords64_nil, sepConj_emp, sepConj_assoc, BitVec.add_assoc]
  rfl

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2Mem
