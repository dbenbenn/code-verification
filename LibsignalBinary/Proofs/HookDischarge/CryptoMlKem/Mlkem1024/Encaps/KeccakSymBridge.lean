/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge

/-!
# `kyber_encapsulate` (`B07`) — Relocation-Free Fetch, `BTreeMem`, & State Bridges (`KeccakSymBridge`)

1. `blk07NoRelocInRange`, `fetch_blk07_range`, `checkInstrsAt07`, and `fetchesInstrsAt_blk07_range`.
2. `O(log N)` 64-bit word memory `BTreeMemFrom` / `BTreeMem` (`d = 9`), `SepLoad64` / `SepStore64` /
   `SepLoad128` / `SepStore128` witnesses, and `↦ₛ` byte-slice bijections (`btreeBytes`).
3. Concrete state/spatial matching (`KZMatches`, `KStateMatches`, `KSpatial`), round-constant
   broadcast load (`sepLoad64_rcAt`), and symbolic address resolution (`resolveByteOff?_sound`,
   `resolveMemIdx?_sound`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge

open Arm64 ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemPlacement)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemData01Bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (keccakRcAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak (packLane64 unpackLane64)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
  (extractLsb_hi_append extractLsb_lo_append)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge
  (pointsTo64_eq_unpackLane64 readLE_8_eq_packLane64 unpack64_eq_unpackLane64 unpackLane64_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs
  (FetchesInstrsAt pcAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
  (SepLoad128 SepStore128)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
  (blkLib07 blkPC07 fetchWordTree07 fetch_blk07_noReloc)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymDefs
  (BTree KCfg KEnv KExpr KState KZFlag evalKExpr readMemWord resolveByteOff? resolveMemIdx?
   writeMemWord)

/-! ## 1. Relocation-Free Fetch & Instruction-Slice Fetch on `B07` -/

@[expose] def blk07NoRelocInRange (wLo wHi : Nat) : Bool :=
  blkLib07.text.relocs.all (fun r => decide (r.off < 4 * wLo ∨ 4 * wHi ≤ r.off))

theorem fetch_blk07_range [MlKemPlacement] {b : BitVec 64} {wLo wHi j : Nat} {inst : Instr}
    (hnr : blk07NoRelocInRange wLo wHi = true) (hmax : wHi ≤ 10252)
    (hlo : wLo ≤ j) (hhi : j < wHi) (hfw : fetchWordTree07 j = some inst) :
    (blkPC07.rebase b (fun _ => none)).fetch (b + BitVec.ofNat 64 (4 * j)) = some inst :=
  fetch_blk07_noReloc hnr (by omega) (by omega) (by omega) hfw

@[expose] def checkInstrsAt07 (wStart : Nat) : List Instr → Bool
  | [] => true
  | inst :: rest => (fetchWordTree07 wStart == some inst) && checkInstrsAt07 (wStart + 1) rest

theorem checkInstrsAt07_get? :
    ∀ {instrs : List Instr} {wStart k : Nat} {inst : Instr},
      checkInstrsAt07 wStart instrs = true →
      instrs[k]? = some inst →
      fetchWordTree07 (wStart + k) = some inst
  | [], _, k, _, _, hk => by simp at hk
  | x :: xs, wStart, 0, inst, hc, hk => by
      simp only [checkInstrsAt07, Bool.and_eq_true] at hc
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      exact beq_iff_eq.mp hc.1
  | x :: xs, wStart, k + 1, inst, hc, hk => by
      simp only [checkInstrsAt07, Bool.and_eq_true] at hc
      simp only [List.getElem?_cons_succ] at hk
      simpa [Nat.add_right_comm, Nat.add_assoc] using checkInstrsAt07_get? hc.2 hk

theorem fetchesInstrsAt_blk07_range [MlKemPlacement] {b : BitVec 64}
    {wSite baseIdx wHi : Nat} {instrs : List Instr}
    (hnr : blk07NoRelocInRange (wSite + baseIdx) wHi = true)
    (hmax : wHi ≤ 10252)
    (hlen : wSite + baseIdx + instrs.length ≤ wHi)
    (hc : checkInstrsAt07 (wSite + baseIdx) instrs = true) :
    FetchesInstrsAt (blkPC07.rebase b (fun _ => none))
      (b + BitVec.ofNat 64 (4 * wSite)) baseIdx instrs := by
  intro k inst hk
  have hk_lt : k < instrs.length := by
    by_contra hge
    simp [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hk
  have hfw := checkInstrsAt07_get? hc hk
  have hpc : pcAt (b + BitVec.ofNat 64 (4 * wSite)) (baseIdx + k) =
      b + BitVec.ofNat 64 (4 * (wSite + baseIdx + k)) := by
    unfold pcAt
    rw [BitVec.add_assoc]
    congr 1
    rw [← BitVec.ofNat_add]
    congr 1; omega
  rw [hpc]
  exact fetch_blk07_range hnr hmax (by omega) (by omega) (by simpa [Nat.add_assoc] using hfw)

/-! ## 2. `O(log N)` 64-Bit Word Memory (`BTreeMemFrom`, `BTreeMem`, `btreeBytes`) -/

@[expose] def BTreeMemFrom (ptr : BitVec 64) (start : Nat) :
    Nat → BTree (BitVec 64) 9 → SepProp
  | 0, _ => emp
  | c + 1, t => (ptr ↦₆₄ t.get start) ∗ BTreeMemFrom (ptr + 8#64) (start + 1) c t

@[expose] def BTreeMem (ptr : BitVec 64) (len : Nat) (t : BTree (BitVec 64) 9) : SepProp :=
  BTreeMemFrom ptr 0 len t

theorem BTreeMemFrom.congr {ptr : BitVec 64} {start cnt : Nat} {t1 t2 : BTree (BitVec 64) 9}
    (h : ∀ i, start ≤ i → i < start + cnt → t1.get i = t2.get i) :
    BTreeMemFrom ptr start cnt t1 = BTreeMemFrom ptr start cnt t2 := by
  induction cnt generalizing ptr start with
  | zero => rfl
  | succ c ih =>
      simp only [BTreeMemFrom]
      rw [h start (Nat.le_refl _) (by omega),
        ih (ptr := ptr + 8#64) (start := start + 1) fun i _ _ => h i (by omega) (by omega)]

theorem BTreeMem.congr {ptr : BitVec 64} {len : Nat} {t1 t2 : BTree (BitVec 64) 9}
    (h : ∀ i, i < len → t1.get i = t2.get i) :
    BTreeMem ptr len t1 = BTreeMem ptr len t2 :=
  BTreeMemFrom.congr fun i _ hi => h i (by omega)

theorem BTreeMemFrom.focus {ptr : BitVec 64} {start cnt k : Nat}
    (hlo : start ≤ k) (hhi : k < start + cnt) (h512 : start + cnt ≤ 512)
    (t : BTree (BitVec 64) 9) :
    ∃ Frame : SepProp,
      BTreeMemFrom ptr start cnt t =
        ((ptr + BitVec.ofNat 64 (8 * (k - start))) ↦₆₄ t.get k) ∗ Frame ∧
      ∀ v : BitVec 64,
        ((ptr + BitVec.ofNat 64 (8 * (k - start))) ↦₆₄ v) ∗ Frame =
          BTreeMemFrom ptr start cnt (t.set k v) := by
  have hk512 : k < 2 ^ 9 := by omega
  induction cnt generalizing ptr start with
  | zero => exact absurd hhi (by omega)
  | succ c ih =>
      by_cases hk : k = start
      · subst hk
        refine ⟨BTreeMemFrom (ptr + 8#64) (k + 1) c t, ?_, fun v => ?_⟩
        · simp [BTreeMemFrom]
        · simp only [Nat.sub_self, Nat.mul_zero, BitVec.add_zero,
            BTreeMemFrom, BTree.get_set t k v hk512 k hk512, ↓reduceIte]
          congr 1
          exact BTreeMemFrom.congr fun i hi1 hi2 => by
            rw [BTree.get_set t k v hk512 i (by omega)]
            simp [show i ≠ k by omega]
      · rcases ih (ptr := ptr + 8#64) (start := start + 1) (by omega) (by omega) (by omega) with
          ⟨F, hF, hUpd⟩
        have hadj : (ptr + 8#64) + BitVec.ofNat 64 (8 * (k - (start + 1))) =
            ptr + BitVec.ofNat 64 (8 * (k - start)) := by
          rw [BitVec.add_assoc]
          congr 1
          rw [← BitVec.ofNat_add]
          congr 1; omega
        rw [hadj] at hF hUpd
        refine ⟨(ptr ↦₆₄ t.get start) ∗ F, ?_, fun v => ?_⟩
        · simp only [BTreeMemFrom, hF]
          rw [← sepConj_assoc, sepConj_comm (ptr ↦₆₄ t.get start), sepConj_assoc]
        · rw [← sepConj_assoc, sepConj_comm ((ptr + BitVec.ofNat 64 (8 * (k - start))) ↦₆₄ v),
            sepConj_assoc, hUpd v]
          simp only [BTreeMemFrom, BTree.get_set t k v hk512 start (by omega),
            show start ≠ k by omega, ↓reduceIte]

theorem BTreeMem.focus {ptr : BitVec 64} {len k : Nat} (hk : k < len) (h512 : len ≤ 512)
    (t : BTree (BitVec 64) 9) :
    ∃ Frame : SepProp,
      BTreeMem ptr len t = ((ptr + BitVec.ofNat 64 (8 * k)) ↦₆₄ t.get k) ∗ Frame ∧
      ∀ v : BitVec 64,
        ((ptr + BitVec.ofNat 64 (8 * k)) ↦₆₄ v) ∗ Frame = BTreeMem ptr len (t.set k v) := by
  simpa [BTreeMem] using BTreeMemFrom.focus (Nat.zero_le k) (by omega) (by omega) t

theorem sepLoad64_btreeMem {ea ptr : BitVec 64} {len k : Nat} {t : BTree (BitVec 64) 9}
    (hk : k < len) (h512 : len ≤ 512) (hea : ptr + BitVec.ofNat 64 (8 * k) = ea) :
    SepLoad64 ea (BTreeMem ptr len t) (t.get k) := by
  rcases BTreeMem.focus hk h512 t with ⟨Fm, hFm, _⟩
  exact SepLoad64.of_eq_addr hFm hea

theorem sepStore64_btreeMem {ea ptr : BitVec 64} {len k : Nat} {val : BitVec 64}
    {t : BTree (BitVec 64) 9} (hk : k < len) (h512 : len ≤ 512)
    (hea : ptr + BitVec.ofNat 64 (8 * k) = ea) :
    SepStore64 ea val (BTreeMem ptr len t) (BTreeMem ptr len (t.set k val)) := by
  rcases BTreeMem.focus hk h512 t with ⟨Fm, hFm, hUpd⟩
  exact SepStore64.of_eq_addr hFm (hUpd val).symm hea

theorem sepLoad128_btreeMem {ea ptr : BitVec 64} {len k : Nat} {t : BTree (BitVec 64) 9}
    (hk : k + 2 ≤ len) (h512 : len ≤ 512) (hea : ptr + BitVec.ofNat 64 (8 * k) = ea) :
    SepLoad128 ea (BTreeMem ptr len t) (t.get (k + 1) ++ t.get k) := by
  have h8 : BitVec.ofNat 64 (8 * (k + 1)) = BitVec.ofNat 64 (8 * k) + 8#64 :=
    BitVec.ofNat_add (8 * k) 8
  have hea8 : ptr + BitVec.ofNat 64 (8 * (k + 1)) = ea + 8#64 := by
    rw [← hea, h8, ← BitVec.add_assoc]
  refine ⟨?_, ?_⟩
  · rw [extractLsb_lo_append]
    exact sepLoad64_btreeMem (by omega) h512 hea
  · rw [extractLsb_hi_append]
    exact sepLoad64_btreeMem (by omega) h512 hea8

theorem sepStore128_btreeMem {ea ptr : BitVec 64} {len k : Nat} {vHi vLo : BitVec 64}
    {t : BTree (BitVec 64) 9} (hk : k + 2 ≤ len) (h512 : len ≤ 512)
    (hea : ptr + BitVec.ofNat 64 (8 * k) = ea) :
    SepStore128 ea (vHi ++ vLo) (BTreeMem ptr len t)
      (BTreeMem ptr len ((t.set k vLo).set (k + 1) vHi)) := by
  have h8 : BitVec.ofNat 64 (8 * (k + 1)) = BitVec.ofNat 64 (8 * k) + 8#64 :=
    BitVec.ofNat_add (8 * k) 8
  have hea8 : ptr + BitVec.ofNat 64 (8 * (k + 1)) = ea + 8#64 := by
    rw [← hea, h8, ← BitVec.add_assoc]
  refine ⟨⟨BTreeMem ptr len (t.set k vLo), ?_, ?_⟩⟩
  · rw [extractLsb_lo_append]
    exact sepStore64_btreeMem (by omega) h512 hea
  · rw [extractLsb_hi_append]
    exact sepStore64_btreeMem (by omega) h512 hea8

@[expose] def btreeBytesFrom (start : Nat) : Nat → BTree (BitVec 64) 9 → List (BitVec 8)
  | 0, _ => []
  | c + 1, t => unpackLane64 (t.get start) ++ btreeBytesFrom (start + 1) c t

@[expose] def btreeBytes (len : Nat) (t : BTree (BitVec 64) 9) : List (BitVec 8) :=
  btreeBytesFrom 0 len t

@[simp] theorem btreeBytesFrom_length (start cnt : Nat) (t : BTree (BitVec 64) 9) :
    (btreeBytesFrom start cnt t).length = 8 * cnt := by
  induction cnt generalizing start with
  | zero => simp [btreeBytesFrom]
  | succ c ih =>
      simp only [btreeBytesFrom, List.length_append, unpackLane64_length, ih]
      omega

@[simp] theorem btreeBytes_length (len : Nat) (t : BTree (BitVec 64) 9) :
    (btreeBytes len t).length = 8 * len :=
  btreeBytesFrom_length 0 len t

theorem BTreeMemFrom_eq_bytes (ptr : BitVec 64) (start cnt : Nat) (t : BTree (BitVec 64) 9) :
    BTreeMemFrom ptr start cnt t = (ptr ↦ₛ btreeBytesFrom start cnt t) := by
  induction cnt generalizing ptr start with
  | zero => simp [BTreeMemFrom, btreeBytesFrom, pointsToBytes_nil]
  | succ c ih =>
      simp only [BTreeMemFrom, btreeBytesFrom, pointsTo64_eq_unpackLane64, ih,
        pointsToBytes_append, unpackLane64_length]

theorem BTreeMem_eq_bytes (ptr : BitVec 64) (len : Nat) (t : BTree (BitVec 64) 9) :
    BTreeMem ptr len t = (ptr ↦ₛ btreeBytes len t) :=
  BTreeMemFrom_eq_bytes ptr 0 len t

theorem BTreeMem_entails_memRegion (ptr : BitVec 64) (len : Nat) (t : BTree (BitVec 64) 9) :
    BTreeMem ptr len t ⊢ memRegion ptr (8 * len) := by
  rw [BTreeMem_eq_bytes]
  have h := pointsToBytes_entails_memRegion ptr (btreeBytes len t)
  rwa [btreeBytes_length] at h

theorem btreeBytesFrom_split (start a b : Nat) (t : BTree (BitVec 64) 9) :
    btreeBytesFrom start (a + b) t =
      btreeBytesFrom start a t ++ btreeBytesFrom (start + a) b t := by
  induction a generalizing start with
  | zero => simp [btreeBytesFrom]
  | succ a' ih =>
      simp only [Nat.succ_add, btreeBytesFrom, ih (start + 1), List.append_assoc]
      have hadj : start + 1 + a' = start + (a' + 1) := by omega
      rw [show (start + a').succ = start + 1 + a' by omega, hadj]

theorem btreeBytes_drop_take {off cnt len : Nat} (h : off + cnt ≤ len)
    (t : BTree (BitVec 64) 9) :
    ((btreeBytes len t).drop (8 * off)).take (8 * cnt) = btreeBytesFrom off cnt t := by
  have hlen : len = off + (cnt + (len - off - cnt)) := by omega
  unfold btreeBytes
  rw [hlen, btreeBytesFrom_split 0 off _, btreeBytesFrom_split (0 + off) cnt _, Nat.zero_add]
  have hd : 8 * off = (btreeBytesFrom 0 off t).length := (btreeBytesFrom_length 0 off t).symm
  rw [hd, List.drop_left]
  have ht : 8 * cnt = (btreeBytesFrom off cnt t).length := (btreeBytesFrom_length off cnt t).symm
  rw [ht, List.take_left]

@[expose] def bytesToBTree9 (bs : List (BitVec 8)) : BTree (BitVec 64) 9 :=
  BTree.ofFn 9 (fun k => packLane64 bs (8 * k))

private theorem unpackLane64_packLane64_zero {bs : List (BitVec 8)} (h : bs.length = 8) :
    unpackLane64 (packLane64 bs 0) = bs := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try solve | cases h
  rw [← unpack64_eq_unpackLane64, ← readLE_8_eq_packLane64, ← ByteSlice.pack64_eq_readLE_8]
  exact unpack64_pack64 b0 b1 b2 b3 b4 b5 b6 b7

private theorem packLane64_drop (bs : List (BitVec 8)) (d off : Nat) :
    packLane64 (bs.drop d) off = packLane64 bs (d + off) := by
  unfold packLane64
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_assoc]

private theorem packLane64_take8 (bs : List (BitVec 8)) :
    packLane64 (bs.take 8) 0 = packLane64 bs 0 := by
  unfold packLane64
  simp [List.getD_eq_getElem?_getD]

theorem btreeBytesFrom_congr {start cnt : Nat} {t1 t2 : BTree (BitVec 64) 9}
    (h : ∀ i, start ≤ i → i < start + cnt → t1.get i = t2.get i) :
    btreeBytesFrom start cnt t1 = btreeBytesFrom start cnt t2 := by
  induction cnt generalizing start with
  | zero => rfl
  | succ c ih =>
      simp only [btreeBytesFrom]
      rw [h start (Nat.le_refl _) (by omega),
        ih (start := start + 1) fun i _ _ => h i (by omega) (by omega)]

private theorem btreeBytesFrom_bytesToBTree9 :
    ∀ (cnt start : Nat) {bs : List (BitVec 8)},
      bs.length = 8 * (start + cnt) →
      start + cnt ≤ 512 →
      btreeBytesFrom start cnt (bytesToBTree9 bs) = bs.drop (8 * start)
  | 0, start, bs, h, _ => by
      simp only [btreeBytesFrom]
      exact (List.drop_eq_nil_of_le (by omega)).symm
  | c + 1, start, bs, h, h512 => by
      have hhd : (bytesToBTree9 bs).get start = packLane64 bs (8 * start) :=
        BTree.get_ofFn 9 _ start (by omega)
      have h8 : ((bs.drop (8 * start)).take 8).length = 8 := by
        simp [List.length_take_of_le (by simp; omega : 8 ≤ (bs.drop (8 * start)).length)]
      have hu : unpackLane64 (packLane64 bs (8 * start)) = (bs.drop (8 * start)).take 8 := by
        have hp : packLane64 bs (8 * start) = packLane64 ((bs.drop (8 * start)).take 8) 0 := by
          rw [packLane64_take8, packLane64_drop, Nat.add_zero]
        rw [hp, unpackLane64_packLane64_zero h8]
      have hrec := btreeBytesFrom_bytesToBTree9 c (start + 1) (bs := bs) (by omega) (by omega)
      simp only [btreeBytesFrom, hhd, hu, hrec]
      have hd : bs.drop (8 * (start + 1)) = (bs.drop (8 * start)).drop 8 := by
        rw [List.drop_drop]
        exact congrArg (fun n => bs.drop n) (by omega)
      rw [hd, List.take_append_drop]

theorem pointsToBytes_eq_btreeMem (len : Nat) (ptr : BitVec 64) {bs : List (BitVec 8)}
    (hlen : bs.length = 8 * len) (h512 : len ≤ 512) :
    (ptr ↦ₛ bs) = BTreeMem ptr len (bytesToBTree9 bs) := by
  rw [BTreeMem_eq_bytes]
  unfold btreeBytes
  rw [btreeBytesFrom_bytesToBTree9 len 0 (by simpa using hlen) (by omega)]
  simp

theorem SepWP.of_memRegion_btreeMem {prog : Program} {target_pc : BitVec 64}
    {s : State} {Full F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (len : Nat) (ptr : BitVec 64) (h512 : len ≤ 512 := by decide)
    (hn : 8 * len ≤ 2 ^ 64 := by decide)
    (hf : Full = memRegion ptr (8 * len) ∗ F := by sep_focus)
    (h : ∀ t : BTree (BitVec 64) 9, SepWP prog target_pc s (BTreeMem ptr len t ∗ F) post oom) :
    SepWP prog target_pc s Full post oom := by
  rw [hf, memRegion_eq_exists_bytes ptr (8 * len) hn]
  apply SepWP.of_sepExists_left
  intro bs
  rw [sepConj_assoc]
  apply SepWP.pure_elim
  intro hlen
  rw [pointsToBytes_eq_btreeMem len ptr hlen h512]
  exact h (bytesToBTree9 bs)

/-! ## 3. Concrete State/Spatial Matching (`KStateMatches`, `KSpatial`) & Helpers -/

@[expose] def KCfgValid (cfg : KCfg) : Prop :=
  cfg.lenA ≤ 512 ∧ cfg.lenB ≤ 512 ∧ cfg.offA % 8 = 0 ∧ cfg.offB % 8 = 0

instance (cfg : KCfg) : Decidable (KCfgValid cfg) := by
  unfold KCfgValid; infer_instance

@[expose] def evalMemTree (env : KEnv) (t : BTree KExpr 9) : BTree (BitVec 64) 9 :=
  t.map (evalKExpr env)

@[expose] def KZMatches (env : KEnv) : Option KZFlag → PState → Prop
  | none, _ => True
  | some (.constBool b), ps => ConditionHolds .EQ ps = b ∧ ConditionHolds .NE ps = !b
  | some .loopDone, ps =>
      let done := (BitVec.ofNat 64 (8 * env.rLoop) + 8#64 == 192#64)
      ConditionHolds .EQ ps = done ∧ ConditionHolds .NE ps = !done

structure KStateMatches (env : KEnv) (st : KState) (s : State) : Prop where
  hsp    : s.sp = env.sp
  hsp_al : s.spAligned = true
  hvregs : ∀ r : BitVec 5,
    s.readVReg128 r =
      evalKExpr env (st.vregs.get r.toNat).2 ++ evalKExpr env (st.vregs.get r.toNat).1
  hgprs  : ∀ r : BitVec 5, r ≠ 31#5 →
    s.readReg64 (.gpr r) = evalKExpr env (st.gprs.get r.toNat)
  hzflag : KZMatches env st.zFlag s.pstate

@[expose] def KSpatial (cfg : KCfg) (env : KEnv) (st : KState) (F : SepProp) : SepProp :=
  (env.rcBase ↦ᵣ mlkemData01Bytes) ∗
    (BTreeMem (env.sp + BitVec.ofNat 64 cfg.offA) cfg.lenA (evalMemTree env st.memA) ∗
      (BTreeMem (env.sp + BitVec.ofNat 64 cfg.offB) cfg.lenB (evalMemTree env st.memB) ∗ F))

private theorem conditionHolds_ne_eq_not_eq (ps : PState) :
    ConditionHolds .NE ps = !(ConditionHolds .EQ ps) := by
  cases ps; simp [ConditionHolds]

theorem kzMatches_subs64_const (env : KEnv) (v imm : BitVec 64) :
    KZMatches env (some (.constBool (v == imm))) (subsPState64 v imm) := by
  refine ⟨conditionHolds_eq_subsPState64 v imm, ?_⟩
  rw [conditionHolds_ne_eq_not_eq, conditionHolds_eq_subsPState64]

theorem kzMatches_subs64_loopDone (env : KEnv) :
    KZMatches env (some .loopDone)
      (subsPState64 (BitVec.ofNat 64 (8 * env.rLoop) + 8#64) 192#64) := by
  dsimp only [KZMatches]
  refine ⟨conditionHolds_eq_subsPState64 _ _, ?_⟩
  rw [conditionHolds_ne_eq_not_eq, conditionHolds_eq_subsPState64]

theorem matches_writeVReg {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) (rd : BitVec 5) (p : KExpr × KExpr)
    {val : BitVec 128} (hval : val = evalKExpr env p.2 ++ evalKExpr env p.1) :
    KStateMatches env { st with vregs := st.vregs.set rd.toNat p }
      (s.writeVReg128 rd val) := by
  refine ⟨hm.hsp, hm.hsp_al, ?_, hm.hgprs, hm.hzflag⟩
  intro r
  have hrd : rd.toNat < 2 ^ 5 := rd.isLt
  have hr : r.toNat < 2 ^ 5 := r.isLt
  rw [BTree.get_set st.vregs rd.toNat p hrd r.toNat hr]
  by_cases heq : r = rd
  · subst heq
    simp [State.readVReg128, State.writeVReg128, hval]
  · have hne : r.toNat ≠ rd.toNat := fun h => heq (BitVec.eq_of_toNat_eq h)
    simp only [hne, ↓reduceIte]
    simpa [State.readVReg128, State.writeVReg128, heq] using hm.hvregs r

theorem matches_writeGpr {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) {rd : BitVec 5} (hrd : rd ≠ 31#5)
    (e : KExpr) {val : BitVec 64} (hval : val = evalKExpr env e) :
    KStateMatches env { st with gprs := st.gprs.set rd.toNat e }
      (s.writeReg64 (.gpr rd) val) := by
  refine ⟨by simp [State.writeReg64, hm.hsp],
    by simpa [State.spAligned, State.writeReg64] using hm.hsp_al,
    hm.hvregs, ?_, hm.hzflag⟩
  intro r hr
  rw [BTree.get_set st.gprs rd.toNat e rd.isLt r.toNat r.isLt]
  have hrdF : (rd == 31#5) = false := beq_false_of_ne hrd
  have hrF : (r == 31#5) = false := beq_false_of_ne hr
  by_cases heq : r = rd
  · subst heq
    simp [State.readReg64, State.writeReg64, hrdF, RegFile.read, RegFile.write, hval]
  · have hne : r.toNat ≠ rd.toNat := fun h => heq (BitVec.eq_of_toNat_eq h)
    simp only [hne, ↓reduceIte]
    simpa [State.readReg64, State.writeReg64, hrdF, hrF, RegFile.read, RegFile.write, heq]
      using hm.hgprs r hr

theorem matches_setMem {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) (m' : Memory) :
    KStateMatches env st (s.setMem m') :=
  ⟨hm.hsp, hm.hsp_al, hm.hvregs,
   fun r hr => by simpa [State.setMem, State.readReg64] using hm.hgprs r hr,
   hm.hzflag⟩

theorem sepLoad64_rcAt {cfg : KCfg} {env : KEnv} {st : KState} {F : SepProp}
    {ea : BitVec 64} {r : Nat} (hr : r < 24)
    (hea : env.rcBase + BitVec.ofNat 64 (8 * r) = ea) :
    SepLoad64 ea (KSpatial cfg env st F) (keccakRcAt r) := by
  have hlen : 8 * r + 8 ≤ mlkemData01Bytes.length := by
    have hm : mlkemData01Bytes.length = 192 := rfl
    omega
  exact (SepLoad64.of_pointsToBytes_readLE_RO (P := KSpatial cfg env st F)
    rfl hlen hea)

theorem resolveByteOff?_sound {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) {addr : AddrMode} {byteOff : Nat}
    (hr : resolveByteOff? st addr = some byteOff) :
    checkAddrSPAligned s addr = true ∧
      evalAddrMode s addr = (env.sp + BitVec.ofNat 64 byteOff, none) := by
  unfold resolveByteOff? at hr
  cases addr with
  | Offset base off64 | UnscaledOffset base off64 =>
      cases base with
      | sp =>
          simp only at hr
          split at hr <;> try cases hr
          next hcond =>
          rw [Bool.and_eq_true] at hcond
          have hoff : off64 = BitVec.ofNat 64 off64.toNat := beq_iff_eq.mp hcond.2
          refine ⟨by simp [checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, hm.hsp_al], ?_⟩
          simp [evalAddrMode, hm.hsp, ← hoff]
      | gpr r =>
          simp only at hr
          by_cases hr31 : (r == 31#5) = true
          · simp [hr31] at hr
          · have hr31F : (r == 31#5) = false := Bool.eq_false_iff.mpr hr31
            have hrNe : r ≠ 31#5 := fun h => hr31 (beq_iff_eq.mpr h)
            simp only [hr31F, Bool.false_eq_true, ↓reduceIte] at hr
            cases hg : st.gprs.get r.toNat <;> simp only [hg] at hr <;> try cases hr
            case spAdd bOff =>
              split at hr <;> try cases hr
              next hcond =>
              rw [Bool.and_eq_true] at hcond
              have htot : bOff + off64 = BitVec.ofNat 64 (bOff + off64).toNat :=
                beq_iff_eq.mp hcond.2
              have hreg := hm.hgprs r hrNe
              rw [hg] at hreg
              simp only [evalKExpr] at hreg
              refine ⟨by simp [checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned], ?_⟩
              simp only [evalAddrMode, hreg, BitVec.add_assoc]
              exact Prod.ext (congrArg (env.sp + ·) htot) rfl
      | xzr => simp at hr
  | _ => simp at hr

theorem resolveMemIdx?_sound {cfg : KCfg} (hv : KCfgValid cfg) {env : KEnv} {st : KState}
    {s : State} (hm : KStateMatches env st s) {addr : AddrMode} {words : Nat}
    {inB : Bool} {idx : Nat}
    (hr : resolveMemIdx? cfg st addr words = some (inB, idx)) :
    checkAddrSPAligned s addr = true ∧
      if inB then
        idx + words ≤ cfg.lenB ∧
          evalAddrMode s addr =
            ((env.sp + BitVec.ofNat 64 cfg.offB) + BitVec.ofNat 64 (8 * idx), none)
      else
        idx + words ≤ cfg.lenA ∧
          evalAddrMode s addr =
            ((env.sp + BitVec.ofNat 64 cfg.offA) + BitVec.ofNat 64 (8 * idx), none) := by
  rcases hv with ⟨_, _, hmodA, hmodB⟩
  unfold resolveMemIdx? at hr
  cases hb : resolveByteOff? st addr with
  | none => simp [hb] at hr
  | some byteOff =>
      simp only [hb] at hr
      rcases resolveByteOff?_sound hm hb with ⟨hsp, haddr⟩
      refine ⟨hsp, ?_⟩
      by_cases hmod : (!(Nat.beq (byteOff % 8) 0)) = true
      · simp [hmod] at hr
      · have hmod0 : byteOff % 8 = 0 := by
          cases hm8 : Nat.beq (byteOff % 8) 0
          · simp [hm8] at hmod
          · exact Nat.eq_of_beq_eq_true hm8
        have hnotF : (!(Nat.beq (byteOff % 8) 0)) = false := Bool.eq_false_iff.mpr hmod
        simp only [hnotF, Bool.false_eq_true, ↓reduceIte] at hr
        split at hr
        · next hA =>
            cases hr
            simp only [Bool.false_eq_true, ↓reduceIte]
            simp only [Bool.and_eq_true, Nat.ble_eq] at hA
            refine ⟨by omega, ?_⟩
            rw [haddr, BitVec.add_assoc]
            congr 2
            rw [← BitVec.ofNat_add]
            congr 1; omega
        · split at hr <;> try cases hr
          next hB =>
            simp only [↓reduceIte]
            simp only [Bool.and_eq_true, Nat.ble_eq] at hB
            refine ⟨by omega, ?_⟩
            rw [haddr, BitVec.add_assoc]
            congr 2
            rw [← BitVec.ofNat_add]
            congr 1; omega

theorem sepLoad64_kspatial {cfg : KCfg} (hv : KCfgValid cfg) {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) {addr : AddrMode} {inB : Bool} {idx : Nat}
    (hr : resolveMemIdx? cfg st addr 1 = some (inB, idx)) (F : SepProp) :
    ∃ ea : BitVec 64,
      checkAddrSPAligned s addr = true ∧
      evalAddrMode s addr = (ea, none) ∧
      SepLoad64 ea (KSpatial cfg env st F) (evalKExpr env (readMemWord st inB idx)) := by
  rcases resolveMemIdx?_sound hv hm hr with ⟨hsp, hrest⟩
  cases inB
  · simp only [Bool.false_eq_true, ↓reduceIte, readMemWord] at hrest ⊢
    refine ⟨_, hsp, hrest.2, ?_⟩
    have hl := sepLoad64_btreeMem (ptr := env.sp + BitVec.ofNat 64 cfg.offA) (k := idx)
      (t := evalMemTree env st.memA) (by omega) hv.1 rfl
    rw [evalMemTree, BTree.get_map] at hl
    exact hl.left.right
  · simp only [↓reduceIte, readMemWord] at hrest ⊢
    refine ⟨_, hsp, hrest.2, ?_⟩
    have hl := sepLoad64_btreeMem (ptr := env.sp + BitVec.ofNat 64 cfg.offB) (k := idx)
      (t := evalMemTree env st.memB) (by omega) hv.2.1 rfl
    rw [evalMemTree, BTree.get_map] at hl
    exact hl.left.right.right

theorem sepStore64_kspatial {cfg : KCfg} (hv : KCfgValid cfg) {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) {addr : AddrMode} {inB : Bool} {idx : Nat}
    (hr : resolveMemIdx? cfg st addr 1 = some (inB, idx)) (e : KExpr) (F : SepProp) :
    ∃ ea : BitVec 64,
      checkAddrSPAligned s addr = true ∧
      evalAddrMode s addr = (ea, none) ∧
      SepStore64 ea (evalKExpr env e) (KSpatial cfg env st F)
        (KSpatial cfg env (writeMemWord st inB idx e) F) := by
  rcases resolveMemIdx?_sound hv hm hr with ⟨hsp, hrest⟩
  cases inB
  · simp only [Bool.false_eq_true, ↓reduceIte] at hrest
    refine ⟨_, hsp, hrest.2, ?_⟩
    have hs := sepStore64_btreeMem (ptr := env.sp + BitVec.ofNat 64 cfg.offA) (k := idx)
      (val := evalKExpr env e) (t := evalMemTree env st.memA) (by omega) hv.1 rfl
    rw [evalMemTree, ← BTree.map_set] at hs
    exact hs.left.right
  · simp only [↓reduceIte] at hrest
    refine ⟨_, hsp, hrest.2, ?_⟩
    have hs := sepStore64_btreeMem (ptr := env.sp + BitVec.ofNat 64 cfg.offB) (k := idx)
      (val := evalKExpr env e) (t := evalMemTree env st.memB) (by omega) hv.2.1 rfl
    rw [evalMemTree, ← BTree.map_set] at hs
    exact hs.left.right.right

theorem sepLoad128_kspatial {cfg : KCfg} (hv : KCfgValid cfg) {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) {addr : AddrMode} {inB : Bool} {idx : Nat}
    (hr : resolveMemIdx? cfg st addr 2 = some (inB, idx)) (F : SepProp) :
    ∃ ea : BitVec 64,
      checkAddrSPAligned s addr = true ∧
      evalAddrMode s addr = (ea, none) ∧
      SepLoad128 ea (KSpatial cfg env st F)
        (evalKExpr env (readMemWord st inB (idx + 1)) ++ evalKExpr env (readMemWord st inB idx)) := by
  rcases resolveMemIdx?_sound hv hm hr with ⟨hsp, hrest⟩
  cases inB
  · simp only [Bool.false_eq_true, ↓reduceIte, readMemWord] at hrest ⊢
    refine ⟨_, hsp, hrest.2, ?_⟩
    have hl := sepLoad128_btreeMem (ptr := env.sp + BitVec.ofNat 64 cfg.offA) (k := idx)
      (t := evalMemTree env st.memA) hrest.1 hv.1 rfl
    rw [evalMemTree, BTree.get_map, BTree.get_map] at hl
    exact hl.left.right
  · simp only [↓reduceIte, readMemWord] at hrest ⊢
    refine ⟨_, hsp, hrest.2, ?_⟩
    have hl := sepLoad128_btreeMem (ptr := env.sp + BitVec.ofNat 64 cfg.offB) (k := idx)
      (t := evalMemTree env st.memB) hrest.1 hv.2.1 rfl
    rw [evalMemTree, BTree.get_map, BTree.get_map] at hl
    exact hl.left.right.right

private theorem add_idx2_eq_add16 (ptr : BitVec 64) (idx : Nat) :
    ptr + BitVec.ofNat 64 (8 * (idx + 2)) = (ptr + BitVec.ofNat 64 (8 * idx)) + 16#64 := by
  have h16 : BitVec.ofNat 64 (8 * (idx + 2)) = BitVec.ofNat 64 (8 * idx) + 16#64 :=
    BitVec.ofNat_add (8 * idx) 16
  rw [h16, ← BitVec.add_assoc]

theorem sepLoad256_kspatial {cfg : KCfg} (hv : KCfgValid cfg) {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) {addr : AddrMode} {inB : Bool} {idx : Nat}
    (hr : resolveMemIdx? cfg st addr 4 = some (inB, idx)) (F : SepProp) :
    ∃ ea : BitVec 64,
      checkAddrSPAligned s addr = true ∧
      evalAddrMode s addr = (ea, none) ∧
      SepLoad128 ea (KSpatial cfg env st F)
        (evalKExpr env (readMemWord st inB (idx + 1)) ++ evalKExpr env (readMemWord st inB idx)) ∧
      SepLoad128 (ea + 16#64) (KSpatial cfg env st F)
        (evalKExpr env (readMemWord st inB (idx + 3)) ++ evalKExpr env (readMemWord st inB (idx + 2))) := by
  rcases resolveMemIdx?_sound hv hm hr with ⟨hsp, hrest⟩
  cases inB
  · simp only [Bool.false_eq_true, ↓reduceIte, readMemWord] at hrest ⊢
    let baseA := env.sp + BitVec.ofNat 64 cfg.offA
    refine ⟨_, hsp, hrest.2, ?_, ?_⟩
    · have hl := sepLoad128_btreeMem (ptr := baseA) (k := idx)
        (t := evalMemTree env st.memA) (by omega) hv.1 rfl
      rw [evalMemTree, BTree.get_map, BTree.get_map] at hl
      exact hl.left.right
    · have hl := sepLoad128_btreeMem (ptr := baseA) (k := idx + 2)
        (t := evalMemTree env st.memA) (by omega) hv.1 (add_idx2_eq_add16 baseA idx)
      rw [evalMemTree, BTree.get_map, BTree.get_map] at hl
      exact hl.left.right
  · simp only [↓reduceIte, readMemWord] at hrest ⊢
    let baseB := env.sp + BitVec.ofNat 64 cfg.offB
    refine ⟨_, hsp, hrest.2, ?_, ?_⟩
    · have hl := sepLoad128_btreeMem (ptr := baseB) (k := idx)
        (t := evalMemTree env st.memB) (by omega) hv.2.1 rfl
      rw [evalMemTree, BTree.get_map, BTree.get_map] at hl
      exact hl.left.right.right
    · have hl := sepLoad128_btreeMem (ptr := baseB) (k := idx + 2)
        (t := evalMemTree env st.memB) (by omega) hv.2.1 (add_idx2_eq_add16 baseB idx)
      rw [evalMemTree, BTree.get_map, BTree.get_map] at hl
      exact hl.left.right.right

theorem sepStore128_kspatial {cfg : KCfg} (hv : KCfgValid cfg) {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) {addr : AddrMode} {inB : Bool} {idx : Nat}
    (hr : resolveMemIdx? cfg st addr 2 = some (inB, idx)) (eLo eHi : KExpr) (F : SepProp) :
    ∃ ea : BitVec 64,
      checkAddrSPAligned s addr = true ∧
      evalAddrMode s addr = (ea, none) ∧
      SepStore128 ea (evalKExpr env eHi ++ evalKExpr env eLo) (KSpatial cfg env st F)
        (KSpatial cfg env (writeMemWord (writeMemWord st inB idx eLo) inB (idx + 1) eHi) F) := by
  rcases resolveMemIdx?_sound hv hm hr with ⟨hsp, hrest⟩
  cases inB
  · simp only [Bool.false_eq_true, ↓reduceIte] at hrest
    refine ⟨_, hsp, hrest.2, ?_⟩
    have hs := sepStore128_btreeMem (ptr := env.sp + BitVec.ofNat 64 cfg.offA) (k := idx)
      (vHi := evalKExpr env eHi) (vLo := evalKExpr env eLo)
      (t := evalMemTree env st.memA) hrest.1 hv.1 rfl
    rw [evalMemTree, ← BTree.map_set, ← BTree.map_set] at hs
    exact hs.left.right
  · simp only [↓reduceIte] at hrest
    refine ⟨_, hsp, hrest.2, ?_⟩
    have hs := sepStore128_btreeMem (ptr := env.sp + BitVec.ofNat 64 cfg.offB) (k := idx)
      (vHi := evalKExpr env eHi) (vLo := evalKExpr env eLo)
      (t := evalMemTree env st.memB) hrest.1 hv.2.1 rfl
    rw [evalMemTree, ← BTree.map_set, ← BTree.map_set] at hs
    exact hs.left.right.right

theorem sepStore256_kspatial {cfg : KCfg} (hv : KCfgValid cfg) {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) {addr : AddrMode} {inB : Bool} {idx : Nat}
    (hr : resolveMemIdx? cfg st addr 4 = some (inB, idx))
    (e1Lo e1Hi e2Lo e2Hi : KExpr) (F : SepProp) :
    let st1 := writeMemWord (writeMemWord st inB idx e1Lo) inB (idx + 1) e1Hi
    let st2 := writeMemWord (writeMemWord st1 inB (idx + 2) e2Lo) inB (idx + 3) e2Hi
    ∃ ea : BitVec 64,
      checkAddrSPAligned s addr = true ∧
      evalAddrMode s addr = (ea, none) ∧
      SepStore128 ea (evalKExpr env e1Hi ++ evalKExpr env e1Lo)
        (KSpatial cfg env st F) (KSpatial cfg env st1 F) ∧
      SepStore128 (ea + 16#64) (evalKExpr env e2Hi ++ evalKExpr env e2Lo)
        (KSpatial cfg env st1 F) (KSpatial cfg env st2 F) := by
  intro st1 st2
  rcases resolveMemIdx?_sound hv hm hr with ⟨hsp, hrest⟩
  cases inB
  · simp only [Bool.false_eq_true, ↓reduceIte] at hrest
    let baseA := env.sp + BitVec.ofNat 64 cfg.offA
    refine ⟨_, hsp, hrest.2, ?_, ?_⟩
    · have hs := sepStore128_btreeMem (ptr := baseA) (k := idx)
        (vHi := evalKExpr env e1Hi) (vLo := evalKExpr env e1Lo)
        (t := evalMemTree env st.memA) (by omega) hv.1 rfl
      rw [evalMemTree, ← BTree.map_set, ← BTree.map_set] at hs
      exact hs.left.right
    · have hs := sepStore128_btreeMem (ptr := baseA) (k := idx + 2)
        (vHi := evalKExpr env e2Hi) (vLo := evalKExpr env e2Lo)
        (t := evalMemTree env st1.memA) (by omega) hv.1 (add_idx2_eq_add16 baseA idx)
      rw [evalMemTree, ← BTree.map_set, ← BTree.map_set] at hs
      exact hs.left.right
  · simp only [↓reduceIte] at hrest
    let baseB := env.sp + BitVec.ofNat 64 cfg.offB
    refine ⟨_, hsp, hrest.2, ?_, ?_⟩
    · have hs := sepStore128_btreeMem (ptr := baseB) (k := idx)
        (vHi := evalKExpr env e1Hi) (vLo := evalKExpr env e1Lo)
        (t := evalMemTree env st.memB) (by omega) hv.2.1 rfl
      rw [evalMemTree, ← BTree.map_set, ← BTree.map_set] at hs
      exact hs.left.right.right
    · have hs := sepStore128_btreeMem (ptr := baseB) (k := idx + 2)
        (vHi := evalKExpr env e2Hi) (vLo := evalKExpr env e2Lo)
        (t := evalMemTree env st1.memB) (by omega) hv.2.1 (add_idx2_eq_add16 baseB idx)
      rw [evalMemTree, ← BTree.map_set, ← BTree.map_set] at hs
      exact hs.left.right.right

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.KeccakSymBridge

