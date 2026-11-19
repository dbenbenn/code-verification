/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagFastShaData0
public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagFastShaData1

/-!
# Fast `BinTree` Evaluator for `evictedSha256` and `dagNodeOk`

Replaces integer-decoded bucket scans in `evictedSha256` with depth-6 `BinTree` byte-bucket lookup
(`fastEvictedSha256`, `dagNodeFastOk`) and proves pointwise equality with `dagNodeOk`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagFastSha

open ByteSpecs (ShaState sha256IV sha256Pad chunks64 sha256With hmacWith toBEBytes)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (sha256CompressFunction shaStateBytes shaStateOfBytes)
open DY.Libsignal.Composed.Refinement (leBytes)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
  (bytesToNat compTag4 compTag4Ipad compTag4Opad compDefaultSha256 compShaMix28)
open Symbolic.BugInjection.Proofs.Common443.CompRTag
  (toBEBytes_length sha256Pad_length sha256Pad_length_mod chunks64_length
   chunks64_append64 padTail64 sha256Pad_append64 sha256With_length chunks64_padTail64_32)
open Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
  (leBytes_bytesToNat bytesToNat_leBytes shaStateBytes_shaStateOfBytes)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsShaRows
  (evictedSha256Bucket evictedSha256Rows evictedSha256)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.DefsI0 (evictedI0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.ShaMacLaws
  (FE_eq evictedSha256_length)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagTree (BinTree btGet)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagDefs
  (DagOp dagOpBytesOk dagNodeOk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagFastShaData0 (fastSubTree0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagFastShaData1 (fastSubTree1)

def fastShaTree : BinTree (List (HwBytes × HwBytes × HwBytes)) :=
  .branch fastSubTree0 fastSubTree1

def fastShaBucket (b : Nat) : List (HwBytes × HwBytes × HwBytes) :=
  (btGet 6 fastShaTree b).getD []

def fastBlkBucketIdx : HwBytes → Nat
  | [] => 0
  | b :: _ => b.toNat % 64

theorem fastBlkBucketIdx_eq (blk : HwBytes) : fastBlkBucketIdx blk = bytesToNat blk % 64 := by
  rcases blk with _ | ⟨b, bs⟩
  · rfl
  · simp [fastBlkBucketIdx, bytesToNat]; omega

def shaBucketSliceOk (lo count : Nat) : Bool :=
  (List.range count).all fun k =>
    let b := lo + k
    decide (fastShaBucket b = (evictedSha256Bucket b).map
      (fun r => (leBytes 32 r.1, leBytes 64 r.2.1, leBytes 32 r.2.2)))

private theorem shaBktSlice_0 : shaBucketSliceOk 0 16 = true := by decide +kernel
private theorem shaBktSlice_1 : shaBucketSliceOk 16 16 = true := by decide +kernel
private theorem shaBktSlice_2 : shaBucketSliceOk 32 16 = true := by decide +kernel
private theorem shaBktSlice_3 : shaBucketSliceOk 48 16 = true := by decide +kernel

private theorem fastShaBucket_of_slice {lo count : Nat} (h : shaBucketSliceOk lo count = true)
    {b : Nat} (hlo : lo ≤ b) (hhi : b < lo + count) :
    fastShaBucket b = (evictedSha256Bucket b).map
      (fun r => (leBytes 32 r.1, leBytes 64 r.2.1, leBytes 32 r.2.2)) := by
  unfold shaBucketSliceOk at h
  have hmem : b - lo ∈ List.range count := List.mem_range.mpr (by omega)
  have hk := List.all_eq_true.mp h (b - lo) hmem
  simp only [decide_eq_true_eq] at hk
  have heq : lo + (b - lo) = b := by omega
  rwa [heq] at hk

theorem fastShaBucket_eq (b : Nat) (hb : b < 64) :
    fastShaBucket b = (evictedSha256Bucket b).map
      (fun r => (leBytes 32 r.1, leBytes 64 r.2.1, leBytes 32 r.2.2)) := by
  if h0 : b < 16 then exact fastShaBucket_of_slice shaBktSlice_0 (by omega) h0
  else if h1 : b < 32 then exact fastShaBucket_of_slice shaBktSlice_1 (by omega) h1
  else if h2 : b < 48 then exact fastShaBucket_of_slice shaBktSlice_2 (by omega) h2
  else exact fastShaBucket_of_slice shaBktSlice_3 (by omega) hb

private theorem rows_in_bounds :
    (evictedSha256Rows.all fun r =>
      decide (r.1 < 2 ^ (8 * 32)) && decide (r.2.1 < 2 ^ (8 * 64))) = true := by
  decide +kernel

private theorem find?_congr_mem {α : Type} {p q : α → Bool} :
    ∀ {xs : List α}, (∀ x ∈ xs, p x = q x) → xs.find? p = xs.find? q
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.find?]
    rw [h x (.head _)]
    cases q x
    · exact find?_congr_mem (fun y hy => h y (.tail _ hy))
    · rfl

/-- Fast SHA-256 compression oracle lookup using `fastShaBucket`. -/
def fastEvictedSha256 (st blk : HwBytes) : HwBytes :=
  if st.take 4 == compTag4 || blk.take 4 == compTag4 ||
     blk.take 4 == compTag4Ipad || blk.take 4 == compTag4Opad then
    compDefaultSha256 st blk
  else if st.length == 32 && blk.length == 64 then
    match (fastShaBucket (fastBlkBucketIdx blk)).find? (fun r => r.1 == st && r.2.1 == blk) with
    | some (_, _, outBs) => outBs
    | none => compDefaultSha256 st blk
  else
    compDefaultSha256 st blk

theorem fastEvictedSha256_eq (st blk : HwBytes) :
    fastEvictedSha256 st blk = evictedSha256 st blk := by
  unfold fastEvictedSha256 evictedSha256
  split
  · rfl
  · split
    · rename_i htag hlen
      simp only [Bool.and_eq_true, beq_iff_eq] at hlen
      obtain ⟨hst, hblk⟩ := hlen
      dsimp only
      rw [fastBlkBucketIdx_eq]
      have hb : bytesToNat blk % 64 < 64 := Nat.mod_lt _ (by decide)
      rw [fastShaBucket_eq _ hb]
      let f : Nat × Nat × Nat → HwBytes × HwBytes × HwBytes :=
        fun r => (leBytes 32 r.1, leBytes 64 r.2.1, leBytes 32 r.2.2)
      let p : HwBytes × HwBytes × HwBytes → Bool :=
        fun r => r.1 == st && r.2.1 == blk
      let q : Nat × Nat × Nat → Bool :=
        fun r => r.1 == bytesToNat st && r.2.1 == bytesToNat blk
      change (match ((evictedSha256Bucket (bytesToNat blk % 64)).map f).find? p with
        | some (_, _, outBs) => outBs
        | none => compDefaultSha256 st blk) =
        (match (evictedSha256Bucket (bytesToNat blk % 64)).find? q with
        | some (_, _, outNat) => leBytes 32 outNat
        | none => compDefaultSha256 st blk)
      rw [List.find?_map]
      have hcongr : List.find? (p ∘ f) (evictedSha256Bucket (bytesToNat blk % 64)) =
          List.find? q (evictedSha256Bucket (bytesToNat blk % 64)) := by
        apply find?_congr_mem
        intro r hr
        have hmem : r ∈ evictedSha256Rows :=
          List.mem_flatMap.mpr ⟨bytesToNat blk % 64, List.mem_range.mpr hb, hr⟩
        have hbd := List.all_eq_true.mp rows_in_bounds r hmem
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hbd
        dsimp only [Function.comp_apply, f, p, q]
        have h1 : (leBytes 32 r.1 == st) = (r.1 == bytesToNat st) := by
          apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]; constructor
          · intro he; rw [← he, bytesToNat_leBytes 32 r.1 hbd.1]
          · intro he; rw [he, ← hst, leBytes_bytesToNat]
        have h2 : (leBytes 64 r.2.1 == blk) = (r.2.1 == bytesToNat blk) := by
          apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]; constructor
          · intro he; rw [← he, bytesToNat_leBytes 64 r.2.1 hbd.2]
          · intro he; rw [he, ← hblk, leBytes_bytesToNat]
        rw [h1, h2]
      rw [hcongr]
      cases List.find? q (evictedSha256Bucket (bytesToNat blk % 64)) with
      | none => rfl
      | some r => rfl
    · rfl

def fastCompress (s : ShaState) (b : HwBytes) : ShaState :=
  shaStateOfBytes (fastEvictedSha256 (shaStateBytes s) b)

theorem fastCompress_eq : fastCompress = sha256CompressFunction evictedI0 := by
  funext s b
  have hfe : sha256CompressFunction evictedI0 s b =
      shaStateOfBytes (evictedSha256 (shaStateBytes s) b) := FE_eq s b
  rw [hfe, ← fastEvictedSha256_eq]
  rfl

def bytesEq : HwBytes → HwBytes → Bool
  | [], [] => true
  | x :: xs, y :: ys =>
    match Nat.beq x.toFin.val y.toFin.val with
    | true => bytesEq xs ys
    | false => false
  | _, _ => false

private theorem nat_beq_toFin_eq (x y : BitVec 8) :
    Nat.beq x.toFin.val y.toFin.val = (x == y) := by
  apply Bool.eq_iff_iff.mpr
  simp [Nat.beq_eq, BitVec.toNat_inj]

theorem bytesEq_eq_beq : ∀ (xs ys : HwBytes), bytesEq xs ys = (xs == ys)
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    have hxy := nat_beq_toFin_eq x y
    have ih := bytesEq_eq_beq xs ys
    rw [bytesEq, hxy]
    change (match x == y with | true => bytesEq xs ys | false => false) = ((x == y) && (xs == ys))
    cases (x == y) <;> simp [ih]

def hasTag4 (t : Nat) : HwBytes → Bool
  | a :: b :: c :: d :: _ =>
    Nat.beq a.toFin.val t && Nat.beq b.toFin.val t &&
    Nat.beq c.toFin.val t && Nat.beq d.toFin.val t
  | _ => false

theorem hasTag4_eq_take4 (b0 : BitVec 8) (bs : HwBytes) :
    hasTag4 b0.toFin.val bs = (bs.take 4 == [b0, b0, b0, b0]) := by
  match bs with
  | [] => rfl
  | [a] => change false = ((a == b0) && false); simp
  | [a, b] => change false = ((a == b0) && ((b == b0) && false)); simp
  | [a, b, c] => change false = ((a == b0) && ((b == b0) && ((c == b0) && false))); simp
  | a :: b :: c :: d :: _ =>
    rw [hasTag4, nat_beq_toFin_eq, nat_beq_toFin_eq, nat_beq_toFin_eq, nat_beq_toFin_eq]
    change ((a == b0 && b == b0 && c == b0 && d == b0) =
      (a == b0 && (b == b0 && (c == b0 && (d == b0 && true)))))
    simp [Bool.and_assoc]

def xor4Stream : Nat → HwBytes → HwBytes → HwBytes → HwBytes → HwBytes
  | 0, _, _, _, _ => []
  | k + 1, s, x, y, z =>
    let (sb, s') := match s with | a :: r => (a, r) | [] => (0#8, [])
    let (xb, x') := match x with | a :: r => (a, r) | [] => (0#8, [])
    let (yb, y') := match y with | a :: r => (a, r) | [] => (0#8, [])
    let (zb, z') := match z with | a :: r => (a, r) | [] => (0#8, [])
    (sb ^^^ xb ^^^ yb ^^^ zb) :: xor4Stream k s' x' y' z'

private theorem head_pair_eq (bs : HwBytes) :
    (match bs with | a :: r => (a, r) | [] => (0#8, [])) = (bs.getD 0 0#8, bs.tail) := by
  cases bs <;> rfl

private theorem getD_tail (bs : HwBytes) (i : Nat) :
    bs.tail.getD i 0#8 = bs.getD (i + 1) 0#8 := by
  cases bs <;> rfl

private theorem xor4Stream_eq_ofFn : ∀ (n : Nat) (s x y z : HwBytes),
    xor4Stream n s x y z = List.ofFn fun i : Fin n =>
      s.getD i.val 0#8 ^^^ x.getD i.val 0#8 ^^^ y.getD i.val 0#8 ^^^ z.getD i.val 0#8
  | 0, _, _, _, _ => rfl
  | k + 1, s, x, y, z => by
    dsimp only [xor4Stream]
    rw [head_pair_eq s, head_pair_eq x, head_pair_eq y, head_pair_eq z,
      xor4Stream_eq_ofFn k, List.ofFn_succ]
    simp

private theorem getD_drop : ∀ (k i : Nat) (bs : HwBytes),
    (bs.drop k).getD i 0#8 = bs.getD (i + k) 0#8
  | 0, i, bs => by simp
  | k + 1, i, [] => by simp
  | k + 1, i, _ :: bs => by
    rw [List.drop_succ_cons, getD_drop k i bs]
    have h : i + (k + 1) = (i + k) + 1 := by omega
    rw [h]; rfl

private theorem getD_take : ∀ (k i : Nat) (bs : HwBytes),
    (bs.take k).getD i 0#8 = if i < k then bs.getD i 0#8 else 0#8
  | 0, i, _ => by simp
  | k + 1, 0, [] => by simp
  | k + 1, 0, _ :: _ => by simp
  | k + 1, i + 1, [] => by simp
  | k + 1, i + 1, _ :: bs => by
    rw [List.take_succ_cons]
    change (bs.take k).getD i 0#8 = if i + 1 < k + 1 then bs.getD i 0#8 else 0#8
    rw [getD_take k i bs]
    have h : (i + 1 < k + 1) ↔ (i < k) := by omega
    simp [h]

def fastDefaultSha256 (st blk : HwBytes) : HwBytes :=
  compTag4 ++ xor4Stream 28 (st.drop 4) blk (blk.drop 28) ((blk.drop 56).take 8)

theorem fastDefaultSha256_eq (st blk : HwBytes) :
    fastDefaultSha256 st blk = compDefaultSha256 st blk := by
  unfold fastDefaultSha256 compDefaultSha256 compShaMix28
  rw [xor4Stream_eq_ofFn]
  congr 1; apply List.ofFn_inj.mpr; funext i
  rw [getD_drop, getD_drop, getD_take, getD_drop]

def findShaRow (st blk : HwBytes) : List (HwBytes × HwBytes × HwBytes) → HwBytes
  | [] => fastDefaultSha256 st blk
  | (rst, rblk, rout) :: rs =>
    match bytesEq rst st with
    | true =>
      match bytesEq rblk blk with
      | true => rout
      | false => findShaRow st blk rs
    | false => findShaRow st blk rs

private theorem findShaRow_eq (st blk : HwBytes) :
    ∀ (rows : List (HwBytes × HwBytes × HwBytes)),
      findShaRow st blk rows =
        match rows.find? (fun r => r.1 == st && r.2.1 == blk) with
        | some (_, _, outBs) => outBs
        | none => compDefaultSha256 st blk
  | [] => fastDefaultSha256_eq st blk
  | (rst, rblk, rout) :: rs => by
    rw [findShaRow, bytesEq_eq_beq, bytesEq_eq_beq]
    cases h1 : (rst == st) <;> cases h2 : (rblk == blk) <;>
      simp [List.find?, h1, h2, findShaRow_eq st blk rs]

def fastShaCompressBytes32_64 (st blk : HwBytes) : HwBytes :=
  match hasTag4 0xd7 st || hasTag4 0xd7 blk || hasTag4 0xe1 blk || hasTag4 0x8b blk with
  | true => fastDefaultSha256 st blk
  | false =>
    let idx := match blk with | [] => 0 | b :: _ => b.toFin.val % 64
    findShaRow st blk (fastShaBucket idx)

private theorem blk_idx_eq (blk : HwBytes) :
    (match blk with | [] => 0 | b :: _ => b.toFin.val % 64) = fastBlkBucketIdx blk := by
  cases blk <;> rfl

theorem fastShaCompressBytes32_64_eq {st blk : HwBytes}
    (hst : st.length = 32) (hblk : blk.length = 64) :
    fastShaCompressBytes32_64 st blk = fastEvictedSha256 st blk := by
  unfold fastShaCompressBytes32_64 fastEvictedSha256
  have ht1 : hasTag4 0xd7 st = (st.take 4 == compTag4) := hasTag4_eq_take4 0xd7#8 st
  have ht2 : hasTag4 0xd7 blk = (blk.take 4 == compTag4) := hasTag4_eq_take4 0xd7#8 blk
  have ht3 : hasTag4 0xe1 blk = (blk.take 4 == compTag4Ipad) := hasTag4_eq_take4 0xe1#8 blk
  have ht4 : hasTag4 0x8b blk = (blk.take 4 == compTag4Opad) := hasTag4_eq_take4 0x8b#8 blk
  rw [ht1, ht2, ht3, ht4, blk_idx_eq blk]
  cases htag : (st.take 4 == compTag4 || blk.take 4 == compTag4 ||
      blk.take 4 == compTag4Ipad || blk.take 4 == compTag4Opad)
  · simp [hst, hblk, findShaRow_eq]
  · simp [fastDefaultSha256_eq]

def ivBytes32 : HwBytes :=
  [0x67#8, 0xe6#8, 0x09#8, 0x6a#8, 0x85#8, 0xae#8, 0x67#8, 0xbb#8,
   0x72#8, 0xf3#8, 0x6e#8, 0x3c#8, 0x3a#8, 0xf5#8, 0x4f#8, 0xa5#8,
   0x7f#8, 0x52#8, 0x0e#8, 0x51#8, 0x8c#8, 0x68#8, 0x05#8, 0x9b#8,
   0xab#8, 0xd9#8, 0x83#8, 0x1f#8, 0x19#8, 0xcd#8, 0xe0#8, 0x5b#8]

private theorem shaStateBytes_sha256IV : shaStateBytes sha256IV = ivBytes32 := by decide

def swapWords4 : HwBytes → HwBytes
  | a :: b :: c :: d :: rest => d :: c :: b :: a :: swapWords4 rest
  | rest => rest

private theorem swapWords4_le_eq_be : ∀ (ws : List (BitVec 32)),
    swapWords4 (ws.flatMap fun w =>
      [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8]) =
    ws.flatMap (toBEBytes 4)
  | [] => rfl
  | w :: ws => by
    change w.extractLsb' 24 8 :: w.extractLsb' 16 8 :: w.extractLsb' 8 8 :: w.extractLsb' 0 8 ::
      swapWords4 (ws.flatMap _) = toBEBytes 4 w ++ ws.flatMap (toBEBytes 4)
    rw [swapWords4_le_eq_be ws]; rfl

private theorem swapWords4_shaStateBytes (s : ShaState) :
    swapWords4 (shaStateBytes s) = s.toList.flatMap (toBEBytes 4) :=
  swapWords4_le_eq_be s.toList

def fastBe8 (lenBits : Nat) : HwBytes :=
  let b7 := BitVec.ofNat 8 lenBits
  let u1 := lenBits / 256
  let b6 := BitVec.ofNat 8 u1
  let u2 := u1 / 256
  let b5 := BitVec.ofNat 8 u2
  let u3 := u2 / 256
  let b4 := BitVec.ofNat 8 u3
  let u4 := u3 / 256
  let b3 := BitVec.ofNat 8 u4
  let u5 := u4 / 256
  let b2 := BitVec.ofNat 8 u5
  let u6 := u5 / 256
  let b1 := BitVec.ofNat 8 u6
  let b0 := BitVec.ofNat 8 (u6 / 256)
  [b0, b1, b2, b3, b4, b5, b6, b7]

private theorem extract_byte64_ofNat (n k : Nat) (hk : k < 8) :
    (BitVec.ofNat 64 n).extractLsb' (8 * k) 8 = BitVec.ofNat 8 (n / 2 ^ (8 * k)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have hd : 0 < 2 ^ (8 * k) := by positivity
  have hpow : 2 ^ 64 = 2 ^ (8 * k) * (256 * 2 ^ (64 - 8 * (k + 1))) := by
    have h1 : 256 = 2 ^ 8 := by decide
    rw [h1, ← Nat.pow_add, ← Nat.pow_add]
    congr 1; omega
  rw [hpow]
  set M := 256 * 2 ^ (64 - 8 * (k + 1))
  have hdiv : n = 2 ^ (8 * k) * (M * (n / (2 ^ (8 * k) * M))) + n % (2 ^ (8 * k) * M) := by
    rw [← Nat.mul_assoc]
    exact (Nat.div_add_mod n (2 ^ (8 * k) * M)).symm
  conv_rhs => rw [hdiv]
  rw [Nat.mul_add_div hd]
  have hm : 256 * (2 ^ (64 - 8 * (k + 1)) * (n / (2 ^ (8 * k) * M))) +
      n % (2 ^ (8 * k) * M) / 2 ^ (8 * k) =
      M * (n / (2 ^ (8 * k) * M)) + n % (2 ^ (8 * k) * M) / 2 ^ (8 * k) := by
    dsimp [M]; ring
  rw [← hm, Nat.mul_add_mod]

private theorem fastBe8_eq (lenBits : Nat) :
    fastBe8 lenBits = toBEBytes 8 (BitVec.ofNat 64 lenBits) := by
  change fastBe8 lenBits =
    [(BitVec.ofNat 64 lenBits).extractLsb' (8 * 7) 8,
     (BitVec.ofNat 64 lenBits).extractLsb' (8 * 6) 8,
     (BitVec.ofNat 64 lenBits).extractLsb' (8 * 5) 8,
     (BitVec.ofNat 64 lenBits).extractLsb' (8 * 4) 8,
     (BitVec.ofNat 64 lenBits).extractLsb' (8 * 3) 8,
     (BitVec.ofNat 64 lenBits).extractLsb' (8 * 2) 8,
     (BitVec.ofNat 64 lenBits).extractLsb' (8 * 1) 8,
     (BitVec.ofNat 64 lenBits).extractLsb' (8 * 0) 8]
  repeat rw [extract_byte64_ofNat lenBits _ (by decide)]
  unfold fastBe8
  simp only [Nat.div_div_eq_div_mul, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  rfl

def splitAt64 : Nat → HwBytes → HwBytes × HwBytes
  | 0, bs => ([], bs)
  | k + 1, b :: bs =>
    let p := splitAt64 k bs
    (b :: p.1, p.2)
  | _, [] => ([], [])

private theorem splitAt64_eq : ∀ (k : Nat) (bs : HwBytes),
    splitAt64 k bs = (bs.take k, bs.drop k)
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, b :: bs => by
    dsimp only [splitAt64]
    rw [splitAt64_eq k bs]; rfl

def foldChunks64 : Nat → HwBytes → HwBytes → HwBytes
  | 0, st, _ => st
  | fuel + 1, st, bs =>
    let p := splitAt64 64 bs
    foldChunks64 fuel (fastShaCompressBytes32_64 st p.1) p.2

private theorem fastCompress_step_bytes {s : ShaState} {st blk : HwBytes}
    (hs : shaStateBytes s = st) (hst : st.length = 32) (hblk : blk.length = 64) :
    shaStateBytes (fastCompress s blk) = fastShaCompressBytes32_64 st blk ∧
      (fastShaCompressBytes32_64 st blk).length = 32 := by
  have hfe : fastShaCompressBytes32_64 st blk = fastEvictedSha256 st blk :=
    fastShaCompressBytes32_64_eq hst hblk
  have hlen : (fastShaCompressBytes32_64 st blk).length = 32 := by
    rw [hfe, fastEvictedSha256_eq]; exact evictedSha256_length st blk
  refine ⟨?_, hlen⟩
  unfold fastCompress
  rw [hs, ← hfe]
  exact shaStateBytes_shaStateOfBytes _ hlen

private theorem foldChunks64_eq (n : Nat) : ∀ (s : ShaState) (st bs : HwBytes),
    shaStateBytes s = st → st.length = 32 → bs.length = 64 * n →
    foldChunks64 n st bs = shaStateBytes ((chunks64 bs).foldl fastCompress s) := by
  induction n with
  | zero =>
    intro s st bs hs _ hbs
    have hnil : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil
    have hc : chunks64 [] = [] := rfl
    simp [foldChunks64, hc, hs]
  | succ n ih =>
    intro s st bs hs hst hbs
    dsimp only [foldChunks64]
    rw [splitAt64_eq]
    have htake : (bs.take 64).length = 64 := by simp; omega
    have hdrop : (bs.drop 64).length = 64 * n := by simp; omega
    have hbs_eq : bs = bs.take 64 ++ bs.drop 64 := (List.take_append_drop 64 bs).symm
    have hchunks : chunks64 bs = bs.take 64 :: chunks64 (bs.drop 64) := by
      conv_lhs => rw [hbs_eq]
      exact chunks64_append64 (bs.take 64) (bs.drop 64) htake
    obtain ⟨hs', hst'⟩ := fastCompress_step_bytes hs hst htake
    rw [hchunks, List.foldl_cons]
    exact ih (fastCompress s (bs.take 64)) _ (bs.drop 64) hs' hst' hdrop

def fastShaFrom (st : HwBytes) (prefixBlocks : Nat) (m : HwBytes) : HwBytes :=
  let mLen := m.length
  let totalLen := 64 * prefixBlocks + mLen
  let zLen := (119 - mLen % 64) % 64
  let padded := m ++ (0x80#8 :: List.replicate zLen 0#8 ++ fastBe8 (8 * totalLen))
  let nBlocks := (mLen + 9 + zLen) / 64
  swapWords4 (foldChunks64 nBlocks st padded)

private theorem fastShaFrom_zero_eq (m : HwBytes) :
    fastShaFrom ivBytes32 0 m = sha256With fastCompress m := by
  unfold fastShaFrom sha256With
  dsimp only
  have hpad : m ++ (0x80#8 :: List.replicate ((119 - m.length % 64) % 64) 0#8 ++
      fastBe8 (8 * (64 * 0 + m.length))) = sha256Pad m := by
    unfold sha256Pad
    simp only [Nat.mul_zero, Nat.zero_add, fastBe8_eq]
    simp [List.append_assoc]
  rw [hpad]
  have hlen1 := sha256Pad_length m
  have hmod := sha256Pad_length_mod m
  have hlen : (sha256Pad m).length = 64 * ((m.length + 9 + (119 - m.length % 64) % 64) / 64) := by
    omega
  rw [foldChunks64_eq _ sha256IV ivBytes32 (sha256Pad m) shaStateBytes_sha256IV rfl hlen,
      swapWords4_shaStateBytes]

private theorem fastShaFrom_one_eq {blk0 m : HwBytes} (hblk0 : blk0.length = 64) :
    fastShaFrom (fastShaCompressBytes32_64 ivBytes32 blk0) 1 m =
      sha256With fastCompress (blk0 ++ m) := by
  unfold fastShaFrom sha256With
  dsimp only
  have hmmod : (64 + m.length) % 64 = m.length % 64 := by omega
  have hpad : m ++ (0x80#8 :: List.replicate ((119 - m.length % 64) % 64) 0#8 ++
      fastBe8 (8 * (64 * 1 + m.length))) = padTail64 m := by
    unfold padTail64
    simp only [Nat.mul_one, hmmod, fastBe8_eq]
    simp [List.append_assoc]
  rw [hpad]
  have hsp := sha256Pad_append64 blk0 m hblk0
  have hlen_sp := sha256Pad_length (blk0 ++ m)
  have hmod_sp := sha256Pad_length_mod (blk0 ++ m)
  have hlen_bm : (blk0 ++ m).length = 64 + m.length := by simp [hblk0]
  have hlen_pt : (blk0 ++ padTail64 m).length = 64 + (padTail64 m).length := by simp [hblk0]
  have hlen : (padTail64 m).length = 64 * ((m.length + 9 + (119 - m.length % 64) % 64) / 64) := by
    rw [hsp] at hlen_sp hmod_sp
    omega
  obtain ⟨hs1, hst1⟩ := fastCompress_step_bytes shaStateBytes_sha256IV rfl hblk0
  have hchunks : chunks64 (sha256Pad (blk0 ++ m)) = blk0 :: chunks64 (padTail64 m) := by
    rw [hsp]; exact chunks64_append64 blk0 (padTail64 m) hblk0
  rw [hchunks, List.foldl_cons,
      foldChunks64_eq _ (fastCompress sha256IV blk0) _ (padTail64 m) hs1 hst1 hlen,
      swapWords4_shaStateBytes]

def padXor64 : Nat → BitVec 8 → HwBytes → HwBytes
  | 0, _, _ => []
  | k + 1, pad, [] => List.replicate (k + 1) pad
  | k + 1, pad, b :: bs => (b ^^^ pad) :: padXor64 k pad bs

private theorem padXor64_eq : ∀ (k : Nat) (pad : BitVec 8) (bs : HwBytes),
    bs.length ≤ k →
    padXor64 k pad bs = (bs ++ List.replicate (k - bs.length) 0#8).map (· ^^^ pad)
  | 0, pad, bs, hbs => by
    have hnil : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil; rfl
  | k + 1, pad, [], _ => by
    simp [padXor64]
  | k + 1, pad, b :: bs, hbs => by
    have hbs' : bs.length ≤ k := by simp at hbs; omega
    have hsub : k + 1 - (b :: bs).length = k - bs.length := by simp
    rw [padXor64, hsub, List.cons_append, List.map_cons, padXor64_eq k pad bs hbs']

def outerPadTail32 : HwBytes :=
  0x80#8 :: List.replicate 29 0#8 ++ [0x03#8, 0x00#8]

private theorem outerPadTail32_eq {inner : HwBytes} (hinner : inner.length = 32) :
    inner ++ outerPadTail32 = padTail64 inner := by
  unfold padTail64 outerPadTail32
  rw [hinner]
  have htail : 0x80#8 :: List.replicate 29 0#8 ++ [0x03#8, 0x00#8] =
      ([0x80#8] ++ List.replicate ((119 - (64 + 32) % 64) % 64) 0#8) ++
      toBEBytes 8 (BitVec.ofNat 64 (8 * (64 + 32))) := by decide
  simpa [List.append_assoc] using congrArg (inner ++ ·) htail

def fastHmacBytes (k m : HwBytes) : HwBytes :=
  let k' := if Nat.blt 64 k.length then fastShaFrom ivBytes32 0 k else k
  let stI := fastShaCompressBytes32_64 ivBytes32 (padXor64 64 0x36#8 k')
  let inner := fastShaFrom stI 1 m
  let stO1 := fastShaCompressBytes32_64 ivBytes32 (padXor64 64 0x5c#8 k')
  let stO2 := fastShaCompressBytes32_64 stO1 (inner ++ outerPadTail32)
  swapWords4 stO2

private theorem sha256With_two_blocks_32 {kO inner : HwBytes}
    (hkO : kO.length = 64) (hinner : inner.length = 32) :
    swapWords4 (fastShaCompressBytes32_64
      (fastShaCompressBytes32_64 ivBytes32 kO) (inner ++ outerPadTail32)) =
      sha256With fastCompress (kO ++ inner) := by
  rw [outerPadTail32_eq hinner]
  have hpt_len : (padTail64 inner).length = 64 := by
    rw [← outerPadTail32_eq hinner]; simp [hinner, outerPadTail32]
  obtain ⟨hsO1, hstO1⟩ := fastCompress_step_bytes shaStateBytes_sha256IV rfl hkO
  obtain ⟨hsO2, _⟩ := fastCompress_step_bytes hsO1 hstO1 hpt_len
  unfold sha256With
  rw [sha256Pad_append64 kO inner hkO, chunks64_append64 kO (padTail64 inner) hkO,
      chunks64_padTail64_32 inner hinner, List.foldl_cons, List.foldl_cons, List.foldl_nil,
      ← hsO2, swapWords4_shaStateBytes]

theorem fastHmacBytes_eq (k m : HwBytes) :
    fastHmacBytes k m = hmacWith fastCompress k m := by
  unfold fastHmacBytes hmacWith
  dsimp only
  have hblt : Nat.blt 64 k.length = decide (64 < k.length) := by
    apply Bool.eq_iff_iff.mpr
    simp [Nat.blt, Nat.ble_eq]; omega
  rw [hblt]
  have hk' : (if decide (64 < k.length) = true then fastShaFrom ivBytes32 0 k else k) =
      (if 64 < k.length then sha256With fastCompress k else k) := by
    by_cases hk : 64 < k.length <;> simp [hk, fastShaFrom_zero_eq]
  rw [hk']
  set k' := if 64 < k.length then sha256With fastCompress k else k
  have hk'len : k'.length ≤ 64 := by
    dsimp [k']
    split
    · rw [sha256With_length]; omega
    · omega
  have h0 : (0 : BitVec 8) = 0#8 := rfl
  have h36 : (0x36 : BitVec 8) = 0x36#8 := rfl
  have h5c : (0x5c : BitVec 8) = 0x5c#8 := rfl
  rw [h0, h36, h5c]
  have hpadI := padXor64_eq 64 0x36#8 k' hk'len
  have hpadO := padXor64_eq 64 0x5c#8 k' hk'len
  set kI := (k' ++ List.replicate (64 - k'.length) 0#8).map (· ^^^ 0x36#8)
  set kO := (k' ++ List.replicate (64 - k'.length) 0#8).map (· ^^^ 0x5c#8)
  have hkI_len : kI.length = 64 := by dsimp [kI]; simp; omega
  have hkO_len : kO.length = 64 := by dsimp [kO]; simp; omega
  rw [hpadI, hpadO, fastShaFrom_one_eq hkI_len]
  exact sha256With_two_blocks_32 hkO_len (sha256With_length fastCompress (kI ++ m))

def checkSuffixNot0100 (len : Nat) (v : HwBytes) : Bool :=
  if Nat.ble 38 len then
    match v.drop (len - 2) with
    | [a, b] => !(Nat.beq a.toFin.val 1 && Nat.beq b.toFin.val 0)
    | _ => true
  else true

theorem checkSuffixNot0100_eq (v : HwBytes) :
    checkSuffixNot0100 v.length v =
      !(decide (38 ≤ v.length) && (v.drop (v.length - 2) == [0x01#8, 0x00#8])) := by
  unfold checkSuffixNot0100
  have hble : Nat.ble 38 v.length = decide (38 ≤ v.length) := by
    apply Bool.eq_iff_iff.mpr; simp [Nat.ble_eq]
  rw [hble]
  by_cases h38 : 38 ≤ v.length
  · simp only [decide_eq_true h38, ↓reduceIte, Bool.true_and]
    match v.drop (v.length - 2) with
    | [] => rfl
    | [a] =>
      change true = !((a == 0x01#8) && false); simp
    | [a, b] =>
      dsimp only
      have ha : Nat.beq a.toFin.val 1 = (a == 0x01#8) := nat_beq_toFin_eq a 0x01#8
      have hb : Nat.beq b.toFin.val 0 = (b == 0x00#8) := nat_beq_toFin_eq b 0x00#8
      rw [ha, hb]
      change (!(a == 0x01#8 && b == 0x00#8)) = (!(a == 0x01#8 && (b == 0x00#8 && true)))
      simp
    | a :: b :: _ :: _ =>
      change true = !((a == 0x01#8) && ((b == 0x00#8) && false)); simp
  · simp [h38]

def fastOpBytesOk (bytesOf : Nat → HwBytes) (id : Nat) (op : DagOp) (v : HwBytes) : Bool :=
  match op with
  | .rand _ sz => !Nat.beq sz 0
  | .lit bs => bytesEq v bs
  | .concat l r => bytesEq v (bytesOf l ++ bytesOf r)
  | .kdf a b => bytesEq v (fastHmacBytes (bytesOf a) (bytesOf b))
  | .trunc8 a => bytesEq v ((bytesOf a).take 8)
  | _ => dagOpBytesOk bytesOf id op

def fastTreeNodeOk (tree : BinTree (DagOp × HwBytes)) (bytesOf : Nat → HwBytes) (id : Nat) : Bool :=
  match btGet 13 tree id with
  | none => false
  | some (op, v) =>
    let len := v.length
    op.childrenLt id &&
    Nat.blt len 2048 &&
    fastOpBytesOk bytesOf id op v &&
    (!op.isAI || (Nat.ble 8 len && checkSuffixNot0100 len v))

private theorem fastOpBytesOk_eq {bytesOf : Nat → HwBytes} {id : Nat} {op : DagOp} {v : HwBytes}
    (hv : bytesOf id = v) :
    fastOpBytesOk bytesOf id op v = dagOpBytesOk bytesOf id op := by
  subst hv
  cases op with
  | rand ts sz => cases sz <;> rfl
  | lit bs => exact bytesEq_eq_beq _ _
  | concat l r => exact bytesEq_eq_beq _ _
  | kdf a b =>
    dsimp only [fastOpBytesOk, dagOpBytesOk]
    rw [bytesEq_eq_beq, fastHmacBytes_eq, fastCompress_eq]
  | trunc8 a => exact bytesEq_eq_beq _ _
  | _ => rfl

theorem fastTreeNodeOk_sound {tree : BinTree (DagOp × HwBytes)} {opOf : Nat → DagOp}
    {bytesOf : Nat → HwBytes} {id : Nat}
    (hop : ∀ p, btGet 13 tree id = some p → opOf id = p.1)
    (hbs : ∀ p, btGet 13 tree id = some p → bytesOf id = p.2)
    (hok : fastTreeNodeOk tree bytesOf id = true) :
    dagNodeOk opOf bytesOf id = true := by
  unfold fastTreeNodeOk at hok
  cases hget : btGet 13 tree id with
  | none => rw [hget] at hok; contradiction
  | some p =>
    rcases p with ⟨op, v⟩
    rw [hget] at hok
    dsimp only at hok
    have hop' : opOf id = op := hop (op, v) hget
    have hbs' : bytesOf id = v := hbs (op, v) hget
    have hblt : Nat.blt v.length 2048 = decide (v.length < 2048) := by
      apply Bool.eq_iff_iff.mpr; simp [Nat.blt, Nat.ble_eq]
    have hble : Nat.ble 8 v.length = decide (8 ≤ v.length) := by
      apply Bool.eq_iff_iff.mpr; simp [Nat.ble_eq]
    rw [hblt, hble, checkSuffixNot0100_eq v, fastOpBytesOk_eq hbs'] at hok
    unfold dagNodeOk
    simpa [hop', hbs'] using hok

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagFastSha
