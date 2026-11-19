/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Math -- proof-setup: allow-public-import

/-!
# Equivalence of `Sha256Math.sha256CompressState` and `LibsignalSpqrV1.sha256Compress`

Proves functional extensionality (`sha256CompressState = CryptoVerification.LibsignalSpqrV1.sha256Compress`)
between the untrusted `Sha256Ref` block-compression adapter verified against the compiled machine
code in `CryptoSha256` and the FIPS 180-4 reference compression function in
`LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoSha256.SpqrBridge

open CryptoGames.HMAC (ShaState)
open CryptoVerification.LibsignalSpqrV1
  (K256 be32 bigS0 bigS1 schedule sha256Compress smallS0 smallS1)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Ref
  (beU32OfBytes sha256BigSigma0 sha256BigSigma1 sha256Ch sha256CompressBlock sha256K sha256Maj
   sha256Round sha256Schedule sha256SmallSigma0 sha256SmallSigma1)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Math (sha256CompressState)

private theorem word_add_rev4 (a b c d : BitVec 32) :
    d + c + b + a = a + b + c + d := by
  bv_omega

private theorem getElem!_list_eq_getD (xs : List (BitVec 32)) (i : Nat) :
    xs[i]! = xs.getD i 0#32 := by
  by_cases h : i < xs.length
  · rw [getElem!_pos xs i h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    rfl
  · have hge : xs.length ≤ i := Nat.le_of_not_lt h
    rw [getElem!_neg xs i h, List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
    rfl

private theorem getElem!_array_eq_getD_toList (w : Array (BitVec 32)) (i : Nat) :
    w[i]! = w.toList.getD i 0#32 := by
  by_cases h : i < w.size
  · have h' : i < w.toList.length := by simpa using h
    rw [getElem!_pos w i h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h']
    rfl
  · have h' : ¬ i < w.toList.length := by simpa using h
    have hge : w.toList.length ≤ i := Nat.le_of_not_lt h'
    rw [getElem!_neg w i h, List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
    rfl

private theorem foldl_push_toList {β : Type} (f : β → BitVec 32) :
    ∀ (xs : List β) (acc : Array (BitVec 32)),
      (xs.foldl (fun w x => w.push (f x)) acc).toList = acc.toList ++ xs.map f
  | [], acc => by simp
  | x :: xs, acc => by
    rw [List.foldl_cons, foldl_push_toList f xs (acc.push (f x)), Array.toList_push,
      List.append_assoc, List.singleton_append, List.map_cons]

private theorem schedule_step_loop :
    ∀ (idxs : List Nat) (w : Array (BitVec 32)),
      (idxs.foldl (fun (w : Array (BitVec 32)) i =>
        w.push (smallS1 w[(16 + i) - 2]! + w[(16 + i) - 7]! +
          smallS0 w[(16 + i) - 15]! + w[(16 + i) - 16]!)) w).toList =
      idxs.foldl (fun (ws : List (BitVec 32)) i =>
        ws ++ [ws.getD i 0#32 + sha256SmallSigma0 (ws.getD (i + 1) 0#32) +
          ws.getD (i + 9) 0#32 + sha256SmallSigma1 (ws.getD (i + 14) 0#32)]) w.toList
  | [], _ => rfl
  | i :: idxs, w => by
    simp only [List.foldl_cons]
    rw [schedule_step_loop idxs]
    congr 1
    simp only [Array.toList_push, getElem!_array_eq_getD_toList,
      show (16 + i) - 2 = i + 14 by omega,
      show (16 + i) - 7 = i + 9 by omega,
      show (16 + i) - 15 = i + 1 by omega,
      show (16 + i) - 16 = i by omega]
    congr 1
    congr 1
    exact word_add_rev4 _ _ _ _

private theorem schedule_toList_eq (blk : List (BitVec 8)) :
    (schedule blk).toList =
      sha256Schedule ((List.range 16).map fun i => beU32OfBytes ((blk.drop (4 * i)).take 4)) := by
  unfold schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.reduceSub, Nat.reduceAdd, Nat.add_one_sub_one, Nat.div_one,
    List.forIn_pure_yield_eq_foldl, pure_bind, Id.run_pure,
    List.range'_eq_map_range, List.foldl_map, Nat.zero_add]
  rw [schedule_step_loop, foldl_push_toList]
  simp only [sha256Schedule, List.nil_append]
  refine congrArg (fun init => (List.range 48).foldl _ init) ?_
  have hbe : be32 = beU32OfBytes := rfl
  rw [hbe]
  have hlen : ((List.range 16).map fun i => beU32OfBytes ((blk.drop (4 * i)).take 4)).length = 16 := by
    simp
  exact (List.take_of_length_le (Nat.le_of_eq hlen)).symm

private abbrev State8 :=
  BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32

private def state8ToList (s : State8) : List (BitVec 32) :=
  [s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2.1, s.2.2.2.2.2.2.1, s.2.2.2.2.2.2.2]

private def spqrRoundStep (w : Array (BitVec 32)) (t : Nat) (s : State8) : State8 :=
  let a := s.1; let b := s.2.1; let c := s.2.2.1; let d := s.2.2.2.1
  let e := s.2.2.2.2.1; let f := s.2.2.2.2.2.1; let g := s.2.2.2.2.2.2.1; let h := s.2.2.2.2.2.2.2
  let t1 := h + bigS1 e + ((e &&& f) ^^^ (~~~e &&& g)) + K256[t]! + w[t]!
  let t2 := bigS0 a + ((a &&& b) ^^^ (a &&& c) ^^^ (b &&& c))
  (t1 + t2, a, b, c, d + t1, e, f, g)

private theorem round_loop_eq (w : Array (BitVec 32)) :
    ∀ (idxs : List Nat) (s : State8),
      state8ToList (idxs.foldl (fun st t => spqrRoundStep w t st) s) =
        idxs.foldl (fun cur t =>
          sha256Round cur (sha256K.getD t 0#32) (w.toList.getD t 0#32)) (state8ToList s)
  | [], _ => rfl
  | t :: idxs, (a, b, c, d, e, f, g, h) => by
    simp only [List.foldl_cons]
    rw [round_loop_eq w idxs]
    refine congrArg (fun init => idxs.foldl _ init) ?_
    simp only [spqrRoundStep, state8ToList, sha256Round,
      getElem!_list_eq_getD, getElem!_array_eq_getD_toList]
    rfl

theorem sha256CompressState_apply_eq (H : ShaState) (blk : List (BitVec 8)) :
    sha256CompressState H blk = sha256Compress H blk := by
  match H with
  | ⟨[h0, h1, h2, h3, h4, h5, h6, h7], hhL⟩ =>
  have hhL' : hhL = rfl := Subsingleton.elim _ _
  subst hhL'
  apply List.Vector.eq
  have hspqr : (sha256Compress ⟨[h0, h1, h2, h3, h4, h5, h6, h7], rfl⟩ blk).toList =
      let out := state8ToList ((List.range 64).foldl (fun st t => spqrRoundStep (schedule blk) t st)
        (h0, h1, h2, h3, h4, h5, h6, h7))
      (List.Vector.ofFn fun i : Fin 8 =>
        [h0, h1, h2, h3, h4, h5, h6, h7][i.val]! + out[i.val]!).toList := by
    unfold sha256Compress
    simp only [List.Vector.toList_mk, getElem!_list_eq_getD, List.getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.reduceAdd, Nat.add_one_sub_one, Nat.div_one,
      List.forIn_pure_yield_eq_foldl, pure_bind, Id.run_pure,
      List.range'_eq_map_range, List.foldl_map, Nat.zero_add,
      state8ToList, spqrRoundStep]
  rw [hspqr]
  change sha256CompressBlock [h0, h1, h2, h3, h4, h5, h6, h7] blk = _
  simp only [sha256CompressBlock, ← schedule_toList_eq blk]
  have hinit : [h0, h1, h2, h3, h4, h5, h6, h7] = state8ToList (h0, h1, h2, h3, h4, h5, h6, h7) := rfl
  conv_lhs => rw [hinit, ← round_loop_eq (schedule blk) (List.range 64) (h0, h1, h2, h3, h4, h5, h6, h7)]
  generalize ((List.range 64).foldl (fun st t => spqrRoundStep (schedule blk) t st)
    (h0, h1, h2, h3, h4, h5, h6, h7)) = sFinal
  rcases sFinal with ⟨a, b, c, d, e, f, g, h⟩
  simp [state8ToList, List.Vector.toList_ofFn, List.ofFn, Fin.foldr, Fin.foldr.loop,
    List.range, List.range.loop]

theorem sha256CompressState_eq_spqrSha256Compress :
    sha256CompressState = sha256Compress := by
  funext H blk
  exact sha256CompressState_apply_eq H blk

end LibsignalBinary.Proofs.HookDischarge.CryptoSha256.SpqrBridge
