/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Tail -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeStateEmpty.Proof -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

/-!
# Preamble Varint Loops of Empty-State `spqr::recv`

Verifies the epoch and index LEB128 varint-decoding loops and post-loop bounds checks of
`spqr::recv` on an empty state.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.InImage.DecodeStateEmpty
  (mr_cut' vecU8Tail vecArg_at_nil)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Exposing a single byte in `msg.at A` -/

/-- The remainder of `msg.at A` when byte `b` at `msg.ptr + pre.length` is focused (`msg.bytes = pre ++ b :: post`). -/
@[expose] def msgByteFrame (A : RustAlloc) (msg : VecArg) (pre post : List (BitVec 8)) : SepProp :=
  (msg.v ↦₆₄ msg.cap) ∗ ((msg.v + 8#64) ↦₆₄ msg.ptr) ∗
    ((msg.v + 16#64) ↦₆₄ BitVec.ofNat 64 msg.bytes.length) ∗
    ⌜msg.bytes.length ≤ msg.cap.toNat ∧ msg.cap.toNat < 2 ^ 63 ∧ msg.ptr ≠ 0⌝ ∗
    A.live msg.ptr msg.cap.toNat 1 ∗
    (msg.ptr ↦ₛ pre) ∗
    ((msg.ptr + BitVec.ofNat 64 pre.length + 1#64) ↦ₛ post) ∗
    memRegion (msg.ptr + BitVec.ofNat 64 msg.bytes.length) (msg.cap.toNat - msg.bytes.length)

theorem msg_expose_byte (A : RustAlloc) (msg : VecArg) (pre post : List (BitVec 8)) (b : BitVec 8)
    (off : BitVec 64) (hsplit : msg.bytes = pre ++ b :: post)
    (hoff : off = msg.ptr + BitVec.ofNat 64 pre.length) :
    msg.at A ⊢ (off ↦₈ b) ∗ msgByteFrame A msg pre post := by
  simp only [VecArg.at, vecU8At, vecHeader, msgByteFrame, sepConj_assoc, sepConj_pure_left_comm]
  refine Entails.pure_left fun hp => Entails.pure_right hp ?_
  have hcap : msg.cap ≠ 0 := by
    intro hc
    have h0 : msg.cap.toNat = 0 := by rw [hc]; rfl
    have hpos : 0 < msg.bytes.length := by rw [hsplit]; simp
    omega
  have hpts : (msg.ptr ↦ₛ msg.bytes) =
      (msg.ptr ↦ₛ pre) ∗ (off ↦₈ b) ∗ ((off + 1#64) ↦ₛ post) := by
    rw [hsplit, pointsToBytes_append, pointsToBytes_cons, ← hoff]
  simp only [hcap, ↓reduceIte, hpts, ← hoff]
  exact Entails.of_eq (by ac_rfl)

theorem msg_unexpose_byte (A : RustAlloc) (msg : VecArg) (pre post : List (BitVec 8)) (b : BitVec 8)
    (off : BitVec 64) (hsplit : msg.bytes = pre ++ b :: post)
    (hoff : off = msg.ptr + BitVec.ofNat 64 pre.length) :
    ((off ↦₈ b) ∗ msgByteFrame A msg pre post) ⊢ msg.at A := by
  simp only [VecArg.at, vecU8At, vecHeader, msgByteFrame, sepConj_assoc, sepConj_pure_left_comm]
  refine Entails.pure_left fun hp => Entails.pure_right hp ?_
  have hcap : msg.cap ≠ 0 := by
    intro hc
    have h0 : msg.cap.toNat = 0 := by rw [hc]; rfl
    have hpos : 0 < msg.bytes.length := by rw [hsplit]; simp
    omega
  have hpts : (msg.ptr ↦ₛ msg.bytes) =
      (msg.ptr ↦ₛ pre) ∗ (off ↦₈ b) ∗ ((off + 1#64) ↦ₛ post) := by
    rw [hsplit, pointsToBytes_append, pointsToBytes_cons, ← hoff]
  simp only [hcap, ↓reduceIte, hpts, ← hoff]
  exact Entails.of_eq (by ac_rfl)

/-! ## Pure bitvector and varint lemmas -/

theorem varint_out_norm (out : BitVec 64) (b : BitVec 8) (i : Nat) (hi : i < 10) :
    (BitVec.setWidth 64 b &&& 127#64) <<< (7 * i % 64) ||| out =
      out ||| (BitVec.setWidth 64 b &&& 127#64) <<< (7 * i) := by
  have hm : 7 * i % 64 = 7 * i := Nat.mod_eq_of_lt (by omega)
  rw [hm, BitVec.or_comm]

theorem list_cons_of_length_pos {α : Type} {l : List α} (h : 0 < l.length) :
    ∃ x xs, l = x :: xs := by
  cases l with
  | nil => simp at h
  | cons x xs => exact ⟨x, xs, rfl⟩

theorem nat_le_of_bv_ule {a b : Nat} (ha : a ≤ 10) (hb : b ≤ 10)
    (h : (BitVec.ofNat 64 a).ule (BitVec.ofNat 64 b) = true) : a ≤ b := by
  simp [BitVec.ule, BitVec.toNat_ofNat] at h
  omega

theorem nat_lt_of_not_bv_ule {a b : Nat} (ha : a ≤ 10) (hb : b ≤ 10)
    (h : ¬(BitVec.ofNat 64 a).ule (BitVec.ofNat 64 b) = true) : b < a := by
  simp [BitVec.ule, BitVec.toNat_ofNat] at h
  omega

theorem hb_ne_of_sxtb_tb (b : BitVec 8)
    (htb : (BitVec.zeroExtend 64
      (BitVec.truncate 32
        (BitVec.zeroExtend 64 b >>> 0 &&& 255#64 |||
          (if b.getLsbD 7 = true then (bv% (2 ^ 64 - 1)) else 0#64) &&& bv% (2 ^ 64 - 256)))).getLsbD 31 = true) :
    b &&& 0x80#8 ≠ 0#8 := by
  revert b htb; decide

theorem hb_eq_of_not_sxtb_tb (b : BitVec 8)
    (htb : ¬(BitVec.zeroExtend 64
      (BitVec.truncate 32
        (BitVec.zeroExtend 64 b >>> 0 &&& 255#64 |||
          (if b.getLsbD 7 = true then (bv% (2 ^ 64 - 1)) else 0#64) &&& bv% (2 ^ 64 - 256)))).getLsbD 31 = true) :
    b &&& 0x80#8 = 0#8 := by
  revert b htb; decide

theorem csel_rest1_min_10 {msg_len pre1_len rest1_len : Nat}
    (hlen : msg_len = 1 + pre1_len + rest1_len) (hlt : msg_len < 2 ^ 63) :
    (if (BitVec.ofNat 64 msg_len - BitVec.ofNat 64 (1 + pre1_len)).ult 10#64 = true then
      BitVec.ofNat 64 msg_len - BitVec.ofNat 64 (1 + pre1_len)
    else 10#64) = BitVec.ofNat 64 (min rest1_len 10) := by
  have h1 : 1 + pre1_len < 2 ^ 63 := by omega
  have h2 : rest1_len < 2 ^ 63 := by omega
  have hsub : BitVec.ofNat 64 msg_len - BitVec.ofNat 64 (1 + pre1_len) =
      BitVec.ofNat 64 rest1_len := by bv_omega
  rw [hsub]
  clear hsub
  by_cases h : rest1_len < 10
  · have hlt10 : (BitVec.ofNat 64 rest1_len).ult 10#64 = true := by
      simp [BitVec.ult, BitVec.toNat_ofNat]; omega
    have hmin : min rest1_len 10 = rest1_len := Nat.min_eq_left (Nat.le_of_lt h)
    simp [hlt10, hmin]
  · have hlt10 : ¬((BitVec.ofNat 64 rest1_len).ult 10#64 = true) := by
      simp [BitVec.ult, BitVec.toNat_ofNat]; omega
    have hmin : min rest1_len 10 = 10 := Nat.min_eq_right (by omega)
    simp [hlt10, hmin]

theorem rest1_nil_of_ule {version : BitVec 8} {msg_bytes pre₁ rest1 : List (BitVec 8)}
    (hmsg : msg_bytes = version :: (pre₁ ++ rest1))
    (_hlt : msg_bytes.length < 2 ^ 63)
    (hls : (BitVec.ofNat 64 msg_bytes.length).ule (BitVec.ofNat 64 (1 + pre₁.length)) = true) :
    rest1 = [] := by
  have hlen : msg_bytes.length = 1 + pre₁.length + rest1.length := by
    rw [hmsg, List.length_cons, List.length_append]
    omega
  simp [BitVec.ule, BitVec.toNat_ofNat] at hls
  have h0 : rest1.length = 0 := by omega
  exact List.eq_nil_of_length_eq_zero h0

theorem rest1_cons_of_not_ule {version : BitVec 8} {msg_bytes pre₁ rest1 : List (BitVec 8)}
    (hmsg : msg_bytes = version :: (pre₁ ++ rest1))
    (_hlt : msg_bytes.length < 2 ^ 63)
    (hls : ¬(BitVec.ofNat 64 msg_bytes.length).ule (BitVec.ofNat 64 (1 + pre₁.length)) = true) :
    ∃ b₀ rest1', rest1 = b₀ :: rest1' := by
  have hlen : msg_bytes.length = 1 + pre₁.length + rest1.length := by
    rw [hmsg, List.length_cons, List.length_append]
    omega
  simp [BitVec.ule, BitVec.toNat_ofNat] at hls
  have hpos : 0 < rest1.length := by omega
  exact list_cons_of_length_pos hpos

theorem spqrVarintAux_err_of_hi {i : Nat} {out : BitVec 64} {b : BitVec 8} {rest' : List (BitVec 8)}
    (hb : b &&& 0x80#8 ≠ 0#8) (hend : i + 1 = 10 ∨ rest' = []) :
    spqrVarintAux i out (b :: rest') = none := by
  rw [spqrVarintAux]
  simp only [hb, ↓reduceIte, maxVarintBytes]
  rcases hend with h10 | rfl
  · simp [h10]
  · by_cases h10 : i + 1 = 10 <;> simp [h10, spqrVarintAux]

theorem spqrVarintAux_ok_of_lo {i : Nat} {out : BitVec 64} {b : BitVec 8} {rest' : List (BitVec 8)}
    (hb : b &&& 0x80#8 = 0#8) :
    spqrVarintAux i out (b :: rest') =
      some (out ||| ((b &&& 0x7F#8).zeroExtend 64 <<< (7 * i)), rest') := by
  rw [spqrVarintAux]
  simp [hb]

theorem spqrVarintAux_step_of_hi {i : Nat} {out : BitVec 64} {b : BitVec 8} {rest' : List (BitVec 8)}
    (hb : b &&& 0x80#8 ≠ 0#8) (hi : i + 1 < 10) :
    spqrVarintAux i out (b :: rest') =
      spqrVarintAux (i + 1) (out ||| ((b &&& 0x7F#8).zeroExtend 64 <<< (7 * i))) rest' := by
  conv => lhs; rw [spqrVarintAux]
  have hne : i + 1 ≠ maxVarintBytes := by unfold maxVarintBytes; omega
  simp [hb, hne]

theorem index_bounds_ne {msg_len pre1_len j : Nat}
    (h1 : 1 ≤ pre1_len) (hlen : pre1_len + j + 2 ≤ msg_len) (hlt : msg_len < 2 ^ 63) :
    BitVec.ofNat 64 (msg_len - 2) ≠ BitVec.ofNat 64 (pre1_len - 1 + j) := by
  bv_omega

theorem varint_end_of_ge {j : Nat} {rest1 pre2 rest' : List (BitVec 8)} {b : BitVec 8}
    (hj : j < 10) (hrest1 : rest1 = pre2 ++ b :: rest') (hpre2 : pre2.length = j)
    (hge : min rest1.length 10 ≤ j + 1) :
    j + 1 = 10 ∨ rest' = [] := by
  have hlen : rest1.length = j + 1 + rest'.length := by
    rw [hrest1, List.length_append, List.length_cons, hpre2]; omega
  by_cases h10 : j + 1 = 10
  · exact Or.inl h10
  · right
    have h0 : rest'.length = 0 := by omega
    exact List.eq_nil_of_length_eq_zero h0

theorem varint_cont_of_lt {j : Nat} {rest1 pre2 rest' : List (BitVec 8)} {b : BitVec 8}
    (hrest1 : rest1 = pre2 ++ b :: rest') (hpre2 : pre2.length = j)
    (hlt : j + 1 < min rest1.length 10) :
    j + 1 < 10 ∧ ∃ b' rest'', rest' = b' :: rest'' := by
  have hlen : rest1.length = j + 1 + rest'.length := by
    rw [hrest1, List.length_append, List.length_cons, hpre2]; omega
  refine ⟨by omega, ?_⟩
  cases rest' with
  | nil => simp [List.length_nil] at hlen; omega
  | cons b' rest'' => exact ⟨b', rest'', rfl⟩

/-! ## Post-index check (`+252 .. +272`, `0x54728 .. 0x5473c`) -/

end CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty
