/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Hash.Sha512
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhHooksCommon
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKeccak -- proof-setup: allow-public-import
import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealX25519 -- build-order: serialize heavy leaves (CI memory)
meta import ProofLib.ProgramReflection

/-!
# Certified FIPS 180-4 SHA-512 Table Cache for Kernel Evaluation

Provides a kernel-evaluatable SHA-512 compression implementation (`sha512CompressFast`) built on
the forced 64-bit bitwise helpers in `CompHooks0RealKeccak`, certifies all 14 rows of
`compSha512Rows` via `rfl_kernel`, and exports `sha512CompressTabled = sha512CompressState`.
-/

namespace Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealSha512

open scoped ProofLib.ProgramReflection
open CryptoGames.SHA512 (
  beU64OfBytes sha512BigSigma0 sha512BigSigma1 sha512Ch sha512CompressBlock
  sha512CompressState sha512K sha512Maj sha512Round sha512Schedule sha512SmallSigma0
  sha512SmallSigma1
)
open CryptoVerification.E2E (Sha512State sha512StateBytesLE)
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement (leBytes)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed (bytesToSha512StateLE)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed.Interp0 (bytesToNat compSha512Rows)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealKeccak (
  add64Fast add64Fast_eq and64Fast and64Fast_eq forceListBV64 forceListBV64_eq not64Fast
  not64Fast_eq rotr64Fast rotr64Fast_eq shr64Fast shr64Fast_eq withForcedBV64 withForcedBV64_eq
  withForcedNat withForcedNat_eq xor64Fast xor64Fast_eq
)

public section
set_option autoImplicit false

private theorem leBytes_bytesToNat : ∀ bs : HwBytes, leBytes bs.length (bytesToNat bs) = bs
  | [] => rfl
  | b :: bs => by
    have h1 : BitVec.ofNat 8 (b.toNat + 256 * bytesToNat bs) = b := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofNat, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt]
    have h2 : (b.toNat + 256 * bytesToNat bs) / 256 = bytesToNat bs := by
      rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt b.isLt, Nat.zero_add]
    simp only [List.length_cons, leBytes, bytesToNat, h1, h2, leBytes_bytesToNat bs]

@[expose] def beU64Fast (bs : List (BitVec 8)) : BitVec 64 :=
  match bs with
  | [b0, b1, b2, b3, b4, b5, b6, b7] =>
    withForcedNat
      (((((((b0.toNat * 256 + b1.toNat) * 256 + b2.toNat) * 256 + b3.toNat) * 256 +
        b4.toNat) * 256 + b5.toNat) * 256 + b6.toNat) * 256 + b7.toNat)
      (BitVec.ofNat 64)
  | _ => beU64OfBytes bs

private theorem beU64Fast_eq (bs : List (BitVec 8)) : beU64Fast bs = beU64OfBytes bs := by
  have step (acc : BitVec 64) (b : BitVec 8) (hacc : acc.toNat < 2 ^ 56) :
      (acc <<< 8 ||| b.zeroExtend 64).toNat = acc.toNat * 256 + b.toNat := by
    have hsh : (acc <<< 8).toNat = acc.toNat * 256 := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; exact Nat.mod_eq_of_lt (by omega)
    have hze : (b.zeroExtend 64).toNat = b.toNat := by
      rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := b.isLt; omega)
    have hand : ((acc <<< 8) &&& b.zeroExtend 64) = 0#64 := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_and, hsh, hze]; change _ = 0
      apply Nat.eq_of_testBit_eq; intro i; rw [Nat.testBit_and, Nat.zero_testBit]; by_cases hi : i < 8
      · have h1 : (acc.toNat * 256).testBit i = false := by
          rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
          simp [Nat.not_le_of_lt hi]
        rw [h1, Bool.false_and]
      · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by omega) (by omega))),
            Bool.and_false]
    rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hand, BitVec.toNat_add, hsh, hze]
    exact Nat.mod_eq_of_lt (by have := b.isLt; omega)
  unfold beU64Fast; split
  · next b0 b1 b2 b3 b4 b5 b6 b7 =>
    rw [withForcedNat_eq]
    apply BitVec.eq_of_toNat_eq; unfold beU64OfBytes; simp only [List.foldl_cons, List.foldl_nil]
    have hz : (0#64).toNat = 0 := rfl
    let a0 := 0#64
    let a1 := a0 <<< 8 ||| b0.zeroExtend 64
    let a2 := a1 <<< 8 ||| b1.zeroExtend 64
    let a3 := a2 <<< 8 ||| b2.zeroExtend 64
    let a4 := a3 <<< 8 ||| b3.zeroExtend 64
    let a5 := a4 <<< 8 ||| b4.zeroExtend 64
    let a6 := a5 <<< 8 ||| b5.zeroExtend 64
    let a7 := a6 <<< 8 ||| b6.zeroExtend 64
    have s0 := step a0 b0 (by decide)
    have s1 := step a1 b1 (by change a1.toNat < _; rw [s0, hz]; have := b0.isLt; omega)
    have s2 := step a2 b2 (by change a2.toNat < _; rw [s1, s0, hz]; have := b0.isLt; have := b1.isLt; omega)
    have s3 := step a3 b3 (by
      change a3.toNat < _; rw [s2, s1, s0, hz]
      have := b0.isLt; have := b1.isLt; have := b2.isLt; omega)
    have s4 := step a4 b4 (by
      change a4.toNat < _; rw [s3, s2, s1, s0, hz]
      have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt; omega)
    have s5 := step a5 b5 (by
      change a5.toNat < _; rw [s4, s3, s2, s1, s0, hz]
      have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt; have := b4.isLt; omega)
    have s6 := step a6 b6 (by
      change a6.toNat < _; rw [s5, s4, s3, s2, s1, s0, hz]
      have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt
      have := b4.isLt; have := b5.isLt; omega)
    have s7 := step a7 b7 (by
      change a7.toNat < _; rw [s6, s5, s4, s3, s2, s1, s0, hz]
      have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt
      have := b4.isLt; have := b5.isLt; have := b6.isLt; omega)
    change (BitVec.ofNat 64 _).toNat = (a7 <<< 8 ||| b7.zeroExtend 64).toNat
    rw [BitVec.toNat_ofNat, s7, s6, s5, s4, s3, s2, s1, s0, hz]
    have hlt : (((((((b0.toNat * 256 + b1.toNat) * 256 + b2.toNat) * 256 + b3.toNat) * 256 +
        b4.toNat) * 256 + b5.toNat) * 256 + b6.toNat) * 256 + b7.toNat) < 2 ^ 64 := by
      have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt
      have := b4.isLt; have := b5.isLt; have := b6.isLt; have := b7.isLt; omega
    rw [Nat.mod_eq_of_lt hlt]; omega
  · rfl

@[expose] def smallSigma0Fast (x : BitVec 64) : BitVec 64 :=
  xor64Fast (xor64Fast (rotr64Fast x 1) (rotr64Fast x 8)) (shr64Fast x 7)
@[expose] def smallSigma1Fast (x : BitVec 64) : BitVec 64 :=
  xor64Fast (xor64Fast (rotr64Fast x 19) (rotr64Fast x 61)) (shr64Fast x 6)
@[expose] def bigSigma0Fast (x : BitVec 64) : BitVec 64 :=
  xor64Fast (xor64Fast (rotr64Fast x 28) (rotr64Fast x 34)) (rotr64Fast x 39)
@[expose] def bigSigma1Fast (x : BitVec 64) : BitVec 64 :=
  xor64Fast (xor64Fast (rotr64Fast x 14) (rotr64Fast x 18)) (rotr64Fast x 41)
@[expose] def chFast (x y z : BitVec 64) : BitVec 64 :=
  xor64Fast (and64Fast x y) (and64Fast (not64Fast x) z)
@[expose] def majFast (x y z : BitVec 64) : BitVec 64 :=
  xor64Fast (xor64Fast (and64Fast x y) (and64Fast x z)) (and64Fast y z)

@[expose] def sha512ScheduleFast (w16 : List (BitVec 64)) : List (BitVec 64) :=
  (List.range 64).foldl (fun ws i =>
    withForcedBV64
      (add64Fast
        (add64Fast
          (add64Fast (ws.getD i 0#64) (smallSigma0Fast (ws.getD (i + 1) 0#64)))
          (ws.getD (i + 9) 0#64))
        (smallSigma1Fast (ws.getD (i + 14) 0#64)))
      fun next => ws ++ [next])
    (forceListBV64 (w16.take 16) id)

@[expose] def sha512RoundFast (st : List (BitVec 64)) (k w : BitVec 64) : List (BitVec 64) :=
  let a := st.getD 0 0#64; let b := st.getD 1 0#64
  let c := st.getD 2 0#64; let d := st.getD 3 0#64
  let e := st.getD 4 0#64; let f := st.getD 5 0#64
  let g := st.getD 6 0#64; let h := st.getD 7 0#64
  withForcedBV64
    (add64Fast (add64Fast (add64Fast (add64Fast h (bigSigma1Fast e)) (chFast e f g)) k) w)
    fun t1 =>
  let t2 := add64Fast (bigSigma0Fast a) (majFast a b c)
  withForcedBV64 (add64Fast t1 t2) fun a' =>
  withForcedBV64 (add64Fast d t1) fun e' => [a', a, b, c, e', e, f, g]

@[expose] def sha512CompressBlockFast (st : List (BitVec 64)) (block : List (BitVec 8)) : List (BitVec 64) :=
  forceListBV64 st fun st0 =>
  forceListBV64
    (sha512ScheduleFast ((List.range 16).map fun i => beU64Fast ((block.drop (8 * i)).take 8)))
    fun ws =>
  forceListBV64
    ((List.range 80).foldl (fun cur i =>
      sha512RoundFast cur (withForcedBV64 (sha512K.getD i 0#64) id) (ws.getD i 0#64)) st0)
    fun final =>
  forceListBV64 ((List.range 8).map fun i => add64Fast (st0.getD i 0#64) (final.getD i 0#64)) id

private theorem sha512CompressBlockFast_eq (st : List (BitVec 64)) (block : List (BitVec 8)) :
    sha512CompressBlockFast st block = sha512CompressBlock st block := by
  have hs0 : smallSigma0Fast = sha512SmallSigma0 := by
    funext x; unfold smallSigma0Fast sha512SmallSigma0
    simp only [xor64Fast_eq, shr64Fast_eq, rotr64Fast_eq x 1 (by decide), rotr64Fast_eq x 8 (by decide)]
  have hs1 : smallSigma1Fast = sha512SmallSigma1 := by
    funext x; unfold smallSigma1Fast sha512SmallSigma1
    simp only [xor64Fast_eq, shr64Fast_eq, rotr64Fast_eq x 19 (by decide), rotr64Fast_eq x 61 (by decide)]
  have hb0 : bigSigma0Fast = sha512BigSigma0 := by
    funext x; unfold bigSigma0Fast sha512BigSigma0
    simp only [xor64Fast_eq, rotr64Fast_eq x 28 (by decide),
      rotr64Fast_eq x 34 (by decide), rotr64Fast_eq x 39 (by decide)]
  have hb1 : bigSigma1Fast = sha512BigSigma1 := by
    funext x; unfold bigSigma1Fast sha512BigSigma1
    simp only [xor64Fast_eq, rotr64Fast_eq x 14 (by decide),
      rotr64Fast_eq x 18 (by decide), rotr64Fast_eq x 41 (by decide)]
  have hch : chFast = sha512Ch := by
    funext x y z; unfold chFast sha512Ch; simp only [xor64Fast_eq, and64Fast_eq, not64Fast_eq]
  have hmaj : majFast = sha512Maj := by
    funext x y z; unfold majFast sha512Maj; simp only [xor64Fast_eq, and64Fast_eq]
  have hsched : ∀ w16, sha512ScheduleFast w16 = sha512Schedule w16 := by
    intro w16; unfold sha512ScheduleFast sha512Schedule
    simp only [withForcedBV64_eq, forceListBV64_eq, id_eq, add64Fast_eq, hs0, hs1]
  have hround : sha512RoundFast = sha512Round := by
    funext cur k w; unfold sha512RoundFast sha512Round
    simp only [withForcedBV64_eq, add64Fast_eq, hb0, hb1, hch, hmaj]
  unfold sha512CompressBlockFast sha512CompressBlock
  simp only [withForcedBV64_eq, forceListBV64_eq, id_eq, add64Fast_eq, beU64Fast_eq, hsched, hround]

@[expose] def sha512CompressFast (st : Sha512State) (block : List (BitVec 8)) : Sha512State :=
  ⟨sha512CompressBlockFast st.toList block, by simp [sha512CompressBlockFast, forceListBV64_eq]⟩

theorem sha512CompressFast_eq (st : Sha512State) (block : List (BitVec 8)) :
    sha512CompressFast st block = sha512CompressState st block := by
  apply List.Vector.eq
  exact sha512CompressBlockFast_eq st.toList block

/-! ## `bytesToSha512StateLE` / `sha512StateBytesLE` Roundtrip & Table Certificate -/

private theorem word64_roundtrip (w : BitVec 64) :
    BitVec.ofNat 64 (bytesToNat (toLEBytes 8 w)) = w := by
  apply BitVec.eq_of_toNat_eq
  have hw := w.isLt
  simp only [toLEBytes, BitVec.extractLsb', List.ofFn_succ, List.ofFn_zero, Fin.val_zero,
    Fin.val_succ, bytesToNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

private theorem toLEBytes8_length (w : BitVec 64) : (toLEBytes 8 w).length = 8 := by
  simp [toLEBytes]

private theorem sha512StateBytesLE_length (st : Sha512State) :
    (sha512StateBytesLE st).length = 64 := by
  rcases st with ⟨ws, hws⟩
  rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try cases hws
  simp [sha512StateBytesLE, List.Vector.toList, toLEBytes]

private theorem take8_append {α : Type} {xs ys : List α} (h : xs.length = 8) :
    (xs ++ ys).take 8 = xs := by
  rcases xs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try cases h
  rfl

private theorem drop_add8_append {α : Type} {xs ys : List α} (h : xs.length = 8) (n : Nat) :
    (xs ++ ys).drop (n + 8) = ys.drop n := by
  rcases xs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try cases h
  rfl

private theorem drop8_append {α : Type} {xs ys : List α} (h : xs.length = 8) :
    (xs ++ ys).drop 8 = ys := by
  simpa using drop_add8_append h 0

theorem bytesToSha512StateLE_sha512StateBytesLE (st : Sha512State) :
    bytesToSha512StateLE (sha512StateBytesLE st) = st := by
  rcases st with ⟨ws, hws⟩
  rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try cases hws
  apply List.Vector.eq
  let b0 := toLEBytes 8 w0; let b1 := toLEBytes 8 w1
  let b2 := toLEBytes 8 w2; let b3 := toLEBytes 8 w3
  let b4 := toLEBytes 8 w4; let b5 := toLEBytes 8 w5
  let b6 := toLEBytes 8 w6; let b7 := toLEBytes 8 w7
  let flat := b0 ++ (b1 ++ (b2 ++ (b3 ++ (b4 ++ (b5 ++ (b6 ++ b7))))))
  have l0 : b0.length = 8 := toLEBytes8_length w0
  have l1 : b1.length = 8 := toLEBytes8_length w1
  have l2 : b2.length = 8 := toLEBytes8_length w2
  have l3 : b3.length = 8 := toLEBytes8_length w3
  have l4 : b4.length = 8 := toLEBytes8_length w4
  have l5 : b5.length = 8 := toLEBytes8_length w5
  have l6 : b6.length = 8 := toLEBytes8_length w6
  have l7 : b7.length = 8 := toLEBytes8_length w7
  have s0 : (flat.drop 0).take 8 = b0 := take8_append l0
  have d1 : flat.drop 8 = b1 ++ (b2 ++ (b3 ++ (b4 ++ (b5 ++ (b6 ++ b7))))) := drop8_append l0
  have s1 : (flat.drop 8).take 8 = b1 := by rw [d1]; exact take8_append l1
  have d2 : flat.drop 16 = b2 ++ (b3 ++ (b4 ++ (b5 ++ (b6 ++ b7)))) := by
    change flat.drop (8 + 8) = _; rw [drop_add8_append l0, drop8_append l1]
  have s2 : (flat.drop 16).take 8 = b2 := by rw [d2]; exact take8_append l2
  have d3 : flat.drop 24 = b3 ++ (b4 ++ (b5 ++ (b6 ++ b7))) := by
    change flat.drop (16 + 8) = _; rw [drop_add8_append l0, drop_add8_append l1, drop8_append l2]
  have s3 : (flat.drop 24).take 8 = b3 := by rw [d3]; exact take8_append l3
  have d4 : flat.drop 32 = b4 ++ (b5 ++ (b6 ++ b7)) := by
    change flat.drop (24 + 8) = _
    rw [drop_add8_append l0, drop_add8_append l1, drop_add8_append l2, drop8_append l3]
  have s4 : (flat.drop 32).take 8 = b4 := by rw [d4]; exact take8_append l4
  have d5 : flat.drop 40 = b5 ++ (b6 ++ b7) := by
    change flat.drop (32 + 8) = _
    rw [drop_add8_append l0, drop_add8_append l1, drop_add8_append l2,
      drop_add8_append l3, drop8_append l4]
  have s5 : (flat.drop 40).take 8 = b5 := by rw [d5]; exact take8_append l5
  have d6 : flat.drop 48 = b6 ++ b7 := by
    change flat.drop (40 + 8) = _
    rw [drop_add8_append l0, drop_add8_append l1, drop_add8_append l2,
      drop_add8_append l3, drop_add8_append l4, drop8_append l5]
  have s6 : (flat.drop 48).take 8 = b6 := by rw [d6]; exact take8_append l6
  have d7 : flat.drop 56 = b7 := by
    change flat.drop (48 + 8) = _
    rw [drop_add8_append l0, drop_add8_append l1, drop_add8_append l2,
      drop_add8_append l3, drop_add8_append l4, drop_add8_append l5, drop8_append l6]
  have s7 : (flat.drop 56).take 8 = b7 := by rw [d7, List.take_of_length_le (Nat.le_of_eq l7)]
  change [BitVec.ofNat 64 (bytesToNat ((flat.drop 0).take 8)),
          BitVec.ofNat 64 (bytesToNat ((flat.drop 8).take 8)),
          BitVec.ofNat 64 (bytesToNat ((flat.drop 16).take 8)),
          BitVec.ofNat 64 (bytesToNat ((flat.drop 24).take 8)),
          BitVec.ofNat 64 (bytesToNat ((flat.drop 32).take 8)),
          BitVec.ofNat 64 (bytesToNat ((flat.drop 40).take 8)),
          BitVec.ofNat 64 (bytesToNat ((flat.drop 48).take 8)),
          BitVec.ofNat 64 (bytesToNat ((flat.drop 56).take 8))] =
         [w0, w1, w2, w3, w4, w5, w6, w7]
  rw [s0, s1, s2, s3, s4, s5, s6, s7]
  dsimp only [b0, b1, b2, b3, b4, b5, b6, b7]
  simp only [word64_roundtrip]

private theorem compSha512Rows_cert :
    (compSha512Rows.all fun r =>
      decide (sha512CompressFast (bytesToSha512StateLE (leBytes 64 r.1)) (leBytes 128 r.2.1) =
        bytesToSha512StateLE (leBytes 64 r.2.2))) = true := by
  rfl_kernel

@[expose] def sha512CompressTabled (st : Sha512State) (blk : List (BitVec 8)) : Sha512State :=
  if blk.length == 128 then
    let kSt := bytesToNat (sha512StateBytesLE st)
    let kBlk := bytesToNat blk
    match compSha512Rows.find? (fun r => r.1 == kSt && r.2.1 == kBlk) with
    | some (_, _, outNat) => bytesToSha512StateLE (leBytes 64 outNat)
    | none => sha512CompressFast st blk
  else sha512CompressFast st blk

theorem sha512CompressTabled_eq_ref : sha512CompressTabled = sha512CompressState := by
  funext st blk
  unfold sha512CompressTabled
  split
  · next hblk =>
    have hblkLen : blk.length = 128 := beq_iff_eq.mp hblk
    dsimp only
    cases hfind : compSha512Rows.find?
        (fun r => r.1 == bytesToNat (sha512StateBytesLE st) && r.2.1 == bytesToNat blk) with
    | none => exact sha512CompressFast_eq st blk
    | some r =>
      rcases r with ⟨rSt, rBlk, outNat⟩
      dsimp only
      have hmem := List.mem_of_find?_eq_some hfind
      have hpred := List.find?_some hfind
      rcases Bool.and_eq_true _ _ |>.mp hpred with ⟨heqSt, heqBlk⟩
      have hrSt : rSt = bytesToNat (sha512StateBytesLE st) := beq_iff_eq.mp heqSt
      have hrBlk : rBlk = bytesToNat blk := beq_iff_eq.mp heqBlk
      have hcert := of_decide_eq_true (List.all_eq_true.mp compSha512Rows_cert _ hmem)
      dsimp only at hcert
      have hstBytes : leBytes 64 rSt = sha512StateBytesLE st := by
        rw [hrSt]
        simpa [sha512StateBytesLE_length st] using leBytes_bytesToNat (sha512StateBytesLE st)
      have hblkBytes : leBytes 128 rBlk = blk := by
        rw [hrBlk]
        simpa [hblkLen] using leBytes_bytesToNat blk
      rw [hstBytes, bytesToSha512StateLE_sha512StateBytesLE, hblkBytes] at hcert
      rw [← hcert]
      exact sha512CompressFast_eq st blk
  · exact sha512CompressFast_eq st blk

end

end Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealSha512
