/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP.StepsProcess
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
import ProofLib.Hoare.Model
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.FrozenHeap
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLift

/-!
# Encapsulation State Serialization (`B11`)

Defines `encapsStateBytes` and layout/slice/separation-logic bridges matching
`mlkem768Encaps1With` and `mlkem768Encaps2List` (`1536`B `rHat` + `512`B `e2` + `32`B `m` =
`2080`B), and proves the `B11` (`EncapsState::to_bytes`) contracts
`blk11_encaps_state_to_bytes_RO_ok`, `blk11_encaps_state_to_bytes_RW_ok`, and
`blk11_encaps_state_to_bytes_short_ok`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.EncapsStateToBytes

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase
  MlKemBlockConstOk
  MlKemPlacement
  add_off_reloc_cancel
  add_reloc_cancel
  add_zero_reloc_cancel
  mbase
  mlkemBlockPlacement_ρ
  mlkemLeaf_ok
  mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (withNonSyscallPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.FrozenHeap (
  OnlyRW
  isROPair_pointsToBytes
  onlyRW_of_isBlock
  rw_to_ro_preserve
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLift (
  mlkemBlockConstOk_withNonSyscallPreserved
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase (
  mlkemKeep
  stripExecOutside_eq_iff_of_perm_eq
  stripS_mem
  stripS_readReg32
  stripS_readReg64
  stripS_regs
  stripS_sp
  stripS_vregs
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly
  compressAndEncode
  mlkem768Encaps1With
  polyAdd
  polyInvNtt
  polyNtt
  polyToCenteredI16Bytes
  sampleMatrixWith
  samplePolyCbd2
  sampleVecCbd2
  sha3_512List
  shake256List
  toByteVec
  vecDotNtt
  zeroPoly
)

gen_block_fetches mlkem 11 mlkemMultiLib MlKemPlacement 202

/-! ## 1. `Spec.MlKem` `2080`-Byte `EncapsState` Layout & Bridges -/

/-- Exact `2080`-byte serialized `EncapsState<3, SIMD128Vector>` representation produced by
    `Spec.MlKem.mlkem768Encaps1With` and consumed by `Spec.MlKem.mlkem768Encaps2List`:
    `3 × 512` bytes of `rHat` (`1536`B) ++ `512` bytes of `e2` ++ `32` bytes of `m`. -/
@[expose] def encapsStateBytes (rHat : Array Poly) (e2 : Poly) (m : List (BitVec 8)) :
    List (BitVec 8) :=
  ((List.range 3).map fun i => polyToCenteredI16Bytes (rHat.getD i zeroPoly)).flatten ++
  polyToCenteredI16Bytes e2 ++
  m

private theorem flatten_map_pair_len {α β : Type _} (xs : List α) (f g : α → β) :
    (xs.map fun x => [f x, g x]).flatten.length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons _ tl ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons,
      List.length_nil, ih]
    omega

@[simp] theorem polyToCenteredI16Bytes_length (p : Poly) :
    (polyToCenteredI16Bytes p).length = 512 := by
  unfold polyToCenteredI16Bytes
  have h := flatten_map_pair_len (List.range 256)
    (fun i => (BitVec.ofInt 16
      (if p.getD i 0 % 3329 ≤ 1664 then ((p.getD i 0 % 3329 : Nat) : Int)
       else ((p.getD i 0 % 3329 : Nat) : Int) - 3329)).truncate 8)
    (fun i => ((BitVec.ofInt 16
      (if p.getD i 0 % 3329 ≤ 1664 then ((p.getD i 0 % 3329 : Nat) : Int)
       else ((p.getD i 0 % 3329 : Nat) : Int) - 3329)) >>> 8).truncate 8)
  simpa [List.length_range] using h

theorem encapsStateBytes_eq_append (rHat : Array Poly) (e2 : Poly) (m : List (BitVec 8)) :
    encapsStateBytes rHat e2 m =
      polyToCenteredI16Bytes (rHat.getD 0 zeroPoly) ++
      polyToCenteredI16Bytes (rHat.getD 1 zeroPoly) ++
      polyToCenteredI16Bytes (rHat.getD 2 zeroPoly) ++
      polyToCenteredI16Bytes e2 ++
      m := by
  unfold encapsStateBytes
  have hr : List.range 3 = [0, 1, 2] := by decide
  rw [hr]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.append_assoc]

@[simp] theorem encapsStateBytes_length (rHat : Array Poly) (e2 : Poly) {m : List (BitVec 8)}
    (hm : m.length = 32) :
    (encapsStateBytes rHat e2 m).length = 2080 := by
  rw [encapsStateBytes_eq_append]
  simp only [List.length_append, polyToCenteredI16Bytes_length, hm]

theorem toByteVec_eq_of_length {n : Nat} {bs : List (BitVec 8)} (h : bs.length = n) :
    (toByteVec n bs).toList = bs := by
  change ((List.range n).map fun i => bs.getD i 0#8) = bs
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

/-- Direct unfolding bridge matching `Spec.MlKem.mlkem768Encaps1With`'s `es` output to
    `encapsStateBytes`. -/
theorem mlkem768Encaps1With_eq (sampler : List (BitVec 8) → Poly)
    (hdr rand32 : List (BitVec 8)) (hhdr : 64 ≤ hdr.length) :
    mlkem768Encaps1With sampler hdr rand32 =
      let seed := hdr.take 32
      let pkHash := (hdr.drop 32).take 32
      let m := rand32.take 32
      let hashed := sha3_512List (m ++ pkHash)
      let ss := hashed.take 32
      let coins := (hashed.drop 32).take 32
      let aTrans := sampleMatrixWith sampler 3 seed false
      let rHat := (sampleVecCbd2 3 coins 0).map polyNtt
      let e1 := sampleVecCbd2 3 coins 3
      let e2 := samplePolyCbd2 (shake256List 128 (coins ++ [6#8]))
      let uVec : Array Poly := Array.ofFn (n := 3) fun ⟨i, _⟩ =>
        polyAdd (polyInvNtt (vecDotNtt 3 (aTrans.getD i #[]) rHat)) (e1.getD i zeroPoly)
      let ct1 := ((List.range 3).map fun i => compressAndEncode 10 (uVec.getD i zeroPoly)).flatten
      some (ct1, encapsStateBytes rHat e2 m, ss) := by
  have hlt : ¬(hdr.length < 64) := by omega
  unfold mlkem768Encaps1With encapsStateBytes
  simp only [hlt, ite_false]

private theorem drop_append_exact {α : Type _} {a b : List α} {k : Nat} (ha : a.length = k) :
    (a ++ b).drop k = b := by
  rw [List.drop_append, List.drop_eq_nil_of_le (by omega), ha, Nat.sub_self,
    List.nil_append, List.drop_zero]

private theorem drop_add_append {α : Type _} {a b : List α} {k : Nat}
    (ha : a.length = k) (m : Nat) :
    (a ++ b).drop (k + m) = b.drop m := by
  rw [List.drop_append, List.drop_eq_nil_of_le (by omega), ha, Nat.add_sub_cancel_left,
    List.nil_append]

private theorem take_append_exact {α : Type _} {a b : List α} {k : Nat} (ha : a.length = k) :
    (a ++ b).take k = a := by
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

/-- Slice extraction of `rHat[i]` (`i < 3`) from `encapsStateBytes`, matching
    `Spec.MlKem.mlkem768Encaps2List`. -/
theorem encapsStateBytes_rHat_slice (rHat : Array Poly) (e2 : Poly) (m : List (BitVec 8))
    (i : Nat) (hi : i < 3) :
    ((encapsStateBytes rHat e2 m).drop (512 * i)).take 512 =
      polyToCenteredI16Bytes (rHat.getD i zeroPoly) := by
  rw [encapsStateBytes_eq_append]
  have h0 : (polyToCenteredI16Bytes (rHat.getD 0 zeroPoly)).length = 512 :=
    polyToCenteredI16Bytes_length _
  have h1 : (polyToCenteredI16Bytes (rHat.getD 1 zeroPoly)).length = 512 :=
    polyToCenteredI16Bytes_length _
  have h2 : (polyToCenteredI16Bytes (rHat.getD 2 zeroPoly)).length = 512 :=
    polyToCenteredI16Bytes_length _
  match i, hi with
  | 0, _ =>
    simp only [Nat.mul_zero, List.drop_zero, List.append_assoc]
    exact take_append_exact h0
  | 1, _ =>
    simp only [Nat.mul_one, List.append_assoc]
    rw [drop_append_exact h0, take_append_exact h1]
  | 2, _ =>
    have hm2 : 512 * 2 = 512 + 512 := rfl
    rw [hm2]
    simp only [List.append_assoc]
    rw [drop_add_append h0, drop_append_exact h1, take_append_exact h2]
  | _ + 3, h => exact absurd h (by omega)

/-- Slice extraction of `e2` (`[1536..2048)`) from `encapsStateBytes`, matching
    `Spec.MlKem.mlkem768Encaps2List`. -/
theorem encapsStateBytes_e2_slice (rHat : Array Poly) (e2 : Poly) (m : List (BitVec 8)) :
    ((encapsStateBytes rHat e2 m).drop 1536).take 512 = polyToCenteredI16Bytes e2 := by
  rw [encapsStateBytes_eq_append]
  have h012 :
      (polyToCenteredI16Bytes (rHat.getD 0 zeroPoly) ++
        polyToCenteredI16Bytes (rHat.getD 1 zeroPoly) ++
        polyToCenteredI16Bytes (rHat.getD 2 zeroPoly)).length = 1536 := by
    simp only [List.length_append, polyToCenteredI16Bytes_length]
  have he2 : (polyToCenteredI16Bytes e2).length = 512 := polyToCenteredI16Bytes_length _
  rw [List.append_assoc _ (polyToCenteredI16Bytes e2) m, drop_append_exact h012,
    take_append_exact he2]

/-- Slice extraction of `m` (`[2048..2080)`) from `encapsStateBytes`, matching
    `Spec.MlKem.mlkem768Encaps2List`. -/
theorem encapsStateBytes_m_slice (rHat : Array Poly) (e2 : Poly) {m : List (BitVec 8)}
    (hm : m.length = 32) :
    ((encapsStateBytes rHat e2 m).drop 2048).take 32 = m := by
  rw [encapsStateBytes_eq_append]
  have h012e :
      (polyToCenteredI16Bytes (rHat.getD 0 zeroPoly) ++
        polyToCenteredI16Bytes (rHat.getD 1 zeroPoly) ++
        polyToCenteredI16Bytes (rHat.getD 2 zeroPoly) ++
        polyToCenteredI16Bytes e2).length = 2048 := by
    simp only [List.length_append, polyToCenteredI16Bytes_length]
  rw [drop_append_exact h012e]
  exact List.take_of_length_le (by omega)

/-- Join contiguous `1536`B `rHat` + `512`B `e2` + `32`B `m` writable slices into a single
    `2080`-byte `statePtr ↦ₛ ...` slice (matching `B03`'s `sp + 2192` stack layout). -/
theorem pointsToBytes_encapsState_join (ptr : BitVec 64)
    {rHatBytes e2Bytes mBytes : List (BitVec 8)}
    (hr : rHatBytes.length = 1536) (he : e2Bytes.length = 512) :
    ((ptr ↦ₛ rHatBytes) ∗ ((ptr + 1536#64) ↦ₛ e2Bytes) ∗ ((ptr + 2048#64) ↦ₛ mBytes)) =
      (ptr ↦ₛ (rHatBytes ++ e2Bytes ++ mBytes)) := by
  rw [List.append_assoc, pointsToBytes_append, hr, pointsToBytes_append, he]
  have h2048 : ptr + 1536#64 + BitVec.ofNat 64 512 = ptr + 2048#64 := by bv_omega
  rw [h2048]

/-- Specialize `pointsToBytes_encapsState_join` directly to `encapsStateBytes rHat e2 m`. -/
theorem pointsToBytes_encapsStateBytes_eq (ptr : BitVec 64)
    (rHat : Array Poly) (e2 : Poly) (m : List (BitVec 8)) :
    ((ptr ↦ₛ ((List.range 3).map fun i => polyToCenteredI16Bytes (rHat.getD i zeroPoly)).flatten) ∗
      ((ptr + 1536#64) ↦ₛ polyToCenteredI16Bytes e2) ∗
      ((ptr + 2048#64) ↦ₛ m)) =
      (ptr ↦ₛ encapsStateBytes rHat e2 m) := by
  have hr :
      (((List.range 3).map fun i => polyToCenteredI16Bytes (rHat.getD i zeroPoly)).flatten).length =
        1536 := by
    have hrange : List.range 3 = [0, 1, 2] := by decide
    rw [hrange]
    simp [polyToCenteredI16Bytes_length]
  exact pointsToBytes_encapsState_join ptr hr (polyToCenteredI16Bytes_length e2)

/-! ## 2. `B11` (`EncapsState::to_bytes`) Subroutine Specifications -/

structure EncapsStateToBytesArgs where
  statePtr   : BitVec 64
  outPtr     : BitVec 64
  stateBytes : List (BitVec 8)

@[expose] def EncapsStateToBytesPurePre (a : EncapsStateToBytesArgs) (s0 : State) : Prop :=
  s0.readReg64 .x0 = a.statePtr ∧
  s0.readReg64 .x1 = a.outPtr ∧
  2080 ≤ (s0.readReg64 .x2).toNat ∧
  a.stateBytes.length = 2080

/-- Zero-stack read-only `B11` (`EncapsState::<3, SIMD128Vector>::to_bytes`) contract. -/
@[expose] def mlkemEncapsStateToBytesROSpec : Spec EncapsStateToBytesArgs where
  pre := fun a s0 =>
    ⌜EncapsStateToBytesPurePre a s0⌝ ∗
    memRegion a.outPtr 2080 ∗
    (a.statePtr ↦ᵣ a.stateBytes)
  post := fun a s0 sf =>
    ⌜ProofLib.NonSyscallPreserved s0 sf ∧
      sf.readReg64 .x0 = 0xff#64 ∧
      sf.readReg32 .x0 = 0xff#32⌝ ∗
    (a.outPtr ↦ₛ a.stateBytes) ∗
    (a.statePtr ↦ᵣ a.stateBytes)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Zero-stack writable-source `B11` (`EncapsState::<3, SIMD128Vector>::to_bytes`) contract
    (matches `B03`'s stack-allocated `EncapsState` at `sp + 2192`). -/
@[expose] def mlkemEncapsStateToBytesRWSpec : Spec EncapsStateToBytesArgs where
  pre := fun a s0 =>
    ⌜EncapsStateToBytesPurePre a s0⌝ ∗
    memRegion a.outPtr 2080 ∗
    (a.statePtr ↦ₛ a.stateBytes)
  post := fun a s0 sf =>
    ⌜ProofLib.NonSyscallPreserved s0 sf ∧
      sf.readReg64 .x0 = 0xff#64 ∧
      sf.readReg32 .x0 = 0xff#32⌝ ∗
    (a.outPtr ↦ₛ a.stateBytes) ∗
    (a.statePtr ↦ₛ a.stateBytes)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Short-output-slice (`x2 < 2080`) error-return contract for `B11` (`w0 = 1`, memory/vregs
    unchanged). -/
@[expose] def mlkemEncapsStateToBytesShortSpec : Spec Unit where
  pre := fun _ s0 =>
    ⌜(s0.readReg64 .x2).toNat < 2080⌝
  post := fun _ s0 sf =>
    ⌜ProofLib.NonSyscallPreserved s0 sf ∧
      sf.mem = s0.mem ∧
      sf.vregs = s0.vregs ∧
      sf.readReg64 .x0 = 1#64 ∧
      sf.readReg32 .x0 = 1#32⌝
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-! ## 3. Bitmask Copy-Set Collapse Helpers (`260 × 8` Bytes) -/

private abbrev copyMask (old src : List (BitVec 8)) (mask : Nat) : List (BitVec 8) :=
  ByteSlice.copySet old src (fun i => mask.testBit (i / 8))

private theorem copyMask_zero (old src : List (BitVec 8)) :
    copyMask old src 0 = old := by
  unfold copyMask
  rw [ByteSlice.copySet_congr (q := fun _ => false) (fun _ _ => Nat.zero_testBit _),
    ByteSlice.copySet_false]

private theorem testBit_pow2_eq (k m : Nat) :
    (1 <<< k).testBit m = decide (m = k) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : k = m
  · subst h; simp
  · have h' : m ≠ k := Ne.symm h
    simp [h, h']

private theorem getLsbD_happend {n m : Nat} (x : BitVec n) (y : BitVec m) (i : Nat) :
    (x ++ y).getLsbD i = if i < m then y.getLsbD i else x.getLsbD (i - m) :=
  BitVec.getLsbD_append

private theorem extractLsb_pack64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) (j : Nat) (hj : j < 8) :
    (pack64 b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' (8 * j) 8 =
      match j with
      | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3
      | 4 => b4 | 5 => b5 | 6 => b6 | _ => b7 := by
  unfold pack64
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    ext k hk
    rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_extractLsb']
    repeat rw [getLsbD_happend]
    simp only [hk, decide_true, Bool.true_and]
    split_ifs <;> first | rfl | omega | (congr 1; omega)
  | _ + 8, h => exact absurd h (by omega)

private theorem write64_copyMask_pack64 {old src : List (BitVec 8)} (hlen : old.length = 2080)
    (mask off i0 i1 i2 i3 i4 i5 i6 i7 : Nat)
    (hidx : decide (off % 8 = 0 ∧ off + 8 ≤ 2080 ∧
      i0 = off ∧ i1 = off + 1 ∧ i2 = off + 2 ∧ i3 = off + 3 ∧
      i4 = off + 4 ∧ i5 = off + 5 ∧ i6 = off + 6 ∧ i7 = off + 7) = true) :
    ByteSlice.write64 (copyMask old src mask) off
      (pack64 (src.getD i0 0#8) (src.getD i1 0#8) (src.getD i2 0#8) (src.getD i3 0#8)
        (src.getD i4 0#8) (src.getD i5 0#8) (src.getD i6 0#8) (src.getD i7 0#8)) =
      copyMask old src (mask ||| (1 <<< (off / 8))) := by
  obtain ⟨hmod, hle, hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7⟩ := of_decide_eq_true hidx
  rw [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7]
  unfold copyMask ByteSlice.write64
  rw [ByteSlice.writeLE_copySet 8 old src _ off _ (by omega) (fun j hj => by
    rw [extractLsb_pack64 _ _ _ _ _ _ _ _ j hj]
    match j, hj with
    | 0, _ => simp
    | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl
    | _ + 8, h => exact absurd h (by omega))]
  apply ByteSlice.copySet_congr
  intro i _hi
  rw [Nat.testBit_or, testBit_pow2_eq]
  have hdiv : (off ≤ i ∧ i < off + 8) ↔ i / 8 = off / 8 := by omega
  by_cases h : off ≤ i ∧ i < off + 8
  · simp [h.1, h.2, hdiv.1 h]
  · have hne : i / 8 ≠ off / 8 := mt hdiv.2 h
    rcases Decidable.not_and_iff_or_not.1 h with h1 | h2
    · simp [h1, hne]
    · simp [h2, hne]

private theorem testBit_all260 :
    ∀ k, k < 260 → ((1 <<< 260) - 1).testBit k = true := by
  decide +kernel

private theorem copyMask_full {old src : List (BitVec 8)} {mask : Nat}
    (hold : old.length = 2080) (hsrc : src.length = 2080)
    (hm : decide (mask = (1 <<< 260) - 1) = true := by decide) :
    copyMask old src mask = src := by
  obtain rfl := of_decide_eq_true hm
  exact ByteSlice.copySet_all (hold.trans hsrc.symm) fun i hi =>
    testBit_all260 (i / 8) (by omega)

/-! ## 4. Proofs of `B11` Contracts -/

private theorem mlkemConstOk_map {j : Nat} {α β : Type} {spec : Spec α} {spec' : Spec β}
    (h : MlKemBlockConstOk j spec)
    (hmap : ∀ (y : β) (R : SepProp) (s0 : State),
      (s0.mem ⊨ spec'.pre y s0 ∗ R) →
      ∃ x R', (s0.mem ⊨ spec.pre x s0 ∗ R') ∧
        ∀ sf, (sf.mem ⊨ spec.post x s0 sf ∗ R') → (sf.mem ⊨ spec'.post y s0 sf ∗ R))
    (hpan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl) :
    MlKemBlockConstOk j spec' := by
  intro _
  refine subroutine_ok_map h (fun y R s0 hpre => ?_)
    (h_no_panic := fun x R' s0 sf _ hp => by
      dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec] at hp
      rw [hpan] at hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit := fun x c R' s0 sf _ he => by
      dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec] at he
      rw [hex] at he; exact not_satisfies_false_sepConj he)
    (h_oom := fun x y R R' s0 sf _ ho => by
      dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec] at ho
      rw [hoom] at ho; exact False.elim (not_satisfies_false_sepConj ho))
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec] at hpre
  rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre_spec⟩ := hpre
  obtain ⟨x, R', hpre_x, hpost_x⟩ := hmap y R s0 hpre_spec
  refine ⟨x, R', ?_, fun sf hpost => ?_⟩
  · dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec]
    rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, pure_sepConj_of_true hcl0]
    exact hpre_x
  · dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec] at hpost ⊢
    exact hpost_x sf hpost

private abbrev mlkemEncapsStateToBytesROBaseSpec : Spec EncapsStateToBytesArgs where
  pre := mlkemEncapsStateToBytesROSpec.pre
  post := fun a _s0 sf =>
    ⌜sf.readReg64 .x0 = 0xff#64 ∧ sf.readReg32 .x0 = 0xff#32⌝ ∗
    (a.outPtr ↦ₛ a.stateBytes) ∗
    (a.statePtr ↦ᵣ a.stateBytes)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem calleeSavedPreserved_trans {s0 s1 s2 : State}
    (h01 : CalleeSavedPreserved s0 s1) (h12 : CalleeSavedPreserved s1 s2) :
    CalleeSavedPreserved s0 s2 := by
  unfold CalleeSavedPreserved at *
  simp_all only [and_self]

private theorem regs_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).regs = s.regs := rfl
private theorem regs_setMem (s : State) (m : Memory) : (s.setMem m).regs = s.regs := rfl
private theorem regs_setPState (s : State) (ps : PState) : (s.setPState ps).regs = s.regs := rfl
private theorem regs_writeVReg128 (s : State) (v : BitVec 5) (val : BitVec 128) :
    (s.writeVReg128 v val).regs = s.regs := rfl

private abbrev blk11Post [MlKemPlacement] (b : BitVec 64) (a : EncapsStateToBytesArgs)
    (R : SepProp) (s0 : State) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R →
      sf.mem ⊨ (ToBaseSpec.toSpec mlkemEncapsStateToBytesROBaseSpec b).post a s0 sf ∗ R) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

private abbrev blk11Oom (b : BitVec 64) (a : EncapsStateToBytesArgs) (s0 : State) :
    State → SepProp :=
  fun sf => (ToBaseSpec.toSpec mlkemEncapsStateToBytesROBaseSpec b).onOom a s0 sf

private abbrev q128_1440 (bs : List (BitVec 8)) : BitVec 128 :=
  pack64 (bs.getD 1448 0#8) (bs.getD 1449 0#8) (bs.getD 1450 0#8) (bs.getD 1451 0#8)
    (bs.getD 1452 0#8) (bs.getD 1453 0#8) (bs.getD 1454 0#8) (bs.getD 1455 0#8) ++
  pack64 (bs.getD 1440 0#8) (bs.getD 1441 0#8) (bs.getD 1442 0#8) (bs.getD 1443 0#8)
    (bs.getD 1444 0#8) (bs.getD 1445 0#8) (bs.getD 1446 0#8) (bs.getD 1447 0#8)

private abbrev q128_1536 (bs : List (BitVec 8)) : BitVec 128 :=
  pack64 (bs.getD 1544 0#8) (bs.getD 1545 0#8) (bs.getD 1546 0#8) (bs.getD 1547 0#8)
    (bs.getD 1548 0#8) (bs.getD 1549 0#8) (bs.getD 1550 0#8) (bs.getD 1551 0#8) ++
  pack64 (bs.getD 1536 0#8) (bs.getD 1537 0#8) (bs.getD 1538 0#8) (bs.getD 1539 0#8)
    (bs.getD 1540 0#8) (bs.getD 1541 0#8) (bs.getD 1542 0#8) (bs.getD 1543 0#8)

set_option maxHeartbeats 300000 in
private theorem blk11_ro_part4 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase mlkemPl11 b) (_hbase : mlkemPl11.base = b)
    {a : EncapsStateToBytesArgs} {R : SepProp} {s0 s : State}
    (hx0 : s0.readReg64 .x0 = a.statePtr)
    (hx1 : s0.readReg64 .x1 = a.outPtr)
    (hstate_len : a.stateBytes.length = 2080)
    {out₀ : List (BitVec 8)} (hout₀ : out₀.length = 2080)
    {mask : Nat}
    (hmask : decide (mask = ((1 <<< 192) - 1) ^^^ (3 <<< 180) ^^^ (3 <<< 186)) = true := by decide)
    (hpc : s.pc = b + 520#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp)
    (hregs : s.regs = s0.regs)
    (hcs : CalleeSavedPreserved s0 s)
    (hq1 : s.readVReg128 1#5 = q128_1536 a.stateBytes)
    (hq2 : s.readVReg128 2#5 = q128_1440 a.stateBytes) :
    SepWP (mlkemPC11.rebase b) (s0.readReg64 .lr) s
      ((a.outPtr ↦ₛ copyMask out₀ a.stateBytes mask) ∗ (a.statePtr ↦ᵣ a.stateBytes))
      (blk11Post b a R s0) (blk11Oom b a s0) := by
  obtain rfl := of_decide_eq_true hmask
  have hx0' : s.readReg64 (Reg.gpr 0#5) = a.statePtr := by rw [State.readReg64, hregs]; exact hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = a.outPtr := by rw [State.readReg64, hregs]; exact hx1
  have hlr' : s.readReg64 (Reg.gpr 30#5) = s0.readReg64 .lr := by simp [State.readReg64, hregs]
  iterate 4 (
    wp_steps 16
    simp (disch := decide) only [write64_copyMask_pack64 hout₀,
      Nat.reduceDiv, Nat.reduceShiftLeft])
  wp_steps
  simp (disch := decide) only [write64_copyMask_pack64 hout₀,
    Nat.reduceDiv, Nat.reduceShiftLeft]
  rw [copyMask_full hout₀ hstate_len]
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine ⟨fun hm => ?_, by simp only [wp_norm, hsp],
    calleeSavedPreserved_trans hcs (by simp only [CalleeSavedPreserved, wp_norm, and_self])⟩
  dsimp only [ToBaseSpec.toSpec, mlkemEncapsStateToBytesROBaseSpec]
  rw [sepConj_assoc, pure_sepConj_of_true]
  · exact hm
  · exact ⟨by simp only [wp_norm], by simp only [wp_norm]⟩

set_option maxHeartbeats 300000 in
private theorem blk11_ro_part3 [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase mlkemPl11 b) (hbase : mlkemPl11.base = b)
    {a : EncapsStateToBytesArgs} {R : SepProp} {s0 s : State}
    (hx0 : s0.readReg64 .x0 = a.statePtr)
    (hx1 : s0.readReg64 .x1 = a.outPtr)
    (hstate_len : a.stateBytes.length = 2080)
    {out₀ : List (BitVec 8)} (hout₀ : out₀.length = 2080)
    {mask : Nat}
    (hmask : decide (mask = (1 <<< 124) - 1) = true := by decide)
    (hpc : s.pc = b + 264#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp)
    (hregs : s.regs = s0.regs)
    (hcs : CalleeSavedPreserved s0 s) :
    SepWP (mlkemPC11.rebase b) (s0.readReg64 .lr) s
      ((a.outPtr ↦ₛ copyMask out₀ a.stateBytes mask) ∗ (a.statePtr ↦ᵣ a.stateBytes))
      (blk11Post b a R s0) (blk11Oom b a s0) := by
  obtain rfl := of_decide_eq_true hmask
  have hx0' : s.readReg64 (Reg.gpr 0#5) = a.statePtr := by rw [State.readReg64, hregs]; exact hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = a.outPtr := by rw [State.readReg64, hregs]; exact hx1
  iterate 4 (
    wp_steps 16
    simp (disch := decide) only [write64_copyMask_pack64 hout₀,
      Nat.reduceDiv, Nat.reduceShiftLeft])
  exact blk11_ro_part4 hb hbase hx0 hx1 hstate_len hout₀
    (hpc := by simp only [wp_norm])
    (hrun := by simp only [wp_norm, hrun])
    (hsp := by simp only [wp_norm, hsp])
    (hregs := by simp only [regs_setPC, regs_setMem, regs_writeVReg128, hregs])
    (hcs := calleeSavedPreserved_trans hcs (by simp only [CalleeSavedPreserved, wp_norm, and_self]))
    (hq1 := by simp only [arm64_norm])
    (hq2 := by simp only [arm64_norm])

set_option maxHeartbeats 300000 in
private theorem blk11_ro_part2 [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase mlkemPl11 b) (hbase : mlkemPl11.base = b)
    {a : EncapsStateToBytesArgs} {R : SepProp} {s0 s : State}
    (hx0 : s0.readReg64 .x0 = a.statePtr)
    (hx1 : s0.readReg64 .x1 = a.outPtr)
    (hstate_len : a.stateBytes.length = 2080)
    {out₀ : List (BitVec 8)} (hout₀ : out₀.length = 2080)
    {mask : Nat}
    (hmask : decide (mask = (1 <<< 60) - 1) = true := by decide)
    (hpc : s.pc = b + 136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp)
    (hregs : s.regs = s0.regs)
    (hcs : CalleeSavedPreserved s0 s) :
    SepWP (mlkemPC11.rebase b) (s0.readReg64 .lr) s
      ((a.outPtr ↦ₛ copyMask out₀ a.stateBytes mask) ∗ (a.statePtr ↦ᵣ a.stateBytes))
      (blk11Post b a R s0) (blk11Oom b a s0) := by
  obtain rfl := of_decide_eq_true hmask
  have hx0' : s.readReg64 (Reg.gpr 0#5) = a.statePtr := by rw [State.readReg64, hregs]; exact hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = a.outPtr := by rw [State.readReg64, hregs]; exact hx1
  iterate 4 (
    wp_steps 8
    simp (disch := decide) only [write64_copyMask_pack64 hout₀,
      Nat.reduceDiv, Nat.reduceShiftLeft])
  exact blk11_ro_part3 hb hbase hx0 hx1 hstate_len hout₀
    (hpc := by simp only [wp_norm])
    (hrun := by simp only [wp_norm, hrun])
    (hsp := by simp only [wp_norm, hsp])
    (hregs := by simp only [regs_setPC, regs_setMem, regs_writeVReg128, hregs])
    (hcs := calleeSavedPreserved_trans hcs (by simp only [CalleeSavedPreserved, wp_norm, and_self]))

set_option maxHeartbeats 300000 in
private theorem blk11_encaps_state_to_bytes_RO_base_ok :
    MlKemBlockConstOk 11 mlkemEncapsStateToBytesROBaseSpec := by
  intro _
  refine mlkemLeaf_ok (j := 11) mlkemPC11 mlkemPl11 (spec := mlkemEncapsStateToBytesROBaseSpec)
    (h := fun b hb hbase => ?_)
  apply subroutine_ok_of_sepWP_init
  intro a R s0 hpc hrun hpre _hsp
  dsimp only [ToBaseSpec.toSpec, mlkemEncapsStateToBytesROBaseSpec,
    mlkemEncapsStateToBytesROSpec, EncapsStateToBytesPurePre] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hstate_len⟩, hspat⟩ := hpre
  have hx0' : s0.readReg64 (Reg.gpr 0#5) = a.statePtr := hx0
  have hx1' : s0.readReg64 (Reg.gpr 1#5) = a.outPtr := hx1
  have hx2' : 2080 ≤ (s0.readReg64 (Reg.gpr 2#5)).toNat := hx2
  refine ⟨memRegion a.outPtr 2080 ∗ (a.statePtr ↦ᵣ a.stateBytes), hspat, ?_⟩
  apply SepWP.memRegion_bytes a.outPtr 2080
  intro out₀ hout₀
  rw [← copyMask_zero out₀ a.stateBytes]
  wp_steps 2
  wp_if
  swap
  · exfalso
    simp only [BitVec.ule_iff_toNat_le,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *
    omega
  iterate 3 (
    wp_steps 8
    simp (disch := decide) only [write64_copyMask_pack64 hout₀,
      Nat.reduceDiv, Nat.reduceShiftLeft])
  wp_steps 6
  simp (disch := decide) only [write64_copyMask_pack64 hout₀,
    Nat.reduceDiv, Nat.reduceShiftLeft]
  exact blk11_ro_part2 hb hbase hx0 hx1 hstate_len hout₀
    (hpc := by simp only [wp_norm])
    (hrun := by simp only [wp_norm, hrun])
    (hsp := by simp only [wp_norm])
    (hregs := by simp only [regs_setPC, regs_setMem, regs_setPState, regs_writeVReg128])
    (hcs := by simp only [CalleeSavedPreserved, wp_norm, and_self])

/-- `B11` (`EncapsState::<3, SIMD128Vector>::to_bytes`) read-only contract (`0` stack)
    with `NonSyscallPreserved`. -/
theorem blk11_encaps_state_to_bytes_RO_ok :
    MlKemBlockConstOk 11 mlkemEncapsStateToBytesROSpec := by
  intro _
  exact (mlkemConstOk_map (spec' := mlkemEncapsStateToBytesROSpec)
    (mlkemBlockConstOk_withNonSyscallPreserved blk11_encaps_state_to_bytes_RO_base_ok
      (h_pre := fun mpl x R s0 h => by
        dsimp [mlkemEncapsStateToBytesROBaseSpec, mlkemEncapsStateToBytesROSpec,
          EncapsStateToBytesPurePre] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs] using h)
      (h_post := fun mpl x R s0 sf hnsp h => by
        dsimp [mlkemEncapsStateToBytesROBaseSpec, mlkemEncapsStateToBytesROSpec] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs,
          stripS_mem, stripExecOutside_eq_iff_of_perm_eq (mlkemKeep mpl) hnsp.2.1] using h))
    fun args R _s0 hpre => ⟨args, R, hpre, fun _sf hpost => by
      dsimp only [withNonSyscallPreserved, mlkemEncapsStateToBytesROBaseSpec,
        mlkemEncapsStateToBytesROSpec] at hpost ⊢
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨⟨hpost.1, hpost.2.1⟩, hpost.2.2⟩⟩)

/-- `B11` (`EncapsState::<3, SIMD128Vector>::to_bytes`) writable-source contract (`0` stack)
    with `NonSyscallPreserved` (lifted via `FrozenHeap.rw_to_ro_preserve`). -/
theorem blk11_encaps_state_to_bytes_RW_ok :
    MlKemBlockConstOk 11 mlkemEncapsStateToBytesRWSpec := by
  intro _
  simp only [subroutine_ok_iff, reaches_outcome_iff]
  intro a R s0 hpc hrun hpre hsp hL1
  dsimp only [ToBaseSpec.toSpec, MultiPlacedLib.withCodeLoaded,
    mlkemEncapsStateToBytesRWSpec] at hpre
  rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre_body⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_body
  obtain ⟨hpure, hspat⟩ := hpre_body
  have hspat' : s0.mem ⊨
      (a.statePtr ↦ₛ a.stateBytes) ∗ (memRegion a.outPtr 2080 ∗ R) :=
    Satisfies.mono (by sep_frame) hspat
  have hpair := isROPair_pointsToBytes a.statePtr a.stateBytes
  have hWf : OnlyRW (a.outPtr ↦ₛ a.stateBytes) :=
    onlyRW_of_isBlock (IsBlock.pointsToBytes _ _)
  obtain ⟨R', hpre_ro, hrecover⟩ := rw_to_ro_preserve hpair hWf hspat'
  have hcallee_pre : s0.mem ⊨
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemEncapsStateToBytesROSpec).pre a s0 ∗ R' := by
    dsimp only [MultiPlacedLib.withCodeLoaded, mlkemEncapsStateToBytesROSpec]
    rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, pure_sepConj_of_true hcl0, sepConj_assoc,
      pure_sepConj_of_true hpure]
    exact Satisfies.mono (by sep_frame) hpre_ro
  obtain ⟨sf, hsteps, hout⟩ := reaches_outcome_iff.1
    (subroutine_ok_iff.1 blk11_encaps_state_to_bytes_RO_ok a R' s0 hpc hrun hcallee_pre hsp) hL1
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [MultiPlacedLib.withCodeLoaded, mlkemEncapsStateToBytesROSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hpure_post, hpost_ro⟩ := hpost
    have hpost_wf : sf.mem ⊨
        (a.statePtr ↦ᵣ a.stateBytes) ∗ ((a.outPtr ↦ₛ a.stateBytes) ∗ R') :=
      Satisfies.mono (by sep_frame) hpost_ro
    have hpost_rw := hrecover hpure_post.1 (Satisfies.of_sep_right hpost_wf)
    dsimp only [ToBaseSpec.toSpec, MultiPlacedLib.withCodeLoaded, mlkemEncapsStateToBytesRWSpec]
    rw [sepConj_assoc, pure_sepConj_of_true hpure_post]
    exact Satisfies.mono (by sep_frame) hpost_rw
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

private abbrev mlkemEncapsStateToBytesShortBaseSpec : Spec Unit where
  pre := mlkemEncapsStateToBytesShortSpec.pre
  post := fun _ s0 sf =>
    ⌜sf.mem = s0.mem ∧
      sf.vregs = s0.vregs ∧
      sf.readReg64 .x0 = 1#64 ∧
      sf.readReg32 .x0 = 1#32⌝
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem blk11_encaps_state_to_bytes_short_base_ok :
    MlKemBlockConstOk 11 mlkemEncapsStateToBytesShortBaseSpec := by
  intro _
  refine mlkemLeaf_ok (j := 11) mlkemPC11 mlkemPl11
    (spec := mlkemEncapsStateToBytesShortBaseSpec) (h := fun b _hb _hbase => ?_)
  apply subroutine_ok_of_sepWP_init
  intro _ R s0 hpc hrun hpre _hsp
  dsimp only [ToBaseSpec.toSpec, mlkemEncapsStateToBytesShortBaseSpec,
    mlkemEncapsStateToBytesShortSpec] at hpre
  rw [satisfies_pure_sepConj] at hpre
  obtain ⟨hx2, hR⟩ := hpre
  have hx2' : (s0.readReg64 (Reg.gpr 2#5)).toNat < 2080 := hx2
  refine ⟨emp, by rwa [emp_sepConj], ?_⟩
  wp_steps 2
  wp_if
  · exfalso
    simp only [BitVec.ule_iff_toNat_le,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *
    omega
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine ⟨fun hm => ?_, by simp only [wp_norm],
    by simp only [CalleeSavedPreserved, wp_norm, and_self]⟩
  rw [emp_sepConj] at hm
  change _ ⊨ ⌜_⌝ ∗ R
  rw [pure_sepConj_of_true]
  · exact hm
  · exact ⟨rfl, rfl, by simp only [wp_norm], by simp only [wp_norm]⟩

/-- `B11` short-output-slice (`x2 < 2080`) error-return contract (`w0 = 1`)
    with `NonSyscallPreserved`. -/
theorem blk11_encaps_state_to_bytes_short_ok :
    MlKemBlockConstOk 11 mlkemEncapsStateToBytesShortSpec := by
  intro _
  exact (mlkemConstOk_map (spec' := mlkemEncapsStateToBytesShortSpec)
    (mlkemBlockConstOk_withNonSyscallPreserved blk11_encaps_state_to_bytes_short_base_ok
      (h_pre := fun mpl x R s0 h => by
        dsimp [mlkemEncapsStateToBytesShortBaseSpec, mlkemEncapsStateToBytesShortSpec] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs] using h)
      (h_post := fun mpl x R s0 sf hnsp h => by
        dsimp [mlkemEncapsStateToBytesShortBaseSpec, mlkemEncapsStateToBytesShortSpec] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs,
          stripS_mem, stripExecOutside_eq_iff_of_perm_eq (mlkemKeep mpl) hnsp.2.1] using h))
    fun u R _s0 hpre => ⟨u, R, hpre, fun _sf hpost => by
      dsimp only [withNonSyscallPreserved, mlkemEncapsStateToBytesShortBaseSpec,
        mlkemEncapsStateToBytesShortSpec] at hpost ⊢
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨⟨hpost.1, hpost.2.1⟩, hpost.2.2⟩⟩)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.EncapsStateToBytes
