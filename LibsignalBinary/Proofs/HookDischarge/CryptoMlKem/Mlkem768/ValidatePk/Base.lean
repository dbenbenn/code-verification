/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.GenPlacedFetches
public import ProofLib.ProgramReflection
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public meta import ProofLib.ProgramReflection
public meta import ProofLib.GenDecodes
public meta import ProofLib.GenPlacedFetches
import ProofLib.SepLogic.WP.StepsProcess
import ProofLib.SepLogic.WPFrozen

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Base

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open ProofLib.ProgramReflection (WordTree)
open CryptoVerification.LibsignalSpqrV1 (MlKem Bytes)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
  (MlKemPlacement mlkemMpl MlKemBlockOk MlKemBlockConstOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
  (mlkemBcmpRW1ROSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec
  (mlkemQ byteDecodeRaw bytesToBits mlkem768ValidPk mlkem768Incremental)

/-! ## 1. Block 21 (`validate_pk_bytes`) `PlacedLib` & `WordTree` Setup -/

@[expose] def blkLib21 : PlacedLib := mlkemMultiLib.blockLib 21
@[expose] def blkPl21 [MlKemPlacement] : Placement := mlkemMultiLib.blockPlacement mlkemMpl 21
theorem blkPlaceable21 [MlKemPlacement] : blkLib21.Placeable blkPl21 :=
  mlkemMultiLib.placeable_blockLib (by decide) MlKemPlacement.placeable
@[expose] def blkPC21 [MlKemPlacement] : Program := blkLib21.program blkPl21
@[expose] def blkProg21 : Program := { code := blkLib21.text.code, symbols := blkLib21.text.symbols }
@[expose] def blkTree21 : WordTree := word_tree_of% blkProg21
theorem blk21_code_eq : blkLib21.text.code = blkTree21.toBytes := by rfl_kernel
theorem blk21_tree_size : blkTree21.checkSize? = some 530 := by rfl_kernel

/-! ## 2. Two-RW `bcmp` Lifting from `mlkemBcmpRW1ROSpec` -/

/-- `bcmp` contract when both slices `p` and `q` are owned read-write (`↦ₛ`). -/
@[expose] def mlkemBcmpRW2Spec :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) where
  pre := fun (p, q, bs, cs) s0 =>
    ⌜s0.readReg64 .x0 = p ∧
      s0.readReg64 .x1 = q ∧
      (s0.readReg64 .x2).toNat = bs.length ∧
      cs.length = bs.length ∧
      bs.length < 2 ^ 64⌝ ∗
      (p ↦ₛ bs) ∗ (q ↦ₛ cs)
  post := fun (p, q, bs, cs) s0 sf =>
    ⌜ProofLib.NonSyscallPreserved s0 sf ∧
      sf.mem = s0.mem ∧
      sf.vregs = s0.vregs ∧
      (sf.readReg32 .x0 = 0#32 ↔ bs = cs)⌝ ∗
      (p ↦ₛ bs) ∗ (q ↦ₛ cs)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

theorem mlkemBcmpRW1RO_simulates_RW2 :
    SpecSimulates mlkemBcmpRW1ROSpec mlkemBcmpRW2Spec := by
  refine SpecSimulates.of_map ?_
  intro ⟨p, q, bs, cs⟩ R s0 hm
  refine ⟨(p, q, bs, cs), R, ?_, ?_⟩
  · dsimp only [mlkemBcmpRW2Spec] at hm
    dsimp only [mlkemBcmpRW1ROSpec]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    rcases hm with ⟨hpure, hm⟩
    refine ⟨hpure, ?_⟩
    rw [← sepConj_assoc, sepConj_comm (p ↦ₛ bs) (q ↦ₛ cs), sepConj_assoc] at hm
    have hm2 := Satisfies.pointsToBytes_to_ro hm
    rwa [← sepConj_assoc, sepConj_comm (q ↦ᵣ cs) (p ↦ₛ bs), sepConj_assoc] at hm2
  · intro sf _ _ hpost
    dsimp only [mlkemBcmpRW1ROSpec] at hpost
    dsimp only [mlkemBcmpRW2Spec] at hm ⊢
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hpure, _⟩
    have hmem : sf.mem = s0.mem := hpure.2.1
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
    have hm_sf : sf.mem ⊨ (p ↦ₛ bs) ∗ (q ↦ₛ cs) ∗ R := hmem ▸ hm.2
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, hm_sf⟩

theorem mlkemBcmpRW2_of_rw1ro (h : MlKemBlockConstOk 30 mlkemBcmpRW1ROSpec) :
    MlKemBlockConstOk 30 mlkemBcmpRW2Spec := by
  intro _
  exact (mlkemBcmpRW1RO_simulates_RW2.withCodeLoaded mlkemMultiLib mlkemMpl).subroutine_ok h

/-! ## 3. Core & Hook-Shaped Contracts for `validate_pk_bytes` (`B21`) -/

/-- Prepend `MlKemRoOk mpl s0.mem` to a `Spec`'s precondition. -/
@[expose] def withMlKemRoOk {α : Type} (mpl : MultiPlacement) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => ⌜MlKemRoOk mpl s0.mem⌝ ∗ spec.pre x s0 }

/-- Tight-stack (`5824 = 4784 + 1040` bytes) core contract for `B21` (`validate_pk_bytes`). -/
@[expose] def mlkemValidatePkCoreSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) where
  pre := fun (hdrA, hdr, ekA, ek) s0 =>
    ⌜s0.readReg64 .x0 = hdrA ∧
      (s0.readReg64 .x1).toNat = hdr.length ∧
      s0.readReg64 .x2 = ekA ∧
      (s0.readReg64 .x3).toNat = ek.length ∧
      MlKemRoOk mpl s0.mem⌝ ∗
      (hdrA ↦ₛ hdr) ∗ (ekA ↦ₛ ek) ∗ stackAt s0.sp 5824
  post := fun (hdrA, hdr, ekA, ek) s0 sf =>
    ⌜ProofLib.NonSyscallPreserved s0 sf ∧
      ((sf.readReg64 .x0).setWidth 8 = 0xff#8 ↔
        mlkem768Incremental.validPkBytes hdr ek = true)⌝ ∗
      (hdrA ↦ₛ hdr) ∗ (ekA ↦ₛ ek) ∗ stackAt s0.sp 5824
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Polymorphic caller-struct projection spec matching `Hooks.mlkemValidatePkSpec mlkem768Incremental`
    by `rfl` when instantiated with `MlkemValidatePkCall` projections. -/
@[expose] def mlkemValidatePkProjSpec {C : Type}
    (hdrA : C → BitVec 64) (hdr : C → List (BitVec 8))
    (ekA : C → BitVec 64) (ek : C → List (BitVec 8)) : Spec C where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = hdrA x ∧ (s.readReg64 .x1).toNat = (hdr x).length ∧
      s.readReg64 .x2 = ekA x ∧ (s.readReg64 .x3).toNat = (ek x).length⌝ ∗
      (hdrA x ↦ₛ hdr x) ∗ (ekA x ↦ₛ ek x) ∗ stackAt s.sp extHookStack
  post := fun x s0 sf =>
    ⌜((sf.readReg64 .x0).setWidth 8 = 0xff#8 ↔
        mlkem768Incremental.validPkBytes (hdr x) (ek x) = true) ∧
      sf.trace = s0.trace⌝ ∗
      (hdrA x ↦ₛ hdr x) ∗ (ekA x ↦ₛ ek x) ∗ stackAt s0.sp extHookStack

theorem mlkemValidatePkCore_simulates_proj {C : Type}
    (hdrA : C → BitVec 64) (hdr : C → List (BitVec 8))
    (ekA : C → BitVec 64) (ek : C → List (BitVec 8)) (mpl : MultiPlacement) :
    SpecSimulates (mlkemValidatePkCoreSpec mpl)
      (withMlKemRoOk mpl (keepsFs (mlkemValidatePkProjSpec hdrA hdr ekA ek))) := by
  refine SpecSimulates.of_map ?_
  intro y R s0 hm
  dsimp only [withMlKemRoOk, keepsFs, mlkemValidatePkProjSpec] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hro, hm⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hx0, hx1, hx2, hx3⟩, hm⟩
  rw [stackAt_shrink s0.sp extHookStack 5824 (by decide)] at hm
  set slack := memRegion (s0.sp - BitVec.ofNat 64 extHookStack) (extHookStack - 5824)
  refine ⟨(hdrA y, hdr y, ekA y, ek y), slack ∗ R, ?_, ?_⟩
  · dsimp only [mlkemValidatePkCoreSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hro⟩, ?_⟩
    rw [sepConj_comm slack (stackAt s0.sp 5824),
      sepConj_assoc (stackAt s0.sp 5824) slack R] at hm
    exact hm
  · intro sf _ _ hpost
    dsimp only [mlkemValidatePkCoreSpec] at hpost
    dsimp only [withMlKemRoOk, keepsFs, mlkemValidatePkProjSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hnsp, hiff⟩, hpost⟩
    have htr : sf.trace = s0.trace := hnsp.1
    have hfs : sf.fs = s0.fs := hnsp.2.2.2.2.2.2
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfs, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hiff, htr⟩, ?_⟩
    rw [← sepConj_assoc (stackAt s0.sp 5824) slack R,
      sepConj_comm (stackAt s0.sp 5824) slack,
      ← stackAt_shrink s0.sp extHookStack 5824 (by decide)] at hpost
    exact hpost

/-! ## 4. Pure 24-Bit Triple & 384-Byte Polynomial `deserialize_12` / `serialize_12` Round-Trip -/

/-- Even 12-bit coefficient from a 3-byte triple `(b0, b1, b2)`. -/
@[expose] def rawCoeff0 (b0 b1 : BitVec 8) : Nat :=
  (b0.zeroExtend 16 ||| ((b1.zeroExtend 16 &&& 0x0f#16) <<< 8)).toNat

/-- Odd 12-bit coefficient from a 3-byte triple `(b0, b1, b2)`. -/
@[expose] def rawCoeff1 (b1 b2 : BitVec 8) : Nat :=
  ((b1.zeroExtend 16 >>> 4) ||| (b2.zeroExtend 16 <<< 4)).toNat

/-- NEON `deserialize_12` modular reduction of a 12-bit candidate `< 4096` into `[0, 3329)`. -/
@[expose] def reduce12 (d : Nat) : BitVec 16 :=
  BitVec.ofNat 16 (if 3329 ≤ d then d - 3329 else d)

/-- Pack two 12-bit coefficients `(c0, c1)` into 3 bytes `[b0', b1', b2']`. -/
@[expose] def packTriple12 (c0 c1 : BitVec 16) : List (BitVec 8) :=
  let w24 : BitVec 24 :=
    (c0.zeroExtend 24 &&& 0xfff#24) ||| ((c1.zeroExtend 24 &&& 0xfff#24) <<< 12)
  [w24.truncate 8, (w24 >>> 8).truncate 8, (w24 >>> 16).truncate 8]

/-- Round-trip of a 3-byte triple through `deserialize_12` followed by `serialize_12`. -/
@[expose] def reencodeTriple (b0 b1 b2 : BitVec 8) : List (BitVec 8) :=
  packTriple12 (reduce12 (rawCoeff0 b0 b1)) (reduce12 (rawCoeff1 b1 b2))

/-- Round-trip of `128` 3-byte triples (`384` bytes = one encoded ML-KEM polynomial). -/
@[expose] def reencodePoly384 (bs : List (BitVec 8)) : List (BitVec 8) :=
  ((List.range 128).map fun t =>
    reencodeTriple (bs.getD (3 * t) 0#8) (bs.getD (3 * t + 1) 0#8)
      (bs.getD (3 * t + 2) 0#8)).flatten

theorem rawCoeff0_lt_4096 (b0 b1 : BitVec 8) : rawCoeff0 b0 b1 < 4096 := by
  have hb0 : b0.toNat < 256 := b0.isLt
  have hb1 : b1.toNat < 256 := b1.isLt
  unfold rawCoeff0
  have h : (b0.zeroExtend 16 ||| ((b1.zeroExtend 16 &&& 0x0f#16) <<< 8)) < 0x1000#16 := by
    bv_bits
  exact BitVec.lt_def.mp h

theorem rawCoeff1_lt_4096 (b1 b2 : BitVec 8) : rawCoeff1 b1 b2 < 4096 := by
  unfold rawCoeff1
  have h : ((b1.zeroExtend 16 >>> 4) ||| (b2.zeroExtend 16 <<< 4)) < 0x1000#16 := by
    bv_bits
  exact BitVec.lt_def.mp h

/-- Exact bit-reconstruction identity: packing the raw 12-bit pair `(rawCoeff0, rawCoeff1)`
    recovers `[b0, b1, b2]`. -/
theorem packTriple12_raw (b0 b1 b2 : BitVec 8) :
    packTriple12 (BitVec.ofNat 16 (rawCoeff0 b0 b1))
      (BitVec.ofNat 16 (rawCoeff1 b1 b2)) = [b0, b1, b2] := by
  unfold packTriple12 rawCoeff0 rawCoeff1
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_⟩ <;> bv_bits

/-- Injectivity of `packTriple12` on 12-bit values (`< 4096`). -/
theorem packTriple12_inj {c0 c1 d0 d1 : Nat}
    (hc0 : c0 < 4096) (hc1 : c1 < 4096) (hd0 : d0 < 4096) (hd1 : d1 < 4096)
    (heq : packTriple12 (BitVec.ofNat 16 c0) (BitVec.ofNat 16 c1) =
           packTriple12 (BitVec.ofNat 16 d0) (BitVec.ofNat 16 d1)) :
    c0 = d0 ∧ c1 = d1 := by
  unfold packTriple12 at heq
  simp only [List.cons.injEq, and_true] at heq
  rcases heq with ⟨h0, h1, h2⟩
  have hbv0 : BitVec.ofNat 16 c0 < 0x1000#16 := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hc0
  have hbv1 : BitVec.ofNat 16 c1 < 0x1000#16 := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hc1
  have hdv0 : BitVec.ofNat 16 d0 < 0x1000#16 := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hd0
  have hdv1 : BitVec.ofNat 16 d1 < 0x1000#16 := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hd1
  have eq0 : BitVec.ofNat 16 c0 = BitVec.ofNat 16 d0 := by bv_bits
  have eq1 : BitVec.ofNat 16 c1 = BitVec.ofNat 16 d1 := by bv_bits
  have hmod0 := congrArg BitVec.toNat eq0
  have hmod1 := congrArg BitVec.toNat eq1
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c0 < 65536 by omega),
    Nat.mod_eq_of_lt (show d0 < 65536 by omega),
    Nat.mod_eq_of_lt (show c1 < 65536 by omega),
    Nat.mod_eq_of_lt (show d1 < 65536 by omega)] at hmod0 hmod1
  exact ⟨hmod0, hmod1⟩

/-- Key 24-bit round-trip equivalence: `reencodeTriple b0 b1 b2 = [b0, b1, b2]` holds if and only
    if both 12-bit coefficients are strictly `< 3329`. -/
theorem reencodeTriple_eq_iff (b0 b1 b2 : BitVec 8) :
    reencodeTriple b0 b1 b2 = [b0, b1, b2] ↔
      rawCoeff0 b0 b1 < mlkemQ ∧ rawCoeff1 b1 b2 < mlkemQ := by
  have hd0 := rawCoeff0_lt_4096 b0 b1
  have hd1 := rawCoeff1_lt_4096 b1 b2
  unfold reencodeTriple reduce12 mlkemQ
  constructor
  · intro h
    rw [← packTriple12_raw b0 b1 b2] at h
    have hinj := packTriple12_inj
      (by split <;> omega) (by split <;> omega) hd0 hd1 h
    rcases hinj with ⟨h0, h1⟩
    constructor
    · by_contra hge; split at h0 <;> omega
    · by_contra hge; split at h1 <;> omega
  · rintro ⟨hlt0, hlt1⟩
    have hneg0 : ¬ (3329 ≤ rawCoeff0 b0 b1) := by omega
    have hneg1 : ¬ (3329 ≤ rawCoeff1 b1 b2) := by omega
    simp only [hneg0, hneg1, ↓reduceIte]
    exact packTriple12_raw b0 b1 b2

private theorem bits_lo8 (b : BitVec 8) :
    (((((((((0 ||| (((b.toNat >>> 0) &&& 1) <<< 0)) |||
      (((b.toNat >>> 1) &&& 1) <<< 1)) |||
      (((b.toNat >>> 2) &&& 1) <<< 2)) |||
      (((b.toNat >>> 3) &&& 1) <<< 3)) |||
      (((b.toNat >>> 4) &&& 1) <<< 4)) |||
      (((b.toNat >>> 5) &&& 1) <<< 5)) |||
      (((b.toNat >>> 6) &&& 1) <<< 6)) |||
      (((b.toNat >>> 7) &&& 1) <<< 7))) = b.toNat := by
  revert b; decide +kernel

private theorem bits_hi4 (b : BitVec 8) :
    (((((0 ||| (((b.toNat >>> 0) &&& 1) <<< 8)) |||
      (((b.toNat >>> 1) &&& 1) <<< 9)) |||
      (((b.toNat >>> 2) &&& 1) <<< 10)) |||
      (((b.toNat >>> 3) &&& 1) <<< 11))) =
      ((b.zeroExtend 16 &&& 0x0f#16) <<< 8).toNat := by
  revert b; decide +kernel

private theorem bits_lo4_shr4 (b : BitVec 8) :
    (((((0 ||| (((b.toNat >>> 4) &&& 1) <<< 0)) |||
      (((b.toNat >>> 5) &&& 1) <<< 1)) |||
      (((b.toNat >>> 6) &&& 1) <<< 2)) |||
      (((b.toNat >>> 7) &&& 1) <<< 3))) =
      (b.zeroExtend 16 >>> 4).toNat := by
  revert b; decide +kernel

private theorem bits_hi8_shl4 (b : BitVec 8) :
    (((((((((0 ||| (((b.toNat >>> 0) &&& 1) <<< 4)) |||
      (((b.toNat >>> 1) &&& 1) <<< 5)) |||
      (((b.toNat >>> 2) &&& 1) <<< 6)) |||
      (((b.toNat >>> 3) &&& 1) <<< 7)) |||
      (((b.toNat >>> 4) &&& 1) <<< 8)) |||
      (((b.toNat >>> 5) &&& 1) <<< 9)) |||
      (((b.toNat >>> 6) &&& 1) <<< 10)) |||
      (((b.toNat >>> 7) &&& 1) <<< 11))) =
      (b.zeroExtend 16 <<< 4).toNat := by
  revert b; decide +kernel

private theorem bytesToBits_getD (bs : List (BitVec 8)) (idx : Nat)
    (hidx : idx < 8 * bs.length) :
    (bytesToBits bs).getD idx 0 = ((bs.getD (idx / 8) 0#8).toNat >>> (idx % 8)) &&& 1 := by
  have hdiv : idx / 8 < bs.length := by omega
  simp [bytesToBits, Array.getD, List.getD, hidx, hdiv]

private theorem array_ofFn_getD {n : Nat} (f : Fin n → Nat) (i : Nat) (hi : i < n) :
    (Array.ofFn f).getD i 0 = f ⟨i, hi⟩ := by
  simp [Array.getD, hi]

theorem byteDecodeRaw12_even {bs : List (BitVec 8)} (hlen : bs.length = 384)
    {t : Nat} (ht : t < 128) :
    (byteDecodeRaw 12 bs).getD (2 * t) 0 =
      rawCoeff0 (bs.getD (3 * t) 0#8) (bs.getD (3 * t + 1) 0#8) := by
  have h2t : 2 * t < 256 := by omega
  unfold byteDecodeRaw
  rw [array_ofFn_getD _ _ h2t]
  have hr12 : List.range 12 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] := by decide
  rw [hr12]
  simp only [List.foldl]
  repeat rw [bytesToBits_getD bs _ (by omega)]
  have d0 : (2 * t * 12 + 0) / 8 = 3 * t ∧ (2 * t * 12 + 0) % 8 = 0 := by omega
  have d1 : (2 * t * 12 + 1) / 8 = 3 * t ∧ (2 * t * 12 + 1) % 8 = 1 := by omega
  have d2 : (2 * t * 12 + 2) / 8 = 3 * t ∧ (2 * t * 12 + 2) % 8 = 2 := by omega
  have d3 : (2 * t * 12 + 3) / 8 = 3 * t ∧ (2 * t * 12 + 3) % 8 = 3 := by omega
  have d4 : (2 * t * 12 + 4) / 8 = 3 * t ∧ (2 * t * 12 + 4) % 8 = 4 := by omega
  have d5 : (2 * t * 12 + 5) / 8 = 3 * t ∧ (2 * t * 12 + 5) % 8 = 5 := by omega
  have d6 : (2 * t * 12 + 6) / 8 = 3 * t ∧ (2 * t * 12 + 6) % 8 = 6 := by omega
  have d7 : (2 * t * 12 + 7) / 8 = 3 * t ∧ (2 * t * 12 + 7) % 8 = 7 := by omega
  have d8 : (2 * t * 12 + 8) / 8 = 3 * t + 1 ∧ (2 * t * 12 + 8) % 8 = 0 := by omega
  have d9 : (2 * t * 12 + 9) / 8 = 3 * t + 1 ∧ (2 * t * 12 + 9) % 8 = 1 := by omega
  have d10 : (2 * t * 12 + 10) / 8 = 3 * t + 1 ∧ (2 * t * 12 + 10) % 8 = 2 := by omega
  have d11 : (2 * t * 12 + 11) / 8 = 3 * t + 1 ∧ (2 * t * 12 + 11) % 8 = 3 := by omega
  rw [d0.1, d0.2, d1.1, d1.2, d2.1, d2.2, d3.1, d3.2, d4.1, d4.2, d5.1, d5.2,
      d6.1, d6.2, d7.1, d7.2, d8.1, d8.2, d9.1, d9.2, d10.1, d10.2, d11.1, d11.2]
  set b0 := bs.getD (3 * t) 0#8
  set b1 := bs.getD (3 * t + 1) 0#8
  rw [bits_lo8 b0]
  have hassoc :
      ((((b0.toNat ||| (((b1.toNat >>> 0) &&& 1) <<< 8)) |||
        (((b1.toNat >>> 1) &&& 1) <<< 9)) |||
        (((b1.toNat >>> 2) &&& 1) <<< 10)) |||
        (((b1.toNat >>> 3) &&& 1) <<< 11)) =
      b0.toNat |||
        (((((0 ||| (((b1.toNat >>> 0) &&& 1) <<< 8)) |||
          (((b1.toNat >>> 1) &&& 1) <<< 9)) |||
          (((b1.toNat >>> 2) &&& 1) <<< 10)) |||
          (((b1.toNat >>> 3) &&& 1) <<< 11))) := by
    simp [Nat.or_assoc]
  rw [hassoc, bits_hi4 b1]
  unfold rawCoeff0
  have hb0lt : b0.toNat < 65536 := by have := b0.isLt; omega
  simp [BitVec.toNat_or, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hb0lt]

theorem byteDecodeRaw12_odd {bs : List (BitVec 8)} (hlen : bs.length = 384)
    {t : Nat} (ht : t < 128) :
    (byteDecodeRaw 12 bs).getD (2 * t + 1) 0 =
      rawCoeff1 (bs.getD (3 * t + 1) 0#8) (bs.getD (3 * t + 2) 0#8) := by
  have h2t : 2 * t + 1 < 256 := by omega
  unfold byteDecodeRaw
  rw [array_ofFn_getD _ _ h2t]
  have hr12 : List.range 12 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] := by decide
  rw [hr12]
  simp only [List.foldl]
  repeat rw [bytesToBits_getD bs _ (by omega)]
  have d0 : ((2 * t + 1) * 12 + 0) / 8 = 3 * t + 1 ∧ ((2 * t + 1) * 12 + 0) % 8 = 4 := by omega
  have d1 : ((2 * t + 1) * 12 + 1) / 8 = 3 * t + 1 ∧ ((2 * t + 1) * 12 + 1) % 8 = 5 := by omega
  have d2 : ((2 * t + 1) * 12 + 2) / 8 = 3 * t + 1 ∧ ((2 * t + 1) * 12 + 2) % 8 = 6 := by omega
  have d3 : ((2 * t + 1) * 12 + 3) / 8 = 3 * t + 1 ∧ ((2 * t + 1) * 12 + 3) % 8 = 7 := by omega
  have d4 : ((2 * t + 1) * 12 + 4) / 8 = 3 * t + 2 ∧ ((2 * t + 1) * 12 + 4) % 8 = 0 := by omega
  have d5 : ((2 * t + 1) * 12 + 5) / 8 = 3 * t + 2 ∧ ((2 * t + 1) * 12 + 5) % 8 = 1 := by omega
  have d6 : ((2 * t + 1) * 12 + 6) / 8 = 3 * t + 2 ∧ ((2 * t + 1) * 12 + 6) % 8 = 2 := by omega
  have d7 : ((2 * t + 1) * 12 + 7) / 8 = 3 * t + 2 ∧ ((2 * t + 1) * 12 + 7) % 8 = 3 := by omega
  have d8 : ((2 * t + 1) * 12 + 8) / 8 = 3 * t + 2 ∧ ((2 * t + 1) * 12 + 8) % 8 = 4 := by omega
  have d9 : ((2 * t + 1) * 12 + 9) / 8 = 3 * t + 2 ∧ ((2 * t + 1) * 12 + 9) % 8 = 5 := by omega
  have d10 : ((2 * t + 1) * 12 + 10) / 8 = 3 * t + 2 ∧ ((2 * t + 1) * 12 + 10) % 8 = 6 := by omega
  have d11 : ((2 * t + 1) * 12 + 11) / 8 = 3 * t + 2 ∧ ((2 * t + 1) * 12 + 11) % 8 = 7 := by omega
  rw [d0.1, d0.2, d1.1, d1.2, d2.1, d2.2, d3.1, d3.2, d4.1, d4.2, d5.1, d5.2,
      d6.1, d6.2, d7.1, d7.2, d8.1, d8.2, d9.1, d9.2, d10.1, d10.2, d11.1, d11.2]
  set b1 := bs.getD (3 * t + 1) 0#8
  set b2 := bs.getD (3 * t + 2) 0#8
  rw [bits_lo4_shr4 b1]
  have hassoc :
      (((((((((b1.zeroExtend 16 >>> 4).toNat ||| (((b2.toNat >>> 0) &&& 1) <<< 4)) |||
        (((b2.toNat >>> 1) &&& 1) <<< 5)) |||
        (((b2.toNat >>> 2) &&& 1) <<< 6)) |||
        (((b2.toNat >>> 3) &&& 1) <<< 7)) |||
        (((b2.toNat >>> 4) &&& 1) <<< 8)) |||
        (((b2.toNat >>> 5) &&& 1) <<< 9)) |||
        (((b2.toNat >>> 6) &&& 1) <<< 10)) |||
        (((b2.toNat >>> 7) &&& 1) <<< 11)) =
      (b1.zeroExtend 16 >>> 4).toNat |||
        (((((((((0 ||| (((b2.toNat >>> 0) &&& 1) <<< 4)) |||
          (((b2.toNat >>> 1) &&& 1) <<< 5)) |||
          (((b2.toNat >>> 2) &&& 1) <<< 6)) |||
          (((b2.toNat >>> 3) &&& 1) <<< 7)) |||
          (((b2.toNat >>> 4) &&& 1) <<< 8)) |||
          (((b2.toNat >>> 5) &&& 1) <<< 9)) |||
          (((b2.toNat >>> 6) &&& 1) <<< 10)) |||
          (((b2.toNat >>> 7) &&& 1) <<< 11))) := by
    simp [Nat.or_assoc]
  rw [hassoc, bits_hi8_shl4 b2]
  unfold rawCoeff1
  simp [BitVec.toNat_or]

@[simp] theorem reencodeTriple_length (b0 b1 b2 : BitVec 8) :
    (reencodeTriple b0 b1 b2).length = 3 := rfl

private theorem list_eq_flatten_triples {bs : List (BitVec 8)} (n : Nat)
    (hlen : bs.length = 3 * n) :
    bs = ((List.range n).map fun t =>
      [bs.getD (3 * t) 0#8, bs.getD (3 * t + 1) 0#8, bs.getD (3 * t + 2) 0#8]).flatten := by
  refine List.ext_getElem ?_ ?_
  · have hsum : (((List.range n).map fun t =>
        [bs.getD (3 * t) 0#8, bs.getD (3 * t + 1) 0#8, bs.getD (3 * t + 2) 0#8]).map
          List.length).sum = 3 * n := by
      simp [Function.comp_def]; omega
    rw [List.length_flatten, hsum, hlen]
  · intro idx h1 h2
    have hq : idx / 3 < n := by omega
    symm
    rw [List.getElem_eq_iff]
    have hsplit : List.range n = List.range (idx / 3) ++ (idx / 3) :: (List.range n).drop (idx / 3 + 1) := by
      have htake : (List.range n).take (idx / 3) = List.range (idx / 3) := by
        rw [List.take_range]; congr 1; omega
      have hcons : (List.range n).drop (idx / 3) =
          (idx / 3) :: (List.range n).drop (idx / 3 + 1) := by
        rw [← List.getElem_cons_drop (h := by simp [hq]), List.getElem_range]
      calc List.range n
          = (List.range n).take (idx / 3) ++ (List.range n).drop (idx / 3) :=
            (List.take_append_drop _ _).symm
        _ = List.range (idx / 3) ++ (idx / 3) :: (List.range n).drop (idx / 3 + 1) := by
            rw [htake, hcons]
    rw [hsplit]
    simp only [List.map_append, List.map_cons, List.flatten_append, List.flatten_cons]
    have hpre_len : (((List.range (idx / 3)).map fun t =>
        [bs.getD (3 * t) 0#8, bs.getD (3 * t + 1) 0#8, bs.getD (3 * t + 2) 0#8])).flatten.length =
        3 * (idx / 3) := by
      rw [List.length_flatten]
      simp [Function.comp_def]; omega
    rw [List.getElem?_append_right (by omega), hpre_len]
    have hrem : idx - 3 * (idx / 3) = idx % 3 := by omega
    rw [hrem]
    rcases (show idx % 3 = 0 ∨ idx % 3 = 1 ∨ idx % 3 = 2 by omega) with hr | hr | hr
    · simp [hr, List.getD, show 3 * (idx / 3) = idx by omega, h1]
    · simp [hr, List.getD, show 3 * (idx / 3) + 1 = idx by omega, h1]
    · simp [hr, List.getD, show 3 * (idx / 3) + 2 = idx by omega, h1]

@[simp] theorem reencodePoly384_length (bs : List (BitVec 8)) :
    (reencodePoly384 bs).length = 384 := by
  unfold reencodePoly384
  rw [List.length_flatten]
  simp [Function.comp_def]

private theorem flatten_triples_inj :
    ∀ {xs ys : List (List (BitVec 8))},
      xs.length = ys.length →
      (∀ x ∈ xs, x.length = 3) →
      (∀ y ∈ ys, y.length = 3) →
      xs.flatten = ys.flatten → xs = ys
  | [], [], _, _, _, _ => rfl
  | x :: xs, y :: ys, hlen, hx, hy, hflat => by
    have hx3 : x.length = 3 := hx x (by simp)
    have hy3 : y.length = 3 := hy y (by simp)
    simp only [List.flatten_cons] at hflat
    have hxy : x = y := by
      have ht := congrArg (List.take 3) hflat
      rwa [List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega),
        List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at ht
    have hrest : xs.flatten = ys.flatten := by
      have hd := congrArg (List.drop 3) hflat
      rwa [List.drop_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
        List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega),
        List.nil_append, List.nil_append] at hd
    rw [hxy, flatten_triples_inj (by simpa using hlen)
      (fun a ha => hx a (by simp [ha])) (fun b hb => hy b (by simp [hb])) hrest]
  | [], _ :: _, hlen, _, _, _ => by cases hlen
  | _ :: _, [], hlen, _, _, _ => by cases hlen

/-- Full 384-byte polynomial equivalence: `reencodePoly384 bs = bs` iff all 256 decoded 12-bit
    coefficients are `< 3329`. -/
theorem reencodePoly384_eq_iff {bs : List (BitVec 8)} (hlen : bs.length = 384) :
    reencodePoly384 bs = bs ↔
      ((List.range 256).all fun j => decide ((byteDecodeRaw 12 bs).getD j 0 < mlkemQ)) = true := by
  have hbs := list_eq_flatten_triples 128 (by omega : bs.length = 3 * 128)
  constructor
  · intro heq
    conv at heq => rhs; rw [hbs]
    unfold reencodePoly384 at heq
    have hlists := flatten_triples_inj (by simp)
      (by intro x hx; rcases List.mem_map.mp hx with ⟨t, _, rfl⟩; rfl)
      (by intro y hy; rcases List.mem_map.mp hy with ⟨t, _, rfl⟩; rfl)
      heq
    rw [List.all_eq_true]
    intro j hj
    have hjlt : j < 256 := List.mem_range.mp hj
    have htlt : j / 2 < 128 := by omega
    have h_elem := congrArg (fun l => l[j / 2]?) hlists
    simp only [List.getElem?_map, List.getElem?_range htlt, Option.map_some,
      Option.some.injEq] at h_elem
    have htrip := (reencodeTriple_eq_iff _ _ _).mp h_elem
    rw [decide_eq_true_eq]
    rcases (show j = 2 * (j / 2) ∨ j = 2 * (j / 2) + 1 by omega) with hje | hjo
    · rw [hje, byteDecodeRaw12_even hlen htlt]; exact htrip.1
    · rw [hjo, byteDecodeRaw12_odd hlen htlt]; exact htrip.2
  · intro hall
    rw [List.all_eq_true] at hall
    conv_rhs => rw [hbs]
    unfold reencodePoly384
    congr 1
    apply List.map_congr_left
    intro t ht
    have htlt : t < 128 := List.mem_range.mp ht
    have hev : (byteDecodeRaw 12 bs).getD (2 * t) 0 < mlkemQ := by
      simpa [decide_eq_true_eq] using hall (2 * t) (List.mem_range.mpr (by omega))
    have hod : (byteDecodeRaw 12 bs).getD (2 * t + 1) 0 < mlkemQ := by
      simpa [decide_eq_true_eq] using hall (2 * t + 1) (List.mem_range.mpr (by omega))
    rw [byteDecodeRaw12_even hlen htlt] at hev
    rw [byteDecodeRaw12_odd hlen htlt] at hod
    exact (reencodeTriple_eq_iff _ _ _).mpr ⟨hev, hod⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Base
