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
public import ProofLib.SepLogic.SafeSepWP
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
public meta import ProofLib.ProgramReflection
public meta import ProofLib.GenDecodes
public meta import ProofLib.GenPlacedFetches
import ProofLib.SepLogic.WP.StepsProcess
import ProofLib.SepLogic.WPFrozen

/-!
# `kyber::encapsulate` (`B24` → `B07`) — Block Setup, Specifications, & Callee-Saved Frame (`Base`)

1. Blocks `B07` (`10,252` words) and `B24` (`4` words) `PlacedLib`, `WordTree`, and
   relocation-free `fetch_blk07_noReloc` helper.
2. `safeSepWP_seq_env` and `safe_subroutine_ok_of_simulates` combinators for shared
   total/partial segment composition.
3. Tight-stack (`34,240 = 33,104 + 1,136` bytes) core specs (`blk07EncapsRawSpec`,
   `blk07EncapsTermRawSpec`, `kyberEncapsRawSpec`, `kyberEncapsCoreSpec`,
   `kyberEncapsTermRawSpec`, `kyberEncapsTermCoreSpec`) preserving `(rA ↦ₛ rand)` intact.
4. Caller-struct projection specs (`kyberEncapsKeepRandProjSpec`,
   `kyberEncapsKeepRandConcatProjSpec`, `kemEncapsProjSpec`, `kemEncapsVecProjSpec`) for
   `34240 ≤ stk` and `stk = extHookStack` (`65536`), with `SpecSimulates` bridges.
5. Spilled callee-saved frame `SavedFrame07` (`[sp0 - 160, sp0)`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open ProofLib.ProgramReflection (WordTree)
open ProofLib.GenPlacedFetches (hookAtOff?_rebase_of_placeable fetch_rebase_of_noReloc)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemPlacement
  mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (withNonSyscallPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Kyber1024EncapsTerminates
  kyber1024Encaps
  kyber1024Encaps_ct_len
  kyber1024Encaps_ss_len
  toByteVec
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  cell_entails_memRegion8
  toByteVec_toList_of_length
  withMlKemRoOk
)

/-! ## 1. Blocks `B07` (`10,252` words) & `B24` (`4` words) Setup -/

@[expose] def blkLib07 : PlacedLib := mlkemMultiLib.blockLib 7
@[expose] def blkPl07 [MlKemPlacement] : Placement := mlkemMultiLib.blockPlacement mlkemMpl 7
theorem blkPlaceable07 [MlKemPlacement] : blkLib07.Placeable blkPl07 :=
  mlkemMultiLib.placeable_blockLib (by decide) MlKemPlacement.placeable
@[expose] def blkPC07 [MlKemPlacement] : Program := blkLib07.program blkPl07
@[expose] def blkProg07 : Program := { code := blkLib07.text.code, symbols := blkLib07.text.symbols }

set_option maxRecDepth 200000 in
@[expose] def blkTree07 : WordTree := word_tree_of% blkProg07

set_option maxRecDepth 200000 in
theorem blk07_code_eq : blkLib07.text.code = blkTree07.toBytes := by rfl_kernel

theorem blk07_tree_size : blkTree07.checkSize? = some 10252 := by rfl_kernel

@[expose] def fetchWordTree07 (j : Nat) : Option Instr :=
  match blkTree07.getQuad? j with
  | none => none
  | some (b0, b1, b2, b3) => Arm64.decode (b3 ++ b2 ++ b1 ++ b0)

theorem fetch_blk07_noReloc [MlKemPlacement] {loOff hiOff : Nat}
    (hrel : blkLib07.text.relocs.all (fun r => decide (r.off < loOff ∨ hiOff ≤ r.off)) = true)
    {b : BitVec 64} {j : Nat} {inst : Instr}
    (hlo : loOff ≤ 4 * j) (hhi : 4 * j < hiOff) (hbound : 4 * j + 4 ≤ 4 * 10252)
    (hfw : fetchWordTree07 j = some inst) :
    (blkPC07.rebase b (fun _ => none)).fetch (b + BitVec.ofNat 64 (4 * j)) = some inst := by
  have hnrel : (blkLib07.text.relocAt? (4 * j)).isNone = true := by
    cases hr : blkLib07.text.relocAt? (4 * j) with
    | none => rfl
    | some r =>
      have hmem := CodeBlock.relocAt?_mem hr
      have hoff := CodeBlock.relocAt?_off hr
      have hall := (List.all_eq_true.mp hrel) r hmem
      simp only [decide_eq_true_eq] at hall
      omega
  have hdec : blkTree07.fetchDecodeAt (4 * j) = some inst := by
    unfold WordTree.fetchDecodeAt
    have hdiv : 4 * j / 4 = j := by omega
    rw [hdiv]
    unfold fetchWordTree07 at hfw
    cases hq : blkTree07.getQuad? j with
    | none => simp [hq] at hfw
    | some q =>
      rcases q with ⟨b0, b1, b2, b3⟩
      simp [hq] at hfw ⊢
      exact hfw
  have hnh := hookAtOff?_rebase_of_placeable (pl := blkPl07) (b := b)
    (X := fun _ => none) blk07_code_eq blk07_tree_size blkPlaceable07 (off := 4 * j) (by omega)
  exact fetch_rebase_of_noReloc blk07_code_eq blk07_tree_size
    (by omega) hbound (by omega) hdec hnrel hnh

@[expose] def blkLib24 : PlacedLib := mlkemMultiLib.blockLib 24
@[expose] def blkPl24 [MlKemPlacement] : Placement := mlkemMultiLib.blockPlacement mlkemMpl 24
theorem blkPlaceable24 [MlKemPlacement] : blkLib24.Placeable blkPl24 :=
  mlkemMultiLib.placeable_blockLib (by decide) MlKemPlacement.placeable
@[expose] def blkPC24 [MlKemPlacement] : Program := blkLib24.program blkPl24
@[expose] def blkProg24 : Program := { code := blkLib24.text.code, symbols := blkLib24.text.symbols }
@[expose] def blkTree24 : WordTree := word_tree_of% blkProg24

theorem blk24_code_eq : blkLib24.text.code = blkTree24.toBytes := by rfl_kernel
theorem blk24_tree_size : blkTree24.checkSize? = some 4 := by rfl_kernel

/-! ## 2. Partial/Total Segment Composition & Simulation Combinators -/

/-- Sequence a total `SepWP` segment `h1` with a `SafeSepWP` continuation `h2` while preserving
    `CodeLoaded` and `MlKemRoOk` across `KeepsFrozen` transitions. -/
theorem safeSepWP_seq_env {prog : Program} {mid : BitVec 64} {s : State}
    {P : SepProp} {post1 Q : State → SepProp → Prop} {mpl : MultiPlacement}
    (hcl : mlkemMultiLib.CodeLoaded mpl s.mem)
    (hro : MlKemRoOk mpl s.mem)
    (h1 : SepWP prog mid s P post1)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      mlkemMultiLib.CodeLoaded mpl sm.mem → MlKemRoOk mpl sm.mem →
      post1 sm Pm → SafeSepWP prog sm Pm Q) :
    SafeSepWP prog s P Q :=
  SafeSepWP.of_sepWP
    (SepWP.mono_frozen
      (post' := fun sm Pm => SafeSepWP prog sm Pm Q)
      (Φ := fun m => mlkemMultiLib.CodeLoaded mpl m ∧ MlKemRoOk mpl m)
      (fun _ _ ⟨hc, hr⟩ hkf => ⟨hc.of_keepsFrozen hkf, hr.of_keepsFrozen hkf⟩)
      ⟨hcl, hro⟩ h1
      (fun sm Pm hpc hrun ⟨hc, hr⟩ hp1 => h2 sm Pm hpc hrun hc hr hp1))

/-- Transport `safe_subroutine_ok` along `SpecSimulates`. -/
theorem safe_subroutine_ok_of_simulates {α β : Type} {spec₁ : Spec α} {spec₂ : Spec β}
    (hsim : SpecSimulates spec₁ spec₂) {prog : Program} {entry : BitVec 64}
    (h : safe_subroutine_ok prog entry spec₁) :
    safe_subroutine_ok prog entry spec₂ :=
  fun y R s0 hentry hpre =>
    let ⟨x, R₁, hpre₁, hm⟩ := hsim y R s0 hpre
    (h x R₁ s0 hentry hpre₁).mono fun sf hout => hm sf hout

/-! ## 3. Core Specifications (`B07` & `B24`, Tight Stack `34,240` B) -/

/-- Vector-typed wrapper around `kyber1024Encaps` matching `E2E.PqxdhPrims.encaps`. -/
@[expose] noncomputable def kyber1024EncapsVec
    (pk : List.Vector (BitVec 8) 1568) (rand : List.Vector (BitVec 8) 32) :
    List.Vector (BitVec 8) 1568 × List.Vector (BitVec 8) 32 :=
  let (ct, ss) := kyber1024Encaps pk.toList rand.toList
  (toByteVec 1568 ct, toByteVec 32 ss)

@[simp] theorem kyber1024EncapsVec_fst_toList
    (pk : List.Vector (BitVec 8) 1568) (rand : List.Vector (BitVec 8) 32) :
    (kyber1024EncapsVec pk rand).1.toList = (kyber1024Encaps pk.toList rand.toList).1 := by
  simp only [kyber1024EncapsVec]
  exact toByteVec_toList_of_length (kyber1024Encaps_ct_len pk.toList rand.toList)

@[simp] theorem kyber1024EncapsVec_snd_toList
    (pk : List.Vector (BitVec 8) 1568) (rand : List.Vector (BitVec 8) 32) :
    (kyber1024EncapsVec pk rand).2.toList = (kyber1024Encaps pk.toList rand.toList).2 := by
  simp only [kyber1024EncapsVec]
  exact toByteVec_toList_of_length (kyber1024Encaps_ss_len pk.toList rand.toList)

/-- Tight-stack (`34,240` bytes) raw contract for `B07` (`kyber_encapsulate`, ABI `x0 = ret`,
    `x1 = pkA`, `x2 = rA`), preserving `(rA ↦ₛ rand)` intact with zero termination hypothesis. -/
@[expose] noncomputable def blk07EncapsRawSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) where
  pre := fun (ret, pkA, pk, rA, rand) s0 =>
    ⌜s0.readReg64 .x0 = ret ∧
      s0.readReg64 .x1 = pkA ∧
      s0.readReg64 .x2 = rA ∧
      pk.length = 1568 ∧
      rand.length = 32 ∧
      MlKemRoOk mpl s0.mem⌝ ∗
      (pkA ↦ₛ pk) ∗ (rA ↦ₛ rand) ∗ memRegion ret 1600 ∗ stackAt s0.sp 34240
  post := fun (ret, pkA, pk, rA, rand) s0 _sf =>
    let (ct, ss) := kyber1024Encaps pk rand
    (pkA ↦ₛ pk) ∗ (rA ↦ₛ rand) ∗ (ret ↦ₛ ct) ∗ ((ret + 1568#64) ↦ₛ ss) ∗ stackAt s0.sp 34240
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Tight-stack (`34,240` bytes) total-correctness raw contract for `B07` (`Kyber1024EncapsTerminates pk`). -/
@[expose] noncomputable def blk07EncapsTermRawSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) where
  pre := fun (ret, pkA, pk, rA, rand) s0 =>
    ⌜s0.readReg64 .x0 = ret ∧
      s0.readReg64 .x1 = pkA ∧
      s0.readReg64 .x2 = rA ∧
      pk.length = 1568 ∧
      rand.length = 32 ∧
      Kyber1024EncapsTerminates pk ∧
      MlKemRoOk mpl s0.mem⌝ ∗
      (pkA ↦ₛ pk) ∗ (rA ↦ₛ rand) ∗ memRegion ret 1600 ∗ stackAt s0.sp 34240
  post := (blk07EncapsRawSpec mpl).post
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Tight-stack (`34,240` bytes) raw contract for `B24` (`mlkem1024::kyber::encapsulate`,
    ABI `x8 = ret`, `x0 = pkA`, `x1 = rA`), preserving `(rA ↦ₛ rand)` intact. -/
@[expose] noncomputable def kyberEncapsRawSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) where
  pre := fun (ret, pkA, pk, rA, rand) s0 =>
    ⌜s0.readReg64 .x8 = ret ∧
      s0.readReg64 .x0 = pkA ∧
      s0.readReg64 .x1 = rA ∧
      pk.length = 1568 ∧
      rand.length = 32 ∧
      MlKemRoOk mpl s0.mem⌝ ∗
      (pkA ↦ₛ pk) ∗ (rA ↦ₛ rand) ∗ memRegion ret 1600 ∗ stackAt s0.sp 34240
  post := fun (ret, pkA, pk, rA, rand) s0 _sf =>
    let (ct, ss) := kyber1024Encaps pk rand
    (pkA ↦ₛ pk) ∗ (rA ↦ₛ rand) ∗ (ret ↦ₛ ct) ∗ ((ret + 1568#64) ↦ₛ ss) ∗ stackAt s0.sp 34240
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Tight-stack (`34,240` bytes) core contract for `B24` with `NonSyscallPreserved`. -/
@[expose] noncomputable def kyberEncapsCoreSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) :=
  withNonSyscallPreserved (kyberEncapsRawSpec mpl)

/-- Tight-stack (`34,240` bytes) total-correctness raw contract for `B24` (`Kyber1024EncapsTerminates pk`). -/
@[expose] noncomputable def kyberEncapsTermRawSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) where
  pre := fun (ret, pkA, pk, rA, rand) s0 =>
    ⌜s0.readReg64 .x8 = ret ∧
      s0.readReg64 .x0 = pkA ∧
      s0.readReg64 .x1 = rA ∧
      pk.length = 1568 ∧
      rand.length = 32 ∧
      Kyber1024EncapsTerminates pk ∧
      MlKemRoOk mpl s0.mem⌝ ∗
      (pkA ↦ₛ pk) ∗ (rA ↦ₛ rand) ∗ memRegion ret 1600 ∗ stackAt s0.sp 34240
  post := (kyberEncapsRawSpec mpl).post
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Tight-stack (`34,240` bytes) total-correctness core contract for `B24` with `NonSyscallPreserved`. -/
@[expose] noncomputable def kyberEncapsTermCoreSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) :=
  withNonSyscallPreserved (kyberEncapsTermRawSpec mpl)

/-- Core contract for `B24` specialized to a fixed `pk : List (BitVec 8)`. -/
@[expose] noncomputable def kyberEncapsAtPkCoreSpec (pk : List (BitVec 8)) (mpl : MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  withNonSyscallPreserved
    { pre := fun (ret, pkA, rA, rand) s0 =>
        ⌜s0.readReg64 .x8 = ret ∧
          s0.readReg64 .x0 = pkA ∧
          s0.readReg64 .x1 = rA ∧
          pk.length = 1568 ∧
          rand.length = 32 ∧
          MlKemRoOk mpl s0.mem⌝ ∗
          (pkA ↦ₛ pk) ∗ (rA ↦ₛ rand) ∗ memRegion ret 1600 ∗ stackAt s0.sp 34240
      post := fun (ret, pkA, rA, rand) s0 _sf =>
        let (ct, ss) := kyber1024Encaps pk rand
        (pkA ↦ₛ pk) ∗ (rA ↦ₛ rand) ∗ (ret ↦ₛ ct) ∗ ((ret + 1568#64) ↦ₛ ss) ∗ stackAt s0.sp 34240
      onPanic := fun _ _ _ => ⌜False⌝
      onExit  := fun _ _ _ _ => ⌜False⌝
      onOom   := fun _ _ _ => ⌜False⌝ }

/-! ## 4. Caller-Struct Projection Specifications (`34240 ≤ stk`) -/

/-- Caller-struct projection spec preserving `(rA x ↦ₛ rand x)` in `post` (split output
    `(ret x ↦ₛ ct) ∗ ((ret x + 0x620#64) ↦ₛ ss)`). -/
@[expose] def kyberEncapsKeepRandProjSpec (stk : Nat)
    (K : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) × List (BitVec 8))
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List (BitVec 8))
    (rA : C → BitVec 64) (rand : C → List (BitVec 8)) : Spec C where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = pkA x ∧ s.readReg64 .x1 = rA x ∧ s.readReg64 .x8 = ret x ∧
      (pk x).length = 1568 ∧ (rand x).length = 32⌝ ∗
      (pkA x ↦ₛ pk x) ∗ (rA x ↦ₛ rand x) ∗ memRegion (ret x) 1600 ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (pkA x ↦ₛ pk x) ∗ (rA x ↦ₛ rand x) ∗
      (ret x ↦ₛ (K (pk x) (rand x)).1) ∗
      ((ret x + 0x620#64) ↦ₛ (K (pk x) (rand x)).2) ∗
      stackAt s0.sp stk

/-- Caller-struct projection spec preserving `(rA x ↦ₛ rand x)` in `post` with contiguous
    `(ret x ↦ₛ (ct ++ ss))` output (matching `HandshakeDerive` / `kyberEncapsStubSpec`). -/
@[expose] def kyberEncapsKeepRandConcatProjSpec (stk : Nat)
    (K : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) × List (BitVec 8))
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List (BitVec 8))
    (rA : C → BitVec 64) (rand : C → List (BitVec 8)) : Spec C where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = pkA x ∧ s.readReg64 .x1 = rA x ∧ s.readReg64 .x8 = ret x ∧
      (pk x).length = 1568 ∧ (rand x).length = 32⌝ ∗
      (pkA x ↦ₛ pk x) ∗ (rA x ↦ₛ rand x) ∗ memRegion (ret x) 1600 ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (pkA x ↦ₛ pk x) ∗ (rA x ↦ₛ rand x) ∗
      (ret x ↦ₛ ((K (pk x) (rand x)).1 ++ (K (pk x) (rand x)).2)) ∗
      stackAt s0.sp stk

/-- Caller-struct projection spec weakening `(rA x ↦ₛ rand x)` to `memRegion (rA x) 32` in `post`
    (`List` presentation). -/
@[expose] def kemEncapsProjSpec (stk : Nat)
    (K : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) × List (BitVec 8))
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List (BitVec 8))
    (rA : C → BitVec 64) (rand : C → List (BitVec 8)) : Spec C where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = pkA x ∧ s.readReg64 .x1 = rA x ∧ s.readReg64 .x8 = ret x ∧
      (pk x).length = 1568 ∧ (rand x).length = 32⌝ ∗
      (pkA x ↦ₛ pk x) ∗ (rA x ↦ₛ rand x) ∗ memRegion (ret x) 1600 ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (pkA x ↦ₛ pk x) ∗ memRegion (rA x) 32 ∗
      (ret x ↦ₛ (K (pk x) (rand x)).1) ∗
      ((ret x + 0x620#64) ↦ₛ (K (pk x) (rand x)).2) ∗
      stackAt s0.sp stk

/-- Caller-struct projection spec weakening `(rA x ↦ₛ (rand x).toList)` to `memRegion (rA x) 32`
    in `post` (`List.Vector` presentation, matching `CliExt.kemEncapsSpec Q` by `rfl` at
    `stk = extHookStack` and `K = Q.encaps`). -/
@[expose] def kemEncapsVecProjSpec (stk : Nat)
    (K : List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32 →
      List.Vector (BitVec 8) 1568 × List.Vector (BitVec 8) 32)
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List.Vector (BitVec 8) 1568)
    (rA : C → BitVec 64) (rand : C → List.Vector (BitVec 8) 32) : Spec C where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = pkA x ∧ s.readReg64 .x1 = rA x ∧ s.readReg64 .x8 = ret x⌝ ∗
      (pkA x ↦ₛ (pk x).toList) ∗ (rA x ↦ₛ (rand x).toList) ∗
      memRegion (ret x) 1600 ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (pkA x ↦ₛ (pk x).toList) ∗ memRegion (rA x) 32 ∗
      (ret x ↦ₛ (K (pk x) (rand x)).1.toList) ∗
      ((ret x + 0x620#64) ↦ₛ (K (pk x) (rand x)).2.toList) ∗
      stackAt s0.sp stk

/-! ## 5. Simulation Bridges (`SpecSimulates`) -/

theorem kyberEncapsTermCore_simulates_atPk (pk : List (BitVec 8))
    (hTerm : Kyber1024EncapsTerminates pk) (mpl : MultiPlacement) :
    SpecSimulates (kyberEncapsTermCoreSpec mpl) (kyberEncapsAtPkCoreSpec pk mpl) := by
  refine SpecSimulates.of_map ?_
  rintro ⟨ret, pkA, rA, rand⟩ R s0 hm
  refine ⟨(ret, pkA, pk, rA, rand), R, ?_, fun sf _ _ hp => hp⟩
  dsimp only [kyberEncapsAtPkCoreSpec, withNonSyscallPreserved] at hm
  dsimp only [kyberEncapsTermCoreSpec, withNonSyscallPreserved, kyberEncapsTermRawSpec]
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
  rcases hm with ⟨⟨hx8, hx0, hx1, hpk, hrnd, hro⟩, hm⟩
  exact ⟨⟨hx8, hx0, hx1, hpk, hrnd, hTerm, hro⟩, hm⟩

theorem kyberEncapsCore_simulates_keepRand {stk : Nat}
    (hstk : 34240 ≤ stk := by decide) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (K : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) × List (BitVec 8))
    (hK : ∀ pk rand, K pk rand = kyber1024Encaps pk rand)
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List (BitVec 8))
    (rA : C → BitVec 64) (rand : C → List (BitVec 8)) (mpl : MultiPlacement) :
    SpecSimulates (kyberEncapsCoreSpec mpl)
      (withMlKemRoOk mpl (keepsFs (kyberEncapsKeepRandProjSpec stk K ret pkA pk rA rand))) := by
  refine SpecSimulates.of_map ?_
  intro y R s0 hm
  dsimp only [withMlKemRoOk, keepsFs, kyberEncapsKeepRandProjSpec] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hro, hm⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hx0, hx1, hx8, hpk, hrnd⟩, hm⟩
  rw [stackAt_shrink s0.sp stk 34240 hstk hstk_fit] at hm
  set slack := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 34240)
  refine ⟨(ret y, pkA y, pk y, rA y, rand y), slack ∗ R, ?_, ?_⟩
  · dsimp only [kyberEncapsCoreSpec, withNonSyscallPreserved, kyberEncapsRawSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx8, hx0, hx1, hpk, hrnd, hro⟩, ?_⟩
    rw [sepConj_comm slack (stackAt s0.sp 34240),
      sepConj_assoc (stackAt s0.sp 34240) slack R] at hm
    exact hm
  · intro sf _ _ hpost
    dsimp only [kyberEncapsCoreSpec, withNonSyscallPreserved, kyberEncapsRawSpec] at hpost
    dsimp only [withMlKemRoOk, keepsFs, kyberEncapsKeepRandProjSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hnsp, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hnsp.2.2.2.2.2.2, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hnsp.1, ?_⟩
    rw [hK]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc] at hpost ⊢
    rw [← sepConj_assoc (stackAt s0.sp 34240) slack R,
      sepConj_comm (stackAt s0.sp 34240) slack,
      ← stackAt_shrink s0.sp stk 34240 hstk hstk_fit] at hpost
    exact hpost

theorem kyberEncapsTermCore_simulates_keepRand {stk : Nat}
    (hstk : 34240 ≤ stk := by decide) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (K : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) × List (BitVec 8))
    (hK : ∀ pk rand, K pk rand = kyber1024Encaps pk rand)
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List (BitVec 8))
    (rA : C → BitVec 64) (rand : C → List (BitVec 8))
    (hTerm : ∀ x, Kyber1024EncapsTerminates (pk x)) (mpl : MultiPlacement) :
    SpecSimulates (kyberEncapsTermCoreSpec mpl)
      (withMlKemRoOk mpl (keepsFs (kyberEncapsKeepRandProjSpec stk K ret pkA pk rA rand))) := by
  refine SpecSimulates.of_map ?_
  intro y R s0 hm
  dsimp only [withMlKemRoOk, keepsFs, kyberEncapsKeepRandProjSpec] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hro, hm⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hx0, hx1, hx8, hpk, hrnd⟩, hm⟩
  rw [stackAt_shrink s0.sp stk 34240 hstk hstk_fit] at hm
  set slack := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 34240)
  refine ⟨(ret y, pkA y, pk y, rA y, rand y), slack ∗ R, ?_, ?_⟩
  · dsimp only [kyberEncapsTermCoreSpec, withNonSyscallPreserved, kyberEncapsTermRawSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx8, hx0, hx1, hpk, hrnd, hTerm y, hro⟩, ?_⟩
    rw [sepConj_comm slack (stackAt s0.sp 34240),
      sepConj_assoc (stackAt s0.sp 34240) slack R] at hm
    exact hm
  · intro sf _ _ hpost
    dsimp only [kyberEncapsTermCoreSpec, withNonSyscallPreserved, kyberEncapsTermRawSpec,
      kyberEncapsRawSpec] at hpost
    dsimp only [withMlKemRoOk, keepsFs, kyberEncapsKeepRandProjSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hnsp, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hnsp.2.2.2.2.2.2, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hnsp.1, ?_⟩
    rw [hK]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc] at hpost ⊢
    rw [← sepConj_assoc (stackAt s0.sp 34240) slack R,
      sepConj_comm (stackAt s0.sp 34240) slack,
      ← stackAt_shrink s0.sp stk 34240 hstk hstk_fit] at hpost
    exact hpost

theorem keepRand_simulates_concat (stk : Nat)
    (K : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) × List (BitVec 8))
    (hK_len : ∀ pk rand, (K pk rand).1.length = 1568)
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List (BitVec 8))
    (rA : C → BitVec 64) (rand : C → List (BitVec 8)) (mpl : MultiPlacement) :
    SpecSimulates
      (withMlKemRoOk mpl (keepsFs (kyberEncapsKeepRandProjSpec stk K ret pkA pk rA rand)))
      (withMlKemRoOk mpl (keepsFs (kyberEncapsKeepRandConcatProjSpec stk K ret pkA pk rA rand))) := by
  refine SpecSimulates.of_map ?_
  intro y R s0 hm
  refine ⟨y, R, hm, fun sf _ _ hpost => ?_⟩
  dsimp only [withMlKemRoOk, keepsFs, kyberEncapsKeepRandProjSpec] at hpost
  dsimp only [withMlKemRoOk, keepsFs, kyberEncapsKeepRandConcatProjSpec]
  rw [pointsToBytes_append (ret y) (K (pk y) (rand y)).1 (K (pk y) (rand y)).2,
    hK_len (pk y) (rand y)]
  simpa only [sepConj_assoc] using hpost

theorem keepRand_simulates_kemEncaps (stk : Nat)
    (K : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) × List (BitVec 8))
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List (BitVec 8))
    (rA : C → BitVec 64) (rand : C → List (BitVec 8)) (mpl : MultiPlacement) :
    SpecSimulates
      (withMlKemRoOk mpl (keepsFs (kyberEncapsKeepRandProjSpec stk K ret pkA pk rA rand)))
      (withMlKemRoOk mpl (keepsFs (kemEncapsProjSpec stk K ret pkA pk rA rand))) := by
  refine SpecSimulates.of_map ?_
  intro y R s0 hm
  have hrnd : (rand y).length = 32 := by
    dsimp only [withMlKemRoOk, keepsFs, kemEncapsProjSpec] at hm
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm
    have hm2 := hm.2
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm2
    exact hm2.1.2.2.2.2
  refine ⟨y, R, hm, fun sf _ _ hpost => ?_⟩
  dsimp only [withMlKemRoOk, keepsFs, kyberEncapsKeepRandProjSpec] at hpost
  dsimp only [withMlKemRoOk, keepsFs, kemEncapsProjSpec]
  have hent : (rA y ↦ₛ rand y) ⊢ memRegion (rA y) 32 := by
    rw [← hrnd]
    exact pointsToBytes_entails_memRegion (rA y) (rand y)
  exact Satisfies.mono
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left hent)))))
    (by simpa only [sepConj_assoc] using hpost)

theorem kemEncaps_simulates_vec (stk : Nat)
    (K : List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32 →
      List.Vector (BitVec 8) 1568 × List.Vector (BitVec 8) 32)
    (KList : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) × List (BitVec 8))
    (hK : ∀ pk rand,
      (K pk rand).1.toList = (KList pk.toList rand.toList).1 ∧
      (K pk rand).2.toList = (KList pk.toList rand.toList).2)
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List.Vector (BitVec 8) 1568)
    (rA : C → BitVec 64) (rand : C → List.Vector (BitVec 8) 32) (mpl : MultiPlacement) :
    SpecSimulates
      (withMlKemRoOk mpl (keepsFs
        (kemEncapsProjSpec stk KList ret pkA (fun x => (pk x).toList) rA (fun x => (rand x).toList))))
      (withMlKemRoOk mpl (keepsFs (kemEncapsVecProjSpec stk K ret pkA pk rA rand))) := by
  refine SpecSimulates.of_map ?_
  intro y R s0 hm
  refine ⟨y, R, ?_, fun sf _ _ hpost => ?_⟩
  · dsimp only [withMlKemRoOk, keepsFs, kemEncapsVecProjSpec] at hm
    dsimp only [withMlKemRoOk, keepsFs, kemEncapsProjSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    rcases hm with ⟨hro, hm⟩
    refine ⟨hro, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    rcases hm with ⟨⟨hx0, hx1, hx8⟩, hm⟩
    exact ⟨⟨hx0, hx1, hx8, (pk y).toList_length, (rand y).toList_length⟩, hm⟩
  · dsimp only [withMlKemRoOk, keepsFs, kemEncapsProjSpec] at hpost
    dsimp only [withMlKemRoOk, keepsFs, kemEncapsVecProjSpec]
    obtain ⟨h1, h2⟩ := hK (pk y) (rand y)
    rw [h1, h2]
    exact hpost

/-! ## 6. Spilled Callee-Saved Frame (`[sp0 - 160, sp0)`) -/

/-- Spilled callee-saved registers (`d15..d8`, `x29, x30`, `x28..x19`) at `[sp0 - 160, sp0)`. -/
@[expose] def SavedFrame07 (sp0 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 160#64) ↦₆₄ (s0.readVReg128 15#5).truncate 64) ∗
  ((sp0 - 152#64) ↦₆₄ (s0.readVReg128 14#5).truncate 64) ∗
  ((sp0 - 144#64) ↦₆₄ (s0.readVReg128 13#5).truncate 64) ∗
  ((sp0 - 136#64) ↦₆₄ (s0.readVReg128 12#5).truncate 64) ∗
  ((sp0 - 128#64) ↦₆₄ (s0.readVReg128 11#5).truncate 64) ∗
  ((sp0 - 120#64) ↦₆₄ (s0.readVReg128 10#5).truncate 64) ∗
  ((sp0 - 112#64) ↦₆₄ (s0.readVReg128 9#5).truncate 64) ∗
  ((sp0 - 104#64) ↦₆₄ (s0.readVReg128 8#5).truncate 64) ∗
  ((sp0 - 96#64)  ↦₆₄ s0.readReg64 .fp) ∗
  ((sp0 - 88#64)  ↦₆₄ s0.readReg64 .lr) ∗
  ((sp0 - 80#64)  ↦₆₄ s0.readReg64 .x28) ∗
  ((sp0 - 72#64)  ↦₆₄ s0.readReg64 .x27) ∗
  ((sp0 - 64#64)  ↦₆₄ s0.readReg64 .x26) ∗
  ((sp0 - 56#64)  ↦₆₄ s0.readReg64 .x25) ∗
  ((sp0 - 48#64)  ↦₆₄ s0.readReg64 .x24) ∗
  ((sp0 - 40#64)  ↦₆₄ s0.readReg64 .x23) ∗
  ((sp0 - 32#64)  ↦₆₄ s0.readReg64 .x22) ∗
  ((sp0 - 24#64)  ↦₆₄ s0.readReg64 .x21) ∗
  ((sp0 - 16#64)  ↦₆₄ s0.readReg64 .x20) ∗
  ((sp0 - 8#64)   ↦₆₄ s0.readReg64 .x19)

theorem savedFrame07_entails_memRegion160 (sp0 : BitVec 64) (s0 : State) :
    SavedFrame07 sp0 s0 ⊢ memRegion (sp0 - 160#64) 160 := by
  unfold SavedFrame07
  have hsplit :
      memRegion (sp0 - 160#64) 160 =
        memRegion (sp0 - 160#64) 8 ∗ memRegion (sp0 - 152#64) 8 ∗
        memRegion (sp0 - 144#64) 8 ∗ memRegion (sp0 - 136#64) 8 ∗
        memRegion (sp0 - 128#64) 8 ∗ memRegion (sp0 - 120#64) 8 ∗
        memRegion (sp0 - 112#64) 8 ∗ memRegion (sp0 - 104#64) 8 ∗
        memRegion (sp0 - 96#64) 8 ∗ memRegion (sp0 - 88#64) 8 ∗
        memRegion (sp0 - 80#64) 8 ∗ memRegion (sp0 - 72#64) 8 ∗
        memRegion (sp0 - 64#64) 8 ∗ memRegion (sp0 - 56#64) 8 ∗
        memRegion (sp0 - 48#64) 8 ∗ memRegion (sp0 - 40#64) 8 ∗
        memRegion (sp0 - 32#64) 8 ∗ memRegion (sp0 - 24#64) 8 ∗
        memRegion (sp0 - 16#64) 8 ∗ memRegion (sp0 - 8#64) 8 := by
    rw [memRegion_split' (b' := sp0 - 152#64) (n := 8) (k := 152) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 152#64) (b' := sp0 - 144#64) (n := 8) (k := 144) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 144#64) (b' := sp0 - 136#64) (n := 8) (k := 136) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 136#64) (b' := sp0 - 128#64) (n := 8) (k := 128) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 128#64) (b' := sp0 - 120#64) (n := 8) (k := 120) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 120#64) (b' := sp0 - 112#64) (n := 8) (k := 112) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 112#64) (b' := sp0 - 104#64) (n := 8) (k := 104) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 104#64) (b' := sp0 - 96#64) (n := 8) (k := 96) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 96#64) (b' := sp0 - 88#64) (n := 8) (k := 88) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 88#64) (b' := sp0 - 80#64) (n := 8) (k := 80) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 80#64) (b' := sp0 - 72#64) (n := 8) (k := 72) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 72#64) (b' := sp0 - 64#64) (n := 8) (k := 64) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 64#64) (b' := sp0 - 56#64) (n := 8) (k := 56) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 56#64) (b' := sp0 - 48#64) (n := 8) (k := 48) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 48#64) (b' := sp0 - 40#64) (n := 8) (k := 40) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 40#64) (b' := sp0 - 32#64) (n := 8) (k := 32) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 32#64) (b' := sp0 - 24#64) (n := 8) (k := 24) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 24#64) (b' := sp0 - 16#64) (n := 8) (k := 16) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp0 - 16#64) (b' := sp0 - 8#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide)]
  rw [hsplit]
  refine sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
      (cell_entails_memRegion8 _ _)))))))))))))))))))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
