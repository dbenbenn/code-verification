/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.GenPlacedFetches
public import ProofLib.GenPlacedOddSites
public import ProofLib.Placed.Multi
public import ProofLib.Placed.AdrpLdst
public import ProofLib.Placed.OpcodeExclusion
public import ProofLib.RelocDecode
public import ProofLib.SepLogic.SafeSepWP
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public meta import Lean
public meta import ProofLib
public meta import ProofLib.ProgramReflection
public meta import ProofLib.GenDecodes
public meta import ProofLib.GenPlacedFetches
public meta import ProofLib.GenPlacedOddSites

/-!
# Multi-block placement, cross-block calls, and SIMD `:lo12:` fetch infrastructure

Exports:
- `MlKemPlacement`, `mlkemMpl`, `mbase`: ambient multi-block placement for `mlkemMultiLib`.
- `@[simp, arm64_norm, wp_norm]` symbol resolution lemmas (`resolve_blk00`..`resolve_blk31`
  and `resolve_ro00`..`resolve_ro10`).
- `MlKemBlockOk`, `MlKemBlockConstOk`, `MlKemBlockSafeOk`: per-block total (`subroutine_ok`)
  and partial (`safe_subroutine_ok`) subroutine contracts and `O(1)` cross-block call transfer.
- `wp_mlkem_call` and `wp_mlkem_tailcall`: cross-block `BL` and `B` tactics preserving
  `mlkemMultiLib.CodeLoaded mlkemMpl` across arbitrary memory writes.
- `MlKemBase`, `mlkemLeaf_ok`, `mlkemCaller_ok`, `mlkemSafeCaller_ok`, and
  `mlkemBlockPlacement_ρ`: per-block entry combinators paired with `gen_block_fetches`.
- `fetch_rebase_ldst128Lo12_site` and `gen_mlkem_ldst128_site`: `O(log N)` fetch lemmas for
  128-bit SIMD `.ldst128Lo12` (`LDR Qt, [Xn, :lo12:cst16.<k>]`) relocation sites.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)

/-! ## 1. Ambient Multi-Block Placement & Static Block Properties -/

/-- Ambient valid multi-block placement for `mlkemMultiLib`. -/
class MlKemPlacement where
  mpl : MultiPlacement
  placeable : mlkemMultiLib.Placeable mpl

/-- Ambient `MultiPlacement` projection. -/
abbrev mlkemMpl [MlKemPlacement] : MultiPlacement :=
  MlKemPlacement.mpl

/-- Base address `mpl.base i` of block `i` under `MlKemPlacement`. -/
abbrev mbase [MlKemPlacement] (i : Nat) : BitVec 64 :=
  MlKemPlacement.mpl.base i

@[simp] theorem mlkemMultiLib_blocks_length : mlkemMultiLib.blocks.length = 32 := rfl

private theorem add_zero_64 (x : BitVec 64) : x + BitVec.ofNat 64 0 = x :=
  BitVec.add_zero x

/-! ## 2. Block & `.rodata` Symbol Resolution Normalization -/

@[simp, arm64_norm, wp_norm] theorem resolve_blk00 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_sha3::generic_keccak::simd128::keccak2::<72, 6>" = mpl.base 0 :=
  add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk01 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 31>" = mpl.base 1 :=
  add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk02 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_sha3::generic_keccak::simd128::keccak2::<136, 6>" = mpl.base 2 :=
  add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk03 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_ml_kem::ind_cca::incremental::neon::encapsulate1_serialized::<3, 1088, 960, 10, 320, 2, 128, 2, 128>" = mpl.base 3 :=
  add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk04 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_ml_kem::ind_cca::incremental::neon::decapsulate_compressed_key::<3, 1152, 2400, 1152, 1184, 1088, 1152, 960, 128, 10, 4, 320, 2, 128, 2, 128, 1120>" = mpl.base 4 :=
  add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk05 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_ml_kem::ind_cca::incremental::neon::generate_keypair_compressed::<3, 1152, 1152, 2400, 1184, 1152, 2, 128, 2400>" = mpl.base 5 :=
  add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk06 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_ml_kem::ind_cca::instantiations::neon::kyber_decapsulate::<4, 3168, 1536, 1568, 1568, 1536, 1408, 160, 11, 5, 352, 2, 128, 2, 128, 1600>" = mpl.base 6 :=
  add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk07 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_ml_kem::ind_cca::instantiations::neon::kyber_encapsulate::<4, 1568, 1568, 1536, 1408, 160, 11, 5, 352, 2, 128, 2, 128>" = mpl.base 7 :=
  add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk08 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "<libcrux_sha3::generic_keccak::KeccakState<2, core::core_arch::arm_shared::neon::uint64x2_t> as libcrux_sha3::traits::Squeeze2<core::core_arch::arm_shared::neon::uint64x2_t>>::squeeze2::<136>" = mpl.base 8 :=
  add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk09 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "<libcrux_sha3::generic_keccak::KeccakState<2, core::core_arch::arm_shared::neon::uint64x2_t> as libcrux_sha3::traits::Absorb<2>>::load_block::<136>" = mpl.base 9 :=
  add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk10 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "<libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes>::from_seed" = mpl.base 10 :=
  add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk11 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "<libcrux_ml_kem::ind_cca::incremental::types::EncapsState<3, libcrux_ml_kem::vector::neon::vector_type::SIMD128Vector>>::to_bytes" = mpl.base 11 :=
  add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk12 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_ml_kem::constant_time_ops::is_non_zero" = mpl.base 12 :=
  add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk13 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_ml_kem::constant_time_ops::compare_ciphertexts_in_constant_time" = mpl.base 13 :=
  add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk14 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_ml_kem::constant_time_ops::select_shared_secret_in_constant_time" = mpl.base 14 :=
  add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk15 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_ml_kem::constant_time_ops::inz" = mpl.base 15 :=
  add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk16 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_ml_kem::constant_time_ops::compare_ciphertexts_select_shared_secret_in_constant_time" = mpl.base 16 :=
  add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk17 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_ml_kem::constant_time_ops::compare" = mpl.base 17 :=
  add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk18 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_ml_kem::constant_time_ops::select_ct" = mpl.base 18 :=
  add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk19 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_ml_kem::mlkem768::incremental::encapsulate1" = mpl.base 19 :=
  add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk20 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_ml_kem::mlkem768::incremental::encapsulate2" = mpl.base 20 :=
  add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk21 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_ml_kem::mlkem768::incremental::validate_pk_bytes" = mpl.base 21 :=
  add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk22 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key" = mpl.base 22 :=
  add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk23 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_ml_kem::mlkem1024::kyber::decapsulate" = mpl.base 23 :=
  add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk24 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_ml_kem::mlkem1024::kyber::encapsulate" = mpl.base 24 :=
  add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk25 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "<libcrux_ml_kem::vector::portable::vector_type::PortableVector as libcrux_ml_kem::vector::traits::Operations>::deserialize_4" = mpl.base 25 :=
  add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk26 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "<libcrux_ml_kem::vector::portable::vector_type::PortableVector as libcrux_ml_kem::vector::traits::Operations>::deserialize_5" = mpl.base 26 :=
  add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk27 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "<libcrux_ml_kem::vector::portable::vector_type::PortableVector as libcrux_ml_kem::vector::traits::Operations>::deserialize_11" = mpl.base 27 :=
  add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk28 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "memcpy" = mpl.base 28 :=
  add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk29 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "memset" = mpl.base 29 :=
  add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk30 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "bcmp" = mpl.base 30 :=
  add_zero_64 _
@[simp, arm64_norm, wp_norm] theorem resolve_blk31 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "memcmp" = mpl.base 31 :=
  add_zero_64 _

-- `.rodata` symbol resolution → `mpl.ρ sym`
@[simp, arm64_norm, wp_norm] theorem resolve_ro00 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0" =
      mpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0" := rfl
@[simp, arm64_norm, wp_norm] theorem resolve_ro01 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" =
      mpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" := rfl
@[simp, arm64_norm, wp_norm] theorem resolve_ro02 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_ml_kem:.rodata.cst16.0" =
      mpl.ρ "libcrux_ml_kem:.rodata.cst16.0" := rfl
@[simp, arm64_norm, wp_norm] theorem resolve_ro03 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_ml_kem:.rodata.cst16.1" =
      mpl.ρ "libcrux_ml_kem:.rodata.cst16.1" := rfl
@[simp, arm64_norm, wp_norm] theorem resolve_ro04 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_ml_kem:.rodata.cst16.2" =
      mpl.ρ "libcrux_ml_kem:.rodata.cst16.2" := rfl
@[simp, arm64_norm, wp_norm] theorem resolve_ro05 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_ml_kem:.rodata.cst16.3" =
      mpl.ρ "libcrux_ml_kem:.rodata.cst16.3" := rfl
@[simp, arm64_norm, wp_norm] theorem resolve_ro06 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_ml_kem:.rodata.cst16.4" =
      mpl.ρ "libcrux_ml_kem:.rodata.cst16.4" := rfl
@[simp, arm64_norm, wp_norm] theorem resolve_ro07 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_ml_kem:.rodata.cst16.5" =
      mpl.ρ "libcrux_ml_kem:.rodata.cst16.5" := rfl
@[simp, arm64_norm, wp_norm] theorem resolve_ro08 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_ml_kem:.rodata.cst16.6" =
      mpl.ρ "libcrux_ml_kem:.rodata.cst16.6" := rfl
@[simp, arm64_norm, wp_norm] theorem resolve_ro09 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_ml_kem:.rodata.cst16.7" =
      mpl.ρ "libcrux_ml_kem:.rodata.cst16.7" := rfl
@[simp, arm64_norm, wp_norm] theorem resolve_ro10 (mpl : MultiPlacement) :
    mlkemMultiLib.resolve mpl "libcrux_ml_kem:.rodata.cst16.8" =
      mpl.ρ "libcrux_ml_kem:.rodata.cst16.8" := rfl

/-! ## 3. Per-Block Total & Partial Subroutine Contracts & Call Combinators -/

/-- Layout-generic total (`subroutine_ok`) contract for block `j` under `MlKemPlacement`,
    wrapped with `mlkemMultiLib.withCodeLoaded mlkemMpl`. -/
abbrev MlKemBlockOk (j : Nat) {α S : Type} [ToBaseSpec S α]
    (spec : MultiPlacement → S) : Prop :=
  ∀ [MlKemPlacement],
    subroutine_ok (mlkemMultiLib.blockProgram mlkemMpl j)
      (mlkemMpl.base j)
      (mlkemMultiLib.withCodeLoaded mlkemMpl
        (ToBaseSpec.toSpec (spec mlkemMpl) (mlkemMpl.base j)))

/-- Placement-independent specialization of `MlKemBlockOk` (for functions with no `.rodata`
    symbol references). -/
abbrev MlKemBlockConstOk (j : Nat) {α S : Type} [ToBaseSpec S α]
    (spec : S) : Prop :=
  MlKemBlockOk j (fun _ => spec)

/-- Layout-generic partial-correctness (`safe_subroutine_ok`) contract for block `j` under
    `MlKemPlacement`, wrapped with `mlkemMultiLib.withCodeLoaded mlkemMpl` (used to prove
    unconditional memory/caller safety across rejection-sampled `SampleNTT` loops). -/
abbrev MlKemBlockSafeOk (j : Nat) {α S : Type} [ToBaseSpec S α]
    (spec : MultiPlacement → S) : Prop :=
  ∀ [MlKemPlacement],
    safe_subroutine_ok (mlkemMultiLib.blockProgram mlkemMpl j)
      (mlkemMpl.base j)
      (mlkemMultiLib.withCodeLoaded mlkemMpl
        (ToBaseSpec.toSpec (spec mlkemMpl) (mlkemMpl.base j)))

/-- Every `MlKemBlockOk` contract automatically weakens to `MlKemBlockSafeOk`. -/
theorem MlKemBlockOk.to_safe {j : Nat} {α S : Type} [ToBaseSpec S α]
    {spec : MultiPlacement → S} (hok : MlKemBlockOk j spec) :
    MlKemBlockSafeOk j spec :=
  fun [MlKemPlacement] => Arm64.subroutine_ok.to_safe hok

/-- Adjoin `lib.withCodeLoaded mpl` to any `subroutine_ok` contract. -/
theorem withCodeLoaded_of_subroutine_ok {α : Type} {lib : MultiPlacedLib}
    {mpl : MultiPlacement} {P : Program} {entry : BitVec 64} {spec : Spec α}
    (hok : subroutine_ok P entry spec) :
    subroutine_ok P entry (lib.withCodeLoaded mpl spec) := by
  refine subroutine_ok_mono hok (fun x R s0 hpre => ?_) (fun _ _ _ _ hp => hp)
  dsimp only [MultiPlacedLib.withCodeLoaded] at hpre
  rw [sepConj_comm (spec.pre x s0) ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.2

/-- Adjoin `lib.withCodeLoaded mpl` to any `safe_subroutine_ok` contract. -/
theorem withCodeLoaded_of_safe_subroutine_ok {α : Type} {lib : MultiPlacedLib}
    {mpl : MultiPlacement} {P : Program} {entry : BitVec 64} {spec : Spec α}
    (hok : safe_subroutine_ok P entry spec) :
    safe_subroutine_ok P entry (lib.withCodeLoaded mpl spec) := by
  refine hok.mono (fun x R s0 hpre => ?_) (fun _ _ _ _ hp => hp)
  dsimp only [MultiPlacedLib.withCodeLoaded] at hpre
  rw [sepConj_comm (spec.pre x s0) ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.2

/-- Switch the active `Program` in `safe_reaches` from `Q` to `P` when both have the same hooks
    and `svc` handler and `Q.CodeLoaded s0.mem` holds at `s0`. -/
theorem safe_reaches_of_sameHooks {P Q : Program} {s0 : State} {Goal : State → Prop}
    (hext : ∀ pc, Q.externAt? pc = P.externAt? pc) (hsvc : Q.svc = P.svc)
    (hQL : Q.CodeLoaded s0.mem) (hQ : safe_reaches Q s0 Goal) :
    safe_reaches P s0 Goal := by
  intro _
  rcases hQ hQL with ⟨sf, hsf, hG⟩ | hall
  · exact Or.inl ⟨sf, Steps.of_sameHooks hext hsvc hsf, hG⟩
  · refine Or.inr fun t ht => ?_
    have htQ : Steps Q s0 t := Steps.of_sameHooks (fun pc => (hext pc).symm) hsvc.symm ht
    have hrun := (hall t htQ).1
    exact ⟨hrun, Step.progress P hrun⟩

/-- Transfer a `safe_subroutine_ok` proved on block `j` of a `MultiPlacedLib` (wrapped with
    `lib.withCodeLoaded mpl`) to any hook-free program `P`. -/
theorem safe_subroutine_ok_of_block {α : Type} {lib : MultiPlacedLib}
    {mpl : MultiPlacement} {P : Program} {j : Nat} {entry : BitVec 64} {spec : Spec α}
    (hj : j < lib.blocks.length)
    (hcall : safe_subroutine_ok (lib.blockProgram mpl j) entry (lib.withCodeLoaded mpl spec))
    (hext : ∀ pc, P.externAt? pc = none := by intro; simp)
    (hsvc : P.svc = Syscall.standard := by rfl) :
    safe_subroutine_ok P entry (lib.withCodeLoaded mpl spec) := by
  intro x R s0 hentry hpre
  have hpre' : s0.mem ⊨ ⌜lib.CodeLoaded mpl s0.mem⌝ ∗ (spec.pre x s0 ∗ R) := by
    simpa [MultiPlacedLib.withCodeLoaded, sepConj_assoc] using hpre
  rw [satisfies_pure_sepConj] at hpre'
  exact safe_reaches_of_sameHooks
    (by intro pc; simp [hext pc])
    (by simp [hsvc, MultiPlacedLib.blockProgram, PlacedLib.program])
    (hpre'.1 j hj)
    (hcall x R s0 hentry hpre)

/-- Transfer a proved `MlKemBlockOk` or `MlKemBlockConstOk` contract for block `j` to any
    hook-free rebased block program `(lib.program pl).rebase b (fun _ => none)`. -/
theorem mlkemCall_of_blockOk [MlKemPlacement] (P : Program)
    {lib : PlacedLib} {pl : Placement} {b : BitVec 64} {j : Nat}
    {α : Type} {spec : Spec α}
    (hok : subroutine_ok (mlkemMultiLib.blockProgram mlkemMpl j) (mlkemMpl.base j)
      (mlkemMultiLib.withCodeLoaded mlkemMpl spec))
    (hP : P = (lib.program pl).rebase b (fun _ => none) := by rfl)
    (hj : j < mlkemMultiLib.blocks.length := by decide) :
    subroutine_ok P (mlkemMpl.base j)
      (mlkemMultiLib.withCodeLoaded mlkemMpl spec) := by
  subst hP
  exact mlkemMultiLib.subroutine_ok_of_block hj hok
    (fun pc => PlacedLib.externAt?_program_rebase_none lib pl b pc)
    rfl

/-- Transfer a proved `MlKemBlockSafeOk` contract for block `j` to any hook-free rebased block
    program `(lib.program pl).rebase b (fun _ => none)`. -/
theorem mlkemSafeCall_of_blockSafeOk [MlKemPlacement] (P : Program)
    {lib : PlacedLib} {pl : Placement} {b : BitVec 64} {j : Nat}
    {α : Type} {spec : Spec α}
    (hok : safe_subroutine_ok (mlkemMultiLib.blockProgram mlkemMpl j) (mlkemMpl.base j)
      (mlkemMultiLib.withCodeLoaded mlkemMpl spec))
    (hP : P = (lib.program pl).rebase b (fun _ => none) := by rfl)
    (hj : j < mlkemMultiLib.blocks.length := by decide) :
    safe_subroutine_ok P (mlkemMpl.base j)
      (mlkemMultiLib.withCodeLoaded mlkemMpl spec) := by
  subst hP
  exact safe_subroutine_ok_of_block hj hok
    (fun pc => PlacedLib.externAt?_program_rebase_none lib pl b pc)
    rfl

/-- Export a `MlKemBlockOk j spec` proof to `mlkemMultiLib.subroutineOk sym spec`. -/
theorem mlkemSubroutineOk_of_blockOk {j : Nat} {sym : String}
    {α S : Type} [ToBaseSpec S α] {spec : MultiPlacement → S}
    (hok : MlKemBlockOk j spec)
    (hexp : sym ∈ mlkemMultiLib.exports := by decide)
    (hsym : lookupBlockSym sym mlkemMultiLib.blocks = some (j, 0) := by decide) :
    mlkemMultiLib.subroutineOk sym spec := by
  refine ⟨hexp, j, 0, hsym, fun mpl hP => ?_⟩
  letI : MlKemPlacement := ⟨mpl, hP⟩
  have hfn : mlkemMultiLib.fnAddr mpl sym = mpl.base j := by
    simp [MultiPlacedLib.fnAddr, hsym]
  rw [hfn]
  exact hok

/-- Export a `MlKemBlockConstOk j spec` proof to `mlkemMultiLib.subroutineOk sym (fun _ => spec)`. -/
theorem mlkemSubroutineOk_of_constBlockOk {j : Nat} {sym : String}
    {α S : Type} [ToBaseSpec S α] {spec : S}
    (hok : MlKemBlockConstOk j spec)
    (hexp : sym ∈ mlkemMultiLib.exports := by decide)
    (hsym : lookupBlockSym sym mlkemMultiLib.blocks = some (j, 0) := by decide) :
    mlkemMultiLib.subroutineOk sym (fun _ => spec) :=
  mlkemSubroutineOk_of_blockOk (spec := fun _ => spec) hok hexp hsym

/-- Preserve `lib.CodeLoaded mpl` across a `BL` subroutine call returning to `s.readReg64 .lr`. -/
theorem seq_codeLoaded_lr {prog : Program} {target_pc : BitVec 64} {s : Arm64.State}
    {P : SepProp} {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp}
    {lib : MultiPlacedLib} {mpl : MultiPlacement}
    (hcl : lib.CodeLoaded mpl s.mem)
    (h : SepWP prog (s.readReg64 .lr) s P (fun sm Pm =>
      lib.CodeLoaded mpl sm.mem → SepWP prog target_pc sm Pm post oom) oom) :
    SepWP prog target_pc s P post oom :=
  MultiPlacedLib.seq_codeLoaded hcl h

open Lean Meta in
/-- Check whether the current `SepWP` goal's continuation is a `MultiPlacedLib.seq_codeLoaded`
    cut (`fun sm Pm => MultiPlacedLib.CodeLoaded ... sm.mem → ...`). -/
meta def goalIsSeqCodeLoaded (g : MVarId) : MetaM Bool := g.withContext do
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  unless ty.isAppOfArity ``SepWP 6 do return false
  let postExpr := (ty.getArg! 4).consumeMData
  unless postExpr.isLambda && postExpr.bindingBody!.consumeMData.isLambda do return false
  let body2 := postExpr.bindingBody!.consumeMData.bindingBody!.consumeMData
  match body2 with
  | .forallE _ dom _ _ => return dom.consumeMData.isAppOfArity ``MultiPlacedLib.CodeLoaded 3
  | _ => return false

open Lean Meta in
/-- Clear any existing `MultiPlacedLib.CodeLoaded` hypotheses from the current main goal
    before introducing a refreshed post-call `CodeLoaded` hypothesis, so sequential
    `wp_mlkem_call` invocations keep `O(1)` `CodeLoaded` hypotheses in context. -/
meta def clearOldCodeLoadedHyps : Elab.Tactic.TacticM Unit := do
  let g ← Elab.Tactic.getMainGoal
  let fvars ← g.withContext do
    let mut acc : Array FVarId := #[]
    for ld in ← getLCtx do
      if ld.isImplementationDetail then continue
      let ty := (← instantiateMVars ld.type).consumeMData
      if ty.isAppOfArity ``MultiPlacedLib.CodeLoaded 3 then
        acc := acc.push ld.fvarId
    return acc
  if !fvars.isEmpty then
    Elab.Tactic.replaceMainGoal [← g.tryClearMany fvars]

/-- Step a cross-block `BL` call to `hcall : MlKemBlockOk j spec` in `O(1)`, closing any active
    `wp_cut_codeLoaded` segment before the call and refreshing `mlkemMultiLib.CodeLoaded`
    on the post-call memory `sf.mem`. -/
syntax "wp_mlkem_call" ppSpace colGt term:max (ppSpace colGt wppCallOpt)* : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| wp_mlkem_call $hcall:term $[$opts:wppCallOpt]*) => do
    if ← goalIsSeqCodeLoaded (← getMainGoal) then
      let hclPre ← mkFreshUserName `hcl_pre
      let hclPreId := mkIdent hclPre
      evalTactic (← `(tactic| (
        apply SepWP.done
        · first | wp_norm_lhs | wp_norm_goal | rfl
        · first | assumption | wp_norm_lhs
        intro $hclPreId:ident)))
    let gCur ← getMainGoal
    let progStx ← gCur.withContext do
      let ty := (← instantiateMVars (← gCur.getType)).consumeMData
      unless ty.isAppOfArity ``SepWP 6 do
        throwError "wp_mlkem_call: expected `SepWP` goal, got `{ty}`"
      Term.exprToSyntax (ty.getArg! 0)
    let hclPost ← mkFreshUserName `hcl_post
    let hclPostId := mkIdent hclPost
    evalTactic (← `(tactic| (
      apply seq_codeLoaded_lr ‹_›
      wp_call (mlkemCall_of_blockOk $progStx $hcall) $[$opts]*)))
    let postCallGoals ← getGoals
    let mut newGoals : List MVarId := []
    for g in postCallGoals do
      if ← goalIsSeqCodeLoaded g then
        setGoals [g]
        evalTactic (← `(tactic| (
          apply SepWP.done
          · first | assumption | wp_norm_lhs | wp_norm_goal | rfl
          · first | assumption | wp_norm_lhs)))
        clearOldCodeLoadedHyps
        evalTactic (← `(tactic| intro $hclPostId:ident))
        newGoals := newGoals ++ (← getGoals)
      else
        newGoals := newGoals ++ [g]
    setGoals newGoals

/-- Step a cross-block `B` tail-jump to `hcall : MlKemBlockOk j spec` in `O(1)`, closing any active
    `wp_cut_codeLoaded` segment before the tail-jump. -/
syntax "wp_mlkem_tailcall" ppSpace colGt term:max : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| wp_mlkem_tailcall $hcall:term) => do
    if ← goalIsSeqCodeLoaded (← getMainGoal) then
      let hclPre ← mkFreshUserName `hcl_pre
      let hclPreId := mkIdent hclPre
      evalTactic (← `(tactic| (
        apply SepWP.done
        · first | wp_norm_lhs | wp_norm_goal | rfl
        · first | assumption | wp_norm_lhs
        intro $hclPreId:ident)))
    let gCur ← getMainGoal
    let progStx ← gCur.withContext do
      let ty := (← instantiateMVars (← gCur.getType)).consumeMData
      unless ty.isAppOfArity ``SepWP 6 do
        throwError "wp_mlkem_tailcall: expected `SepWP` goal, got `{ty}`"
      Term.exprToSyntax (ty.getArg! 0)
    evalTactic (← `(tactic| wp_tailcall (mlkemCall_of_blockOk $progStx $hcall)))

/-! ## 4. Per-Block Entry Combinators (`MlKemBase`, `mlkemLeaf_ok`, `mlkemCaller_ok`, `mlkemSafeCaller_ok`) -/

@[simp, arm64_norm, wp_norm]
theorem add_off_reloc_cancel (b target off : BitVec 64) :
    b + off + (target - b - off) = target := by
  bv_omega

@[simp, arm64_norm, wp_norm]
theorem add_zero_reloc_cancel (b target : BitVec 64) :
    b + (target - b - 0#64) = target := by
  bv_omega

@[simp, arm64_norm, wp_norm]
theorem add_reloc_cancel (b target : BitVec 64) :
    b + (target - b) = target := by
  bv_omega

/-- Reducible abbreviation for `b = pl.base` that is not syntactically an `Eq`,
    preventing `wp_steps` from rewriting `b` in `b + off#64` PCs while allowing `tryPairStepHook`
    to discharge `b = pl.base` by reducible `assumption`. -/
abbrev MlKemBase (pl : Placement) (b : BitVec 64) : Prop :=
  b = pl.base

/-- Pure-leaf entry combinator for block `j`: reduces `MlKemBlockOk` or `MlKemBlockConstOk`
    to proving `subroutine_ok (P.rebase b (fun _ => none)) b ...` with `hb : MlKemBase pl b` and
    `hbase : pl.base = b` in context. -/
theorem mlkemLeaf_ok [MlKemPlacement] {j : Nat} (P : Program) (pl : Placement)
    {α S : Type} [ToBaseSpec S α] {spec : S}
    (hpl : pl = mlkemMultiLib.blockPlacement mlkemMpl j := by rfl)
    (hP : P = (mlkemMultiLib.blockLib j).program pl := by rfl)
    (h : ∀ (b : BitVec 64), MlKemBase pl b → pl.base = b →
      subroutine_ok (P.rebase b (fun _ => none)) b
        (ToBaseSpec.toSpec spec b)) :
    subroutine_ok (mlkemMultiLib.blockProgram mlkemMpl j) (mlkemMpl.base j)
      (mlkemMultiLib.withCodeLoaded mlkemMpl
        (ToBaseSpec.toSpec spec (mlkemMpl.base j))) := by
  subst hpl hP
  exact withCodeLoaded_of_subroutine_ok (lib := mlkemMultiLib) (mpl := mlkemMpl)
    (h (mlkemMultiLib.blockPlacement mlkemMpl j).base rfl rfl)

/-- Cross-block caller entry combinator for block `j` (`subroutine_ok`). -/
theorem mlkemCaller_ok [MlKemPlacement] {j : Nat} (P : Program) (pl : Placement)
    {α S : Type} [ToBaseSpec S α] {spec : S}
    (hpl : pl = mlkemMultiLib.blockPlacement mlkemMpl j := by rfl)
    (hP : P = (mlkemMultiLib.blockLib j).program pl := by rfl)
    (h : ∀ (b : BitVec 64), MlKemBase pl b → pl.base = b →
      subroutine_ok (P.rebase b (fun _ => none)) b
        (mlkemMultiLib.withCodeLoaded mlkemMpl
          (ToBaseSpec.toSpec spec b))) :
    subroutine_ok (mlkemMultiLib.blockProgram mlkemMpl j) (mlkemMpl.base j)
      (mlkemMultiLib.withCodeLoaded mlkemMpl
        (ToBaseSpec.toSpec spec (mlkemMpl.base j))) := by
  subst hpl hP
  exact h (mlkemMultiLib.blockPlacement mlkemMpl j).base rfl rfl

/-- Cross-block caller entry combinator for block `j` (`safe_subroutine_ok`). -/
theorem mlkemSafeCaller_ok [MlKemPlacement] {j : Nat} (P : Program) (pl : Placement)
    {α S : Type} [ToBaseSpec S α] {spec : S}
    (hpl : pl = mlkemMultiLib.blockPlacement mlkemMpl j := by rfl)
    (hP : P = (mlkemMultiLib.blockLib j).program pl := by rfl)
    (h : ∀ (b : BitVec 64), MlKemBase pl b → pl.base = b →
      safe_subroutine_ok (P.rebase b (fun _ => none)) b
        (mlkemMultiLib.withCodeLoaded mlkemMpl
          (ToBaseSpec.toSpec spec b))) :
    safe_subroutine_ok (mlkemMultiLib.blockProgram mlkemMpl j) (mlkemMpl.base j)
      (mlkemMultiLib.withCodeLoaded mlkemMpl
        (ToBaseSpec.toSpec spec (mlkemMpl.base j))) := by
  subst hpl hP
  exact h (mlkemMultiLib.blockPlacement mlkemMpl j).base rfl rfl

/-- Normalize `(mlkemMultiLib.blockPlacement mlkemMpl j).ρ sym` to
    `mlkemMultiLib.resolve mlkemMpl sym` so `resolve_blk*` and `resolve_ro*` fire automatically. -/
@[simp, arm64_norm, wp_norm]
theorem mlkemBlockPlacement_ρ [MlKemPlacement] (j : Nat) (sym : String) :
    (mlkemMultiLib.blockPlacement mlkemMpl j).ρ sym =
      mlkemMultiLib.resolve mlkemMpl sym := rfl

/-! ## 5. 128-Bit SIMD `:lo12:` Fetch Rule (`R_AARCH64_LDST128_ABS_LO12_NC`) -/

set_option linter.literalFetch false in
/-- At a 128-bit SIMD unsigned-immediate load site (`LDR Qt, [Xn, :lo12:sym]`) with an
    `.ldst128Lo12` relocation, the fetched instruction in `(prog.rebase b X)` is
    `Instr.ldrSimd .Q128 vt (.Offset rn (lo12Of T))` for every base `b`, so `pageOf_add_lo12Of`
    folds `pageOf T + lo12Of T = T`. -/
theorem fetch_rebase_ldst128Lo12_site {lib : PlacedLib} {prog : Program} {pl : Placement}
    {b : BitVec 64} {X : String → Option (State → State)} {off : Nat} {r : RelocEntry}
    {w : BitVec 32} {vt : BitVec 5} {rn : Reg} {T : BitVec 64}
    (hprog : prog = lib.program pl) (hP : lib.Placeable pl)
    (hr : lib.text.relocAt? off = some r) (hk : r.kind = .ldst128Lo12)
    (hh : ((lib.program pl).rebase b X).hookAtOff? off = none)
    (hwd : lib.text.wordAt off = w)
    (htype : decodeSimdLoadStoreType (w.extractLsb' 30 2).toNat (w.extractLsb' 22 2).toNat =
      some (true, .Q128, 4))
    (hw1 : w &&& 0x3f000000#32 = 0x3d000000#32)
    (hvt : w.extractLsb' 0 5 = vt)
    (hrn : Reg.fromSPBits (w.extractLsb' 5 5) = rn)
    (hT : lib.text.target pl r = T) :
    (prog.rebase b X).fetch (b + BitVec.ofNat 64 off) =
      some (.ldrSimd .Q128 vt (.Offset rn (lo12Of T))) := by
  subst hprog hT hwd hvt hrn
  have hroff := CodeBlock.relocAt?_off hr
  obtain ⟨hal4, hlen, hrange⟩ := hP.text.relocs_ok r (CodeBlock.relocAt?_mem hr)
  rw [hroff] at hal4 hlen hrange
  have hnw := hP.text.no_wrap
  have hka : r.kind ≠ .adrpHi21 := by rw [hk]; decide
  have hkadd : r.kind ≠ .addLo12 := by rw [hk]; decide
  have hkc : r.kind ≠ .call26 := by rw [hk]; decide
  have hkj : r.kind ≠ .jump26 := by rw [hk]; decide
  have hng : r.kind.isGotOrTlsIe = false := by rw [hk]; rfl
  have hnrel : lib.text.relaxableAt off = false := CodeBlock.relaxableAt_false_of_kind hr hka
  have hb2b : lib.text.b2bNext? r = none := by simp [CodeBlock.b2bNext?, hkc, hkj]
  rw [CodeBlock.relocInRange_of_not_gotOrTlsIe hng,
    CodeBlock.relocTarget_of_b2bNext_none hb2b, hk] at hrange
  change Lo12Aligned 4 _ at hrange
  have hfetch := Program.fetch_of_readWordOff (prog := (lib.program pl).rebase b X)
    (off := off) (by omega) hh
    (CodeBlock.readWordOff_patched (blk := lib.text) (pl := pl) rfl hal4 hlen)
  rw [CodeBlock.patchedWord_of_unpaired hr hnrel hkadd hkc hkj hng, hk] at hfetch
  simp only [patchRelocWord] at hfetch
  rw [Arm64.Obj.decode_ldstSimdLo12Word htype hw1 hrange] at hfetch
  simpa [Program.rebase] using hfetch

/-- Elaborate `@[simp, arm64_norm] <pfx>PC<NN>_rebase_fetch_0x<off>` for every `.ldst128Lo12`
    (`LDR Qt, [Xn, :lo12:sym]`) relocation site of `<lib>` within `[<ranges>]` in `O(log N)`
    steps via `<tree>.getQuad?`. -/
syntax (name := genMlkemLdst128Stx)
  "gen_mlkem_ldst128 " ident ident ident ident ident " via_placement " ident ident
    " [" decodeRange,* "]" : command

open Lean Meta Elab Term Command ProofLib.GenPlacedFetches in
@[command_elab genMlkemLdst128Stx]
meta def elabGenMlkemLdst128 : CommandElab := fun stx => do
  match stx with
  | `(gen_mlkem_ldst128 $prog:ident $lib:ident $tree:ident $hcode:ident $hsize:ident
        via_placement $plOf:ident $hPOf:ident [$rs:decodeRange,*]) =>
    let mut offs := #[]
    for r in rs.getElems do offs := offs ++ (← rangeOffsets r)
    let sites ← liftTermElabM do
      let progName ← realizeGlobalConstNoOverloadWithInfo prog
      let libName ← realizeGlobalConstNoOverloadWithInfo lib
      let treeName ← realizeGlobalConstNoOverloadWithInfo tree
      let treeVal ← ProofLib.GenDecodes.treeValueOf treeName
      let libE := Lean.mkConst libName
      let relocs ← relocEntries libE
      let mut relocMap : Std.HashMap Nat (Nat × Name × Expr × Expr) := {}
      for entry in relocs do
        if !relocMap.contains entry.1 then
          relocMap := relocMap.insert entry.1 entry
      let pfxStr := progName.getString!
      let mut out : Array (Ident × Nat × Nat × String × Nat × Nat) := #[]
      for off in offs do
        let some (_, kn, symE, rE) := relocMap.get? off | continue
        unless kn == ``RelocKind.ldst128Lo12 do continue
        let sym ← symStringOf symE
        let addend ← addendOf rE
        unless addend == 0 && off % 4 == 0 do continue
        let w0 ← wordOfTreeVal treeVal off
        unless w0 &&& 0x3f000000 == 0x3d000000 &&
            (w0 >>> 30) % 4 == 0 && (w0 >>> 22) % 4 == 3 do continue
        let vt := w0 % 32
        let rn := (w0 >>> 5) % 32
        let thmIdent := mkIdentFrom prog (hexName pfxStr "rebase_fetch" off)
        out := out.push (thmIdent, off, off / 4, sym, vt, rn)
      return out
    withScope (fun sc => { sc with opts := sc.opts.set `linter.literalFetch false }) do
      for (thmId, off, qIdx, sym, vt, rn) in sites do
        let offT := Syntax.mkNumLit (toString off)
        let qIdxT := Syntax.mkNumLit (toString qIdx)
        let vtT := Syntax.mkNumLit (toString vt)
        let symT := Syntax.mkStrLit sym
        let rnT : Term ←
          if rn == 31 then `(Reg.sp)
          else `(Reg.gpr (BitVec.ofNat 5 $(Syntax.mkNumLit (toString rn))))
        elabCommand (← `(command|
          @[simp, arm64_norm]
          theorem $thmId [MlKemPlacement] (b : BitVec 64)
              (X : String → Option (State → State)) :
              (($prog).rebase b X).fetch (b + BitVec.ofNat 64 $offT) =
                some (.ldrSimd .Q128 (BitVec.ofNat 5 $vtT)
                  (.Offset $rnT (lo12Of (($plOf).ρ $symT)))) :=
            fetch_rebase_ldst128Lo12_site
              (lib := $lib) (prog := $prog) (pl := $plOf)
              (b := b) (X := X) (off := $offT)
              (r := { off := $offT, kind := .ldst128Lo12, sym := $symT })
              rfl $hPOf (by decide +kernel) rfl
              (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) $offT)
              (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := $qIdxT) $hcode $hsize (by decide +kernel))
              rfl rfl rfl rfl
              (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)))
  | _ => throwUnsupportedSyntax

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
