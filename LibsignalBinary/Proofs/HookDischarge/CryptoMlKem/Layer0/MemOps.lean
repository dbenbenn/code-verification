/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLift
import VerifiedLibraries.Musl.Proofs.MemcpySym
import VerifiedLibraries.Musl.Proofs.MemsetSym
import VerifiedLibraries.Musl.Proofs.MemcmpProof

/-!
# Zero-Stack Memory Operations (`B28`–`B31`)

Placement-independent contracts with `NonSyscallPreserved` for `memcpy` (`B28`, RO and RW source),
`memset` (`B29`), `bcmp` (`B30`, RO and mixed RW/RO), and `memcmp` (`B31`): `blk28_memcpyRO_ok`,
`blk28_memcpy_ok`, `blk29_memset_ok`, `blk31_bcmpRO_ok`, `blk30_bcmpRO_ok`, and
`blk30_bcmpRW1RO_ok`.
-/

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase
  MlKemBlockConstOk
  MlKemPlacement
  mbase
  mlkemBlockPlacement_ρ
  mlkemCall_of_blockOk
  mlkemCaller_ok
  mlkemMpl
  resolve_blk31
  withCodeLoaded_of_subroutine_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  mlkemBcmpROSpec
  mlkemBcmpRW1ROSpec
  mlkemMemcpyROSpec
  mlkemMemcpySpec
  mlkemMemsetSpec
  withNonSyscallPreserved
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
open VerifiedLibraries.Musl (
  RoSlice8
  SliceLenPair
  memcmpBytes_eq_zero_iff
  memcmpLibcaWords
  memcmpROPreservingSpec
  memcmpROPreserving_libca_codeAt_ok
  memcmpROSpec
  memcpySrc
  memcpySymWords
  memcpy_sepwp
  memsetSymSpec
  memsetWordsSym
  memset_codeAt_ok_sym
  withMemcmpPreserved
)

gen_block_fetches mlkem 30 mlkemMultiLib MlKemPlacement 1

@[simp, arm64_norm, wp_norm]
private theorem mlkemPl30_ρ [MlKemPlacement] (sym : String) :
    mlkemPl30.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

private theorem mlkemBlock_hasWords_relocFree [MlKemPlacement] (i : Nat)
    (hi : i < mlkemMultiLib.blocks.length) (ws : List (BitVec 32))
    (hchk : (mlkemMultiLib.blocks[i]'hi).checkSegment 0 ws [] = true) :
    (mlkemMultiLib.blockProgram mlkemMpl i).hasWords (mlkemMpl.base i) ws := by
  have ⟨hw, _⟩ := mlkemMultiLib.hasWords_of_checkSegment hi (fo := 0) (ws := ws) (R := [])
    (X := fun _ => none) (svc := Syscall.standard) MlKemPlacement.placeable hchk
  have hb0 : mlkemMpl.base i + BitVec.ofNat 64 0 = mlkemMpl.base i := by bv_omega
  have hpr : Obj.patchRelocs [] ws (mlkemMpl.base i + BitVec.ofNat 64 0)
      (mlkemMultiLib.resolve mlkemMpl) = ws := by
    simp [Obj.patchRelocs]
  rwa [hpr, hb0] at hw

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

/-! ## 1. `B28` (`memcpy`) -/

private abbrev mlkemMemcpyROBaseSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := mlkemMemcpyROSpec.pre
  post := fun (dst, src, bs) _s0 sf =>
    ⌜sf.readReg64 .x0 = dst⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ᵣ bs)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private abbrev mlkemMemcpyBaseSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := mlkemMemcpySpec.pre
  post := fun (dst, src, bs) _s0 sf =>
    ⌜sf.readReg64 .x0 = dst⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ₛ bs)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem memcpy_len_le {m : Memory} {ro : Bool} {dst src : BitVec 64}
    {bs : List (BitVec 8)} {R : SepProp} (hlen : bs.length ≤ 2 ^ 64)
    (h : m ⊨ memRegion dst bs.length ∗ memcpySrc ro src bs ∗ R) :
    bs.length ≤ 2 ^ 63 := by
  have hro : m ⊨ (src ↦ᵣ bs) ∗ (memRegion dst bs.length ∗ R) := by
    cases ro <;> dsimp only [memcpySrc, Bool.cond_true, Bool.cond_false] at h
    · refine Satisfies.pointsToBytes_to_ro ?_
      rwa [← sepConj_assoc, sepConj_comm (src ↦ₛ bs), sepConj_assoc]
    · rwa [← sepConj_assoc, sepConj_comm (src ↦ᵣ bs), sepConj_assoc]
  have hsep : ∀ a, InRegion src bs.length a → ¬InRegion dst bs.length a := fun a hs hd =>
    not_satisfies_ownsRO_ownsRW (ownsRO_pointsToBytesRO_at hlen hs)
      (ownsRW_sepConj_left (ownsRW_memRegion dst bs.length a hd)) hro
  have hself : ∀ b : BitVec 64, bs.length > 2 ^ 63 → InRegion b bs.length b := fun b hgt => by
    simp only [InRegion, BitVec.sub_self, BitVec.toNat_zero]; omega
  refine Classical.byContradiction fun hgt => ?_
  by_cases hsd : InRegion dst bs.length src
  · exact hsep src (hself src (by omega)) hsd
  · refine hsep dst ?_ (hself dst (by omega))
    simp only [InRegion] at hsd ⊢
    bv_omega

private theorem blk28_memcpyRO_base_ok : MlKemBlockConstOk 28 mlkemMemcpyROBaseSpec := by
  intro _
  apply withCodeLoaded_of_subroutine_ok
  have hc : (mlkemMultiLib.blockProgram mlkemMpl 28).hasWords (mlkemMpl.base 28) memcpySymWords :=
    mlkemBlock_hasWords_relocFree 28 (by decide) memcpySymWords (by decide +kernel)
  apply subroutine_ok_of_sepWP_init
  rintro ⟨dst, src, bs⟩ R s0 hpc hrun hpre _hsp
  dsimp only [mlkemMemcpyROBaseSpec, mlkemMemcpyROSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hbs_lt⟩, hmem⟩ := hpre
  have hlen64 : bs.length ≤ 2 ^ 64 := Nat.le_of_lt hbs_lt
  have hmem_src : s0.mem ⊨ memRegion dst bs.length ∗ memcpySrc true src bs ∗ R := by
    simpa only [memcpySrc, Bool.cond_true, sepConj_assoc] using hmem
  have hn63 := memcpy_len_le hlen64 hmem_src
  refine ⟨memRegion dst bs.length ∗ memcpySrc true src bs,
    by simpa only [sepConj_assoc] using hmem_src, ?_⟩
  rw [memRegion_eq_exists_bytes dst bs.length hlen64, sepExists_sepConj_left]
  refine SepWP.exists_elim fun old => ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim fun hold => ?_
  refine SepWP.mono (memcpy_sepwp true _ _ hc s0 dst src (s0.readReg64 .x2) old bs
    hpc hrun hx0 hx1 rfl (by omega) (by omega) (by omega)) ?_
  rintro sf P_f - - ⟨⟨hx0f, hspf, hcsf⟩, hent⟩
  refine ⟨fun hm => ?_, hspf, hcsf⟩
  have hm' : sf.mem ⊨ ((dst ↦ₛ bs) ∗ (src ↦ᵣ bs)) ∗ R :=
    Satisfies.mono (sepConj_mono_left hent) hm
  dsimp only [mlkemMemcpyROBaseSpec]
  rw [sepConj_assoc, pure_sepConj_of_true hx0f]
  simpa only [sepConj_assoc] using hm'

private theorem blk28_memcpy_base_ok : MlKemBlockConstOk 28 mlkemMemcpyBaseSpec := by
  intro _
  apply withCodeLoaded_of_subroutine_ok
  have hc : (mlkemMultiLib.blockProgram mlkemMpl 28).hasWords (mlkemMpl.base 28) memcpySymWords :=
    mlkemBlock_hasWords_relocFree 28 (by decide) memcpySymWords (by decide +kernel)
  apply subroutine_ok_of_sepWP_init
  rintro ⟨dst, src, bs⟩ R s0 hpc hrun hpre _hsp
  dsimp only [mlkemMemcpyBaseSpec, mlkemMemcpySpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hbs_lt⟩, hmem⟩ := hpre
  have hlen64 : bs.length ≤ 2 ^ 64 := Nat.le_of_lt hbs_lt
  have hmem_src : s0.mem ⊨ memRegion dst bs.length ∗ memcpySrc false src bs ∗ R := by
    simpa only [memcpySrc, Bool.cond_false, sepConj_assoc] using hmem
  have hn63 := memcpy_len_le hlen64 hmem_src
  refine ⟨memRegion dst bs.length ∗ memcpySrc false src bs,
    by simpa only [sepConj_assoc] using hmem_src, ?_⟩
  rw [memRegion_eq_exists_bytes dst bs.length hlen64, sepExists_sepConj_left]
  refine SepWP.exists_elim fun old => ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim fun hold => ?_
  refine SepWP.mono (memcpy_sepwp false _ _ hc s0 dst src (s0.readReg64 .x2) old bs
    hpc hrun hx0 hx1 rfl (by omega) (by omega) (by omega)) ?_
  rintro sf P_f - - ⟨⟨hx0f, hspf, hcsf⟩, hent⟩
  refine ⟨fun hm => ?_, hspf, hcsf⟩
  have hm' : sf.mem ⊨ ((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ R :=
    Satisfies.mono (sepConj_mono_left hent) hm
  dsimp only [mlkemMemcpyBaseSpec]
  rw [sepConj_assoc, pure_sepConj_of_true hx0f]
  simpa only [sepConj_assoc] using hm'

/-! ## 2. `B29` (`memset`) -/

private abbrev mlkemMemsetBaseSpec : Spec (BitVec 64 × BitVec 8 × Nat) where
  pre := mlkemMemsetSpec.pre
  post := fun (ptr, c, len) _s0 sf =>
    ⌜sf.readReg64 .x0 = ptr⌝ ∗ (ptr ↦ₛ List.replicate len c)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem blk29_memset_base_ok : MlKemBlockConstOk 29 mlkemMemsetBaseSpec := by
  intro _
  apply withCodeLoaded_of_subroutine_ok
  have hc : (mlkemMultiLib.blockProgram mlkemMpl 29).hasWords (mlkemMpl.base 29) memsetWordsSym :=
    mlkemBlock_hasWords_relocFree 29 (by decide) memsetWordsSym (by decide +kernel)
  refine subroutine_ok_map (memset_codeAt_ok_sym _ _ hc) ?_
  rintro ⟨ptr, c, len⟩ R s0 hpre
  dsimp only [mlkemMemsetBaseSpec, mlkemMemsetSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hc8, hx2, _hlen⟩, hmem⟩ := hpre
  refine ⟨(ptr, s0.readReg32 .x1, s0.readReg64 .x2), R, ?_, fun sf hpost => ?_⟩
  · dsimp only [memsetSymSpec, CType.Bytes, CType.MutSlice8, CType.U32, CType.SizeT,
      CType.SemType.valWf]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    have htr32 : (s0.readReg64 .x1).truncate 32 = s0.readReg32 .x1 := by
      simp [State.readReg32, State.readReg64]
    rw [hx2]
    exact ⟨⟨hx0, htr32, rfl, trivial, trivial⟩, hmem⟩
  · simp only [memsetSymSpec, CType.Bytes, CType.MutSlice8,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨_, hx0f⟩, hmem_f⟩ := hpost
    have hc_eq : (s0.readReg32 .x1).setWidth 8 = c := hc8
    rw [hx2, hc_eq] at hmem_f
    dsimp only [mlkemMemsetBaseSpec]
    rw [sepConj_assoc, pure_sepConj_of_true hx0f]
    exact hmem_f

/-! ## 3. `B31` (`memcmp`) and `B30` (`bcmp`) -/

private abbrev mlkemBcmpROBaseSpec :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) where
  pre := mlkemBcmpROSpec.pre
  post := fun (p, q, bs, cs) s0 sf =>
    ⌜sf.mem = s0.mem ∧ sf.vregs = s0.vregs ∧ (sf.readReg32 .x0 = 0#32 ↔ bs = cs)⌝ ∗
      (p ↦ᵣ bs) ∗ (q ↦ᵣ cs)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem blk31_bcmpRO_base_ok : MlKemBlockConstOk 31 mlkemBcmpROBaseSpec := by
  intro _
  apply withCodeLoaded_of_subroutine_ok
  have hc : (mlkemMultiLib.blockProgram mlkemMpl 31).hasWords (mlkemMpl.base 31) memcmpLibcaWords :=
    mlkemBlock_hasWords_relocFree 31 (by decide) memcmpLibcaWords (by decide +kernel)
  refine subroutine_ok_map (memcmpROPreserving_libca_codeAt_ok _ _ hc) ?_
  rintro ⟨p, q, bs, cs⟩ R s0 hpre
  dsimp only [mlkemBcmpROBaseSpec, mlkemBcmpROSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hcs_len, _hbs_lt⟩, hmem⟩ := hpre
  refine ⟨(p, q, s0.readReg64 .x2, bs, cs), R, ?_, fun sf hpost => ?_⟩
  · dsimp only [memcmpROPreservingSpec, withMemcmpPreserved, memcmpROSpec, RoSlice8, SliceLenPair,
      CType.SemType.valWf]
    simp only [sepConj_assoc, satisfies_pure_sepConj, true_and, and_assoc]
    exact ⟨hx0, hx1, hx2, hx2.trans hcs_len.symm, by simpa only [sepConj_assoc] using hmem⟩
  · dsimp only [memcmpROPreservingSpec, withMemcmpPreserved, memcmpROSpec, RoSlice8, CType.I32,
      CType.scalarTy, CType.SemType.valWf] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hmem_eq, hvregs, _⟩, hret, hmem_ro⟩
    have hiff : (sf.readReg32 .x0 = 0#32 ↔ bs = cs) := by
      rw [hret]
      exact memcmpBytes_eq_zero_iff hcs_len.symm
    dsimp only [mlkemBcmpROBaseSpec]
    rw [sepConj_assoc, pure_sepConj_of_true ⟨hmem_eq, hvregs, hiff⟩]
    simpa only [sepConj_assoc] using hmem_ro

private theorem blk30_bcmpRO_base_ok : MlKemBlockConstOk 30 mlkemBcmpROBaseSpec := by
  intro _
  refine mlkemCaller_ok (j := 30) mlkemPC30 mlkemPl30 (spec := mlkemBcmpROBaseSpec)
    (h := fun b hb hbase => ?_)
  apply subroutine_ok_of_sepWP_init
  rintro ⟨p, q, bs, cs⟩ R s0 hpc hrun hpre _hsp
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, mlkemBcmpROBaseSpec,
    mlkemBcmpROSpec] at hpre
  rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre_body⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_body
  obtain ⟨⟨hx0, hx1, hx2, hcs_len, hbs_lt⟩, hspat⟩ := hpre_body
  refine ⟨(p ↦ᵣ bs) ∗ (q ↦ᵣ cs), by simpa only [sepConj_assoc] using hspat, ?_⟩
  wp_mlkem_tailcall blk31_bcmpRO_base_ok
  refine SepWP.done hpc_sf hrun_sf ⟨fun hm => ?_, hsp_sf, ?_⟩
  · rw [sepConj_assoc, pure_sepConj_of_true ⟨‹sf.mem = s0.mem›,
      by simpa [State.setPC] using ‹sf.vregs = (s0.setPC (mlkemMpl.base 31)).vregs›, hpost⟩]
    simpa only [sepConj_assoc] using hm
  · exact ⟨‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, hcs_sf, hvregs⟩

public section

/-- `B28` (`memcpy`) read-only source contract with `NonSyscallPreserved`. -/
theorem blk28_memcpyRO_ok : MlKemBlockConstOk 28 mlkemMemcpyROSpec :=
  mlkemConstOk_map
    (mlkemBlockConstOk_withNonSyscallPreserved blk28_memcpyRO_base_ok
      (h_pre := fun mpl x R s0 h => by
        dsimp [mlkemMemcpyROBaseSpec, mlkemMemcpyROSpec] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs] using h)
      (h_post := fun mpl x R s0 sf hnsp h => by
        dsimp [mlkemMemcpyROBaseSpec, mlkemMemcpyROSpec] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs,
          stripS_mem, stripExecOutside_eq_iff_of_perm_eq (mlkemKeep mpl) hnsp.2.1] using h))
    fun ⟨dst, src, bs⟩ R _s0 hpre => ⟨(dst, src, bs), R, hpre, fun _sf hpost => by
      dsimp only [withNonSyscallPreserved, mlkemMemcpyROBaseSpec, mlkemMemcpyROSpec] at hpost ⊢
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨⟨hpost.1, hpost.2.1⟩, hpost.2.2⟩⟩

/-- `B28` (`memcpy`) read-write source contract with `NonSyscallPreserved`. -/
theorem blk28_memcpy_ok : MlKemBlockConstOk 28 mlkemMemcpySpec :=
  mlkemConstOk_map
    (mlkemBlockConstOk_withNonSyscallPreserved blk28_memcpy_base_ok
      (h_pre := fun mpl x R s0 h => by
        dsimp [mlkemMemcpyBaseSpec, mlkemMemcpySpec] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs] using h)
      (h_post := fun mpl x R s0 sf hnsp h => by
        dsimp [mlkemMemcpyBaseSpec, mlkemMemcpySpec] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs,
          stripS_mem, stripExecOutside_eq_iff_of_perm_eq (mlkemKeep mpl) hnsp.2.1] using h))
    fun ⟨dst, src, bs⟩ R _s0 hpre => ⟨(dst, src, bs), R, hpre, fun _sf hpost => by
      dsimp only [withNonSyscallPreserved, mlkemMemcpyBaseSpec, mlkemMemcpySpec] at hpost ⊢
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨⟨hpost.1, hpost.2.1⟩, hpost.2.2⟩⟩

/-- `B29` (`memset`) contract with `NonSyscallPreserved`. -/
theorem blk29_memset_ok : MlKemBlockConstOk 29 mlkemMemsetSpec :=
  mlkemConstOk_map
    (mlkemBlockConstOk_withNonSyscallPreserved blk29_memset_base_ok
      (h_pre := fun mpl x R s0 h => by
        dsimp [mlkemMemsetBaseSpec, mlkemMemsetSpec] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs] using h)
      (h_post := fun mpl x R s0 sf hnsp h => by
        dsimp [mlkemMemsetBaseSpec, mlkemMemsetSpec] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs,
          stripS_mem, stripExecOutside_eq_iff_of_perm_eq (mlkemKeep mpl) hnsp.2.1] using h))
    fun ⟨ptr, c, len⟩ R _s0 hpre => ⟨(ptr, c, len), R, hpre, fun _sf hpost => by
      dsimp only [withNonSyscallPreserved, mlkemMemsetBaseSpec, mlkemMemsetSpec] at hpost ⊢
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨⟨hpost.1, hpost.2.1⟩, hpost.2.2⟩⟩

/-- `B31` (`memcmp`) read-only contract preserving `mem`, `vregs`, and `NonSyscallPreserved`. -/
theorem blk31_bcmpRO_ok : MlKemBlockConstOk 31 mlkemBcmpROSpec :=
  mlkemConstOk_map
    (mlkemBlockConstOk_withNonSyscallPreserved blk31_bcmpRO_base_ok
      (h_pre := fun mpl x R s0 h => by
        dsimp [mlkemBcmpROBaseSpec, mlkemBcmpROSpec] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs] using h)
      (h_post := fun mpl x R s0 sf hnsp h => by
        dsimp [mlkemBcmpROBaseSpec, mlkemBcmpROSpec] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs,
          stripS_mem, stripExecOutside_eq_iff_of_perm_eq (mlkemKeep mpl) hnsp.2.1] using h))
    fun ⟨p, q, bs, cs⟩ R _s0 hpre => ⟨(p, q, bs, cs), R, hpre, fun _sf hpost => by
      dsimp only [withNonSyscallPreserved, mlkemBcmpROBaseSpec, mlkemBcmpROSpec] at hpost ⊢
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨⟨hpost.1, hpost.2.1.1, hpost.2.1.2.1, hpost.2.1.2.2⟩, hpost.2.2⟩⟩

/-- `B30` (`bcmp` → `B31` tail-jump) read-only contract preserving `mem`, `vregs`, and
    `NonSyscallPreserved`. -/
theorem blk30_bcmpRO_ok : MlKemBlockConstOk 30 mlkemBcmpROSpec :=
  mlkemConstOk_map
    (mlkemBlockConstOk_withNonSyscallPreserved blk30_bcmpRO_base_ok
      (h_pre := fun mpl x R s0 h => by
        dsimp [mlkemBcmpROBaseSpec, mlkemBcmpROSpec] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs] using h)
      (h_post := fun mpl x R s0 sf hnsp h => by
        dsimp [mlkemBcmpROBaseSpec, mlkemBcmpROSpec] at h ⊢
        simpa [stripS_sp, stripS_readReg64, stripS_readReg32, stripS_vregs, stripS_regs,
          stripS_mem, stripExecOutside_eq_iff_of_perm_eq (mlkemKeep mpl) hnsp.2.1] using h))
    fun ⟨p, q, bs, cs⟩ R _s0 hpre => ⟨(p, q, bs, cs), R, hpre, fun _sf hpost => by
      dsimp only [withNonSyscallPreserved, mlkemBcmpROBaseSpec, mlkemBcmpROSpec] at hpost ⊢
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨⟨hpost.1, hpost.2.1.1, hpost.2.1.2.1, hpost.2.1.2.2⟩, hpost.2.2⟩⟩

/-- `B30` (`bcmp`) mixed RW/RO specialization (`p ↦ₛ bs`, `q ↦ᵣ cs`). -/
theorem blk30_bcmpRW1RO_ok : MlKemBlockConstOk 30 mlkemBcmpRW1ROSpec :=
  mlkemConstOk_map blk30_bcmpRO_ok
    fun ⟨p, q, bs, cs⟩ R s0 hpre => by
      dsimp only [mlkemBcmpRW1ROSpec] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      obtain ⟨hpure, hspat⟩ := hpre
      have hspat_ro : s0.mem ⊨ (p ↦ᵣ bs) ∗ ((q ↦ᵣ cs) ∗ R) :=
        Satisfies.pointsToBytes_to_ro (by simpa only [sepConj_assoc] using hspat)
      refine ⟨(p, q, bs, cs), R, ?_, fun sf hpost => ?_⟩
      · dsimp only [mlkemBcmpROSpec]
        rw [sepConj_assoc, pure_sepConj_of_true hpure]
        simpa only [sepConj_assoc] using hspat_ro
      · dsimp only [mlkemBcmpROSpec, mlkemBcmpRW1ROSpec] at hpost ⊢
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
        obtain ⟨hpure_post, _⟩ := hpost
        exact ⟨hpure_post, hpure_post.2.1 ▸ hspat⟩

end

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
