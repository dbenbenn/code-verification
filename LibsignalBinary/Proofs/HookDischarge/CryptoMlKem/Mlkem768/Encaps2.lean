/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem
import LibsignalBinary.Proofs.HookDischarge.Libc.Common
import LibsignalBinary.Proofs.HookDischarge.RustStd.Common
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2b
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5

/-!
# `B20`: `libcrux_ml_kem::mlkem768::incremental::encapsulate2` (`Mlkem768.Encaps2`)

Top-level contracts for block 20 (`2,769` words, `6,128`-byte stack frame, calling `B28` `memcpy`):

- `blk20_encaps2_raw_ok : MlKemBlockOk 20 mlkemEncaps2RawSpec`
- `blk20_encaps2_ok : MlKemBlockOk 20 mlkemEncaps2CoreSpec`
- `blk20_encaps2_proj_ok` (caller-struct projection lift via `mlkemEncaps2Core_simulates_proj`)
- `blk20_encaps2_inc_proj_ok` (specialized to `mlkem768Incremental`)
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBlockOk mlkemCaller_ok mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase (
  mlkemBlockOk_withNonSyscallPreserved mlkemKeep mlkemRoOk_stripExecOutside
  stripS_mem stripS_readReg64 stripS_sp)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly16 byteDecodeRaw bytesToPoly16 mlkem768Encaps2List mlkem768Incremental
  neonCompressSerialize4 neonInvNttMontgomery16 neonPolyNttMul16 toByteVec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  SavedFrame20 blkPC20 blkPl20 mlkemEncaps2CoreSpec mlkemEncaps2Core_simulates_proj
  mlkemEncaps2ProjSpec mlkemEncaps2RawSpec sepWP_seq_env withMlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem Spill13 Spill13Mem Vec32 poly32Mem_entails_memRegion poly32Mem_ofFn
  polyVecNat vecRangeMem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure (msgPoly16 tHatPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2b (Seg2Spatial)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2 (seg12_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure (
  neonDot3 neonDot3_eq_encaps2_fold)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3a (accRegs_zero_iff)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3 (seg3_to_28e8_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd (seg5FinalPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5 (seg45_stack_eq seg5_ok)

private theorem array_ofFn3_getD (f : Fin 3 → Poly16) :
    (Array.ofFn f).getD 0 #[] = f ⟨0, by decide⟩ ∧
    (Array.ofFn f).getD 1 #[] = f ⟨1, by decide⟩ ∧
    (Array.ofFn f).getD 2 #[] = f ⟨2, by decide⟩ := by
  simp [Array.getD]

private theorem encaps2_output_eq (es ek : List (BitVec 8)) :
    let t0 := tHatPoly16 (ek.take 384)
    let t1 := tHatPoly16 ((ek.drop 384).take 384)
    let t2 := tHatPoly16 ((ek.drop 768).take 384)
    let r0 := bytesToPoly16 (es.take 512)
    let r1 := bytesToPoly16 ((es.drop 512).take 512)
    let r2 := bytesToPoly16 ((es.drop 1024).take 512)
    let err2 := bytesToPoly16 ((es.drop 1536).take 512)
    let msgPoly := msgPoly16 ((es.drop 2048).take 32)
    let dot := neonDot3 t0 t1 t2 r0 r1 r2
    neonCompressSerialize4 (seg5FinalPoly (neonInvNttMontgomery16 dot) err2 msgPoly) =
      mlkem768Encaps2List es ek := by
  dsimp only
  let tHat : Array Poly16 := Array.ofFn (n := 3) fun ⟨i, _⟩ =>
    (byteDecodeRaw 12 ((ek.drop (384 * i)).take 384)).map fun c => BitVec.ofNat 16 c
  let rHat : Array Poly16 := Array.ofFn (n := 3) fun ⟨i, _⟩ =>
    bytesToPoly16 ((es.drop (512 * i)).take 512)
  have hdot :
      neonDot3 (tHatPoly16 (ek.take 384))
        (tHatPoly16 ((ek.drop 384).take 384))
        (tHatPoly16 ((ek.drop 768).take 384))
        (bytesToPoly16 (es.take 512))
        (bytesToPoly16 ((es.drop 512).take 512))
        (bytesToPoly16 ((es.drop 1024).take 512)) =
      (List.range 3).foldl
        (fun acc j =>
          let prod := neonPolyNttMul16 (tHat.getD j #[]) (rHat.getD j #[])
          Array.ofFn (n := 256) fun ⟨i, _⟩ => acc.getD i 0#16 + prod.getD i 0#16)
        (Array.replicate 256 0#16) := by
    rw [neonDot3_eq_encaps2_fold tHat rHat]
    rcases array_ofFn3_getD (fun ⟨i, _⟩ =>
      (byteDecodeRaw 12 ((ek.drop (384 * i)).take 384)).map fun c => BitVec.ofNat 16 c) with
      ⟨ht0, ht1, ht2⟩
    rcases array_ofFn3_getD (fun ⟨i, _⟩ =>
      bytesToPoly16 ((es.drop (512 * i)).take 512)) with ⟨hr0, hr1, hr2⟩
    dsimp only [tHat, rHat] at ht0 ht1 ht2 hr0 hr1 hr2 ⊢
    rw [ht0, ht1, ht2, hr0, hr1, hr2]
    simp [tHatPoly16]
  exact congrArg
    (fun d => neonCompressSerialize4 (seg5FinalPoly (neonInvNttMontgomery16 d)
      (bytesToPoly16 ((es.drop 1536).take 512)) (msgPoly16 ((es.drop 2048).take 32))))
    hdot

private theorem encaps2_stackRest_entails (sp : BitVec 64) (es : List (BitVec 8))
    (hes : es.length = 2080) (r0 r1 r2 t0 t1 t2 : Poly16) (v5488 : Vec32) :
    memRegion sp 208 ∗ memRegion (sp + 1744#64) 512 ∗ memRegion (sp + 2288#64) 128 ∗
      memRegion (sp + 2416#64) 512 ∗ memRegion (sp + 2928#64) 512 ∗
      memRegion (sp + 3440#64) 512 ∗
      (PolyMem (sp + 208#64) (polyVecNat r0) ∗
        PolyMem (sp + 720#64) (polyVecNat r1) ∗
        PolyMem (sp + 1232#64) (polyVecNat r2) ∗
        ((sp + 2256#64) ↦ₛ ((es.drop 2048).take 32)) ∗
        PolyMem (sp + 3952#64) (polyVecNat t0) ∗
        PolyMem (sp + 4464#64) (polyVecNat t1) ∗
        PolyMem (sp + 4976#64) (polyVecNat t2) ∗
        Poly32Mem (sp + 5488#64) v5488) ⊢
      memRegion sp 6000 := by
  have hm32 : ((es.drop 2048).take 32).length = 32 := by simp [hes]
  have hm_reg : ((sp + 2256#64) ↦ₛ ((es.drop 2048).take 32)) ⊢ memRegion (sp + 2256#64) 32 := by
    simpa only [hm32] using
      pointsToBytes_entails_memRegion (sp + 2256#64) ((es.drop 2048).take 32)
  have h1536 : memRegion (sp + 208#64) 1536 =
      memRegion (sp + 208#64) 512 ∗ memRegion (sp + 720#64) 512 ∗ memRegion (sp + 1232#64) 512 := by
    rw [show (1536 : Nat) = 512 + 1024 from rfl, memRegion_split _ _ _ (by decide),
      show (sp + 208#64) + 512#64 = sp + 720#64 by bv_omega,
      show (1024 : Nat) = 512 + 512 from rfl, memRegion_split _ _ _ (by decide),
      show (sp + 720#64) + 512#64 = sp + 1232#64 by bv_omega]
  have h2048 : memRegion (sp + 3952#64) 2048 =
      memRegion (sp + 3952#64) 512 ∗ memRegion (sp + 4464#64) 512 ∗
        memRegion (sp + 4976#64) 512 ∗ memRegion (sp + 5488#64) 512 := by
    rw [show (2048 : Nat) = 512 + 1536 from rfl, memRegion_split _ _ _ (by decide),
      show (sp + 3952#64) + 512#64 = sp + 4464#64 by bv_omega,
      show (1536 : Nat) = 512 + 1024 from rfl, memRegion_split _ _ _ (by decide),
      show (sp + 4464#64) + 512#64 = sp + 4976#64 by bv_omega,
      show (1024 : Nat) = 512 + 512 from rfl, memRegion_split _ _ _ (by decide),
      show (sp + 4976#64) + 512#64 = sp + 5488#64 by bv_omega]
  rw [seg45_stack_eq sp, h1536, h2048]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))))
  refine Entails.trans (sepConj_mono (vecRangeMem_entails_memRegion 32 _ _)
    (sepConj_mono (vecRangeMem_entails_memRegion 32 _ _)
      (sepConj_mono (vecRangeMem_entails_memRegion 32 _ _)
        (sepConj_mono hm_reg
          (sepConj_mono (vecRangeMem_entails_memRegion 32 _ _)
            (sepConj_mono (vecRangeMem_entails_memRegion 32 _ _)
              (sepConj_mono (vecRangeMem_entails_memRegion 32 _ _)
                (poly32Mem_entails_memRegion _ _)))))))) ?_
  sep_frame

/-- `B20` (`encapsulate2`) raw total-correctness (`subroutine_ok`) contract prior to
    `NonSyscallPreserved` lifting. -/
theorem blk20_encaps2_raw_ok : MlKemBlockOk 20 mlkemEncaps2RawSpec := by
  intro _
  refine mlkemCaller_ok blkPC20 blkPl20 rfl rfl fun b hb hbase => ?_
  apply subroutine_ok_of_sepWP_init
  rintro ⟨ret, esA, es, ekA, ek⟩ R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, mlkemEncaps2RawSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx8, hx0, hx1, hes, hek, hro0⟩, hspat⟩ := hpre
  refine ⟨(esA ↦ₛ es) ∗ (ekA ↦ₛ ek) ∗ stackAt s0.sp 6128 ∗ memRegion ret 128, ?_, ?_⟩
  · exact Satisfies.mono (by sep_frame) hspat
  · refine sepWP_seq_env hcl0 hro0
      (seg12_ok hb hbase s0 ret esA ekA es ek (memRegion ret 128)
        hpc hrun hsp0 hcl0 hro0 hx8 hx0 hx1 hes hek) ?_
    rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hpost2, hP2⟩
    rcases hpost2 with ⟨hsp2, hspA2, hx8_2, hx9_2, hx10_2, hx11_2, hx12_2,
      hx19_2, hx20_2, hx21_2, hv0, hv1, _hv2, hv8, hv9, hv10, hv11, hv12, hv13,
      hv14, hv15, hv22, hv23, hv24, hv25, hv26, hv27, hv28, hv29, hv30, hv31, hus2⟩
    have hacc2 := (accRegs_zero_iff s2).mpr ⟨hv0, hv1, hv8, hv9, hv10, hv11, hv12,
      hv13, hv14, hv15, hv22, hv23, hv24, hv25, hv26, hv27, hv28, hv29, hv30, hv31⟩
    let sp := s0.sp - 6128#64
    let t0 := tHatPoly16 (ek.take 384)
    let t1 := tHatPoly16 ((ek.drop 384).take 384)
    let t2 := tHatPoly16 ((ek.drop 768).take 384)
    let r0 := bytesToPoly16 (es.take 512)
    let r1 := bytesToPoly16 ((es.drop 512).take 512)
    let r2 := bytesToPoly16 ((es.drop 1024).take 512)
    let err2 := bytesToPoly16 ((es.drop 1536).take 512)
    let msgPoly := msgPoly16 ((es.drop 2048).take 32)
    let Rest3 : SepProp :=
      PolyMem (sp + 1744#64) (polyVecNat err2) ∗
      ((sp + 2256#64) ↦ₛ ((es.drop 2048).take 32)) ∗
      memRegion (sp + 2288#64) 128 ∗
      PolyMem (sp + 2416#64) (polyVecNat msgPoly) ∗
      memRegion (sp + 3440#64) 512 ∗
      SavedFrame20 s0.sp s0 ∗ memRegion ret 128 ∗
      (esA ↦ₛ es) ∗ (ekA ↦ₛ ek)
    have hframe2 : Seg2Spatial s0 esA es ekA ek (memRegion ret 128) ⊢
        Spill13Mem sp Spill13.zero ∗ PolyMem (sp + 208#64) (polyVecNat r0) ∗
          PolyMem (sp + 720#64) (polyVecNat r1) ∗ PolyMem (sp + 1232#64) (polyVecNat r2) ∗
          Poly32Mem (sp + 2928#64) (Vec32.ofFn (fun _ => 0#128)) ∗
          PolyMem (sp + 3952#64) (polyVecNat t0) ∗ PolyMem (sp + 4464#64) (polyVecNat t1) ∗
          PolyMem (sp + 4976#64) (polyVecNat t2) ∗
          Poly32Mem (sp + 5488#64) (Vec32.ofFn (polyVecNat t2)) ∗ Rest3 := by
      dsimp only [Seg2Spatial, sp, t0, t1, t2, r0, r1, r2, err2, msgPoly, Rest3]
      rw [poly32Mem_ofFn (sp + 2928#64) (fun _ => 0#128)]
      sep_frame
    refine sepWP_seq_env hcl2 hro2
      (SepWP.weaken_pre (Entails.trans hP2 hframe2)
        (seg3_to_28e8_ok hb s0 s2 sp ret t0 t1 t2 r0 r1 r2
          (Vec32.ofFn (fun _ => 0#128)) (Vec32.ofFn (polyVecNat t2)) Rest3
          hpc2 hrun2 hsp2 hspA2 hcl2 hro2 hx8_2 hx9_2 hx10_2 hx11_2 hx12_2
          hx19_2 hx20_2 hx21_2 hacc2 hus2)) ?_
    rintro s4 _ hpc4 hrun4 hcl4 hro4 ⟨hpost4, _, _, spill, hs6, hs11, rfl⟩
    let dot := neonDot3 t0 t1 t2 r0 r1 r2
    let inv := neonInvNttMontgomery16 dot
    let v5488' := Vec32.ofFn (polyVecNat (neonPolyNttMul16 t2 r2))
    let StackRest : SepProp :=
      PolyMem (sp + 208#64) (polyVecNat r0) ∗
      PolyMem (sp + 720#64) (polyVecNat r1) ∗
      PolyMem (sp + 1232#64) (polyVecNat r2) ∗
      ((sp + 2256#64) ↦ₛ ((es.drop 2048).take 32)) ∗
      PolyMem (sp + 3952#64) (polyVecNat t0) ∗
      PolyMem (sp + 4464#64) (polyVecNat t1) ∗
      PolyMem (sp + 4976#64) (polyVecNat t2) ∗
      Poly32Mem (sp + 5488#64) v5488'
    let CallerRest : SepProp := (esA ↦ₛ es) ∗ (ekA ↦ₛ ek)
    have hframe4 :
        Spill13Mem sp spill ∗ PolyMem (sp + 2928#64) (polyVecNat inv) ∗
          PolyMem (sp + 208#64) (polyVecNat r0) ∗ PolyMem (sp + 720#64) (polyVecNat r1) ∗
          PolyMem (sp + 1232#64) (polyVecNat r2) ∗ PolyMem (sp + 3952#64) (polyVecNat t0) ∗
          PolyMem (sp + 4464#64) (polyVecNat t1) ∗ PolyMem (sp + 4976#64) (polyVecNat t2) ∗
          Poly32Mem (sp + 5488#64) v5488' ∗ Rest3 ⊢
        Spill13Mem sp spill ∗ memRegion (sp + 3440#64) 512 ∗
          PolyMem (sp + 2928#64) (polyVecNat inv) ∗ PolyMem (sp + 1744#64) (polyVecNat err2) ∗
          PolyMem (sp + 2416#64) (polyVecNat msgPoly) ∗ memRegion (sp + 2288#64) 128 ∗
          SavedFrame20 s0.sp s0 ∗ memRegion ret 128 ∗ StackRest ∗ CallerRest := by
      dsimp only [Rest3, StackRest, CallerRest]
      sep_frame
    refine SepWP.weaken_pre hframe4 ?_
    refine SepWP.mono
      (seg5_ok hb s0 s4 ret spill inv err2 msgPoly StackRest CallerRest
        hsp0 hpc4 hrun4 hpost4 hs6 hs11 hcl4 hro4
        (encaps2_stackRest_entails sp es hes r0 r1 r2 t0 t1 t2 v5488')) ?_
    intro sf Pf _ _ hpost5
    rw [sepPost_apply] at hpost5
    rcases hpost5 with ⟨⟨hsp_sf, hcs_sf⟩, hPf⟩
    refine ⟨fun hm => ?_, hsp_sf, hcs_sf⟩
    have hm1 := Satisfies.mono (sepConj_mono_left hPf) hm
    rw [encaps2_output_eq es ek] at hm1
    exact Satisfies.mono (by dsimp only [CallerRest]; sep_frame) hm1

/-- `B20` (`encapsulate2`) tight-stack core contract lifted with `NonSyscallPreserved`. -/
theorem blk20_encaps2_ok : MlKemBlockOk 20 mlkemEncaps2CoreSpec :=
  mlkemBlockOk_withNonSyscallPreserved blk20_encaps2_raw_ok (by decide)
    (h_pre := fun mpl ⟨_ret, _esA, _es, _ekA, _ek⟩ _R _s0 h => by
      dsimp only [mlkemEncaps2RawSpec] at h ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
      simp only [stripS_readReg64, stripS_sp, stripS_mem]
      exact ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1,
        mlkemRoOk_stripExecOutside (mlkemKeep mpl) h.1.2.2.2.2.2⟩, h.2⟩)
    (h_post := fun _mpl ⟨_ret, _esA, _es, _ekA, _ek⟩ _R _s0 _sf _ h => by
      dsimp only [mlkemEncaps2RawSpec] at h ⊢
      simpa only [stripS_sp] using h)

/-- `B20` (`encapsulate2`) caller-struct projection contract parameterized by `K : MlKem`. -/
theorem blk20_encaps2_proj_ok (K : MlKem)
    (hK : ∀ es ek, K.encaps2 es ek = toByteVec 128 (mlkem768Encaps2List es.toList ek.toList))
    {C : Type}
    (ret : C → BitVec 64)
    (esA : C → BitVec 64) (es : C → List.Vector (BitVec 8) 2080)
    (ekA : C → BitVec 64) (ek : C → List.Vector (BitVec 8) 1152) :
    MlKemBlockOk 20 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (mlkemEncaps2ProjSpec K ret esA es ekA ek))) := by
  intro _
  exact ((mlkemEncaps2Core_simulates_proj K hK ret esA es ekA ek mlkemMpl).withCodeLoaded
    mlkemMultiLib mlkemMpl).subroutine_ok blk20_encaps2_ok

/-- `B20` (`encapsulate2`) unconditional caller-struct projection contract specialized to
    `mlkem768Incremental`. -/
theorem blk20_encaps2_inc_proj_ok
    {C : Type}
    (ret : C → BitVec 64)
    (esA : C → BitVec 64) (es : C → List.Vector (BitVec 8) 2080)
    (ekA : C → BitVec 64) (ek : C → List.Vector (BitVec 8) 1152) :
    MlKemBlockOk 20 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (mlkemEncaps2ProjSpec mlkem768Incremental ret esA es ekA ek))) :=
  blk20_encaps2_proj_ok mlkem768Incremental (fun _ _ => rfl) ret esA es ekA ek

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2
