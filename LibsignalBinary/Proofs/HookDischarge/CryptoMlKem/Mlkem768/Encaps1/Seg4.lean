/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg4Prf
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg4E1
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg4E2

/-!
# `encapsulate1_serialized` (`B03`) — Segment 4 Top-Level (`+0x4728 .. +0x4e38`)

Composes `Seg4Prf` (`+0x4728..+0x4938`), `Seg4E1` (`+0x4938..+0x4b38`), and `Seg4E2`
(`+0x4b38..+0x4e38`) into `seg4_ok`: generates `e1[0..2]` at `[sp + 13984, sp + 15520)`,
stores `e2`'s 32 vectors in reversed order at `[sp + 1248, sp + 1760)`, and zeroes `uVec[0..2]`
at `[sp + 2192, sp + 3728)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg4

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (shake256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd (neonCbd2Poly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (PolyMem polyVecNat)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (entails_sub)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (blkPC03 blkPl03)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg4Prf (seg4_prf_setup)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg4E1 (seg4_e1_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg4E2 (seg4_e2_ok)

attribute [local irreducible] blkPC03 shake256List

@[simp, arm64_norm, wp_norm] abbrev offSeg4Start : BitVec 64 := BitVec.ofNat 64 18216
@[simp, arm64_norm, wp_norm] abbrev offSeg5Start : BitVec 64 := BitVec.ofNat 64 20024

theorem seg4_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (coins : List (BitVec 8)) (b0 : BitVec 8) (Rest : SepProp)
    (hc : coins.length = 32)
    (hpc : s.pc = b + offSeg4Start) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    let prf3 := shake256List 128 (coins ++ [3#8])
    let prf4 := shake256List 128 (coins ++ [4#8])
    let prf5 := shake256List 128 (coins ++ [5#8])
    let prf6 := shake256List 128 (coins ++ [6#8])
    SepWP (blkPC03.rebase b (fun _ => none)) (b + offSeg5Start) s
      (((sp + 12400#64) ↦ₛ coins) ∗ ((sp + 12432#64) ↦₈ b0) ∗
       memRegion (sp + 1248#64) 512 ∗ memRegion (sp + 2192#64) 1536 ∗
       memRegion (sp + 4272#64) 512 ∗ memRegion (sp + 13984#64) 1536 ∗
       memRegion (sp + 15520#64) 128 ∗ memRegion (sp + 15680#64) 128 ∗
       memRegion (sp + 16208#64) 128 ∗ memRegion (sp + 16528#64) 128 ∗
       stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = sp + 2192#64 ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        (Pf ⊢ PolyMem (sp + 1248#64) (fun i => polyVecNat (neonCbd2Poly16 prf6) (31 - i)) ∗
          PolyMem (sp + 2192#64) (fun _ => 0#128) ∗
          PolyMem (sp + 2704#64) (fun _ => 0#128) ∗
          PolyMem (sp + 3216#64) (fun _ => 0#128) ∗
          memRegion (sp + 4272#64) 512 ∗ memRegion (sp + 12400#64) 33 ∗
          PolyMem (sp + 13984#64) (polyVecNat (neonCbd2Poly16 prf3)) ∗
          PolyMem (sp + 14496#64) (polyVecNat (neonCbd2Poly16 prf4)) ∗
          PolyMem (sp + 15008#64) (polyVecNat (neonCbd2Poly16 prf5)) ∗
          memRegion (sp + 15520#64) 128 ∗ memRegion (sp + 15680#64) 128 ∗
          memRegion (sp + 16208#64) 128 ∗ memRegion (sp + 16528#64) 128 ∗
          stackAt sp 1136 ∗ Rest)) := by
  intro prf3 prf4 prf5 prf6
  rw [memRegion_split' (b := sp + 2192#64) (b' := sp + 2576#64) (n := 384) (k := (1152 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 15520#64) (b' := sp + 15619#64) (n := 99) (k := (29 : Nat))
        rfl (by bv_omega) (by decide)]
  refine SepWP.weaken_pre
    (P' := ((sp + 12400#64) ↦ₛ coins) ∗ memRegion (sp + 2192#64) 384 ∗
      memRegion (sp + 4272#64) 512 ∗ memRegion (sp + 13984#64) 1536 ∗
      memRegion (sp + 15520#64) 99 ∗ memRegion (sp + 15680#64) 128 ∗
      memRegion (sp + 16208#64) 128 ∗ memRegion (sp + 16528#64) 128 ∗ stackAt sp 1136 ∗
      (((sp + 12432#64) ↦₈ b0) ∗ memRegion (sp + 1248#64) 512 ∗
        memRegion (sp + 2576#64) 1152 ∗ memRegion (sp + 15619#64) 29 ∗ Rest)) (by sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (seg4_prf_setup hb hbase s sp coins _ hc hpc hrun hsp hspA hx19 hcl hro) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, r8, r9, r19, r20, r21, rv3, _, _, hP1⟩
  refine SepWP.weaken_pre (Entails.trans hP1
    (show (((sp + 12400#64) ↦ₛ coins) ∗
        ((sp + 2192#64) ↦ₛ prf3) ∗ ((sp + 2320#64) ↦ₛ prf4) ∗ ((sp + 2448#64) ↦ₛ prf5) ∗
        memRegion (sp + 4272#64) 512 ∗
        PolyMem (sp + 13984#64) (fun _ => 0#128) ∗ PolyMem (sp + 14496#64) (fun _ => 0#128) ∗
        PolyMem (sp + 15008#64) (fun _ => 0#128) ∗
        memRegion (sp + 15520#64) 99 ∗ memRegion (sp + 15680#64) 128 ∗
        memRegion (sp + 16208#64) 128 ∗ memRegion (sp + 16528#64) 128 ∗ stackAt sp 1136 ∗
        (((sp + 12432#64) ↦₈ b0) ∗ memRegion (sp + 1248#64) 512 ∗
          memRegion (sp + 2576#64) 1152 ∗ memRegion (sp + 15619#64) 29 ∗ Rest)) ⊢
      ((sp + 2192#64) ↦ₛ prf3) ∗ ((sp + 2320#64) ↦ₛ prf4) ∗ ((sp + 2448#64) ↦ₛ prf5) ∗
        memRegion (sp + 4272#64) 512 ∗
        PolyMem (sp + 13984#64) (fun _ => 0#128) ∗ PolyMem (sp + 14496#64) (fun _ => 0#128) ∗
        PolyMem (sp + 15008#64) (fun _ => 0#128) ∗
        (((sp + 12400#64) ↦ₛ coins) ∗ ((sp + 12432#64) ↦₈ b0) ∗
          memRegion (sp + 1248#64) 512 ∗ memRegion (sp + 2576#64) 1152 ∗
          memRegion (sp + 15520#64) 99 ∗ memRegion (sp + 15619#64) 29 ∗
          memRegion (sp + 15680#64) 128 ∗ memRegion (sp + 16208#64) 128 ∗
          memRegion (sp + 16528#64) 128 ∗ stackAt sp 1136 ∗ Rest) by sep_frame)) ?_
  refine sepWP_seq_env hcl1 hro1
    (seg4_e1_ok hb hbase s1 sp coins _ _ _ _ hpc1 hrun1 hsp1 hspA1 r8 r9 r19 r20 r21 rv3) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hx19_2, _, hP2⟩
  refine SepWP.weaken_pre hP2 ?_
  have hm1536 : memRegion (sp + 2192#64) 384 ∗ memRegion (sp + 2576#64) 1152 =
      memRegion (sp + 2192#64) 1536 :=
    (memRegion_split' (b := sp + 2192#64) (b' := sp + 2576#64) (n := 384) (k := (1152 : Nat))
      rfl (by bv_omega) (by decide)).symm
  have hm128 : memRegion (sp + 15520#64) 99 ∗ memRegion (sp + 15619#64) 29 =
      memRegion (sp + 15520#64) 128 :=
    (memRegion_split' (b := sp + 15520#64) (b' := sp + 15619#64) (n := 99) (k := (29 : Nat))
      rfl (by bv_omega) (by decide)).symm
  rw [memRegion_split' (b := sp + 15680#64) (b' := sp + 15712#64) (n := 32) (k := (96 : Nat))
        rfl (by bv_omega) (by decide)]
  refine SepWP.weaken_pre
    (P' := ((sp + 12432#64) ↦₈ b0) ∗ ((sp + 12400#64) ↦ₛ coins) ∗
      memRegion (sp + 1248#64) 512 ∗ memRegion (sp + 2192#64) 1536 ∗
      memRegion (sp + 4272#64) 512 ∗ memRegion (sp + 15520#64) 128 ∗
      memRegion (sp + 15680#64) 32 ∗ stackAt sp 1136 ∗
      (PolyMem (sp + 13984#64) (polyVecNat (neonCbd2Poly16 prf3)) ∗
        PolyMem (sp + 14496#64) (polyVecNat (neonCbd2Poly16 prf4)) ∗
        PolyMem (sp + 15008#64) (polyVecNat (neonCbd2Poly16 prf5)) ∗
        memRegion (sp + 15712#64) 96 ∗ memRegion (sp + 16208#64) 128 ∗
        memRegion (sp + 16528#64) 128 ∗ Rest))
    (entails_sub (Entails.of_eq hm1536) (by sep_frame)
      (entails_sub (Entails.of_eq hm128) (by sep_frame) (by sep_frame))) ?_
  refine sepWP_seq_env hcl2 hro2
    (seg4_e2_ok hb hbase s2 sp coins b0 _ hc hpc2 hrun2 hsp2 hspA2 hx19_2 hcl2 hro2) ?_
  rintro sf Pf hpcf hrunf hclf hrof ⟨hspf, hspAf, hx19f, _, _, hPf⟩
  refine SepWP.done hpcf hrunf ⟨hspf, hspAf, hx19f, hclf, hrof, ?_⟩
  have hm15680 : memRegion (sp + 15680#64) 32 ∗ memRegion (sp + 15712#64) 96 =
      memRegion (sp + 15680#64) 128 :=
    (memRegion_split' (b := sp + 15680#64) (b' := sp + 15712#64) (n := 32) (k := (96 : Nat))
      rfl (by bv_omega) (by decide)).symm
  exact Entails.trans hPf (entails_sub (Entails.of_eq hm15680) (by sep_frame) (by sep_frame))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg4
