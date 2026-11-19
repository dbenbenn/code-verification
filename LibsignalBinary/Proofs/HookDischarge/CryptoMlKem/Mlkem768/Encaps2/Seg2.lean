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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2b -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2a

/-!
# `encapsulate2` (`B20`) — Segment 2 (`+0x04b8 .. +0x0bdc`) & Combined Entry (`+0x0000 .. +0x0bdc`)

Composes `Seg2a.seg2a_ok` (`+0x04b8 → +0x0710`, `deserialize_12` of `tHat[0..2]`) with
`Seg2b.seg2b_ok` (`+0x0710 → +0x0bdc`, unrolled `decompress_1(m)`, zeroing `dot`, `Spill13`,
and accumulator VRegs, and loading `Seg3` loop-entry GPRs) into `seg2_ok`, and composes
`Seg1.seg1_ok` (`+0x0000 → +0x04b8`) with `seg2_ok` into `seg12_ok`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  blkPC20 blkPl20 sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1 (
  Seg1Post Seg1Spatial seg1_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2a (seg2a_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2b (
  Seg2Post Seg2Spatial seg2b_ok)

export LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2b (
  Seg2Post Seg2Spatial)

/-- Full Segment 2 contract (`+0x04b8 → +0x0bdc`). -/
theorem seg2_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl20 b) (hbase : blkPl20.base = b)
    (s0 s1 : State) (ret esA ekA : BitVec 64) (es ek : List (BitVec 8)) (F : SepProp)
    (hpc : s1.pc = b + 0x04b8#64) (hrun : s1.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s1.mem) (hro : MlKemRoOk mlkemMpl s1.mem)
    (hes : es.length = 2080) (hek : ek.length = 1152) (hpost1 : Seg1Post s0 s1 ret ekA) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x0bdc#64) s1
      ((ekA ↦ₛ ek) ∗ Seg1Spatial s0 esA es F)
      (fun s2 P2 => Seg2Post s0 s2 ret ∧ (P2 ⊢ Seg2Spatial s0 esA es ekA ek F)) := by
  refine sepWP_seq_env hcl hro
    (seg2a_ok hb hbase s0 s1 ret esA ekA es ek F hpc hrun hcl hro hek hpost1) ?_
  rintro s2a P2a hpc2a hrun2a hcl2a hro2a ⟨hpost2a, hP2a⟩
  exact SepWP.weaken_pre hP2a
    (seg2b_ok hb s0 s2a ret esA ekA es ek F hpc2a hrun2a hcl2a hro2a hes hpost2a)

/-- Combined Segment 1 + Segment 2 contract (`+0x0000 → +0x0bdc`, entry to `Seg3` loop). -/
theorem seg12_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl20 b) (hbase : blkPl20.base = b)
    (s0 : State) (ret esA ekA : BitVec 64) (es ek : List (BitVec 8)) (F : SepProp)
    (hpc : s0.pc = b)
    (hrun : s0.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s0.mem)
    (hro : MlKemRoOk mlkemMpl s0.mem)
    (hx8 : s0.readReg64 .x8 = ret)
    (hx0 : s0.readReg64 .x0 = esA)
    (hx1 : s0.readReg64 .x1 = ekA)
    (hes : es.length = 2080)
    (hek : ek.length = 1152) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x0bdc#64) s0
      ((esA ↦ₛ es) ∗ (ekA ↦ₛ ek) ∗ stackAt s0.sp 6128 ∗ F)
      (fun s2 P2 => Seg2Post s0 s2 ret ∧ (P2 ⊢ Seg2Spatial s0 esA es ekA ek F)) := by
  have hpre : ((esA ↦ₛ es) ∗ (ekA ↦ₛ ek) ∗ stackAt s0.sp 6128 ∗ F) ⊢
      ((esA ↦ₛ es) ∗ stackAt s0.sp 6128 ∗ ((ekA ↦ₛ ek) ∗ F)) := by sep_frame
  refine SepWP.weaken_pre hpre (sepWP_seq_env hcl hro
    (seg1_ok hb hbase s0 ret esA ekA es ((ekA ↦ₛ ek) ∗ F)
      hpc hrun hsp0 hcl hro hx8 hx0 hx1 hes) ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hpost1, hP1⟩
  have hP1' : P1 ⊢ (ekA ↦ₛ ek) ∗ Seg1Spatial s0 esA es F :=
    Entails.trans hP1 (by dsimp only [Seg1Spatial]; sep_frame)
  exact SepWP.weaken_pre hP1'
    (seg2_ok hb hbase s0 s1 ret esA ekA es ek F hpc1 hrun1 hcl1 hro1 hes hek hpost1)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2
