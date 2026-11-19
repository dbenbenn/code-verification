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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5b

/-!
# `encapsulate2` (`B20`) — Segment 5 & Segment 4+5 Suffix Composition (`+0x10a0 .. +0x2b10` `ret`)

Composes `Seg5a` (`+0x28e8 .. +0x29a8`) and `Seg5b` (`+0x29a8 .. +0x2b10` `ret`) into `seg5_ok`,
and composes `Seg4` (`+0x10a0 .. +0x28e8`) with `seg5_ok` into `seg45_ok`, connecting
`upperInvNtt16`, `seg5FinalPoly`, `neonCompressSerialize4`, and `stackAt s0.sp 6128` restoration.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5

open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (Poly16 neonCompressSerialize4)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  SavedFrame20 UnspilledSaved20 blkPC20 blkPl20 sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem Spill13 Spill13Mem polyVecNat spill13Mem_entails_memRegion vecRangeMem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Pure (upperInvNtt16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4 (Seg4Post seg4_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd (seg5FinalPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5a (seg5a_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5b (seg5b_ok)

/-! ## 1. Stack Frame Decomposition & Restoration (`6128 = 6000 + 128`) -/

theorem stackAt_6128_eq (sp0 : BitVec 64) :
    memRegion (sp0 - 6128#64) 6000 ∗ memRegion (sp0 - 128#64) 128 = stackAt sp0 6128 := by
  unfold stackAt
  have h0 : memRegion (sp0 - BitVec.ofNat 64 6128) 6128 = memRegion (sp0 - 6128#64) 6128 := rfl
  rw [h0, memRegion_split' (b' := sp0 - 128#64) (n := 6000) (k := 128) rfl (by bv_omega) (by decide)]

theorem seg45_stack_eq (sp : BitVec 64) :
    memRegion sp 6000 =
      memRegion sp 208 ∗ memRegion (sp + 1744#64) 512 ∗ memRegion (sp + 2288#64) 128 ∗
      memRegion (sp + 2416#64) 512 ∗ memRegion (sp + 2928#64) 512 ∗ memRegion (sp + 3440#64) 512 ∗
      (memRegion (sp + 208#64) 1536 ∗ memRegion (sp + 2256#64) 32 ∗
        memRegion (sp + 3952#64) 2048) := by
  rw [memRegion_split' (b' := sp + 208#64) (n := 208) (k := (5792 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 1744#64) (n := 1536) (k := (4256 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 2256#64) (n := 512) (k := (3744 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 2288#64) (n := 32) (k := (3712 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 2416#64) (n := 128) (k := (3584 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 2928#64) (n := 512) (k := (3072 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 3440#64) (n := 512) (k := (2560 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b' := sp + 3952#64) (n := 512) (k := (2048 : Nat)) rfl (by bv_omega) (by decide)]
  exact sepProp_ext (by sep_frame) (by sep_frame)

/-! ## 2. Segment 5 (`+0x28e8 → ret`) & Segment 4+5 (`+0x10a0 → ret`) Contracts -/

/-- Segment 5 (`+0x28e8 → ret`) with an arbitrary spatial `Frame`. -/
theorem seg5_raw_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl20 b)
    (s0 s4 : State) (ret : BitVec 64) (spill : Spill13) (inv err2 msgPoly : Poly16)
    (Frame : SepProp)
    (hsp0 : s0.spAligned = true)
    (hpc : s4.pc = b + 0x28e8#64) (hrun : s4.status = .Running)
    (hpost4 : Seg4Post s0 s4 (s0.sp - 6128#64) ret)
    (hs6 : spill.s6 = dup8x16 20159#16) (hs11 : spill.s11 = dup8x16 3329#16)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s4.mem) (hro : MlKemRoOk mlkemMpl s4.mem) :
    let sp := s0.sp - 6128#64
    SepWP (blkPC20.rebase b (fun _ => none)) (s0.readReg64 .lr) s4
      (Spill13Mem sp spill ∗ memRegion (sp + 3440#64) 512 ∗
        PolyMem (sp + 2928#64) (polyVecNat inv) ∗ PolyMem (sp + 1744#64) (polyVecNat err2) ∗
        PolyMem (sp + 2416#64) (polyVecNat msgPoly) ∗ memRegion (sp + 2288#64) 128 ∗
        SavedFrame20 s0.sp s0 ∗ memRegion ret 128 ∗ Frame)
      (sepPost (fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        ((ret ↦ₛ neonCompressSerialize4 (seg5FinalPoly inv err2 msgPoly)) ∗
          memRegion sp 208 ∗ memRegion (sp + 1744#64) 512 ∗ memRegion (sp + 2288#64) 128 ∗
          memRegion (sp + 2416#64) 512 ∗ memRegion (sp + 2928#64) 512 ∗
          memRegion (sp + 3440#64) 512 ∗ memRegion (s0.sp - 128#64) 128 ∗ Frame)) := by
  intro sp
  have hbase : blkPl20.base = b := hb.symm
  refine SepWP.weaken_pre (by sep_frame)
    (sepWP_seq_env hcl hro
      (seg5a_ok hb hbase s0 s4 sp ret spill inv err2 msgPoly
        (memRegion (sp + 2288#64) 128 ∗ SavedFrame20 s0.sp s0 ∗ memRegion ret 128 ∗ Frame)
        hpc hrun hpost4 hs6 hs11 hcl hro) ?_)
  rintro s5 _ hpc5 hrun5 hcl5 hro5 ⟨hsp5, hspA5, hx19_5, hus5, rfl⟩
  refine SepWP.weaken_pre (by sep_frame)
    (SepWP.mono
      (seg5b_ok hb hbase s0 s5 ret (seg5FinalPoly inv err2 msgPoly)
        (Spill13Mem sp spill ∗ PolyMem (sp + 1744#64) (polyVecNat err2) ∗
          PolyMem (sp + 2416#64) (polyVecNat msgPoly) ∗
          PolyMem (sp + 2928#64) (polyVecNat inv) ∗ Frame)
        hsp0 hpc5 hrun5 hsp5 hspA5 hx19_5 hus5 hcl5 hro5) ?_)
  intro sf Pf _ _ hpost; rw [sepPost_apply] at hpost ⊢
  refine ⟨hpost.1, Entails.trans hpost.2 ?_⟩
  have hp (ptr : BitVec 64) (f : Nat → BitVec 128) : PolyMem ptr f ⊢ memRegion ptr 512 :=
    vecRangeMem_entails_memRegion 32 ptr f
  have hsub := sepConj_mono (spill13Mem_entails_memRegion sp spill)
    (sepConj_mono (hp (sp + 1744#64) (polyVecNat err2))
      (sepConj_mono (hp (sp + 2416#64) (polyVecNat msgPoly)) (hp (sp + 2928#64) (polyVecNat inv))))
  exact Entails.trans (by sep_frame) (Entails.trans (sepConj_mono_left hsub) (by sep_frame))

/-- Segment 5 (`+0x28e8 → ret`) collapsing the `6128`-byte stack frame back to `stackAt s0.sp 6128`. -/
theorem seg5_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl20 b)
    (s0 s4 : State) (ret : BitVec 64) (spill : Spill13) (inv err2 msgPoly : Poly16)
    (StackRest CallerRest : SepProp)
    (hsp0 : s0.spAligned = true)
    (hpc : s4.pc = b + 0x28e8#64) (hrun : s4.status = .Running)
    (hpost4 : Seg4Post s0 s4 (s0.sp - 6128#64) ret)
    (hs6 : spill.s6 = dup8x16 20159#16) (hs11 : spill.s11 = dup8x16 3329#16)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s4.mem) (hro : MlKemRoOk mlkemMpl s4.mem)
    (hstk : let sp := s0.sp - 6128#64
      memRegion sp 208 ∗ memRegion (sp + 1744#64) 512 ∗ memRegion (sp + 2288#64) 128 ∗
        memRegion (sp + 2416#64) 512 ∗ memRegion (sp + 2928#64) 512 ∗
        memRegion (sp + 3440#64) 512 ∗ StackRest ⊢ memRegion sp 6000) :
    let sp := s0.sp - 6128#64
    SepWP (blkPC20.rebase b (fun _ => none)) (s0.readReg64 .lr) s4
      (Spill13Mem sp spill ∗ memRegion (sp + 3440#64) 512 ∗
        PolyMem (sp + 2928#64) (polyVecNat inv) ∗ PolyMem (sp + 1744#64) (polyVecNat err2) ∗
        PolyMem (sp + 2416#64) (polyVecNat msgPoly) ∗ memRegion (sp + 2288#64) 128 ∗
        SavedFrame20 s0.sp s0 ∗ memRegion ret 128 ∗ StackRest ∗ CallerRest)
      (sepPost (fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        ((ret ↦ₛ neonCompressSerialize4 (seg5FinalPoly inv err2 msgPoly)) ∗
          stackAt s0.sp 6128 ∗ CallerRest)) := by
  intro sp
  refine SepWP.mono
    (seg5_raw_ok hb s0 s4 ret spill inv err2 msgPoly (StackRest ∗ CallerRest)
      hsp0 hpc hrun hpost4 hs6 hs11 hcl hro) ?_
  intro sf Pf _ _ hpost; rw [sepPost_apply] at hpost ⊢
  refine ⟨hpost.1, Entails.trans hpost.2 ?_⟩
  rw [← stackAt_6128_eq s0.sp]
  exact Entails.trans (by sep_frame) (Entails.trans (sepConj_mono_left hstk) (by sep_frame))

/-- Combined Segment 4 + Segment 5 (`+0x10a0 → ret`) with an arbitrary spatial `Frame`. -/
theorem seg45_raw_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl20 b)
    (s0 s3 : State) (ret : BitVec 64) {p2 : Poly16} (hp2 : p2.size = 256)
    (err2 msgPoly : Poly16) (Frame : SepProp)
    (hsp0 : s0.spAligned = true)
    (hpc : s3.pc = b + 0x10a0#64) (hrun : s3.status = .Running)
    (hsp : s3.sp = s0.sp - 6128#64) (hspA : s3.spAligned = true)
    (hx19 : s3.readReg64 .x19 = ret) (hus : UnspilledSaved20 s0 s3)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s3.mem) (hro : MlKemRoOk mlkemMpl s3.mem) :
    let sp := s0.sp - 6128#64
    SepWP (blkPC20.rebase b (fun _ => none)) (s0.readReg64 .lr) s3
      (memRegion sp 208 ∗ PolyMem (sp + 2928#64) (polyVecNat p2) ∗
        memRegion (sp + 3440#64) 512 ∗ PolyMem (sp + 1744#64) (polyVecNat err2) ∗
        PolyMem (sp + 2416#64) (polyVecNat msgPoly) ∗ memRegion (sp + 2288#64) 128 ∗
        SavedFrame20 s0.sp s0 ∗ memRegion ret 128 ∗ Frame)
      (sepPost (fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        ((ret ↦ₛ neonCompressSerialize4 (seg5FinalPoly (upperInvNtt16 p2) err2 msgPoly)) ∗
          memRegion sp 208 ∗ memRegion (sp + 1744#64) 512 ∗ memRegion (sp + 2288#64) 128 ∗
          memRegion (sp + 2416#64) 512 ∗ memRegion (sp + 2928#64) 512 ∗
          memRegion (sp + 3440#64) 512 ∗ memRegion (s0.sp - 128#64) 128 ∗ Frame)) := by
  intro sp
  refine sepWP_seq_env hcl hro
    (seg4_ok s0 s3 sp ret hp2
      (memRegion (sp + 3440#64) 512 ∗ PolyMem (sp + 1744#64) (polyVecNat err2) ∗
        PolyMem (sp + 2416#64) (polyVecNat msgPoly) ∗ memRegion (sp + 2288#64) 128 ∗
        SavedFrame20 s0.sp s0 ∗ memRegion ret 128 ∗ Frame)
      hpc hrun hsp hspA hx19 hus) ?_
  rintro s4 _ hpc4 hrun4 hcl4 hro4 ⟨hpost4, spill, hs6, hs11, rfl⟩
  exact SepWP.weaken_pre (by sep_frame)
    (seg5_raw_ok hb s0 s4 ret spill (upperInvNtt16 p2) err2 msgPoly Frame
      hsp0 hpc4 hrun4 hpost4 hs6 hs11 hcl4 hro4)

/-- Combined Segment 4 + Segment 5 (`+0x10a0 → ret`) restoring `stackAt s0.sp 6128`. -/
theorem seg45_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl20 b)
    (s0 s3 : State) (ret : BitVec 64) {p2 : Poly16} (hp2 : p2.size = 256)
    (err2 msgPoly : Poly16) (StackRest CallerRest : SepProp)
    (hsp0 : s0.spAligned = true)
    (hpc : s3.pc = b + 0x10a0#64) (hrun : s3.status = .Running)
    (hsp : s3.sp = s0.sp - 6128#64) (hspA : s3.spAligned = true)
    (hx19 : s3.readReg64 .x19 = ret) (hus : UnspilledSaved20 s0 s3)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s3.mem) (hro : MlKemRoOk mlkemMpl s3.mem)
    (hstk : let sp := s0.sp - 6128#64
      memRegion sp 208 ∗ memRegion (sp + 1744#64) 512 ∗ memRegion (sp + 2288#64) 128 ∗
        memRegion (sp + 2416#64) 512 ∗ memRegion (sp + 2928#64) 512 ∗
        memRegion (sp + 3440#64) 512 ∗ StackRest ⊢ memRegion sp 6000) :
    let sp := s0.sp - 6128#64
    SepWP (blkPC20.rebase b (fun _ => none)) (s0.readReg64 .lr) s3
      (memRegion sp 208 ∗ PolyMem (sp + 2928#64) (polyVecNat p2) ∗
        memRegion (sp + 3440#64) 512 ∗ PolyMem (sp + 1744#64) (polyVecNat err2) ∗
        PolyMem (sp + 2416#64) (polyVecNat msgPoly) ∗ memRegion (sp + 2288#64) 128 ∗
        SavedFrame20 s0.sp s0 ∗ memRegion ret 128 ∗ StackRest ∗ CallerRest)
      (sepPost (fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        ((ret ↦ₛ neonCompressSerialize4 (seg5FinalPoly (upperInvNtt16 p2) err2 msgPoly)) ∗
          stackAt s0.sp 6128 ∗ CallerRest)) := by
  intro sp
  refine SepWP.mono
    (seg45_raw_ok hb s0 s3 ret hp2 err2 msgPoly (StackRest ∗ CallerRest)
      hsp0 hpc hrun hsp hspA hx19 hus hcl hro) ?_
  intro sf Pf _ _ hpost; rw [sepPost_apply] at hpost ⊢
  refine ⟨hpost.1, Entails.trans hpost.2 ?_⟩
  rw [← stackAt_6128_eq s0.sp]
  exact Entails.trans (by sep_frame) (Entails.trans (sepConj_mono_left hstk) (by sep_frame))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5
