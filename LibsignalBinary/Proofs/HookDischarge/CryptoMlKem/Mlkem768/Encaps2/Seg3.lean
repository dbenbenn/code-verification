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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3b

/-!
# `encapsulate2` (`B20`) — Segment 3 (`+0x0bdc .. +0x10a0`)

Composes:
1. `Seg3a.seg3a_ok` (`+0x0bdc → +0x0f5c`): 3-way NTT dot product `neonDot3 t0 t1 t2 r0 r1 r2`;
2. `Seg3b.seg3b_ok` (`+0x0f5c → +0x10a0`): lower 2 `InvNTT` butterfly layers (`len = 2, 4`),
   producing `PolyMem (sp + 2928#64) (polyVecNat (lowerInvNtt16 dot))` and `Spill13Mem sp (AccSpill dot)`
   at `+0x10a0` in the exact layout expected by `Seg4.seg4_spill13_ok` / `Seg4.seg4_ok`;
3. `seg3_to_28e8_ok` (`+0x0bdc → +0x28e8`): pre-composed `Seg3` + `Seg4` bridge yielding
   `Seg4Post` + `Spill13Mem` (`s6 = dup8x16 20159#16`, `s11 = dup8x16 3329#16`) +
   `PolyMem (sp + 2928#64) (polyVecNat (neonInvNttMontgomery16 dot))` directly for `Seg5a.seg5a_ok`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3

open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly16 neonInvNttMontgomery16 neonPolyNttMul16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  UnspilledSaved20 blkPC20 blkPl20 sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem Spill13 Spill13Mem Vec32 polyVecNat spill13Mem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure (
  lowerInvNtt16 lowerInvNtt16_size neonDot3 neonDot3_eq_encaps2_fold neonDot3_size polyZero16
  upperInvNtt16_lowerInvNtt16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3a (
  AccRegs AccSpill ro00Sym seg3a_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3b (seg3b_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Pure (upperInvNtt16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4 (
  Seg4Post seg4_spill13_ok)

/-- Register and stack-alignment postcondition at `+0x10a0` matching `Seg4.seg4_spill13_ok` / `seg4_ok`. -/
@[expose] def Seg3Post (s0 s3 : State) (sp ret : BitVec 64) : Prop :=
  s3.sp = sp ∧
  s3.spAligned = true ∧
  s3.readReg64 .x19 = ret ∧
  UnspilledSaved20 s0 s3

@[simp] theorem lowerInvNtt16_neonDot3_size (t0 t1 t2 r0 r1 r2 : Poly16) :
    (lowerInvNtt16 (neonDot3 t0 t1 t2 r0 r1 r2)).size = 256 :=
  lowerInvNtt16_size (neonDot3_size t0 t1 t2 r0 r1 r2)

/-- Pure `InvNTT ∘ foldl` bridge identifying `upperInvNtt16 (lowerInvNtt16 (neonDot3 ...))`
    with `neonInvNttMontgomery16` applied to `Spec/MlKem.lean`'s 3-way `foldl` accumulator. -/
theorem encaps2_invNtt_dot_eq (tHat rHat : Array Poly16) :
    upperInvNtt16 (lowerInvNtt16 (neonDot3
      (tHat.getD 0 #[]) (tHat.getD 1 #[]) (tHat.getD 2 #[])
      (rHat.getD 0 #[]) (rHat.getD 1 #[]) (rHat.getD 2 #[]))) =
    neonInvNttMontgomery16
      ((List.range 3).foldl
        (fun acc j =>
          let prod := neonPolyNttMul16 (tHat.getD j #[]) (rHat.getD j #[])
          Array.ofFn (n := 256) fun ⟨i, _⟩ => acc.getD i 0#16 + prod.getD i 0#16)
        (Array.replicate 256 0#16)) := by
  rw [upperInvNtt16_lowerInvNtt16, neonDot3_eq_encaps2_fold]

/-- Segment 3 (`+0x0bdc → +0x10a0`): 3-way NTT dot product + lower 2 `InvNTT` layers (`len = 2, 4`). -/
theorem seg3_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl20 b)
    (s0 s : State) (sp ret : BitVec 64) (t0 t1 t2 r0 r1 r2 : Poly16)
    (v2928 v5488 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + 0x0bdc#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = 0#64) (hx9 : s.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx10 : s.readReg64 .x10 = sp + 208#64) (hx11 : s.readReg64 .x11 = 62209#64)
    (hx12 : s.readReg64 .x12 = 3329#64) (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = sp + 3952#64) (hx21 : s.readReg64 .x21 = sp + 5488#64)
    (hacc : AccRegs polyZero16 s) (hus : UnspilledSaved20 s0 s) :
    let dot := neonDot3 t0 t1 t2 r0 r1 r2
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x10a0#64) s
      (Spill13Mem sp Spill13.zero ∗ PolyMem (sp + 208#64) (polyVecNat r0) ∗
        PolyMem (sp + 720#64) (polyVecNat r1) ∗ PolyMem (sp + 1232#64) (polyVecNat r2) ∗
        Poly32Mem (sp + 2928#64) v2928 ∗ PolyMem (sp + 3952#64) (polyVecNat t0) ∗
        PolyMem (sp + 4464#64) (polyVecNat t1) ∗ PolyMem (sp + 4976#64) (polyVecNat t2) ∗
        Poly32Mem (sp + 5488#64) v5488 ∗ Rest)
      (fun s3 P3 =>
        Seg3Post s0 s3 sp ret ∧
        P3 = (Spill13Mem sp (AccSpill dot) ∗
          PolyMem (sp + 2928#64) (polyVecNat (lowerInvNtt16 dot)) ∗
          PolyMem (sp + 208#64) (polyVecNat r0) ∗
          PolyMem (sp + 720#64) (polyVecNat r1) ∗
          PolyMem (sp + 1232#64) (polyVecNat r2) ∗
          PolyMem (sp + 3952#64) (polyVecNat t0) ∗
          PolyMem (sp + 4464#64) (polyVecNat t1) ∗
          PolyMem (sp + 4976#64) (polyVecNat t2) ∗
          Poly32Mem (sp + 5488#64) (Vec32.ofFn (polyVecNat (neonPolyNttMul16 t2 r2))) ∗ Rest)) := by
  dsimp only
  let dot := neonDot3 t0 t1 t2 r0 r1 r2
  refine sepWP_seq_env hcl hro (seg3a_ok hb s0 s sp ret t0 t1 t2 r0 r1 r2 v2928 v5488 Rest
    hpc hrun hsp hspA hcl hro hx8 hx9 hx10 hx11 hx12 hx19 hx20 hx21 hacc hus) ?_
  rintro sm Pm hpcm hrunm hclm hrom ⟨hspm, hspAm, hx19m, husm, rfl⟩
  rw [show (Spill13Mem sp (AccSpill dot) ∗ PolyMem (sp + 208#64) (polyVecNat r0) ∗
        PolyMem (sp + 720#64) (polyVecNat r1) ∗ PolyMem (sp + 1232#64) (polyVecNat r2) ∗
        PolyMem (sp + 2928#64) (polyVecNat dot) ∗ PolyMem (sp + 3952#64) (polyVecNat t0) ∗
        PolyMem (sp + 4464#64) (polyVecNat t1) ∗ PolyMem (sp + 4976#64) (polyVecNat t2) ∗
        Poly32Mem (sp + 5488#64) (Vec32.ofFn (polyVecNat (neonPolyNttMul16 t2 r2))) ∗ Rest) =
      (PolyMem (sp + 2928#64) (polyVecNat dot) ∗
        (Spill13Mem sp (AccSpill dot) ∗ PolyMem (sp + 208#64) (polyVecNat r0) ∗
          PolyMem (sp + 720#64) (polyVecNat r1) ∗ PolyMem (sp + 1232#64) (polyVecNat r2) ∗
          PolyMem (sp + 3952#64) (polyVecNat t0) ∗ PolyMem (sp + 4464#64) (polyVecNat t1) ∗
          PolyMem (sp + 4976#64) (polyVecNat t2) ∗
          Poly32Mem (sp + 5488#64) (Vec32.ofFn (polyVecNat (neonPolyNttMul16 t2 r2))) ∗ Rest)) from
    sepProp_ext (by sep_frame) (by sep_frame)]
  refine SepWP.mono (seg3b_ok hb s0 sm sp ret (neonDot3_size t0 t1 t2 r0 r1 r2) _
    hpcm hrunm hspm hspAm hclm hrom hx19m husm) ?_
  rintro s3 P3 _ _ ⟨hsp3, hspA3, hx19_3, hus3, rfl⟩
  exact ⟨⟨hsp3, hspA3, hx19_3, hus3⟩, sepProp_ext (by sep_frame) (by sep_frame)⟩

/-- Composed Segment 3 + Segment 4 (`+0x0bdc → +0x28e8`): full 3-way NTT dot product + all 7 `InvNTT`
    layers, establishing `Seg4Post` and `Spill13Mem` (`s6 = dup8x16 20159#16`, `s11 = dup8x16 3329#16`)
    for `Seg5a.seg5a_ok`. -/
theorem seg3_to_28e8_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl20 b)
    (s0 s : State) (sp ret : BitVec 64) (t0 t1 t2 r0 r1 r2 : Poly16)
    (v2928 v5488 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + 0x0bdc#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = 0#64) (hx9 : s.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx10 : s.readReg64 .x10 = sp + 208#64) (hx11 : s.readReg64 .x11 = 62209#64)
    (hx12 : s.readReg64 .x12 = 3329#64) (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = sp + 3952#64) (hx21 : s.readReg64 .x21 = sp + 5488#64)
    (hacc : AccRegs polyZero16 s) (hus : UnspilledSaved20 s0 s) :
    let dot := neonDot3 t0 t1 t2 r0 r1 r2
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x28e8#64) s
      (Spill13Mem sp Spill13.zero ∗ PolyMem (sp + 208#64) (polyVecNat r0) ∗
        PolyMem (sp + 720#64) (polyVecNat r1) ∗ PolyMem (sp + 1232#64) (polyVecNat r2) ∗
        Poly32Mem (sp + 2928#64) v2928 ∗ PolyMem (sp + 3952#64) (polyVecNat t0) ∗
        PolyMem (sp + 4464#64) (polyVecNat t1) ∗ PolyMem (sp + 4976#64) (polyVecNat t2) ∗
        Poly32Mem (sp + 5488#64) v5488 ∗ Rest)
      (fun s4 P4 =>
        Seg4Post s0 s4 sp ret ∧
        mlkemMultiLib.CodeLoaded mlkemMpl s4.mem ∧
        MlKemRoOk mlkemMpl s4.mem ∧
        ∃ spill : Spill13,
          spill.s6 = dup8x16 20159#16 ∧
          spill.s11 = dup8x16 3329#16 ∧
          P4 = (Spill13Mem sp spill ∗
            PolyMem (sp + 2928#64) (polyVecNat (neonInvNttMontgomery16 dot)) ∗
            PolyMem (sp + 208#64) (polyVecNat r0) ∗
            PolyMem (sp + 720#64) (polyVecNat r1) ∗
            PolyMem (sp + 1232#64) (polyVecNat r2) ∗
            PolyMem (sp + 3952#64) (polyVecNat t0) ∗
            PolyMem (sp + 4464#64) (polyVecNat t1) ∗
            PolyMem (sp + 4976#64) (polyVecNat t2) ∗
            Poly32Mem (sp + 5488#64) (Vec32.ofFn (polyVecNat (neonPolyNttMul16 t2 r2))) ∗ Rest)) := by
  dsimp only
  let dot := neonDot3 t0 t1 t2 r0 r1 r2
  refine sepWP_seq_env hcl hro (seg3_ok hb s0 s sp ret t0 t1 t2 r0 r1 r2 v2928 v5488 Rest
    hpc hrun hsp hspA hcl hro hx8 hx9 hx10 hx11 hx12 hx19 hx20 hx21 hacc hus) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨⟨hsp3, hspA3, hx19_3, hus3⟩, rfl⟩
  refine sepWP_seq_env hcl3 hro3
    (seg4_spill13_ok s0 s3 sp ret (AccSpill dot)
      (lowerInvNtt16_neonDot3_size t0 t1 t2 r0 r1 r2) _
      hpc3 hrun3 hsp3 hspA3 hx19_3 hus3) ?_
  rintro s4 P4 hpc4 hrun4 hcl4 hro4 ⟨hpost4, spill, hs6, hs11, rfl⟩
  rw [upperInvNtt16_lowerInvNtt16]
  exact SepWP.done hpc4 hrun4 ⟨hpost4, hcl4, hro4, spill, hs6, hs11, rfl⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3
