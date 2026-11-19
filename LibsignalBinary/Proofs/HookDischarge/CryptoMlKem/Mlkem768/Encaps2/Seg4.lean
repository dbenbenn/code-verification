/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Pure -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4SymDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Sym
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4b
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4c

/-!
# `encapsulate2` (`B20`) — Segment 4 (`+0x10a0 .. +0x28e8`, Upper 5 `InvNTT` Layers + Barrett)

Composes `Seg4a`, `Seg4b`, and `Seg4c` (`528 + 514 + 512 = 1,554` straight-line instructions) via
`sepWP_of_runSymRange` and `symState4c_poly_eq`, proving that `[sp + 2928 .. sp + 3440)` holds
`polyVecNat (upperInvNtt16 p2)` and establishing the register/spill state at `+0x28e8`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4

open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
  (MlKemPlacement)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec
  (Poly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
  (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
  (blkPC20 UnspilledSaved20)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
  (PolyMem Spill13 Spill13Mem Vec32 polyVecNat poly32Mem_ofFn spill13Mem_ofFn
   SepWP.of_memRegion_vecRangeMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Pure
  (upperInvNtt16 symState4c_poly_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4SymDefs
  (symInit4 runSymRange runSymRange_add SymEnv SymSpatial symInit4_matches)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4Sym
  (sepWP_of_runSymRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4a
  (symState4a seg4a_eval)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4b
  (symState4b seg4b_eval)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4c
  (symState4c seg4c_eval)

private theorem seg4_eval : runSymRange (0x10a0 / 4) 1554 symInit4 = some symState4c :=
  runSymRange_add 1064 1042 512 symInit4 symState4b symState4c
    (runSymRange_add 1064 528 514 symInit4 symState4a symState4b seg4a_eval seg4b_eval)
    seg4c_eval

/-- Post-state register invariants at `+0x28e8` (`bl memcpy` entry). -/
@[expose] def Seg4Post (s0 s4 : State) (sp ret : BitVec 64) : Prop :=
  s4.sp = sp ∧
  s4.spAligned = true ∧
  s4.readReg64 .x19 = ret ∧
  UnspilledSaved20 s0 s4 ∧
  s4.readReg64 .x0 = sp + 3440#64 ∧
  s4.readReg64 .x1 = sp + 2928#64 ∧
  s4.readReg64 .x2 = 512#64 ∧
  s4.readReg64 .x20 = sp + 3440#64

/-- Segment 4 contract starting from an arbitrary initialized `Spill13Mem sp spill0`. -/
theorem seg4_spill13_ok [MlKemPlacement] {b : BitVec 64}
    (s0 s3 : State) (sp ret : BitVec 64) (spill0 : Spill13) {p2 : Poly16} (hp2 : p2.size = 256)
    (F : SepProp)
    (hpc : s3.pc = b + 0x10a0#64)
    (hrun : s3.status = .Running)
    (hsp : s3.sp = sp)
    (hsp_al : s3.spAligned = true)
    (hx19 : s3.readReg64 .x19 = ret)
    (hunsp : UnspilledSaved20 s0 s3) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x28e8#64) s3
      (Spill13Mem sp spill0 ∗ PolyMem (sp + 2928#64) (polyVecNat p2) ∗ F)
      (fun s4 P4 => Seg4Post s0 s4 sp ret ∧
        ∃ spill : Spill13,
          spill.s6 = dup8x16 20159#16 ∧
          spill.s11 = dup8x16 3329#16 ∧
          P4 = (Spill13Mem sp spill ∗
            PolyMem (sp + 2928#64) (polyVecNat (upperInvNtt16 p2)) ∗ F)) := by
  let poly0 : Vec32 := Vec32.ofFn (polyVecNat p2)
  let env : SymEnv :=
    { vreg0 := fun r => s3.readVReg128 (BitVec.ofNat 5 r), spill0 := spill0, poly0 := poly0 }
  have ⟨hm0, hsp0⟩ := symInit4_matches s0 s3 sp ret spill0 poly0 hsp hsp_al hx19 hunsp
  rw [← poly32Mem_ofFn (sp + 2928#64) (polyVecNat p2), ← hsp0 F]
  exact sepWP_of_runSymRange (s0 := s0) (sp := sp) (ret := ret) (env := env) (F := F)
    1554 1064 (by omega) (by omega) seg4_eval hm0 hpc hrun
    (fun s4 _ _ hm4 => by
      refine ⟨⟨hm4.hsp, hm4.hsp_al, hm4.hx19, hm4.hunsp,
        hm4.hx0, hm4.hx1, hm4.hx2, hm4.hx20⟩, symState4c.spill.eval env, rfl, rfl, ?_⟩
      simp only [SymSpatial, symState4c_poly_eq (sp + 2928#64) hp2 env rfl])

/-- Segment 4 contract starting from uninitialized `memRegion sp 208` spill space. -/
theorem seg4_ok [MlKemPlacement] {b : BitVec 64}
    (s0 s3 : State) (sp ret : BitVec 64) {p2 : Poly16} (hp2 : p2.size = 256)
    (F : SepProp)
    (hpc : s3.pc = b + 0x10a0#64)
    (hrun : s3.status = .Running)
    (hsp : s3.sp = sp)
    (hsp_al : s3.spAligned = true)
    (hx19 : s3.readReg64 .x19 = ret)
    (hunsp : UnspilledSaved20 s0 s3) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x28e8#64) s3
      (memRegion sp 208 ∗ PolyMem (sp + 2928#64) (polyVecNat p2) ∗ F)
      (fun s4 P4 => Seg4Post s0 s4 sp ret ∧
        ∃ spill : Spill13,
          spill.s6 = dup8x16 20159#16 ∧
          spill.s11 = dup8x16 3329#16 ∧
          P4 = (Spill13Mem sp spill ∗
            PolyMem (sp + 2928#64) (polyVecNat (upperInvNtt16 p2)) ∗ F)) := by
  apply SepWP.of_memRegion_vecRangeMem 13 sp (by decide) rfl
  intro f
  change SepWP _ _ _ (VecMem.SpillMem sp f ∗ _) _
  rw [← spill13Mem_ofFn sp f]
  exact seg4_spill13_ok s0 s3 sp ret (Spill13.ofFn f) hp2 F hpc hrun hsp hsp_al hx19 hunsp

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4
