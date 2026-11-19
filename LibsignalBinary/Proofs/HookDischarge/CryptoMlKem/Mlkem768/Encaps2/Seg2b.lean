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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2a -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2b1

/-!
# `encapsulate2` (`B20`) — Segment 2b (`+0x0710 .. +0x0bdc`)

Completes `decompress_1(m)` (`+0x0ab8 .. +0x0bdc`), zeros the 32-vector `dot` buffer
`PolyMem (sp + 2928#64) (fun _ => 0#128)` and `Spill13Mem sp Spill13.zero`, zeros accumulator
VRegs `v0..v2, v8..v15, v22..v31`, and composes with `Seg2b1.seg2b1_ok` to establish `seg2b_ok`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2b

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (bytesToPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  SavedFrame20 UnspilledSaved20 blk20_code_eq blk20_tree_size blkLib20 blkPC20 blkPl20
  blkPlaceable20 blkTree20 sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem SepLoad128 SepStore128 Spill13 Spill13Mem Vec32 VecRangeMem
  poly32Mem_ofFn polyVecNat spill13Mem_ofFn step_ldrQ128 step_stpQ128 step_strQ128)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (spAligned_of_chk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure (
  msgPoly16 tHatPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2a (
  Seg2aPost Seg2aSpatial)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2b1 (
  msgVec32Pre seg2b1_ok)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC20 blkLib20 blkTree20 blk20_code_eq blk20_tree_size
  via_placement blkPl20 blkPlaceable20 [0x0ab8 → 0x0bd8]
end

attribute [local irreducible] blkPC20 polyVecNat

private theorem memRegion_1536_seg2b_split (sp : BitVec 64) :
    memRegion (sp + 2416#64) 1536 =
      memRegion (sp + 2416#64) 512 ∗ memRegion (sp + 2928#64) 512 ∗ memRegion (sp + 3440#64) 512 := by
  rw [memRegion_split' (b' := sp + 2928#64) (n := 512) (k := (1024 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 3440#64) (n := 512) (k := 512) rfl (by bv_omega) (by decide)]

private theorem step_strQ_dot {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp : BitVec 64} {pMsg pDot pDot' : Vec32} {Rest : SepProp}
    {post : State → SepProp → Prop}
    {pc : BitVec 64} {imm : BitVec 64} (k : Nat)
    (hchk : (sp &&& 15#64 == 0#64) = true) (hk : k < 32 := by decide)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.strSimd .Q128 0#5 (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (himm : 2928#64 + BitVec.ofNat 64 (16 * k) = imm := by decide)
    (hv0 : s.readVReg128 0#5 = 0#128) (hd : pDot.set k 0#128 = pDot')
    (hexec : s.setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m')
      (Poly32Mem (sp + 2416#64) pMsg ∗ Poly32Mem (sp + 2928#64) pDot' ∗ Rest) post) :
    SepWP prog target_pc s
      (Poly32Mem (sp + 2416#64) pMsg ∗ Poly32Mem (sp + 2928#64) pDot ∗ Rest) post := by
  have ha : (sp + 2928#64) + BitVec.ofNat 64 (16 * k) = s.sp + imm := by
    rw [hsp_eq, ← himm]; bv_omega
  have hsp_al : s.spAligned = true := spAligned_of_chk hsp_eq hchk
  exact step_strQ128 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hsp_al])
    (by simp [evalAddrMode]) hv0
    (SepStore128.right (SepStore128.left (SepStore128.vec32 hk ha hd))) hexec hnext

private theorem step_ldrQ_dot {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp : BitVec 64} {pMsg pDot : Vec32} {Rest : SepProp}
    {post : State → SepProp → Prop}
    {pc : BitVec 64} {vt : BitVec 5} {imm : BitVec 64} (k : Nat)
    (hchk : (sp &&& 15#64 == 0#64) = true) (hk : k < 32 := by decide)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldrSimd .Q128 vt (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (himm : 2928#64 + BitVec.ofNat 64 (16 * k) = imm := by decide)
    (hget : pDot.get k = 0#128)
    (hexec : (s.writeVReg128 vt 0#128).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s'
      (Poly32Mem (sp + 2416#64) pMsg ∗ Poly32Mem (sp + 2928#64) pDot ∗ Rest) post) :
    SepWP prog target_pc s
      (Poly32Mem (sp + 2416#64) pMsg ∗ Poly32Mem (sp + 2928#64) pDot ∗ Rest) post := by
  have ha : (sp + 2928#64) + BitVec.ofNat 64 (16 * k) = s.sp + imm := by
    rw [hsp_eq, ← himm]; bv_omega
  have hsp_al : s.spAligned = true := spAligned_of_chk hsp_eq hchk
  exact step_ldrQ128 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hsp_al])
    (by simp [evalAddrMode])
    (SepLoad128.right (SepLoad128.left (SepLoad128.vec32 hk ha hget))) hexec hnext

private theorem step_stpQ_spill {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp : BitVec 64} {pMsg pDot : Vec32} {sp13 sp13' : Spill13} {Rest : SepProp}
    {post : State → SepProp → Prop}
    {pc : BitVec 64} {imm : BitVec 64} (k : Nat)
    (hchk : (sp &&& 15#64 == 0#64) = true)
    (hk1 : k < 13 := by decide) (hk2 : k + 1 < 13 := by decide)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stpSimd .Q128 1#5 2#5 (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (himm : BitVec.ofNat 64 (16 * k) = imm := by decide)
    (hv1 : s.readVReg128 1#5 = 0#128) (hv2 : s.readVReg128 2#5 = 0#128)
    (hsp13 : (sp13.set k 0#128).set (k + 1) 0#128 = sp13')
    (hexec : s.setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m')
      (Poly32Mem (sp + 2416#64) pMsg ∗ Poly32Mem (sp + 2928#64) pDot ∗
        Spill13Mem sp sp13' ∗ Rest) post) :
    SepWP prog target_pc s
      (Poly32Mem (sp + 2416#64) pMsg ∗ Poly32Mem (sp + 2928#64) pDot ∗
        Spill13Mem sp sp13 ∗ Rest) post := by
  have ha1 : sp + BitVec.ofNat 64 (16 * k) = s.sp + imm := by rw [hsp_eq, ← himm]
  have ha2 : sp + BitVec.ofNat 64 (16 * (k + 1)) = (s.sp + imm) + 16#64 := by
    rw [hsp_eq, ← himm]; bv_omega
  have hsp_al : s.spAligned = true := spAligned_of_chk hsp_eq hchk
  exact step_stpQ128 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hsp_al])
    (by simp [evalAddrMode]) rfl hv1 hv2
    (SepStore128.right (SepStore128.right (SepStore128.left (SepStore128.spill13 hk1 ha1 rfl))))
    (SepStore128.right (SepStore128.right (SepStore128.left (SepStore128.spill13 hk2 ha2 hsp13))))
    hexec hnext

private theorem step_strQ_spill0 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp : BitVec 64} {pMsg pDot : Vec32} {sp13 sp13' : Spill13} {Rest : SepProp}
    {post : State → SepProp → Prop} {pc : BitVec 64}
    (hchk : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.strSimd .Q128 1#5 (.Offset .sp 0#64)))
    (hsp_eq : s.sp = sp) (hv1 : s.readVReg128 1#5 = 0#128) (hsp13 : sp13.set 0 0#128 = sp13')
    (hexec : s.setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m')
      (Poly32Mem (sp + 2416#64) pMsg ∗ Poly32Mem (sp + 2928#64) pDot ∗
        Spill13Mem sp sp13' ∗ Rest) post) :
    SepWP prog target_pc s
      (Poly32Mem (sp + 2416#64) pMsg ∗ Poly32Mem (sp + 2928#64) pDot ∗
        Spill13Mem sp sp13 ∗ Rest) post := by
  have ha : sp + BitVec.ofNat 64 (16 * 0) = s.sp + 0#64 := by rw [hsp_eq]
  have hsp_al : s.spAligned = true := spAligned_of_chk hsp_eq hchk
  exact step_strQ128 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hsp_al])
    (by simp [evalAddrMode]) hv1
    (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.spill13 (k := 0) (by decide) ha hsp13)))) hexec hnext

private theorem step_strQ_msg_fin {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {sp : BitVec 64} {pMsg pMsg' : Vec32} {Rest : SepProp}
    {post : State → SepProp → Prop}
    {pc : BitVec 64} {vt : BitVec 5} {imm : BitVec 64} {val : BitVec 128} (k : Nat)
    (hchk : (sp &&& 15#64 == 0#64) = true) (hk : k < 32 := by decide)
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.strSimd .Q128 vt (.Offset .sp imm)))
    (hsp_eq : s.sp = sp) (himm : 2416#64 + BitVec.ofNat 64 (16 * k) = imm := by decide)
    (hval : s.readVReg128 vt = val) (hp : pMsg.set k val = pMsg')
    (hexec : s.setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m')
      (Poly32Mem (sp + 2416#64) pMsg' ∗ Rest) post) :
    SepWP prog target_pc s (Poly32Mem (sp + 2416#64) pMsg ∗ Rest) post := by
  have ha : (sp + 2416#64) + BitVec.ofNat 64 (16 * k) = s.sp + imm := by
    rw [hsp_eq, ← himm]; bv_omega
  have hsp_al : s.spAligned = true := spAligned_of_chk hsp_eq hchk
  exact step_strQ128 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, hsp_al])
    (by simp [evalAddrMode]) hval (SepStore128.left (SepStore128.vec32 hk ha hp)) hexec hnext

local macro "step_dot_strQ " k:num : tactic => `(tactic| (
  refine step_strQ_dot $k (by assumption) (by decide) (by wp_norm_lhs) (by simp [*])
    (by wp_norm_lhs) (by simp [*]) (by decide) (by simp [*]) rfl (by wp_norm_lhs) ?_
  intro _))

local macro "step_dot_ldrQ " k:num : tactic => `(tactic|
  refine step_ldrQ_dot $k (by assumption) (by decide) (by wp_norm_lhs) (by simp [*])
    (by wp_norm_lhs) (by simp [*]) (by decide) rfl (by wp_norm_lhs) ?_)

local macro "step_spill_stpQ " k:num : tactic => `(tactic| (
  refine step_stpQ_spill $k (by assumption) (by decide) (by decide) (by wp_norm_lhs)
    (by simp [*]) (by wp_norm_lhs) (by simp [*]) (by decide)
    (by wp_norm_lhs) (by wp_norm_lhs) rfl (by wp_norm_lhs) ?_
  intro _))

local macro "step_spill0_strQ" : tactic => `(tactic| (
  refine step_strQ_spill0 (by assumption) (by wp_norm_lhs) (by simp [*]) (by wp_norm_lhs)
    (by simp [*]) (by simp [*]) rfl (by wp_norm_lhs) ?_
  intro _))

local macro "step_msg_fin_strQ " k:num hv:term:arg : tactic => `(tactic| (
  refine step_strQ_msg_fin $k (by assumption) (by decide) (by wp_norm_lhs) (by simp [*])
    (by wp_norm_lhs) (by simp [*]) (by decide) (by simp [$hv:term]; rfl) rfl (by wp_norm_lhs) ?_
  intro _))

private abbrev ro00Sym : String := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0"

private theorem seg2b2_part1 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl20 b)
    (s0 s : State) (sp ret : BitVec 64) (v28 v29 : BitVec 128)
    (pMsg d0 : Vec32) (sp0 : Spill13) (Rest : SepProp)
    (hpc : s.pc = b + 0x0ab8#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hchk : (sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = 0#64)
    (hx9 : s.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx10 : s.readReg64 .x10 = sp + 208#64)
    (hx11 : s.readReg64 .x11 = 62209#64) (hx12 : s.readReg64 .x12 = 3329#64)
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = sp + 3952#64)
    (hx21 : s.readReg64 .x21 = sp + 5488#64)
    (hv0 : s.readVReg128 0#5 = 0#128)
    (hv3 : s.readVReg128 3#5 = v29) (hv4 : s.readVReg128 4#5 = v28)
    (hus : UnspilledSaved20 s0 s) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x0b38#64) s
      (Poly32Mem (sp + 2416#64) pMsg ∗ Poly32Mem (sp + 2928#64) d0 ∗ Spill13Mem sp sp0 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.readReg64 .x8 = 0#64 ∧
        s'.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x10 = sp + 208#64 ∧
        s'.readReg64 .x11 = 62209#64 ∧ s'.readReg64 .x12 = 3329#64 ∧
        s'.readReg64 .x19 = ret ∧ s'.readReg64 .x20 = sp + 3952#64 ∧
        s'.readReg64 .x21 = sp + 5488#64 ∧
        s'.readVReg128 0#5 = 0#128 ∧ s'.readVReg128 1#5 = 0#128 ∧ s'.readVReg128 2#5 = 0#128 ∧
        s'.readVReg128 3#5 = v29 ∧ s'.readVReg128 4#5 = v28 ∧
        UnspilledSaved20 s0 s' ∧
        P' = (Poly32Mem (sp + 2416#64) pMsg ∗
          Poly32Mem (sp + 2928#64) (((((((((((((d0.set 1 0#128).set 0 0#128).set 3 0#128).set 2 0#128).set 5 0#128).set 4 0#128).set 7 0#128).set 6 0#128).set 9 0#128).set 8 0#128).set 11 0#128).set 10 0#128).set 12 0#128) ∗
          Spill13Mem sp ((((((((((((sp0.set 11 0#128).set 12 0#128).set 9 0#128).set 10 0#128).set 7 0#128).set 8 0#128).set 5 0#128).set 6 0#128).set 3 0#128).set 4 0#128).set 1 0#128).set 2 0#128) ∗ Rest)) := by
  step_dot_strQ 1; step_dot_strQ 0; step_dot_ldrQ 1; step_dot_ldrQ 0; step_dot_strQ 3
  step_dot_strQ 2; step_spill_stpQ 11; step_dot_ldrQ 2; step_dot_ldrQ 3; step_dot_strQ 5
  step_dot_strQ 4; step_spill_stpQ 9; step_dot_ldrQ 4; step_dot_ldrQ 5; step_dot_strQ 7
  step_dot_strQ 6; step_spill_stpQ 7; step_dot_ldrQ 6; step_dot_ldrQ 7; step_dot_strQ 9
  step_dot_strQ 8; step_spill_stpQ 5; step_dot_ldrQ 8; step_dot_ldrQ 9; step_dot_strQ 11
  step_dot_strQ 10; step_spill_stpQ 3; step_dot_ldrQ 10; step_dot_ldrQ 11; step_dot_strQ 12
  step_spill_stpQ 1; step_dot_ldrQ 12
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simp [hx8], by simp [hx9], by simp [hx10], by simp [hx11],
      by simp [hx12], by simp [hx19], by simp [hx20], by simp [hx21],
      by simp [hv0], by wp_norm_lhs, by wp_norm_lhs, by simp [hv3], by simp [hv4],
      ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2]⟩, rfl⟩

private theorem seg2b2_part2 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl20 b)
    (s0 s : State) (sp ret : BitVec 64) (v28 v29 : BitVec 128)
    (pMsg d1 : Vec32) (sp1 : Spill13) (Rest : SepProp)
    (hpc : s.pc = b + 0x0b38#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hchk : (sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = 0#64)
    (hx9 : s.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx10 : s.readReg64 .x10 = sp + 208#64)
    (hx11 : s.readReg64 .x11 = 62209#64) (hx12 : s.readReg64 .x12 = 3329#64)
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = sp + 3952#64)
    (hx21 : s.readReg64 .x21 = sp + 5488#64)
    (hv0 : s.readVReg128 0#5 = 0#128) (hv1 : s.readVReg128 1#5 = 0#128)
    (hv2 : s.readVReg128 2#5 = 0#128)
    (hv3 : s.readVReg128 3#5 = v29) (hv4 : s.readVReg128 4#5 = v28)
    (hus : UnspilledSaved20 s0 s) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x0bdc#64) s
      (Poly32Mem (sp + 2416#64) pMsg ∗ Poly32Mem (sp + 2928#64) d1 ∗ Spill13Mem sp sp1 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x8 = 0#64 ∧
        s'.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x10 = sp + 208#64 ∧
        s'.readReg64 .x11 = 62209#64 ∧ s'.readReg64 .x12 = 3329#64 ∧
        s'.readReg64 .x19 = ret ∧ s'.readReg64 .x20 = sp + 3952#64 ∧
        s'.readReg64 .x21 = sp + 5488#64 ∧
        s'.readVReg128 0#5 = 0#128 ∧ s'.readVReg128 1#5 = 0#128 ∧ s'.readVReg128 2#5 = 0#128 ∧
        s'.readVReg128 8#5 = 0#128 ∧ s'.readVReg128 9#5 = 0#128 ∧
        s'.readVReg128 10#5 = 0#128 ∧ s'.readVReg128 11#5 = 0#128 ∧
        s'.readVReg128 12#5 = 0#128 ∧ s'.readVReg128 13#5 = 0#128 ∧
        s'.readVReg128 14#5 = 0#128 ∧ s'.readVReg128 15#5 = 0#128 ∧
        s'.readVReg128 22#5 = 0#128 ∧ s'.readVReg128 23#5 = 0#128 ∧
        s'.readVReg128 24#5 = 0#128 ∧ s'.readVReg128 25#5 = 0#128 ∧
        s'.readVReg128 26#5 = 0#128 ∧ s'.readVReg128 27#5 = 0#128 ∧
        s'.readVReg128 28#5 = 0#128 ∧ s'.readVReg128 29#5 = 0#128 ∧
        s'.readVReg128 30#5 = 0#128 ∧ s'.readVReg128 31#5 = 0#128 ∧
        UnspilledSaved20 s0 s' ∧
        P' = (Poly32Mem (sp + 2416#64) ((pMsg.set 28 v28).set 29 v29) ∗
          Poly32Mem (sp + 2928#64) (((((((((((((((((((d1.set 31 0#128).set 30 0#128).set 29 0#128).set 28 0#128).set 27 0#128).set 26 0#128).set 25 0#128).set 24 0#128).set 23 0#128).set 22 0#128).set 21 0#128).set 20 0#128).set 19 0#128).set 18 0#128).set 17 0#128).set 16 0#128).set 15 0#128).set 14 0#128).set 13 0#128) ∗
          Spill13Mem sp (sp1.set 0 0#128) ∗ Rest)) := by
  step_dot_strQ 31; step_dot_strQ 30; step_dot_strQ 29; step_dot_ldrQ 30; step_dot_strQ 28
  step_dot_ldrQ 29; step_dot_strQ 27; step_dot_ldrQ 28; step_dot_strQ 26; step_dot_ldrQ 27
  step_dot_strQ 25; step_dot_ldrQ 26; step_dot_strQ 24; step_dot_ldrQ 25; step_dot_strQ 23
  step_dot_ldrQ 24; step_dot_strQ 22; step_dot_ldrQ 23; step_dot_strQ 21; step_dot_ldrQ 22
  step_dot_strQ 20; step_dot_ldrQ 21; step_dot_strQ 19; step_dot_ldrQ 20; step_dot_strQ 18
  step_dot_ldrQ 19; step_dot_strQ 17; step_dot_ldrQ 18; step_dot_strQ 16; step_dot_ldrQ 17
  step_dot_strQ 15; step_dot_ldrQ 16; step_dot_strQ 14; step_dot_ldrQ 15; step_dot_strQ 13
  step_dot_ldrQ 14; step_spill0_strQ; step_dot_ldrQ 13; step_dot_ldrQ 31
  step_msg_fin_strQ 28 hv4; step_msg_fin_strQ 29 hv3
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hchk,
      by simp [hx8], by simp [hx9], by simp [hx10], by simp [hx11], by simp [hx12],
      by simp [hx19], by simp [hx20], by simp [hx21],
      by simp [hv0], by wp_norm_lhs, by simp [hv2],
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs,
      ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2]⟩, rfl⟩

/-! ## Exported Segment 2 Contract (`+0x0710 → +0x0bdc`) -/

@[expose] def Seg2Post [MlKemPlacement] (s0 s2 : State) (ret : BitVec 64) : Prop :=
  let sp := s0.sp - 6128#64
  s2.sp = sp ∧ s2.spAligned = true ∧
  s2.readReg64 .x8 = 0#64 ∧
  s2.readReg64 .x9 =
    mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0" + 134#64 ∧
  s2.readReg64 .x10 = sp + 208#64 ∧
  s2.readReg64 .x11 = 62209#64 ∧ s2.readReg64 .x12 = 3329#64 ∧
  s2.readReg64 .x19 = ret ∧ s2.readReg64 .x20 = sp + 3952#64 ∧
  s2.readReg64 .x21 = sp + 5488#64 ∧
  s2.readVReg128 0#5 = 0#128 ∧ s2.readVReg128 1#5 = 0#128 ∧ s2.readVReg128 2#5 = 0#128 ∧
  s2.readVReg128 8#5 = 0#128 ∧ s2.readVReg128 9#5 = 0#128 ∧
  s2.readVReg128 10#5 = 0#128 ∧ s2.readVReg128 11#5 = 0#128 ∧
  s2.readVReg128 12#5 = 0#128 ∧ s2.readVReg128 13#5 = 0#128 ∧
  s2.readVReg128 14#5 = 0#128 ∧ s2.readVReg128 15#5 = 0#128 ∧
  s2.readVReg128 22#5 = 0#128 ∧ s2.readVReg128 23#5 = 0#128 ∧
  s2.readVReg128 24#5 = 0#128 ∧ s2.readVReg128 25#5 = 0#128 ∧
  s2.readVReg128 26#5 = 0#128 ∧ s2.readVReg128 27#5 = 0#128 ∧
  s2.readVReg128 28#5 = 0#128 ∧ s2.readVReg128 29#5 = 0#128 ∧
  s2.readVReg128 30#5 = 0#128 ∧ s2.readVReg128 31#5 = 0#128 ∧
  UnspilledSaved20 s0 s2

@[expose] def Seg2Spatial (s0 : State) (esA : BitVec 64) (es : List (BitVec 8))
    (ekA : BitVec 64) (ek : List (BitVec 8)) (F : SepProp) : SepProp :=
  let sp := s0.sp - 6128#64
  (esA ↦ₛ es) ∗ (ekA ↦ₛ ek) ∗ SavedFrame20 s0.sp s0 ∗ Spill13Mem sp Spill13.zero ∗
  PolyMem (sp + 208#64) (polyVecNat (bytesToPoly16 (es.take 512))) ∗
  PolyMem (sp + 720#64) (polyVecNat (bytesToPoly16 ((es.drop 512).take 512))) ∗
  PolyMem (sp + 1232#64) (polyVecNat (bytesToPoly16 ((es.drop 1024).take 512))) ∗
  PolyMem (sp + 1744#64) (polyVecNat (bytesToPoly16 ((es.drop 1536).take 512))) ∗
  ((sp + 2256#64) ↦ₛ ((es.drop 2048).take 32)) ∗ memRegion (sp + 2288#64) 128 ∗
  PolyMem (sp + 2416#64) (polyVecNat (msgPoly16 ((es.drop 2048).take 32))) ∗
  PolyMem (sp + 2928#64) (fun _ => 0#128) ∗ memRegion (sp + 3440#64) 512 ∗
  PolyMem (sp + 3952#64) (polyVecNat (tHatPoly16 (ek.take 384))) ∗
  PolyMem (sp + 4464#64) (polyVecNat (tHatPoly16 ((ek.drop 384).take 384))) ∗
  PolyMem (sp + 4976#64) (polyVecNat (tHatPoly16 ((ek.drop 768).take 384))) ∗
  Poly32Mem (sp + 5488#64) (Vec32.ofFn (polyVecNat (tHatPoly16 ((ek.drop 768).take 384)))) ∗ F

theorem seg2b_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl20 b)
    (s0 s2a : State) (ret esA ekA : BitVec 64) (es ek : List (BitVec 8)) (F : SepProp)
    (hpc : s2a.pc = b + 0x0710#64) (hrun : s2a.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s2a.mem) (hro : MlKemRoOk mlkemMpl s2a.mem)
    (hes : es.length = 2080) (hpost2a : Seg2aPost s0 s2a ret) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x0bdc#64) s2a
      (Seg2aSpatial s0 esA es ekA ek F)
      (fun s2 P2 => Seg2Post s0 s2 ret ∧ (P2 ⊢ Seg2Spatial s0 esA es ekA ek F)) := by
  dsimp only [Seg2aPost] at hpost2a
  dsimp only [Seg2aSpatial]
  set sp := s0.sp - 6128#64
  set msg := (es.drop 2048).take 32
  rcases hpost2a with ⟨hsp, hspA, hx19, hx20, hx21, hus⟩
  have hmsg : msg.length = 32 := by simp [msg, hes]
  have hchk : (sp &&& 15#64 == 0#64) = true := by rw [← hsp]; exact hspA
  rw [memRegion_1536_seg2b_split]
  refine VecMem.SepWP.of_memRegion_vecRangeMem 13 sp (by decide) (by sep_focus) fun fSp => ?_
  rw [show VecRangeMem 13 sp fSp = Spill13Mem sp (Spill13.ofFn fSp) from
    (spill13Mem_ofFn sp fSp).symm]
  refine VecMem.SepWP.of_memRegion_vecRangeMem 32 (sp + 2416#64) (by decide) (by sep_focus)
    fun fMsg => ?_
  rw [show VecRangeMem 32 (sp + 2416#64) fMsg = Poly32Mem (sp + 2416#64) (Vec32.ofFn fMsg) from
    (poly32Mem_ofFn _ _).symm]
  refine VecMem.SepWP.of_memRegion_vecRangeMem 32 (sp + 2928#64) (by decide) (by sep_focus)
    fun fDot => ?_
  rw [show VecRangeMem 32 (sp + 2928#64) fDot = Poly32Mem (sp + 2928#64) (Vec32.ofFn fDot) from
    (poly32Mem_ofFn _ _).symm]
  have stepf : ∀ {prog : Program} {pc1 pc2 : BitVec 64} {s : State} {P P1 : SepProp}
      {Q1 Q2 : State → SepProp → Prop},
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      SepWP prog pc1 s P1 Q1 → (P ⊢ P1) →
      (∀ s' P', s'.pc = pc1 → s'.status = .Running →
        mlkemMultiLib.CodeLoaded mlkemMpl s'.mem → MlKemRoOk mlkemMpl s'.mem →
        Q1 s' P' → SepWP prog pc2 s' P' Q2) →
      SepWP prog pc2 s P Q2 :=
    fun hcl' hro' h1 hP' h2 => SepWP.weaken_pre hP' (sepWP_seq_env hcl' hro' h1 h2)
  refine stepf hcl hro
    (seg2b1_ok hb s0 s2a ret hmsg (Vec32.ofFn fMsg) _
      hpc hrun hsp hspA hcl hro hx19 hx20 hx21 hus) (by sep_frame) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨⟨hsp1, _, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx19_1, hx20_1, hx21_1,
      hv0_1, hv3_1, hv4_1, hus1⟩, rfl⟩
  refine stepf hcl1 hro1
    (seg2b2_part1 hb s0 s1 sp ret (polyVecNat (msgPoly16 msg) 28) (polyVecNat (msgPoly16 msg) 29)
      (msgVec32Pre msg (Vec32.ofFn fMsg)) (Vec32.ofFn fDot) (Spill13.ofFn fSp) _
      hpc1 hrun1 hsp1 hchk hx8_1 hx9_1 hx10_1 hx11_1 hx12_1 hx19_1 hx20_1 hx21_1
      hv0_1 hv3_1 hv4_1 hus1) (by sep_frame) ?_
  rintro s2 P2 hpc2 hrun2 _ _
    ⟨hsp2, hx8_2, hx9_2, hx10_2, hx11_2, hx12_2, hx19_2, hx20_2, hx21_2,
     hv0_2, hv1_2, hv2_2, hv3_2, hv4_2, hus2, rfl⟩
  refine SepWP.mono
    (seg2b2_part2 hb s0 s2 sp ret (polyVecNat (msgPoly16 msg) 28) (polyVecNat (msgPoly16 msg) 29)
      (msgVec32Pre msg (Vec32.ofFn fMsg)) _ _ _
      hpc2 hrun2 hsp2 hchk hx8_2 hx9_2 hx10_2 hx11_2 hx12_2 hx19_2 hx20_2 hx21_2
      hv0_2 hv1_2 hv2_2 hv3_2 hv4_2 hus2) ?_
  rintro s3 P3 _ _ ⟨hsp3, hspA3, hx8_3, hx9_3, hx10_3, hx11_3, hx12_3, hx19_3, hx20_3, hx21_3,
    hv0_3, hv1_3, hv2_3, hv8_3, hv9_3, hv10_3, hv11_3, hv12_3, hv13_3, hv14_3, hv15_3,
    hv22_3, hv23_3, hv24_3, hv25_3, hv26_3, hv27_3, hv28_3, hv29_3, hv30_3, hv31_3, hus3, rfl⟩
  have hpMsg : ((msgVec32Pre msg (Vec32.ofFn fMsg)).set 28 (polyVecNat (msgPoly16 msg) 28)).set 29
      (polyVecNat (msgPoly16 msg) 29) = Vec32.ofFn (polyVecNat (msgPoly16 msg)) := rfl
  have hpDot : (((((((((((((((((((((((((((((((((Vec32.ofFn fDot).set 1 0#128).set 0 0#128).set 3 0#128).set 2 0#128).set 5 0#128).set 4 0#128).set 7 0#128).set 6 0#128).set 9 0#128).set 8 0#128).set 11 0#128).set 10 0#128).set 12 0#128).set 31 0#128).set 30 0#128).set 29 0#128).set 28 0#128).set 27 0#128).set 26 0#128).set 25 0#128).set 24 0#128).set 23 0#128).set 22 0#128).set 21 0#128).set 20 0#128).set 19 0#128).set 18 0#128).set 17 0#128).set 16 0#128).set 15 0#128).set 14 0#128).set 13 0#128) =
      Vec32.zero := rfl
  have hpSp : ((((((((((((((Spill13.ofFn fSp).set 11 0#128).set 12 0#128).set 9 0#128).set 10 0#128).set 7 0#128).set 8 0#128).set 5 0#128).set 6 0#128).set 3 0#128).set 4 0#128).set 1 0#128).set 2 0#128)).set 0 0#128 =
      Spill13.zero := rfl
  refine ⟨⟨hsp3, hspA3, hx8_3, hx9_3, hx10_3, hx11_3, hx12_3, hx19_3, hx20_3, hx21_3,
    hv0_3, hv1_3, hv2_3, hv8_3, hv9_3, hv10_3, hv11_3, hv12_3, hv13_3, hv14_3, hv15_3,
    hv22_3, hv23_3, hv24_3, hv25_3, hv26_3, hv27_3, hv28_3, hv29_3, hv30_3, hv31_3, hus3⟩, ?_⟩
  rw [hpMsg, poly32Mem_ofFn, hpDot,
      show Poly32Mem (sp + 2928#64) Vec32.zero = PolyMem (sp + 2928#64) (fun _ => 0#128) from
        poly32Mem_ofFn _ _,
      hpSp]
  dsimp only [Seg2Spatial]
  sep_frame

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2b
