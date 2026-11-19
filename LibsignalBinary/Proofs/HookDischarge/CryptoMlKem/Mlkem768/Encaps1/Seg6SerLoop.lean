/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.GenPlacedFetches
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg5 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg6Simd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg6Ser -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeHigh
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd

/-!
# `encapsulate1_serialized` (`B03`) — Segment 6a Outer/Inner Loop (`+0x6a78 .. +0x6cd8`)

Composes `Seg6Ser` (`seg6_setup`, `seg6_inner_simd`, `step_ser10_tail16`) across the 16-chunk inner
loop and 3-polynomial outer loop to serialize `ct1 = encaps1OutCt1 a.hdr64 a.rand` (`960` B) at
`sp + 11440#64`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg6SerLoop
open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (Poly16 sha3_512List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress (neonCompress8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeHigh (neonSerialize10Mix)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem VecRangeMem
  polyVecNat step_ldrQ128 step_strQ128 vecRangeBytes vecRangeBytes_length
  vecRangeMem_entails_memRegion vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub sepWP_elim_cell8 spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (
  blkPC03 blkPl03 encaps1OutCt1)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd (
  step_bCond_not_taken step_bCond_taken)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg5 (uVecPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg6Simd (
  encaps1OutCt1_eq exec_simdMovi_2d_0 neonCompressSerialize10Poly
  neonCompressSerialize10Poly_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg6Ser (
  Seg6ConstsMem Seg6OuterRegs blk28_memcpy_03 c10321340Vec c1664Vec c3329Vec c67107840Vec
  off6aec off6b38 off6ba4 off6ca0 off6ca4 offSeg6SerEnd offSeg6Start
  seg6_inner_simd seg6_setup ser10PolyPrefix ser10PolyPrefix_16 ser10PolyPrefix_zero
  step_ser10_tail16)

attribute [local irreducible] blkPC03
attribute [local wp_norm ↓ high] exec_simdMovi_2d_0

private def serConstFn : Nat → BitVec 128
  | 0 => c10321340Vec
  | 1 => c1664Vec
  | 2 => c67107840Vec
  | _ => c3329Vec

private theorem seg6ConstsMem_eq_vecRangeMem (sp : BitVec 64) :
    Seg6ConstsMem sp = VecRangeMem 4 (sp + 2128#64) serConstFn := by
  dsimp only [Seg6ConstsMem, VecRangeMem, serConstFn, c10321340Vec, c1664Vec, c67107840Vec, c3329Vec]
  simp only [show (sp + 2128#64) + 16#64 = sp + 2144#64 by bv_omega,
    show (sp + 2144#64) + 16#64 = sp + 2160#64 by bv_omega,
    show (sp + 2160#64) + 16#64 = sp + 2176#64 by bv_omega, sepConj_emp]


theorem step_strQ128_sp_vecRange {prog : Program} {target_pc : BitVec 64}
    {s : State} {Rest : SepProp} {post : State → SepProp → Prop}
    (b sp base : BitVec 64) (pcOff nextOff off n k : Nat) (vt : BitVec 5) (val : BitVec 128)
    (f : Nat → BitVec 128)
    (hk : k < n) (hpc : s.pc = b + BitVec.ofNat 64 pcOff) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) =
      some (.strSimd .Q128 vt (.Offset .sp (BitVec.ofNat 64 off))))
    (hea : base + BitVec.ofNat 64 (16 * k) = sp + BitVec.ofNat 64 off)
    (hval : s.readVReg128 vt = val) (hnextOff : pcOff + 4 = nextOff)
    (hnext : ∀ m' : Memory, SepWP prog target_pc
      ((s.setPC (b + BitVec.ofNat 64 nextOff)).setMem m')
      (VecRangeMem n base (Function.update f k val) ∗ Rest) post) :
    SepWP prog target_pc s (VecRangeMem n base f ∗ Rest) post := by
  have hpc' : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  exact step_strQ128 (s' := s.setPC (b + BitVec.ofNat 64 nextOff)) (vt := vt) (wb := none)
    hpc hrun hfetch
    (by simpa [checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned] using hspA)
    (by simp [evalAddrMode, hsp]) hval
    (SepStore128.left (SepStore128.vecRange hk hea))
    (by simp [applyWriteback, hpc']) hnext

theorem step_ldrQ128_sp_vecRange {prog : Program} {target_pc : BitVec 64}
    {s : State} {Rest : SepProp} {post : State → SepProp → Prop}
    (b sp base : BitVec 64) (pcOff nextOff off n k : Nat) (vt : BitVec 5)
    (f : Nat → BitVec 128)
    (hk : k < n) (hpc : s.pc = b + BitVec.ofNat 64 pcOff) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) =
      some (.ldrSimd .Q128 vt (.Offset .sp (BitVec.ofNat 64 off))))
    (hea : base + BitVec.ofNat 64 (16 * k) = sp + BitVec.ofNat 64 off) (hnextOff : pcOff + 4 = nextOff)
    (hnext : SepWP prog target_pc
      ((s.writeVReg128 vt (f k)).setPC (b + BitVec.ofNat 64 nextOff))
      (VecRangeMem n base f ∗ Rest) post) :
    SepWP prog target_pc s (VecRangeMem n base f ∗ Rest) post := by
  have hpc' : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  exact step_ldrQ128
    (s' := (s.writeVReg128 vt (f k)).setPC (b + BitVec.ofNat 64 nextOff)) (vt := vt) (wb := none)
    hpc hrun hfetch
    (by simpa [checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned] using hspA)
    (by simp [evalAddrMode, hsp])
    (SepLoad128.left (SepLoad128.vecRange hk hea))
    (by simp [applyWriteback, hpc']) hnext

private theorem seg6_prep_poly [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) {idx : Nat} (hidx : idx < 3) (u : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + off6aec) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hregs : Seg6OuterRegs sp idx s)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    let uPtr := sp + BitVec.ofNat 64 (4288 + 512 * idx)
    SepWP (blkPC03.rebase b (fun _ => none)) (b + off6b38) s
      (PolyMem uPtr (polyVecNat u) ∗
        memRegion (sp + 2192#64) 520 ∗ memRegion (sp + 15680#64) 520 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        Seg6OuterRegs sp (idx + 1) sf ∧
        sf.readReg64 .x24 = BitVec.ofNat 64 (320 * idx) ∧
        (Pf ⊢ PolyMem uPtr (polyVecNat u) ∗
          PolyMem (sp + 2192#64) (polyVecNat u) ∗
          memRegion (sp + 2704#64) 8 ∗ memRegion (sp + 15680#64) 520 ∗ Rest)) := by
  subst hbase
  rcases hregs with ⟨hx19, hx20, hx21, hx22, hx23, hx25⟩
  intro uPtr
  set bsU := vecRangeBytes 32 (polyVecNat u)
  have hbsU : bsU.length = 512 := vecRangeBytes_length 32 (polyVecNat u)
  have hm520a : memRegion (sp + 2192#64) 520 = memRegion (sp + 2192#64) 8 ∗ memRegion (sp + 2200#64) 512 :=
    memRegion_split' (b := sp + 2192#64) (b' := sp + 2200#64) (n := 8) (k := (512 : Nat))
      rfl (by clear * -; bv_omega) (by decide)
  have hm520b : memRegion (sp + 2192#64) 520 = memRegion (sp + 2192#64) 512 ∗ memRegion (sp + 2704#64) 8 :=
    memRegion_split' (b := sp + 2192#64) (b' := sp + 2704#64) (n := 512) (k := (8 : Nat))
      rfl (by clear * -; bv_omega) (by decide)
  rw [hm520a]
  refine SepWP.weaken_pre (show PolyMem uPtr (polyVecNat u) ∗
        ((memRegion (sp + 2192#64) 8 ∗ memRegion (sp + 2200#64) 512) ∗
          memRegion (sp + 15680#64) 520 ∗ Rest) ⊢
      memRegion (sp + 2192#64) 8 ∗
        ((uPtr ↦ₛ bsU) ∗ memRegion (sp + 2200#64) 512 ∗ memRegion (sp + 15680#64) 520 ∗ Rest) by
      dsimp only [PolyMem]; rw [← vecRangeMem_eq_pointsToBytes 32 uPtr (polyVecNat u)]; sep_frame) ?_
  apply sepWP_elim_cell8; intro w0
  have huPtr : (sp + 4288#64) + (BitVec.ofNat 64 idx <<< 9) = uPtr := by
    dsimp only [uPtr]; rcases idx with _ | _ | _ | n <;> try omega
    all_goals (clear * -; bv_omega)
  wp_steps 5; wp_step
  apply seq_codeLoaded_lr ‹_›
  wp_call (blk28_memcpy_03 blkPl03.base) (sp + 2200#64, uPtr, bsU)
  apply SepWP.done (by assumption) (by assumption); intro hcl1
  have hjoin1 : ((sp + 2192#64) ↦₆₄ w0) ∗ ((sp + 2200#64) ↦ₛ bsU) =
      ((sp + 2192#64) ↦ₛ (unpack64 w0 ++ bsU)) := by
    rw [pointsTo64_eq_pointsToBytes, pointsToBytes_append, unpack64_length,
      show (sp + 2192#64) + 8#64 = sp + 2200#64 by clear * -; bv_omega]
  have h520len : (unpack64 w0 ++ bsU).length = 520 := by
    simp [List.length_append, unpack64_length, hbsU]
  refine SepWP.weaken_pre
    (P' := ((sp + 2192#64) ↦ₛ (unpack64 w0 ++ bsU)) ∗ memRegion (sp + 15680#64) 520 ∗
      ((uPtr ↦ₛ bsU) ∗ Rest))
    (entails_sub (show ((sp + 2192#64) ↦₆₄ w0) ∗ ((sp + 2200#64) ↦ₛ bsU) ⊢
      ((sp + 2192#64) ↦ₛ (unpack64 w0 ++ bsU)) by rw [hjoin1]; exact Entails.refl _)
      (by sep_frame) (by sep_frame)) ?_
  have hsp1 : sf.sp = sp := hsp_sf.trans hsp
  have hspA1 : sf.spAligned = true := spAligned_of_sp_eq hspA hsp hsp1
  wp_steps 4; wp_step
  apply seq_codeLoaded_lr; · exact hcl1
  wp_call (blk28_memcpy_03 blkPl03.base) (sp + 15680#64, sp + 2192#64, unpack64 w0 ++ bsU)
  apply SepWP.done (by assumption) (by assumption); intro hcl2
  have hsp2 : sf_1.sp = sp := hsp_sf_1.trans hsp1
  have hspA2 : sf_1.spAligned = true := spAligned_of_sp_eq hspA1 hsp1 hsp2
  have hsplit15680 : ((sp + 15680#64) ↦ₛ (unpack64 w0 ++ bsU)) =
      ((sp + 15680#64) ↦ₛ unpack64 w0) ∗ ((sp + 15688#64) ↦ₛ bsU) := by
    rw [pointsToBytes_append, unpack64_length, show (sp + 15680#64) + 8#64 = sp + 15688#64 by clear * -; bv_omega]
  have hm2192 : ((sp + 2192#64) ↦ₛ (unpack64 w0 ++ bsU)) ⊢
      memRegion (sp + 2192#64) 512 ∗ memRegion (sp + 2704#64) 8 := by
    rw [← hm520b, ← h520len]; exact pointsToBytes_entails_memRegion (sp + 2192#64) (unpack64 w0 ++ bsU)
  refine SepWP.weaken_pre
    (P' := ((sp + 15688#64) ↦ₛ bsU) ∗ memRegion (sp + 2192#64) 512 ∗
      (((sp + 15680#64) ↦ₛ unpack64 w0) ∗ memRegion (sp + 2704#64) 8 ∗ (uPtr ↦ₛ bsU) ∗ Rest))
    (by rw [hsplit15680]; exact entails_sub hm2192 (by sep_frame) (by sep_frame)) ?_
  wp_steps 3; wp_step
  apply seq_codeLoaded_lr; · exact hcl2
  wp_call (blk28_memcpy_03 blkPl03.base) (sp + 2192#64, sp + 15688#64, bsU)
  apply SepWP.done (by assumption) (by assumption); intro _
  have hsp3 : sf_2.sp = sp := hsp_sf_2.trans hsp2
  have hspA3 : sf_2.spAligned = true := spAligned_of_sp_eq hspA2 hsp2 hsp3
  have hx19_3 : sf_2.readReg64 .x19 = sp + 2192#64 := (h_22.trans (h_11.trans h)).trans (by simp [hx19])
  have hx20_3 : sf_2.readReg64 .x20 = BitVec.ofNat 64 (idx + 1) := by
    rw [h_23, h_12, h_1]; rcases idx with _ | _ | _ | n <;> try omega
    all_goals rfl
  have hx21_3 : sf_2.readReg64 .x21 = sp + 15680#64 := (h_24.trans (h_13.trans h_2)).trans (by simp [hx21])
  have hx22_3 : sf_2.readReg64 .x22 = sp + 16528#64 := (h_25.trans (h_14.trans h_3)).trans hx22
  have hx23_3 : sf_2.readReg64 .x23 = sp + 4288#64 := (h_26.trans (h_15.trans h_4)).trans hx23
  have hx25_3 : sf_2.readReg64 (.gpr 25#5) = sp + 11440#64 := (h_28.trans (h_17.trans h_6)).trans hx25
  have hx26_3 : sf_2.readReg64 (.gpr 26#5) = BitVec.ofNat 64 idx := (h_29.trans h_18).trans h_7
  have hcond : ConditionHolds .EQ (subsPState64 (BitVec.ofNat 64 idx) 3#64) = false := by
    rcases idx with _ | _ | _ | n <;> try omega
    all_goals simp only [wp_norm, arm64_norm]
  wp_steps 3
  refine step_bCond_not_taken (pc := blkPl03.base + BitVec.ofNat 64 27444)
    (off := 984#64) (dst := blkPl03.base + off6b38) (c := .EQ)
    (by wp_norm_lhs) (by simp [hrun_sf_2]) (by simp only [arm64_norm])
    (by simpa [hx26_3] using hcond)
    (by dsimp only [off6b38]; clear * -; bv_omega) ?_
  refine SepWP.done rfl (by simp [hrun_sf_2])
    ⟨by simp [hsp3], spAligned_of_sp_eq hspA3 hsp3 (by simp [hsp3]),
      ⟨by simp [hx19_3], by simp [hx20_3], by simp [hx21_3],
       by simp [hx22_3], by simp [hx23_3], by simp [hx25_3]⟩,
      by rcases idx with _ | _ | _ | n <;> try omega
         all_goals simp, ?_⟩
  have hm15680 : ((sp + 15680#64) ↦ₛ unpack64 w0) ∗ ((sp + 15688#64) ↦ₛ bsU) ⊢
      memRegion (sp + 15680#64) 520 := by
    rw [← hsplit15680, ← h520len]; exact pointsToBytes_entails_memRegion (sp + 15680#64) (unpack64 w0 ++ bsU)
  dsimp only [PolyMem]
  rw [← vecRangeMem_eq_pointsToBytes 32 uPtr (polyVecNat u),
      ← vecRangeMem_eq_pointsToBytes 32 (sp + 2192#64) (polyVecNat u)]
  exact entails_sub hm15680 (by sep_frame) (by sep_frame)

local macro "step_zero_q " sp:term:arg hrun:term:arg hsp:term:arg hspA:term:arg
    pcOff:num nextOff:num spOff:num k:num : tactic => `(tactic|
  (refine step_strQ128_sp_vecRange blkPl03.base $sp ($sp + 16528#64) $pcOff $nextOff $spOff 20 $k 0#5 0#128 _
      (by decide) (by wp_norm_lhs) (by simp [$hrun:term]) (by simp [$hsp:term])
      (spAligned_of_sp_eq $hspA $hsp (by simp [$hsp:term]))
      (by simp only [arm64_norm]) (by clear * -; bv_omega) (by simp) rfl ?_;
   intro _))

private theorem seg6_zero_load [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) {row : Nat} (Rest : SepProp)
    (hpc : s.pc = b + off6b38) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hregs : Seg6OuterRegs sp row s) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + off6ba4) s
      (VecRangeMem 4 (sp + 2128#64) serConstFn ∗ memRegion (sp + 16528#64) 320 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        Seg6OuterRegs sp row sf ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x8 = 0xfffffffffffffec0#64 ∧
        sf.readReg64 .x9 = sp + 2208#64 ∧
        sf.readVReg128 5#5 = c3329Vec ∧ sf.readVReg128 6#5 = c67107840Vec ∧
        sf.readVReg128 7#5 = c1664Vec ∧ sf.readVReg128 16#5 = c10321340Vec ∧
        (Pf ⊢ VecRangeMem 4 (sp + 2128#64) serConstFn ∗ memRegion (sp + 16528#64) 320 ∗ Rest)) := by
  subst hbase
  rcases hregs with ⟨hx19, hx20, hx21, hx22, hx23, hx25⟩
  refine SepWP.weaken_pre (show VecRangeMem 4 (sp + 2128#64) serConstFn ∗ (memRegion (sp + 16528#64) 320 ∗ Rest) ⊢
      memRegion (sp + 16528#64) 320 ∗ (VecRangeMem 4 (sp + 2128#64) serConstFn ∗ Rest) by sep_frame) ?_
  apply SepWP.of_memRegion_vecRangeMem 20 (sp + 16528#64) (by decide) (by sep_focus); intro fz
  refine SepWP.weaken_pre (show VecRangeMem 20 (sp + 16528#64) fz ∗ (VecRangeMem 4 (sp + 2128#64) serConstFn ∗ Rest) ⊢
      VecRangeMem 4 (sp + 2128#64) serConstFn ∗ (VecRangeMem 20 (sp + 16528#64) fz ∗ Rest) by sep_frame) ?_
  wp_steps 1
  refine step_ldrQ128_sp_vecRange blkPl03.base sp (sp + 2128#64) 27452 27456 2176 4 3 5#5 serConstFn
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_sp_eq hspA hsp (by simp [hsp]))
    (by simp only [arm64_norm]) (by clear * -; bv_omega) rfl ?_
  refine step_ldrQ128_sp_vecRange blkPl03.base sp (sp + 2128#64) 27456 27460 2160 4 2 6#5 serConstFn
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_sp_eq hspA hsp (by simp [hsp]))
    (by simp only [arm64_norm]) (by clear * -; bv_omega) rfl ?_
  refine step_ldrQ128_sp_vecRange blkPl03.base sp (sp + 2128#64) 27460 27464 2144 4 1 7#5 serConstFn
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_sp_eq hspA hsp (by simp [hsp]))
    (by simp only [arm64_norm]) (by clear * -; bv_omega) rfl ?_
  refine step_ldrQ128_sp_vecRange blkPl03.base sp (sp + 2128#64) 27464 27468 2128 4 0 16#5 serConstFn
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_sp_eq hspA hsp (by simp [hsp]))
    (by simp only [arm64_norm]) (by clear * -; bv_omega) rfl ?_
  wp_steps 2
  refine SepWP.weaken_pre (P' := VecRangeMem 20 (sp + 16528#64) fz ∗ (VecRangeMem 4 (sp + 2128#64) serConstFn ∗ Rest))
    (by sep_frame) ?_
  step_zero_q sp hrun hsp hspA 27476 27480 16832 19; step_zero_q sp hrun hsp hspA 27480 27484 16816 18
  step_zero_q sp hrun hsp hspA 27484 27488 16800 17; step_zero_q sp hrun hsp hspA 27488 27492 16784 16
  step_zero_q sp hrun hsp hspA 27492 27496 16768 15; step_zero_q sp hrun hsp hspA 27496 27500 16752 14
  step_zero_q sp hrun hsp hspA 27500 27504 16736 13; step_zero_q sp hrun hsp hspA 27504 27508 16720 12
  step_zero_q sp hrun hsp hspA 27508 27512 16704 11; step_zero_q sp hrun hsp hspA 27512 27516 16688 10
  step_zero_q sp hrun hsp hspA 27516 27520 16672 9;  step_zero_q sp hrun hsp hspA 27520 27524 16656 8
  step_zero_q sp hrun hsp hspA 27524 27528 16640 7;  step_zero_q sp hrun hsp hspA 27528 27532 16624 6
  step_zero_q sp hrun hsp hspA 27532 27536 16608 5;  step_zero_q sp hrun hsp hspA 27536 27540 16592 4
  step_zero_q sp hrun hsp hspA 27540 27544 16576 3;  step_zero_q sp hrun hsp hspA 27544 27548 16560 2
  step_zero_q sp hrun hsp hspA 27548 27552 16544 1;  step_zero_q sp hrun hsp hspA 27552 27556 16528 0
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_sp_eq hspA hsp (by simp [hsp]),
      ⟨by simp [hx19], by simp [hx20], by simp [hx21], by simp [hx22], by simp [hx23], by simp [hx25]⟩,
      by simp, by simp, by simp,
      by simp [serConstFn], by simp [serConstFn], by simp [serConstFn], by simp [serConstFn], ?_⟩
  exact entails_sub (vecRangeMem_entails_memRegion 20 (sp + 16528#64) _) (by sep_frame) (by sep_frame)

attribute [local irreducible]
  c10321340Vec c1664Vec c67107840Vec c3329Vec
  neonCompress8h neonSerialize10Mix neonCompressSerialize10Poly ser10PolyPrefix
  polyVecNat

private theorem seg6_inner_from [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (c : Nat) (hc : c ≤ 16) (s : State) (sp : BitVec 64) (u : Poly16) (Rest : SepProp)
    (hpc : s.pc = if c < 16 then b + off6ba4 else b + off6ca4)
    (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx8 : s.readReg64 .x8 = 0xfffffffffffffec0#64 + BitVec.ofNat 64 (20 * c))
    (hx9 : s.readReg64 .x9 = sp + BitVec.ofNat 64 (2208 + 32 * c))
    (hx22 : s.readReg64 .x22 = sp + 16528#64)
    (hv5 : s.readVReg128 5#5 = c3329Vec) (hv6 : s.readVReg128 6#5 = c67107840Vec)
    (hv7 : s.readVReg128 7#5 = c1664Vec) (hv16 : s.readVReg128 16#5 = c10321340Vec) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + off6ca4) s
      (PolyMem (sp + 2192#64) (polyVecNat u) ∗
        ((sp + 16528#64) ↦ₛ ser10PolyPrefix u c) ∗
        memRegion ((sp + 16528#64) + BitVec.ofNat 64 (20 * c)) (320 - 20 * c) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = s.spAligned ∧
        (∀ r : Reg, r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → sf.readReg64 r = s.readReg64 r) ∧
        (Pf ⊢ PolyMem (sp + 2192#64) (polyVecNat u) ∗
          ((sp + 16528#64) ↦ₛ neonCompressSerialize10Poly u) ∗ Rest)) := by
  by_cases hc16 : c < 16
  · have hpc' : s.pc = b + off6ba4 := by simpa [hc16] using hpc
    refine SepWP.seq (seg6_inner_simd hb hbase s sp hc16 u _ hpc' hrun hsp hx8 hx9 hx22 hv5 hv6 hv7 hv16) ?_
    rintro s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, hpst1, hx8_1, hx9_1, hx10_1, hx11_1, hregs1, hv0_1, hv2_1,
      hv5_1, hv6_1, hv7_1, hv16_1, rfl⟩
    refine SepWP.weaken_pre (show PolyMem (sp + 2192#64) (polyVecNat u) ∗
          (((sp + 16528#64) ↦ₛ ser10PolyPrefix u c) ∗
            memRegion ((sp + 16528#64) + BitVec.ofNat 64 (20 * c)) (320 - 20 * c) ∗ Rest) ⊢
        ((sp + 16528#64) ↦ₛ ser10PolyPrefix u c) ∗
          memRegion ((sp + 16528#64) + BitVec.ofNat 64 (20 * c)) (320 - 20 * c) ∗
          (PolyMem (sp + 2192#64) (polyVecNat u) ∗ Rest) by sep_frame) ?_
    refine step_ser10_tail16 (dst := sp + 16528#64) (F := PolyMem (sp + 2192#64) (polyVecNat u) ∗ Rest)
      c hc16 hpc1 hrun1 hx10_1 hx11_1 hv0_1 hv2_1 ?_
    intro s2 hpc2 hrun2 ⟨hsp2, hspA2, hpst2⟩ hregs2 ⟨hv5_2, hv6_2, hv7_2, hv16_2⟩
    have hx8_2 : s2.readReg64 .x8 = 0xfffffffffffffec0#64 + BitVec.ofNat 64 (20 * (c + 1)) :=
      (hregs2 .x8 (by decide)).trans hx8_1
    have hx9_2 : s2.readReg64 .x9 = sp + BitVec.ofNat 64 (2208 + 32 * (c + 1)) :=
      (hregs2 .x9 (by decide)).trans hx9_1
    have hx22_2 : s2.readReg64 .x22 = sp + 16528#64 :=
      ((hregs2 .x22 (by decide)).trans (hregs1 .x22 (by decide) (by decide) (by decide) (by decide))).trans hx22
    refine SepWP.weaken_pre (show ((sp + 16528#64) ↦ₛ ser10PolyPrefix u (c + 1)) ∗
          memRegion ((sp + 16528#64) + BitVec.ofNat 64 (20 * (c + 1))) (320 - 20 * (c + 1)) ∗
          (PolyMem (sp + 2192#64) (polyVecNat u) ∗ Rest) ⊢
        PolyMem (sp + 2192#64) (polyVecNat u) ∗
          ((sp + 16528#64) ↦ₛ ser10PolyPrefix u (c + 1)) ∗
          memRegion ((sp + 16528#64) + BitVec.ofNat 64 (20 * (c + 1))) (320 - 20 * (c + 1)) ∗ Rest by sep_frame) ?_
    by_cases hc15 : c < 15
    · refine step_bCond_taken (pc := b + off6ca0)
        (off := -252#64) (dst := b + off6ba4) (c := .NE)
        hpc2 hrun2 (by subst hbase; simp only [off6ca0, arm64_norm])
        (by rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> try omega
            all_goals simp [hpst2, hpst1])
        (by dsimp only [off6ca0, off6ba4]; clear * -; bv_omega) ?_
      refine SepWP.mono (seg6_inner_from hb hbase (c + 1) (by omega) (s2.setPC (b + off6ba4)) sp u Rest
        (by simp [show c + 1 < 16 by omega]) (by simp [hrun2]) (by simp [hsp2, hsp1])
        (by simp [hx8_2]) (by simp [hx9_2]) (by simp [hx22_2])
        (by simp [hv5_2, hv5_1]) (by simp [hv6_2, hv6_1])
        (by simp [hv7_2, hv7_1]) (by simp [hv16_2, hv16_1])) ?_
      intro sf Pf _ _ ⟨hsp_f, hspA_f, hregs_f, hPf⟩
      have hspA_f' : sf.spAligned = s2.spAligned := by simpa [State.spAligned] using hspA_f
      refine ⟨hsp_f, hspA_f'.trans (hspA2.trans hspA1),
        fun r h8 h9 h10 h11 => ?_, hPf⟩
      have hrf : sf.readReg64 r = s2.readReg64 r := by
        simpa using hregs_f r h8 h9 h10 h11
      exact hrf.trans ((hregs2 r h11).trans (hregs1 r h8 h9 h10 h11))
    · have hce : c = 15 := by omega
      subst hce
      refine step_bCond_not_taken (pc := b + off6ca0)
        (off := -252#64) (dst := b + off6ca4) (c := .NE)
        hpc2 hrun2 (by subst hbase; simp only [off6ca0, arm64_norm])
        (by simp [hpst2, hpst1])
        (by dsimp only [off6ca0, off6ca4]; clear * -; bv_omega) ?_
      refine SepWP.done rfl (by simp [hrun2])
        ⟨by simp [hsp2, hsp1],
         (show (s2.setPC (b + off6ca4)).spAligned = s2.spAligned by simp [State.spAligned]).trans (hspA2.trans hspA1),
         fun r h8 h9 h10 h11 => by
           simp only [State.readReg64_setPC]
           exact (hregs2 r h11).trans (hregs1 r h8 h9 h10 h11), ?_⟩
      rw [show (15 : Nat) + 1 = 16 from rfl, ser10PolyPrefix_16]
      simp only [show 320 - 20 * 16 = 0 from rfl, memRegion_zero]
      sep_frame
  · have hce : c = 16 := by omega
    subst hce
    refine SepWP.done (by simpa using hpc) hrun ⟨hsp, rfl, fun _ _ _ _ _ => rfl, ?_⟩
    rw [ser10PolyPrefix_16]
    simp only [show 320 - 20 * 16 = 0 from rfl, memRegion_zero]
    sep_frame
termination_by 16 - c

private theorem seg6_bounce [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) {idx : Nat} (hidx : idx < 3) (u : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + off6ca4) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hregs : Seg6OuterRegs sp (idx + 1) s)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (320 * idx))
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    let outPtr := sp + BitVec.ofNat 64 (11440 + 320 * idx)
    let nextPc := if idx < 2 then b + off6aec else b + offSeg6SerEnd
    SepWP (blkPC03.rebase b (fun _ => none)) nextPc s
      (((sp + 16528#64) ↦ₛ neonCompressSerialize10Poly u) ∗
        memRegion (sp + 16208#64) 320 ∗ memRegion outPtr 320 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        Seg6OuterRegs sp (idx + 1) sf ∧
        (Pf ⊢ (outPtr ↦ₛ neonCompressSerialize10Poly u) ∗
          memRegion (sp + 16208#64) 320 ∗ memRegion (sp + 16528#64) 320 ∗ Rest)) := by
  subst hbase
  rcases hregs with ⟨hx19, hx20, hx21, hx22, hx23, hx25⟩
  intro outPtr nextPc
  set bsC := neonCompressSerialize10Poly u
  have hbsC : bsC.length = 320 := neonCompressSerialize10Poly_length u
  wp_steps 5; wp_step
  apply seq_codeLoaded_lr ‹_›
  wp_call (blk28_memcpy_03 blkPl03.base) (sp + 16208#64, sp + 16528#64, bsC)
  apply SepWP.done (by assumption) (by assumption); intro hcl1
  have hsp1' : sf.sp = sp := hsp_sf.trans hsp
  have hspA1 : sf.spAligned = true := spAligned_of_sp_eq hspA hsp hsp1'
  have h19_1 : sf.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) := ‹_›
  have h20_1 : sf.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) := ‹_›
  have h21_1 : sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) := ‹_›
  have h22_1 : sf.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) := ‹_›
  have h23_1 : sf.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) := ‹_›
  have h24_1 : sf.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) := ‹_›
  have h25_1 : sf.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) := ‹_›
  have houtPtr : (sp + 11440#64) + BitVec.ofNat 64 (320 * idx) = outPtr := by
    dsimp only [outPtr]; clear * - hidx; bv_omega
  have hx0_eq : sf.readReg64 (.gpr 25#5) + sf.readReg64 .x24 = outPtr := by
    change sf.readReg64 (.gpr 25#5) + sf.readReg64 (.gpr 24#5) = outPtr
    rw [h25_1, h24_1]; simpa [Reg.x24, hx25, hx24] using houtPtr
  refine SepWP.weaken_pre (P' := ((sp + 16208#64) ↦ₛ bsC) ∗ memRegion outPtr 320 ∗
      (((sp + 16528#64) ↦ₛ bsC) ∗ Rest)) (by sep_frame) ?_
  wp_steps 4; wp_step
  apply seq_codeLoaded_lr (by simpa using hcl1)
  wp_call (blk28_memcpy_03 blkPl03.base) (outPtr, sp + 16208#64, bsC)
  apply SepWP.done (by assumption) (by assumption); intro _
  have hsp2' : sf_1.sp = sp := hsp_sf_1.trans hsp1'
  have hspA2 : sf_1.spAligned = true := spAligned_of_sp_eq hspA1 hsp1' hsp2'
  have h19_2 : sf_1.readReg64 (.gpr 19#5) = sf.readReg64 (.gpr 19#5) := ‹_›
  have h20_2 : sf_1.readReg64 (.gpr 20#5) = sf.readReg64 (.gpr 20#5) := ‹_›
  have h21_2 : sf_1.readReg64 (.gpr 21#5) = sf.readReg64 (.gpr 21#5) := ‹_›
  have h22_2 : sf_1.readReg64 (.gpr 22#5) = sf.readReg64 (.gpr 22#5) := ‹_›
  have h23_2 : sf_1.readReg64 (.gpr 23#5) = sf.readReg64 (.gpr 23#5) := ‹_›
  have h25_2 : sf_1.readReg64 (.gpr 25#5) = sf.readReg64 (.gpr 25#5) := ‹_›
  have hx20_f : sf_1.readReg64 .x20 = BitVec.ofNat 64 (idx + 1) := by
    simp [Reg.x20] at hx20 ⊢; rw [h20_2, h20_1, hx20]
  have hm16208 : ((sp + 16208#64) ↦ₛ bsC) ⊢ memRegion (sp + 16208#64) 320 := by
    simpa [hbsC] using pointsToBytes_entails_memRegion (sp + 16208#64) bsC
  have hm16528 : ((sp + 16528#64) ↦ₛ bsC) ⊢ memRegion (sp + 16528#64) 320 := by
    simpa [hbsC] using pointsToBytes_entails_memRegion (sp + 16528#64) bsC
  have hpostP : (outPtr ↦ₛ bsC) ∗ ((sp + 16208#64) ↦ₛ bsC) ∗ (((sp + 16528#64) ↦ₛ bsC) ∗ Rest) ⊢
      (outPtr ↦ₛ bsC) ∗ memRegion (sp + 16208#64) 320 ∗ memRegion (sp + 16528#64) 320 ∗ Rest :=
    entails_sub hm16208 (by sep_frame) (entails_sub hm16528 (by sep_frame) (by sep_frame))
  wp_steps 1
  by_cases hidx2 : idx < 2
  · refine step_bCond_taken (pc := blkPl03.base + BitVec.ofNat 64 27860)
      (off := -488#64) (dst := blkPl03.base + off6aec) (c := .NE)
      (by wp_norm_lhs) (by simp [hrun_sf_1]) (by simp only [arm64_norm])
      (by rcases idx with _ | _ | n <;> try omega
          all_goals simp only [wp_norm, arm64_norm])
      (by dsimp only [off6aec]; clear * -; bv_omega) ?_
    refine SepWP.done (by dsimp [nextPc]; simp [hidx2]) (by simp [hrun_sf_1])
      ⟨by simp [hsp2'], spAligned_of_sp_eq hspA2 hsp2' (by simp [hsp2']),
        ⟨by simp [Reg.x19] at hx19 ⊢; rw [h19_2, h19_1, hx19],
         by simp [hx20_f],
         by simp [Reg.x21] at hx21 ⊢; rw [h21_2, h21_1, hx21],
         by simp [Reg.x22] at hx22 ⊢; rw [h22_2, h22_1, hx22],
         by simp [Reg.x23] at hx23 ⊢; rw [h23_2, h23_1, hx23],
         by simp; rw [h25_2, h25_1, hx25]⟩, hpostP⟩
  · have hidxe : idx = 2 := by omega
    subst hidxe
    refine step_bCond_not_taken (pc := blkPl03.base + BitVec.ofNat 64 27860)
      (off := -488#64) (dst := blkPl03.base + offSeg6SerEnd) (c := .NE)
      (by wp_norm_lhs) (by simp [hrun_sf_1]) (by simp only [arm64_norm])
      (by simp only [wp_norm, arm64_norm])
      (by dsimp only [offSeg6SerEnd]; clear * -; bv_omega) ?_
    refine SepWP.done (by dsimp [nextPc]; simp) (by simp [hrun_sf_1])
      ⟨by simp [hsp2'], spAligned_of_sp_eq hspA2 hsp2' (by simp [hsp2']),
        ⟨by simp [Reg.x19] at hx19 ⊢; rw [h19_2, h19_1, hx19],
         by simp [hx20_f],
         by simp [Reg.x21] at hx21 ⊢; rw [h21_2, h21_1, hx21],
         by simp [Reg.x22] at hx22 ⊢; rw [h22_2, h22_1, hx22],
         by simp [Reg.x23] at hx23 ⊢; rw [h23_2, h23_1, hx23],
         by simp; rw [h25_2, h25_1, hx25]⟩, hpostP⟩

private theorem seg6_outer_iter [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) {idx : Nat} (hidx : idx < 3) (u : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + off6aec) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hregs : Seg6OuterRegs sp idx s)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem) :
    let uPtr := sp + BitVec.ofNat 64 (4288 + 512 * idx)
    let outPtr := sp + BitVec.ofNat 64 (11440 + 320 * idx)
    let nextPc := if idx < 2 then b + off6aec else b + offSeg6SerEnd
    SepWP (blkPC03.rebase b (fun _ => none)) nextPc s
      (VecRangeMem 4 (sp + 2128#64) serConstFn ∗
        PolyMem uPtr (polyVecNat u) ∗
        memRegion (sp + 2192#64) 520 ∗ memRegion (sp + 15680#64) 520 ∗
        memRegion (sp + 16208#64) 320 ∗ memRegion (sp + 16528#64) 320 ∗
        memRegion outPtr 320 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        Seg6OuterRegs sp (idx + 1) sf ∧
        (Pf ⊢ VecRangeMem 4 (sp + 2128#64) serConstFn ∗
          PolyMem uPtr (polyVecNat u) ∗
          memRegion (sp + 2192#64) 520 ∗ memRegion (sp + 15680#64) 520 ∗
          memRegion (sp + 16208#64) 320 ∗ memRegion (sp + 16528#64) 320 ∗
          (outPtr ↦ₛ neonCompressSerialize10Poly u) ∗ Rest)) := by
  intro uPtr outPtr nextPc
  have hm520b : memRegion (sp + 2192#64) 520 = memRegion (sp + 2192#64) 512 ∗ memRegion (sp + 2704#64) 8 :=
    memRegion_split' (b := sp + 2192#64) (b' := sp + 2704#64) (n := 512) (k := (8 : Nat))
      rfl (by clear * -; bv_omega) (by decide)
  refine SepWP.weaken_pre (P' := PolyMem uPtr (polyVecNat u) ∗
      memRegion (sp + 2192#64) 520 ∗ memRegion (sp + 15680#64) 520 ∗
      (VecRangeMem 4 (sp + 2128#64) serConstFn ∗ memRegion (sp + 16208#64) 320 ∗
        memRegion (sp + 16528#64) 320 ∗ memRegion outPtr 320 ∗ Rest)) (by sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (seg6_prep_poly hb hbase s sp hidx u _ hpc hrun hsp hspA hregs hcl) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hregs1, hx24_1, hP1⟩
  refine SepWP.weaken_pre (Entails.trans hP1 (show _ ⊢ VecRangeMem 4 (sp + 2128#64) serConstFn ∗
      memRegion (sp + 16528#64) 320 ∗
      (PolyMem uPtr (polyVecNat u) ∗ PolyMem (sp + 2192#64) (polyVecNat u) ∗
        memRegion (sp + 2704#64) 8 ∗ memRegion (sp + 15680#64) 520 ∗
        memRegion (sp + 16208#64) 320 ∗ memRegion outPtr 320 ∗ Rest) by sep_frame)) ?_
  refine sepWP_seq_env hcl1 hro1
    (seg6_zero_load hb hbase s1 sp _ hpc1 hrun1 hsp1 hspA1 hregs1) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hregs2, hx24_2, hx8_2, hx9_2, hv5_2, hv6_2, hv7_2, hv16_2, hP2⟩
  refine SepWP.weaken_pre (Entails.trans hP2 (show _ ⊢ PolyMem (sp + 2192#64) (polyVecNat u) ∗
      ((sp + 16528#64) ↦ₛ ser10PolyPrefix u 0) ∗
      memRegion ((sp + 16528#64) + BitVec.ofNat 64 (20 * 0)) (320 - 20 * 0) ∗
      (VecRangeMem 4 (sp + 2128#64) serConstFn ∗ PolyMem uPtr (polyVecNat u) ∗
        memRegion (sp + 2704#64) 8 ∗ memRegion (sp + 15680#64) 520 ∗
        memRegion (sp + 16208#64) 320 ∗ memRegion outPtr 320 ∗ Rest) by
      rw [ser10PolyPrefix_zero, pointsToBytes_nil]; simp only [Nat.mul_zero, BitVec.add_zero]; sep_frame)) ?_
  refine sepWP_seq_env hcl2 hro2
    (seg6_inner_from hb hbase 0 (by decide) s2 sp u _ (by simpa using hpc2) hrun2 hsp2
      (by simpa using hx8_2) (by simpa using hx9_2) hregs2.2.2.2.1 hv5_2 hv6_2 hv7_2 hv16_2) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 _ ⟨hsp3, hspA3_eq, hgpr3, hP3⟩
  have hspA3 : s3.spAligned = true := hspA3_eq.trans hspA2
  have hregs3 : Seg6OuterRegs sp (idx + 1) s3 :=
    ⟨(hgpr3 .x19 (by decide) (by decide) (by decide) (by decide)).trans hregs2.1,
     (hgpr3 .x20 (by decide) (by decide) (by decide) (by decide)).trans hregs2.2.1,
     (hgpr3 .x21 (by decide) (by decide) (by decide) (by decide)).trans hregs2.2.2.1,
     (hgpr3 .x22 (by decide) (by decide) (by decide) (by decide)).trans hregs2.2.2.2.1,
     (hgpr3 .x23 (by decide) (by decide) (by decide) (by decide)).trans hregs2.2.2.2.2.1,
     (hgpr3 (.gpr 25#5) (by decide) (by decide) (by decide) (by decide)).trans hregs2.2.2.2.2.2⟩
  refine SepWP.weaken_pre (Entails.trans hP3 (show _ ⊢ ((sp + 16528#64) ↦ₛ neonCompressSerialize10Poly u) ∗
      memRegion (sp + 16208#64) 320 ∗ memRegion outPtr 320 ∗
      (VecRangeMem 4 (sp + 2128#64) serConstFn ∗ PolyMem uPtr (polyVecNat u) ∗
        PolyMem (sp + 2192#64) (polyVecNat u) ∗ memRegion (sp + 2704#64) 8 ∗
        memRegion (sp + 15680#64) 520 ∗ Rest) by sep_frame)) ?_
  refine SepWP.mono
    (seg6_bounce hb hbase s3 sp hidx u _ hpc3 hrun3 hsp3 hspA3 hregs3
      ((hgpr3 .x24 (by decide) (by decide) (by decide) (by decide)).trans (hx24_2.trans hx24_1))
      hcl3) ?_
  rintro sf Pf _ _ ⟨hspf, hspAf, hregsf, hPf⟩
  refine ⟨hspf, hspAf, hregsf, Entails.trans hPf ?_⟩
  have hm2192 : PolyMem (sp + 2192#64) (polyVecNat u) ∗ memRegion (sp + 2704#64) 8 ⊢
      memRegion (sp + 2192#64) 520 := by
    rw [hm520b]; exact sepConj_mono_left (vecRangeMem_entails_memRegion 32 (sp + 2192#64) (polyVecNat u))
  exact entails_sub hm2192 (by sep_frame) (by sep_frame)

theorem seg6_ser_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) {hdr rand : List (BitVec 8)}
    (hhdr : hdr.length = 64) (hrand : rand.length = 32) (Rest : SepProp)
    (hpc : s.pc = b + offSeg6Start) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem) :
    let rho := hdr.take 32
    let coins := ((sha3_512List (rand ++ (hdr.drop 32).take 32)).drop 32).take 32
    SepWP (blkPC03.rebase b (fun _ => none)) (b + offSeg6SerEnd) s
      (memRegion (sp + 2128#64) 64 ∗
        PolyMem (sp + 2192#64) (polyVecNat (uVecPoly16 rho coins 0)) ∗
        PolyMem (sp + 2704#64) (polyVecNat (uVecPoly16 rho coins 1)) ∗
        PolyMem (sp + 3216#64) (polyVecNat (uVecPoly16 rho coins 2)) ∗
        memRegion (sp + 4288#64) 1544 ∗
        memRegion (sp + 11440#64) 960 ∗
        memRegion (sp + 15680#64) 520 ∗
        memRegion (sp + 16208#64) 640 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        (Pf ⊢ ((sp + 11440#64) ↦ₛ encaps1OutCt1 hdr rand) ∗
          memRegion (sp + 2128#64) 1600 ∗
          memRegion (sp + 4288#64) 1544 ∗
          memRegion (sp + 15680#64) 520 ∗
          memRegion (sp + 16208#64) 640 ∗ Rest)) := by
  intro rho coins
  set u0 := uVecPoly16 rho coins 0
  set u1 := uVecPoly16 rho coins 1
  set u2 := uVecPoly16 rho coins 2
  have hm1536 : memRegion (sp + 2192#64) 1536 = memRegion (sp + 2192#64) 520 ∗ memRegion (sp + 2712#64) 1016 :=
    memRegion_split' (b := sp + 2192#64) (b' := sp + 2712#64) (n := 520) (k := (1016 : Nat))
      rfl (by clear * -; bv_omega) (by decide)
  have hm960a : memRegion (sp + 11440#64) 960 = memRegion (sp + 11440#64) 320 ∗ memRegion (sp + 11760#64) 640 :=
    memRegion_split' (b := sp + 11440#64) (b' := sp + 11760#64) (n := 320) (k := (640 : Nat))
      rfl (by clear * -; bv_omega) (by decide)
  have hm960b : memRegion (sp + 11760#64) 640 = memRegion (sp + 11760#64) 320 ∗ memRegion (sp + 12080#64) 320 :=
    memRegion_split' (b := sp + 11760#64) (b' := sp + 12080#64) (n := 320) (k := (320 : Nat))
      rfl (by clear * -; bv_omega) (by decide)
  have hm640 : memRegion (sp + 16208#64) 640 = memRegion (sp + 16208#64) 320 ∗ memRegion (sp + 16528#64) 320 :=
    memRegion_split' (b := sp + 16208#64) (b' := sp + 16528#64) (n := 320) (k := (320 : Nat))
      rfl (by clear * -; bv_omega) (by decide)
  refine SepWP.weaken_pre (P' := memRegion (sp + 2128#64) 64 ∗
      PolyMem (sp + 2192#64) (polyVecNat u0) ∗ PolyMem (sp + 2704#64) (polyVecNat u1) ∗
      PolyMem (sp + 3216#64) (polyVecNat u2) ∗ memRegion (sp + 4288#64) 1544 ∗
      (memRegion (sp + 11440#64) 960 ∗ memRegion (sp + 15680#64) 520 ∗ memRegion (sp + 16208#64) 640 ∗ Rest))
    (by sep_frame) ?_
  refine sepWP_seq_env hcl hro (seg6_setup hb hbase s sp u0 u1 u2 _ hpc hrun hsp hspA hcl) ?_
  rintro s0 P0 hpc0 hrun0 hcl0 hro0 ⟨hsp0, hspA0, hregs0, hP0⟩
  have huPtr0 : sp + BitVec.ofNat 64 (4288 + 512 * 0) = sp + 4288#64 := by clear * -; bv_omega
  have huPtr1 : sp + BitVec.ofNat 64 (4288 + 512 * 1) = sp + 4800#64 := by clear * -; bv_omega
  have huPtr2 : sp + BitVec.ofNat 64 (4288 + 512 * 2) = sp + 5312#64 := by clear * -; bv_omega
  have hout0 : sp + BitVec.ofNat 64 (11440 + 320 * 0) = sp + 11440#64 := by clear * -; bv_omega
  have hout1 : sp + BitVec.ofNat 64 (11440 + 320 * 1) = sp + 11760#64 := by clear * -; bv_omega
  have hout2 : sp + BitVec.ofNat 64 (11440 + 320 * 2) = sp + 12080#64 := by clear * -; bv_omega
  refine SepWP.weaken_pre (Entails.trans hP0 (show _ ⊢
      VecRangeMem 4 (sp + 2128#64) serConstFn ∗
      PolyMem (sp + BitVec.ofNat 64 (4288 + 512 * 0)) (polyVecNat u0) ∗
      memRegion (sp + 2192#64) 520 ∗ memRegion (sp + 15680#64) 520 ∗
      memRegion (sp + 16208#64) 320 ∗ memRegion (sp + 16528#64) 320 ∗
      memRegion (sp + BitVec.ofNat 64 (11440 + 320 * 0)) 320 ∗
      (memRegion (sp + 2712#64) 1016 ∗ PolyMem (sp + 4800#64) (polyVecNat u1) ∗
        PolyMem (sp + 5312#64) (polyVecNat u2) ∗ memRegion (sp + 5824#64) 8 ∗
        memRegion (sp + 11760#64) 320 ∗ memRegion (sp + 12080#64) 320 ∗ Rest) by
      rw [seg6ConstsMem_eq_vecRangeMem, hm1536, hm960a, hm960b, hm640, huPtr0, hout0]; sep_frame)) ?_
  refine sepWP_seq_env hcl0 hro0
    (seg6_outer_iter hb hbase s0 sp (by decide : 0 < 3) u0 _ hpc0 hrun0 hsp0 hspA0 hregs0 hcl0 hro0) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hregs1, hP1⟩
  refine SepWP.weaken_pre (Entails.trans hP1 (show _ ⊢
      VecRangeMem 4 (sp + 2128#64) serConstFn ∗
      PolyMem (sp + BitVec.ofNat 64 (4288 + 512 * 1)) (polyVecNat u1) ∗
      memRegion (sp + 2192#64) 520 ∗ memRegion (sp + 15680#64) 520 ∗
      memRegion (sp + 16208#64) 320 ∗ memRegion (sp + 16528#64) 320 ∗
      memRegion (sp + BitVec.ofNat 64 (11440 + 320 * 1)) 320 ∗
      (memRegion (sp + 2712#64) 1016 ∗ PolyMem (sp + 4288#64) (polyVecNat u0) ∗
        PolyMem (sp + 5312#64) (polyVecNat u2) ∗ memRegion (sp + 5824#64) 8 ∗
        ((sp + 11440#64) ↦ₛ neonCompressSerialize10Poly u0) ∗
        memRegion (sp + 12080#64) 320 ∗ Rest) by
      rw [huPtr0, hout0, huPtr1, hout1]; sep_frame)) ?_
  refine sepWP_seq_env hcl1 hro1
    (seg6_outer_iter hb hbase s1 sp (by decide : 1 < 3) u1 _
      (by simpa using hpc1) hrun1 hsp1 hspA1 hregs1 hcl1 hro1) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hregs2, hP2⟩
  refine SepWP.weaken_pre (Entails.trans hP2 (show _ ⊢
      VecRangeMem 4 (sp + 2128#64) serConstFn ∗
      PolyMem (sp + BitVec.ofNat 64 (4288 + 512 * 2)) (polyVecNat u2) ∗
      memRegion (sp + 2192#64) 520 ∗ memRegion (sp + 15680#64) 520 ∗
      memRegion (sp + 16208#64) 320 ∗ memRegion (sp + 16528#64) 320 ∗
      memRegion (sp + BitVec.ofNat 64 (11440 + 320 * 2)) 320 ∗
      (memRegion (sp + 2712#64) 1016 ∗ PolyMem (sp + 4288#64) (polyVecNat u0) ∗
        PolyMem (sp + 4800#64) (polyVecNat u1) ∗ memRegion (sp + 5824#64) 8 ∗
        ((sp + 11440#64) ↦ₛ neonCompressSerialize10Poly u0) ∗
        ((sp + 11760#64) ↦ₛ neonCompressSerialize10Poly u1) ∗ Rest) by
      rw [huPtr1, hout1, huPtr2, hout2]; sep_frame)) ?_
  refine sepWP_seq_env hcl2 hro2
    (seg6_outer_iter hb hbase s2 sp (by decide : 2 < 3) u2 _
      (by simpa using hpc2) hrun2 hsp2 hspA2 hregs2 hcl2 hro2) ?_
  rintro sf Pf hpcf hrunf hclf hrof ⟨hspf, hspAf, _, hPf⟩
  refine SepWP.done (by simpa using hpcf) hrunf ⟨hspf, hspAf, hclf, hrof, Entails.trans hPf ?_⟩
  rw [huPtr2, hout2]
  have hct1 : ((sp + 11440#64) ↦ₛ neonCompressSerialize10Poly u0) ∗
      ((sp + 11760#64) ↦ₛ neonCompressSerialize10Poly u1) ∗
      ((sp + 12080#64) ↦ₛ neonCompressSerialize10Poly u2) =
      ((sp + 11440#64) ↦ₛ encaps1OutCt1 hdr rand) := by
    rw [← encaps1OutCt1_eq hhdr hrand]
    dsimp only [rho, coins, u0, u1, u2]
    rw [pointsToBytes_append, pointsToBytes_append, ← sepConj_assoc,
      neonCompressSerialize10Poly_length, List.length_append,
      neonCompressSerialize10Poly_length, neonCompressSerialize10Poly_length,
      show (sp + 11440#64) + 320#64 = sp + 11760#64 by clear * -; bv_omega,
      show (sp + 11440#64) + BitVec.ofNat 64 (320 + 320) = sp + 12080#64 by clear * -; bv_omega,
      sepConj_assoc]
  have hm1600 : VecRangeMem 4 (sp + 2128#64) serConstFn ∗ memRegion (sp + 2192#64) 520 ∗
      memRegion (sp + 2712#64) 1016 ⊢ memRegion (sp + 2128#64) 1600 := by
    rw [memRegion_split' (b := sp + 2128#64) (b' := sp + 2192#64) (n := 64) (k := (1536 : Nat))
          rfl (by clear * -; bv_omega) (by decide), hm1536]
    exact entails_sub (vecRangeMem_entails_memRegion 4 (sp + 2128#64) serConstFn)
      (by sep_frame) (by sep_frame)
  have hm1544 : PolyMem (sp + 4288#64) (polyVecNat u0) ∗ PolyMem (sp + 4800#64) (polyVecNat u1) ∗
      PolyMem (sp + 5312#64) (polyVecNat u2) ∗ memRegion (sp + 5824#64) 8 ⊢
      memRegion (sp + 4288#64) 1544 := by
    dsimp only [PolyMem]
    rw [memRegion_split' (b := sp + 4288#64) (b' := sp + 5824#64) (n := 1536) (k := (8 : Nat))
          rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b := sp + 4288#64) (b' := sp + 4800#64) (n := 512) (k := (1024 : Nat))
          rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b := sp + 4800#64) (b' := sp + 5312#64) (n := 512) (k := (512 : Nat))
          rfl (by clear * -; bv_omega) (by decide)]
    exact entails_sub (vecRangeMem_entails_memRegion 32 (sp + 4288#64) _) (by sep_frame)
      (entails_sub (vecRangeMem_entails_memRegion 32 (sp + 4800#64) _) (by sep_frame)
        (entails_sub (vecRangeMem_entails_memRegion 32 (sp + 5312#64) _) (by sep_frame) (by sep_frame)))
  rw [hm640]
  exact entails_sub
    (show ((sp + 11440#64) ↦ₛ neonCompressSerialize10Poly u0) ∗
        ((sp + 11760#64) ↦ₛ neonCompressSerialize10Poly u1) ∗
        ((sp + 12080#64) ↦ₛ neonCompressSerialize10Poly u2) ⊢
        ((sp + 11440#64) ↦ₛ encaps1OutCt1 hdr rand) by rw [hct1]; exact Entails.refl _) (by sep_frame)
    (entails_sub hm1600 (by sep_frame)
      (entails_sub hm1544 (by sep_frame) (by sep_frame)))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg6SerLoop
