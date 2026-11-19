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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg2Simd -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode10
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1b

/-!
# `decapsulate_compressed_key` (`B04`) — Segment 2a (`+0x052c .. +0x0734`)

Per-iteration `u[idx]` zeroing, inlined NEON `deserialize_10` + `decompress_10` 16-chunk loop, and
`B28` (`memcpy`) staging into `sp + 11856 + 512 * idx`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg2a

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup4hLow pack4x32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (simdTrn1_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode10 (
  simdShrn16_4h simdUmlal4sLow simdUshr4s simdXtn4h
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem SepStore128 Vec32 poly32Mem_ofFn polyVecNat step_stpQ128 step_strQ128
  vecRangeBytes vecRangeBytes_length vecRangeMem_congr vecRangeMem_eq_pointsToBytes
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (spAligned_of_chk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc (
  svc_fmov_s_w svc_simdIns_h1 svc_simdIns_h2 svc_simdIns_h3 svc_simdIns_h4
  svc_simdIns_h5 svc_simdIns_h6 svc_simdIns_h7 svc_simdTrn1_8h
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  blk04_code_eq blk04_tree_size blkLib04 blkPC04 blkPl04 blkPlaceable04 blkTree04
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1b (
  blk28_memcpy_04 exec_simdMovi_2d_0
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg2Simd (
  decompPoly16 deser10Decomp_chunk_eq exec_simdMovi_4s_512 exec_simdShrn16_4h
  exec_simdUmlal_4s_low exec_simdUshr_4s_10 exec_simdXtn_4h
  rawDeser10Full rawDeser10Pre7 rawGroup10Lanes
)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC04 blkLib04 blkTree04 blk04_code_eq blk04_tree_size
  via_placement blkPl04 blkPlaceable04 [0x052c → 0x0730]
end

attribute [local irreducible]
  blkPC04 polyVecNat decompPoly16
  simdXtn4h simdShrn16_4h simdUmlal4sLow simdUshr4s simdTrn1_8h

@[simp, arm64_norm, wp_norm]
private theorem blkPl04_ρ [MlKemPlacement] (sym : String) :
    blkPl04.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

attribute [local wp_norm ↓ high]
  exec_simdMovi_2d_0 exec_simdMovi_4s_512
  svc_fmov_s_w svc_simdIns_h1 svc_simdIns_h2 svc_simdIns_h3
  svc_simdIns_h4 svc_simdIns_h5 svc_simdIns_h6 svc_simdIns_h7
  exec_simdXtn_4h exec_simdShrn16_4h exec_simdUmlal_4s_low
  exec_simdUshr_4s_10 svc_simdTrn1_8h

private theorem SepStore128.polyMem {k : Nat} {ea ptr : BitVec 64} {f : Nat → BitVec 128}
    {val : BitVec 128} (hk : k < 32) (ha : ptr + BitVec.ofNat 64 (16 * k) = ea) :
    SepStore128 ea val (PolyMem ptr f) (PolyMem ptr (Function.update f k val)) :=
  SepStore128.vecRange (n := 32) hk ha

private theorem polyMem_congr {ptr : BitVec 64} {f g : Nat → BitVec 128}
    (h : ∀ i, i < 32 → f i = g i) : PolyMem ptr f = PolyMem ptr g := vecRangeMem_congr h

private theorem update2_prefix {f g : Nat → BitVec 128} {c : Nat}
    (hf : ∀ j, j < 2 * c → f j = g j) :
    ∀ j, j < 2 * (c + 1) →
      Function.update (Function.update f (2 * c) (g (2 * c))) (2 * c + 1) (g (2 * c + 1)) j = g j := by
  intro j hj
  by_cases h1 : j = 2 * c + 1
  · subst h1; simp
  · rw [Function.update_of_ne h1]
    by_cases h0 : j = 2 * c
    · subst h0; simp
    · rw [Function.update_of_ne h0]; exact hf j (by omega)

private theorem step_ldrb_x9 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {src : BitVec 64} {bs : List (BitVec 8)} {Rest : SepProp}
    {post : State → SepProp → Prop}
    {pc : BitVec 64} {rt : Reg} {am : AddrMode} (j : Nat)
    (hj : j < bs.length) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W32 .B8 false rt am))
    (hal : checkAddrSPAligned s am = true)
    (hea : evalAddrMode s am = (src + BitVec.ofNat 64 j, none))
    (hexec : (s.writeReg .W32 rt ((bs.getD j 0#8).zeroExtend 64)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' ((src ↦ₛ bs) ∗ Rest) post) :
    SepWP prog target_pc s ((src ↦ₛ bs) ∗ Rest) post :=
  SepWP.step_ldr8 (wb := none) hpc hrun hfetch hal hea
    (SepLoad8.of_pointsToBytes rfl hj rfl) hexec hnext

local macro "step_strQ_poly5680 " k:num : tactic => `(tactic| (
  apply step_strQ128
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · first | rfl | wp_norm_lhs | wp_norm_goal | simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, *]
  · wp_norm_lhs
  · wp_norm_lhs
  · apply SepStore128.left; apply SepStore128.vec32 (k := $k); { decide }; { clear * -; bv_omega }; { rfl }
  · wp_norm_lhs
  intro _))

private theorem seg2a_zero [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (s : State) (sp x8v x25v : BitVec 64) (vInit : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + 1324#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = x8v) (hx25 : s.readReg64 .x25 = x25v) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + 1468#64) s
      (Poly32Mem (sp + 5680#64) vInit ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x8 = x8v ∧ sf.readReg64 .x9 = x25v ∧
        sf.readReg64 .x10 = 16#64 ∧ sf.readReg64 .x19 = x8v + 1#64 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = x25v ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readVReg128 8#5 = s.readVReg128 8#5 ∧
        Pf = (PolyMem (sp + 5680#64) (fun _ => 0#128) ∗ Rest)) := by
  wp_steps 4
  step_strQ_poly5680 31; step_strQ_poly5680 30; step_strQ_poly5680 29; step_strQ_poly5680 28
  step_strQ_poly5680 27; step_strQ_poly5680 26; step_strQ_poly5680 25; step_strQ_poly5680 24
  step_strQ_poly5680 23; step_strQ_poly5680 22; step_strQ_poly5680 21; step_strQ_poly5680 20
  step_strQ_poly5680 19; step_strQ_poly5680 18; step_strQ_poly5680 17; step_strQ_poly5680 16
  step_strQ_poly5680 15; step_strQ_poly5680 14; step_strQ_poly5680 13; step_strQ_poly5680 12
  step_strQ_poly5680 11; step_strQ_poly5680 10; step_strQ_poly5680 9; step_strQ_poly5680 8
  step_strQ_poly5680 7; step_strQ_poly5680 6; step_strQ_poly5680 5; step_strQ_poly5680 4
  step_strQ_poly5680 3; step_strQ_poly5680 2; step_strQ_poly5680 1; step_strQ_poly5680 0
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
      by simp [hx8], by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp [hx25], by simp, by simp, by simp, by simp, ?_⟩
  rw [← poly32Mem_ofFn (sp + 5680#64) (fun _ => 0#128)]
  rfl

local macro "step_b9 " c:ident hrun:ident hx9:ident hc:ident off:num : tactic => `(tactic| (
  refine step_ldrb_x9 (20 * $c + $off) (by omega) (by wp_norm_lhs)
    (by first | rfl | simp [$hrun:ident]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, $hx9:ident]; try (clear * - $hc:ident; bv_omega)) (by wp_norm_lhs) ?_))

private structure Seg2aPreserved (s s' : State) : Prop where
  x8  : s'.readReg64 .x8 = s.readReg64 .x8
  x19 : s'.readReg64 .x19 = s.readReg64 .x19
  fp  : s'.readReg64 .fp = s.readReg64 .fp
  x20 : s'.readReg64 .x20 = s.readReg64 .x20
  x22 : s'.readReg64 .x22 = s.readReg64 .x22
  x23 : s'.readReg64 .x23 = s.readReg64 .x23
  x24 : s'.readReg64 .x24 = s.readReg64 .x24
  x25 : s'.readReg64 .x25 = s.readReg64 .x25
  x26 : s'.readReg64 .x26 = s.readReg64 .x26
  x27 : s'.readReg64 .x27 = s.readReg64 .x27
  x28 : s'.readReg64 .x28 = s.readReg64 .x28
  v8  : s'.readVReg128 8#5 = s.readVReg128 8#5

private theorem Seg2aPreserved.trans {s1 s2 s3 : State}
    (h12 : Seg2aPreserved s1 s2) (h23 : Seg2aPreserved s2 s3) : Seg2aPreserved s1 s3 :=
  ⟨h23.x8.trans h12.x8, h23.x19.trans h12.x19, h23.fp.trans h12.fp,
   h23.x20.trans h12.x20, h23.x22.trans h12.x22, h23.x23.trans h12.x23,
   h23.x24.trans h12.x24, h23.x25.trans h12.x25, h23.x26.trans h12.x26,
   h23.x27.trans h12.x27, h23.x28.trans h12.x28, h23.v8.trans h12.v8⟩

@[simp] private theorem ubfm_beq_self : (BitfieldOp.UBFM == BitfieldOp.UBFM) = true := rfl

@[simp] private theorem setWidth16_setWidth64_shr (x : BitVec 8) (s : Nat) :
    BitVec.setWidth 16 (BitVec.setWidth 64 x >>> s) =
      BitVec.setWidth 16 (BitVec.setWidth 32 x >>> s) := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hk, decide_true, Bool.true_and]
  by_cases hks : s + k < 8
  · simp [show s + k < 64 by omega, show s + k < 32 by omega]
  · simp [BitVec.getLsbD_of_ge x (s + k) (by omega)]

@[simp] private theorem setWidth32_setWidth64_shr (x : BitVec 8) (s : Nat) :
    BitVec.setWidth 32 (BitVec.setWidth 64 x >>> s) = BitVec.setWidth 32 x >>> s := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hk, decide_true, Bool.true_and]
  by_cases hks : s + k < 8
  · simp [show s + k < 64 by omega, show s + k < 32 by omega]
  · simp [BitVec.getLsbD_of_ge x (s + k) (by omega)]

private def rawDeser10Pre4 (b0 b1 b2 b3 b4 : BitVec 8) : BitVec 128 :=
  let (g0, g1, g2, g3) := rawGroup10Lanes b0 b1 b2 b3 b4
  setSimdLane (setSimdLane (setSimdLane (g0.zeroExtend 128) 16 1 (g1.zeroExtend 128))
    16 2 (g2.zeroExtend 128)) 16 3 (g3.zeroExtend 128)

private theorem seg2a_iter_p1 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (sp src : BitVec 64) (bs : List (BitVec 8)) (Rest : SepProp)
    (hbs : bs.length = 320) (c : Nat) (hc : c < 16) (s : State)
    (hpc : s.pc = b + 1468#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx9 : s.readReg64 .x9 = src + BitVec.ofNat 64 (20 * c + 9))
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (16 + 32 * c)) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + 1628#64) s ((src ↦ₛ bs) ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .x9 = src + BitVec.ofNat 64 (20 * c + 9) ∧
        s1.readReg64 .x10 = BitVec.ofNat 64 (16 + 32 * c) ∧
        s1.readReg64 .x11 = (bs.getD (20 * c + 16) 0#8).zeroExtend 64 ∧
        s1.readReg64 .x13 = (bs.getD (20 * c + 6) 0#8).zeroExtend 64 ∧
        s1.readReg64 .x14 = (bs.getD (20 * c + 5) 0#8).zeroExtend 64 ∧
        s1.readReg64 .x15 = (bs.getD (20 * c + 15) 0#8).zeroExtend 64 ∧
        s1.readVReg128 0#5 = rawDeser10Pre4
          (bs.getD (20 * c + 0) 0#8) (bs.getD (20 * c + 1) 0#8) (bs.getD (20 * c + 2) 0#8)
          (bs.getD (20 * c + 3) 0#8) (bs.getD (20 * c + 4) 0#8) ∧
        s1.readVReg128 1#5 = rawDeser10Pre4
          (bs.getD (20 * c + 10) 0#8) (bs.getD (20 * c + 11) 0#8) (bs.getD (20 * c + 12) 0#8)
          (bs.getD (20 * c + 13) 0#8) (bs.getD (20 * c + 14) 0#8) ∧
        s1.readVReg128 4#5 = (pack4x32 fun _ => 512#32) ∧
        s1.readVReg128 5#5 = (pack4x32 fun _ => 512#32) ∧
        s1.readVReg128 6#5 = (pack4x32 fun _ => 512#32) ∧
        s1.readVReg128 7#5 = (pack4x32 fun _ => 512#32) ∧
        Seg2aPreserved s s1 ∧ P1 = ((src ↦ₛ bs) ∗ Rest)) := by
  step_b9 c hrun hx9 hc 1; step_b9 c hrun hx9 hc 11; wp_step
  step_b9 c hrun hx9 hc 0; step_b9 c hrun hx9 hc 10; wp_step
  step_b9 c hrun hx9 hc 2; wp_step; step_b9 c hrun hx9 hc 12; wp_steps 4
  step_b9 c hrun hx9 hc 3; wp_steps 4; step_b9 c hrun hx9 hc 13; wp_steps 2
  step_b9 c hrun hx9 hc 4; wp_steps 7; step_b9 c hrun hx9 hc 15; wp_steps 2
  step_b9 c hrun hx9 hc 14; wp_step; step_b9 c hrun hx9 hc 5; wp_step
  step_b9 c hrun hx9 hc 6; wp_step; step_b9 c hrun hx9 hc 16; wp_step
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
      by simp [hx9], by simp [hx10],
      by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
      by simp [rawDeser10Pre4, rawGroup10Lanes, wp_norm, arm64_norm],
      by simp [rawDeser10Pre4, rawGroup10Lanes, wp_norm, arm64_norm],
      by simp, by simp, by simp, by simp,
      ⟨by simp, by simp, by simp, by simp, by simp, by simp,
       by simp, by simp, by simp, by simp, by simp, by simp⟩, rfl⟩

private theorem seg2a_iter_p2 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (sp src : BitVec 64) (bs : List (BitVec 8)) (Rest : SepProp)
    (hbs : bs.length = 320) (c : Nat) (hc : c < 16) (s : State)
    (hpc : s.pc = b + 1628#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx9 : s.readReg64 .x9 = src + BitVec.ofNat 64 (20 * c + 9))
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (16 + 32 * c))
    (_hx11 : s.readReg64 .x11 = (bs.getD (20 * c + 16) 0#8).zeroExtend 64)
    (_hx13 : s.readReg64 .x13 = (bs.getD (20 * c + 6) 0#8).zeroExtend 64)
    (_hx14 : s.readReg64 .x14 = (bs.getD (20 * c + 5) 0#8).zeroExtend 64)
    (_hx15 : s.readReg64 .x15 = (bs.getD (20 * c + 15) 0#8).zeroExtend 64)
    (_hv0 : s.readVReg128 0#5 = rawDeser10Pre4
      (bs.getD (20 * c + 0) 0#8) (bs.getD (20 * c + 1) 0#8) (bs.getD (20 * c + 2) 0#8)
      (bs.getD (20 * c + 3) 0#8) (bs.getD (20 * c + 4) 0#8))
    (_hv1 : s.readVReg128 1#5 = rawDeser10Pre4
      (bs.getD (20 * c + 10) 0#8) (bs.getD (20 * c + 11) 0#8) (bs.getD (20 * c + 12) 0#8)
      (bs.getD (20 * c + 13) 0#8) (bs.getD (20 * c + 14) 0#8))
    (hv4 : s.readVReg128 4#5 = (pack4x32 fun _ => 512#32))
    (hv5 : s.readVReg128 5#5 = (pack4x32 fun _ => 512#32))
    (hv6 : s.readVReg128 6#5 = (pack4x32 fun _ => 512#32))
    (hv7 : s.readVReg128 7#5 = (pack4x32 fun _ => 512#32)) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + 1752#64) s ((src ↦ₛ bs) ∗ Rest)
      (fun s2 P2 =>
        s2.sp = sp ∧ s2.spAligned = true ∧
        s2.readReg64 .x9 = src + BitVec.ofNat 64 (20 * (c + 1) + 9) ∧
        s2.readReg64 .x10 = BitVec.ofNat 64 (16 + 32 * c) ∧
        s2.readVReg128 0#5 = rawDeser10Full
          (bs.getD (20 * c + 0) 0#8) (bs.getD (20 * c + 1) 0#8) (bs.getD (20 * c + 2) 0#8)
          (bs.getD (20 * c + 3) 0#8) (bs.getD (20 * c + 4) 0#8) (bs.getD (20 * c + 5) 0#8)
          (bs.getD (20 * c + 6) 0#8) (bs.getD (20 * c + 7) 0#8) (bs.getD (20 * c + 8) 0#8)
          (bs.getD (20 * c + 9) 0#8) ∧
        s2.readVReg128 1#5 = rawDeser10Full
          (bs.getD (20 * c + 10) 0#8) (bs.getD (20 * c + 11) 0#8) (bs.getD (20 * c + 12) 0#8)
          (bs.getD (20 * c + 13) 0#8) (bs.getD (20 * c + 14) 0#8) (bs.getD (20 * c + 15) 0#8)
          (bs.getD (20 * c + 16) 0#8) (bs.getD (20 * c + 17) 0#8) (bs.getD (20 * c + 18) 0#8)
          (bs.getD (20 * c + 19) 0#8) ∧
        s2.readVReg128 2#5 = simdXtn4h (rawDeser10Pre7
          (bs.getD (20 * c + 0) 0#8) (bs.getD (20 * c + 1) 0#8) (bs.getD (20 * c + 2) 0#8)
          (bs.getD (20 * c + 3) 0#8) (bs.getD (20 * c + 4) 0#8) (bs.getD (20 * c + 5) 0#8)
          (bs.getD (20 * c + 6) 0#8) (bs.getD (20 * c + 7) 0#8) (bs.getD (20 * c + 8) 0#8)) ∧
        s2.readVReg128 3#5 = simdXtn4h (rawDeser10Pre7
          (bs.getD (20 * c + 10) 0#8) (bs.getD (20 * c + 11) 0#8) (bs.getD (20 * c + 12) 0#8)
          (bs.getD (20 * c + 13) 0#8) (bs.getD (20 * c + 14) 0#8) (bs.getD (20 * c + 15) 0#8)
          (bs.getD (20 * c + 16) 0#8) (bs.getD (20 * c + 17) 0#8) (bs.getD (20 * c + 18) 0#8)) ∧
        s2.readVReg128 4#5 = (pack4x32 fun _ => 512#32) ∧
        s2.readVReg128 5#5 = (pack4x32 fun _ => 512#32) ∧
        s2.readVReg128 6#5 = (pack4x32 fun _ => 512#32) ∧
        s2.readVReg128 7#5 = (pack4x32 fun _ => 512#32) ∧
        Seg2aPreserved s s2 ∧ P2 = ((src ↦ₛ bs) ∗ Rest)) := by
  wp_step; step_b9 c hrun hx9 hc 7; wp_steps 6
  step_b9 c hrun hx9 hc 17; wp_step; step_b9 c hrun hx9 hc 8; wp_steps 5
  step_b9 c hrun hx9 hc 18; wp_step; step_b9 c hrun hx9 hc 9; wp_steps 4
  step_b9 c hrun hx9 hc 19; wp_steps 7
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
      by simp; clear * - hc; bv_omega, by simp [hx10],
      by simp [rawDeser10Full, rawDeser10Pre7, rawDeser10Pre4, rawGroup10Lanes, wp_norm, arm64_norm],
      by simp [rawDeser10Full, rawDeser10Pre7, rawDeser10Pre4, rawGroup10Lanes, wp_norm, arm64_norm],
      by simp [rawDeser10Pre7, rawDeser10Pre4, rawGroup10Lanes, wp_norm, arm64_norm],
      by simp [rawDeser10Pre7, rawDeser10Pre4, rawGroup10Lanes, wp_norm, arm64_norm],
      by simp [hv4], by simp [hv5], by simp [hv6], by simp [hv7],
      ⟨by simp, by simp, by simp, by simp, by simp, by simp,
       by simp, by simp, by simp, by simp, by simp, by simp⟩, rfl⟩

private theorem seg2a_iter_p3 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (sp src dst : BitVec 64) (bs : List (BitVec 8)) (Rest : SepProp)
    (hbs : bs.length = 320) (c : Nat) (hc : c < 16) (s : State) (f : Nat → BitVec 128)
    (hpc : s.pc = b + 1752#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx9 : s.readReg64 .x9 = src + BitVec.ofNat 64 (20 * (c + 1) + 9))
    (_hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (16 + 32 * c))
    (_hx27 : s.readReg64 .x27 = dst)
    (hv8_tr : (s.readVReg128 8#5).truncate 64 = (dup4hLow 3329#16).truncate 64)
    (_hv0 : s.readVReg128 0#5 = rawDeser10Full
      (bs.getD (20 * c + 0) 0#8) (bs.getD (20 * c + 1) 0#8) (bs.getD (20 * c + 2) 0#8)
      (bs.getD (20 * c + 3) 0#8) (bs.getD (20 * c + 4) 0#8) (bs.getD (20 * c + 5) 0#8)
      (bs.getD (20 * c + 6) 0#8) (bs.getD (20 * c + 7) 0#8) (bs.getD (20 * c + 8) 0#8)
      (bs.getD (20 * c + 9) 0#8))
    (_hv1 : s.readVReg128 1#5 = rawDeser10Full
      (bs.getD (20 * c + 10) 0#8) (bs.getD (20 * c + 11) 0#8) (bs.getD (20 * c + 12) 0#8)
      (bs.getD (20 * c + 13) 0#8) (bs.getD (20 * c + 14) 0#8) (bs.getD (20 * c + 15) 0#8)
      (bs.getD (20 * c + 16) 0#8) (bs.getD (20 * c + 17) 0#8) (bs.getD (20 * c + 18) 0#8)
      (bs.getD (20 * c + 19) 0#8))
    (_hv2 : s.readVReg128 2#5 = simdXtn4h (rawDeser10Pre7
      (bs.getD (20 * c + 0) 0#8) (bs.getD (20 * c + 1) 0#8) (bs.getD (20 * c + 2) 0#8)
      (bs.getD (20 * c + 3) 0#8) (bs.getD (20 * c + 4) 0#8) (bs.getD (20 * c + 5) 0#8)
      (bs.getD (20 * c + 6) 0#8) (bs.getD (20 * c + 7) 0#8) (bs.getD (20 * c + 8) 0#8)))
    (_hv3 : s.readVReg128 3#5 = simdXtn4h (rawDeser10Pre7
      (bs.getD (20 * c + 10) 0#8) (bs.getD (20 * c + 11) 0#8) (bs.getD (20 * c + 12) 0#8)
      (bs.getD (20 * c + 13) 0#8) (bs.getD (20 * c + 14) 0#8) (bs.getD (20 * c + 15) 0#8)
      (bs.getD (20 * c + 16) 0#8) (bs.getD (20 * c + 17) 0#8) (bs.getD (20 * c + 18) 0#8)))
    (_hv4 : s.readVReg128 4#5 = (pack4x32 fun _ => 512#32))
    (_hv5 : s.readVReg128 5#5 = (pack4x32 fun _ => 512#32))
    (_hv6 : s.readVReg128 6#5 = (pack4x32 fun _ => 512#32))
    (_hv7 : s.readVReg128 7#5 = (pack4x32 fun _ => 512#32)) :
    SepWP (blkPC04.rebase b (fun _ => none))
      (if c < 15 then b + 1468#64 else b + 1820#64) s
      ((src ↦ₛ bs) ∗ PolyMem dst f ∗ Rest)
      (fun s3 P3 =>
        s3.sp = sp ∧ s3.spAligned = true ∧
        s3.readReg64 .x9 = src + BitVec.ofNat 64 (20 * (c + 1) + 9) ∧
        s3.readReg64 .x10 = BitVec.ofNat 64 (16 + 32 * (c + 1)) ∧
        Seg2aPreserved s s3 ∧
        P3 = ((src ↦ₛ bs) ∗ PolyMem dst
          (Function.update (Function.update f (2 * c) (polyVecNat (decompPoly16 10 bs) (2 * c)))
            (2 * c + 1) (polyVecNat (decompPoly16 10 bs) (2 * c + 1))) ∗ Rest)) := by
  wp_steps 15
  obtain ⟨hq0, hq1⟩ := deser10Decomp_chunk_eq bs c hc hbs (s.readVReg128 8#5) hv8_tr
  refine step_stpQ128 (pc := b + 1812#64) (wb := none)
    (ea := dst + BitVec.ofNat 64 (32 * c)) (ea16 := dst + BitVec.ofNat 64 (32 * c) + 16#64)
    (v1 := polyVecNat (decompPoly16 10 bs) (2 * c))
    (v2 := polyVecNat (decompPoly16 10 bs) (2 * c + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; clear * - hc; bv_omega) rfl
    (by rw [← hq0]; simp)
    (by rw [← hq1]; simp)
    (SepStore128.right (SepStore128.left (SepStore128.polyMem (k := 2 * c) (by omega)
      (by clear * -; bv_omega))))
    (SepStore128.right (SepStore128.left (SepStore128.polyMem (k := 2 * c + 1) (by omega)
      (by clear * -; bv_omega))))
    (by wp_norm_lhs) ?_
  intro m'
  wp_step
  wp_if hne
  · have hc15 : c < 15 := by
      by_contra hge; have hc_eq : c = 15 := by omega
      subst hc_eq; simp at hne
    simp only [hc15, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp [hx9], by simp; clear * - hc; bv_omega,
        ⟨by simp, by simp, by simp, by simp, by simp, by simp,
         by simp, by simp, by simp, by simp, by simp, by simp⟩, rfl⟩
  · have hc15 : ¬ c < 15 := by
      intro hlt
      clear * - hne hlt; bv_omega
    simp only [hc15, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp [hx9], by simp; clear * - hc; bv_omega,
        ⟨by simp, by simp, by simp, by simp, by simp, by simp,
         by simp, by simp, by simp, by simp, by simp, by simp⟩, rfl⟩

private theorem seg2a_iter_body [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl04 b)
    (sp src dst : BitVec 64) (bs : List (BitVec 8)) (Rest : SepProp)
    (hbs : bs.length = 320) (c : Nat) (hc : c < 16) (s : State) (f : Nat → BitVec 128)
    (hpc : s.pc = b + 1468#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx9 : s.readReg64 .x9 = src + BitVec.ofNat 64 (20 * c + 9))
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (16 + 32 * c))
    (hx27 : s.readReg64 .x27 = dst)
    (hv8_tr : (s.readVReg128 8#5).truncate 64 = (dup4hLow 3329#16).truncate 64) :
    SepWP (blkPC04.rebase b (fun _ => none))
      (if c < 15 then b + 1468#64 else b + 1820#64) s
      ((src ↦ₛ bs) ∗ PolyMem dst f ∗ Rest)
      (fun s3 P3 =>
        s3.sp = sp ∧ s3.spAligned = true ∧
        s3.readReg64 .x9 = src + BitVec.ofNat 64 (20 * (c + 1) + 9) ∧
        s3.readReg64 .x10 = BitVec.ofNat 64 (16 + 32 * (c + 1)) ∧
        Seg2aPreserved s s3 ∧
        P3 = ((src ↦ₛ bs) ∗ PolyMem dst
          (Function.update (Function.update f (2 * c) (polyVecNat (decompPoly16 10 bs) (2 * c)))
            (2 * c + 1) (polyVecNat (decompPoly16 10 bs) (2 * c + 1))) ∗ Rest)) := by
  refine sepWP_seq_env hcl hro
    (seg2a_iter_p1 hb sp src bs (PolyMem dst f ∗ Rest) hbs c hc s hpc hrun hsp hspA hx9 hx10) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx9_1, hx10_1, hx11_1, hx13_1, hx14_1, hx15_1,
      hv0_1, hv1_1, hv4_1, hv5_1, hv6_1, hv7_1, hpres1, rfl⟩
  refine sepWP_seq_env hcl1 hro1
    (seg2a_iter_p2 hb sp src bs (PolyMem dst f ∗ Rest) hbs c hc s1
      hpc1 hrun1 hsp1 hspA1 hx9_1 hx10_1 hx11_1 hx13_1 hx14_1 hx15_1
      hv0_1 hv1_1 hv4_1 hv5_1 hv6_1 hv7_1) ?_
  rintro s2 P2 hpc2 hrun2 _hcl2 _hro2
    ⟨hsp2, hspA2, hx9_2, hx10_2, hv0_2, hv1_2, hv2_2, hv3_2, hv4_2, hv5_2, hv6_2, hv7_2, hpres2, rfl⟩
  refine SepWP.mono
    (seg2a_iter_p3 hb sp src dst bs Rest hbs c hc s2 f hpc2 hrun2 hsp2 hspA2
      hx9_2 hx10_2 (hpres2.x27.trans (hpres1.x27.trans hx27))
      (by rw [hpres2.v8, hpres1.v8]; exact hv8_tr)
      hv0_2 hv1_2 hv2_2 hv3_2 hv4_2 hv5_2 hv6_2 hv7_2) ?_
  rintro s3 P3 _ _ ⟨hsp3, hspA3, hx9_3, hx10_3, hpres3, hP3⟩
  exact ⟨hsp3, hspA3, hx9_3, hx10_3,
    Seg2aPreserved.trans hpres1 (Seg2aPreserved.trans hpres2 hpres3), hP3⟩

private theorem seg2a_loop [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl04 b)
    (sp src dst : BitVec 64) (bs : List (BitVec 8)) (Rest : SepProp)
    (hbs : bs.length = 320) :
    ∀ (rem c : Nat), c + 1 + rem = 16 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + 1468#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x9 = src + BitVec.ofNat 64 (20 * c + 9) →
      s.readReg64 .x10 = BitVec.ofNat 64 (16 + 32 * c) →
      s.readReg64 .x27 = dst →
      (s.readVReg128 8#5).truncate 64 = (dup4hLow 3329#16).truncate 64 →
      (∀ j, j < 2 * c → f j = polyVecNat (decompPoly16 10 bs) j) →
      SepWP (blkPC04.rebase b (fun _ => none)) (b + 1820#64) s
        ((src ↦ₛ bs) ∗ PolyMem dst f ∗ Rest)
        (fun sf Pf =>
          sf.sp = sp ∧ sf.spAligned = true ∧ Seg2aPreserved s sf ∧
          Pf = ((src ↦ₛ bs) ∗ PolyMem dst (polyVecNat (decompPoly16 10 bs)) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro c hcrem s f hpc hrun hsp hspA hcl hro hx9 hx10 hx27 hv8_tr hf
    have hc15 : c = 15 := by omega
    subst hc15
    have hiter := seg2a_iter_body hb sp src dst bs Rest hbs 15 (by omega) s f
      hpc hrun hsp hspA hcl hro hx9 hx10 hx27 hv8_tr
    simp only [Nat.lt_irrefl, ↓reduceIte] at hiter
    refine SepWP.mono hiter ?_
    rintro sf Pf _ _ ⟨hsp_f, hspA_f, _, _, hpres_f, hPf⟩
    exact ⟨hsp_f, hspA_f, hpres_f,
      hPf.trans (by rw [polyMem_congr (update2_prefix (c := 15) hf)])⟩
  | succ rem ih =>
    intro c hcrem s f hpc hrun hsp hspA hcl hro hx9 hx10 hx27 hv8_tr hf
    have hc15 : c < 15 := by omega
    have hiter := seg2a_iter_body hb sp src dst bs Rest hbs c (by omega) s f
      hpc hrun hsp hspA hcl hro hx9 hx10 hx27 hv8_tr
    simp only [hc15, ↓reduceIte] at hiter
    refine sepWP_seq_env hcl hro hiter ?_
    rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hx9_1, hx10_1, hpres1, rfl⟩
    refine SepWP.mono
      (ih (c + 1) (by omega) s1 _ hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hx9_1 hx10_1
        (hpres1.x27.trans hx27) (by rw [hpres1.v8]; exact hv8_tr) (update2_prefix hf)) ?_
    rintro sf Pf _ _ ⟨hsp_f, hspA_f, hpres2, hPf⟩
    exact ⟨hsp_f, hspA_f, Seg2aPreserved.trans hpres1 hpres2, hPf⟩

/-- Iteration `idx < 3` of Segment 2a (`+0x052c → +0x0734` = `b + 1324#64 → b + 1844#64`):
    zeroes `sp + 5680`, decodes & decompresses 320-byte slice `bs` into `sp + 5680`, and `memcpy`s
    it into `polyPtr = sp + BitVec.ofNat 64 (11856 + 512 * idx)` with `x21 = polyPtr`. -/
theorem seg2a_iter_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (idx : Nat) (hidx : idx < 3)
    (vScratch : Vec32) (bs : List (BitVec 8)) (hbs : bs.length = 320) (Rest : SepProp)
    (hpc : s.pc = b + 1324#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 idx)
    (hx22 : s.readReg64 .x22 = sp + 11856#64)
    (hx25 : s.readReg64 .x25 = sp + BitVec.ofNat 64 (3353 + 320 * idx))
    (hx27 : s.readReg64 .x27 = sp + 5680#64)
    (hv8 : (s.readVReg128 8#5).truncate 64 = (dup4hLow 3329#16).truncate 64) :
    let src := sp + BitVec.ofNat 64 (3344 + 320 * idx)
    let polyPtr := sp + BitVec.ofNat 64 (11856 + 512 * idx)
    SepWP (blkPC04.rebase b (fun _ => none)) (b + 1844#64) s
      (Poly32Mem (sp + 5680#64) vScratch ∗ (src ↦ₛ bs) ∗ memRegion polyPtr 512 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = BitVec.ofNat 64 (idx + 1) ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = polyPtr ∧
        sf.readReg64 .x22 = sp + 11856#64 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = sp + BitVec.ofNat 64 (3353 + 320 * idx) ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = sp + 5680#64 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        (sf.readVReg128 8#5).truncate 64 = (dup4hLow 3329#16).truncate 64 ∧
        (Pf ⊢ Poly32Mem (sp + 5680#64) (Vec32.ofFn (polyVecNat (decompPoly16 10 bs))) ∗
          (src ↦ₛ bs) ∗ Poly32Mem polyPtr (Vec32.ofFn (polyVecNat (decompPoly16 10 bs))) ∗ Rest)) := by
  intro src polyPtr
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  refine sepWP_seq_env hcl hro
    (seg2a_zero hb s sp (BitVec.ofNat 64 idx) (sp + BitVec.ofNat 64 (3353 + 320 * idx))
      vScratch ((src ↦ₛ bs) ∗ memRegion polyPtr 512 ∗ Rest) hpc hrun hsp hspA hx8 hx25) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx8_1, hx9_1, hx10_1, hx19_1, hfp1, hx20_1, hx22_1, hx23_1, hx24_1,
      hx25_1, hx26_1, hx27_1, hx28_1, hv8_1, rfl⟩
  have hreord1 : PolyMem (sp + 5680#64) (fun _ => 0#128) ∗
      ((src ↦ₛ bs) ∗ memRegion polyPtr 512 ∗ Rest) ⊢
      (src ↦ₛ bs) ∗ PolyMem (sp + 5680#64) (fun _ => 0#128) ∗
      (memRegion polyPtr 512 ∗ Rest) := by sep_frame
  have hx9_src : s1.readReg64 .x9 = src + BitVec.ofNat 64 (20 * 0 + 9) := by
    rw [hx9_1]; dsimp only [src]; clear * - hidx; bv_omega
  refine SepWP.weaken_pre hreord1
    (sepWP_seq_env hcl1 hro1
      (seg2a_loop hb sp src (sp + 5680#64) bs (memRegion polyPtr 512 ∗ Rest) hbs
        15 0 rfl s1 (fun _ => 0#128) hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hx9_src hx10_1 (hx27_1.trans hx27)
        (hv8_1 ▸ hv8) (fun _ hj => by omega)) ?_)
  rintro s2 P2 hpc2 hrun2 _hcl2 _hro2 ⟨hsp2, hspA2, hpres2, rfl⟩
  rcases hpres2 with ⟨hx8_2, hx19_2, hfp2, hx20_2, hx22_2, hx23_2, hx24_2,
    hx25_2, hx26_2, hx27_2, hx28_2, hv8_2⟩
  subst hbase
  generalize hpbs_def : vecRangeBytes 32 (polyVecNat (decompPoly16 10 bs)) = pbs
  have hpbs : pbs.length = 512 := by rw [← hpbs_def, vecRangeBytes_length]
  have hp5680 : PolyMem (sp + 5680#64) (polyVecNat (decompPoly16 10 bs)) = ((sp + 5680#64) ↦ₛ pbs) := by
    rw [← hpbs_def]; exact vecRangeMem_eq_pointsToBytes 32 _ _
  have hp5680_32 : ((sp + 5680#64) ↦ₛ pbs) =
      Poly32Mem (sp + 5680#64) (Vec32.ofFn (polyVecNat (decompPoly16 10 bs))) := by
    rw [← hp5680, poly32Mem_ofFn]
  have hpDst : PolyMem polyPtr (polyVecNat (decompPoly16 10 bs)) = (polyPtr ↦ₛ pbs) := by
    rw [← hpbs_def]; exact vecRangeMem_eq_pointsToBytes 32 _ _
  have hpDst_32 : (polyPtr ↦ₛ pbs) =
      Poly32Mem polyPtr (Vec32.ofFn (polyVecNat (decompPoly16 10 bs))) := by
    rw [← hpDst, poly32Mem_ofFn]
  rw [hp5680]
  have hx21_eq : (sp + 11856#64) + (BitVec.ofNat 64 idx <<< 9) = polyPtr := by
    dsimp only [polyPtr]
    rw [BitVec.add_assoc]; congr 1
    rcases (show idx = 0 ∨ idx = 1 ∨ idx = 2 by omega) with rfl | rfl | rfl <;> rfl
  have hreord2 : (src ↦ₛ bs) ∗ ((sp + 5680#64) ↦ₛ pbs) ∗ (memRegion polyPtr 512 ∗ Rest) ⊢
      memRegion ((sp + 11856#64) + (BitVec.ofNat 64 idx <<< 9)) 512 ∗
        ((sp + 5680#64) ↦ₛ pbs) ∗ ((src ↦ₛ bs) ∗ Rest) := by
    rw [hx21_eq]; sep_frame
  refine SepWP.weaken_pre hreord2 ?_
  wp_cut_codeLoaded
  wp_steps 5
  apply SepWP.done (by wp_norm_lhs) (by assumption)
  intro _hcl3
  wp_call (blk28_memcpy_04 blkPl04.base)
    ((sp + 11856#64) + (BitVec.ofNat 64 idx <<< 9), sp + 5680#64, pbs)
  rw [hx21_eq, hp5680_32, hpDst_32]
  have hsp_sf : sf.sp = sp := by simp [*]
  have hspA_sf : sf.spAligned = true := spAligned_of_chk hsp_sf hsp_chk
  have hv8_sf : (sf.readVReg128 8#5).truncate 64 = (dup4hLow 3329#16).truncate 64 := by
    have hd8 : (sf.readVReg128 8#5).truncate 64 = (s2.readVReg128 8#5).truncate 64 := by
      have hcs : calleeSavedVRegs sf = calleeSavedVRegs s2 := by simp [*]
      exact congrArg Prod.fst hcs
    rw [hd8, hv8_2, hv8_1, hv8]
  refine SepWP.done (by wp_norm_lhs) (by assumption)
    ⟨hsp_sf, hspA_sf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hv8_sf, by sep_frame⟩
  · have hidx1 : BitVec.ofNat 64 idx + 1#64 = BitVec.ofNat 64 (idx + 1) := by
      rcases (show idx = 0 ∨ idx = 1 ∨ idx = 2 by omega) with rfl | rfl | rfl <;> rfl
    rw [← hidx1]; simp [*]
  · simp [*]
  · simp [*]
  · rw [← hx21_eq]; simp [*]
  · simp [*]
  · simp [*]
  · simp [*]
  · simp [*]
  · simp [*]
  · simp [*]
  · simp [*]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg2a
