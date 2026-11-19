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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1b -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1c -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg2Simd -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode10
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.Specs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg2b

/-!
# `decapsulate_compressed_key` (`B04`) — Segment 2c (`vPoly` Decompress & Composed `seg2_ok`, `+0x1884 .. +0x199c`)
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg2c

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemCall_of_blockOk mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup4hLow pack4x32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (simdTrn1_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.Specs (
  PortableDeserializeArgs PortableDeserializePurePre deserializeChunkBytes mlkemDeserialize4RWSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize (blk25_deserialize4_RW_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (entails_sub spAligned_of_chk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure (tHatPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc (svc_simdTrn1_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem SepLoad128 SepStore128 Vec128At polyVecNat step_ldrQ128 step_stpQ128 step_strQ128
  vecRangeMem_congr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode10 (
  simdShrn16_4h simdUmlal4sLow simdUshr4s simdXtn4h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  SavedFrame04 blk04_code_eq blk04_tree_size blkLib04 blkPC04 blkPl04 blkPlaceable04 blkTree04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem (Spill21Mem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1b (cst16_3_val exec_simdMovi_2d_0)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1c (
  Seg1Spatial exec_simdDup_4h seg1_ok uHatZetaSpill21)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg2Simd (
  decompPoly16 deser4Decomp_chunk_eq exec_simdMovi_4s_8 exec_simdShrn16_4h
  exec_simdUmlal_4s_low exec_simdUshr_4s_4_op exec_simdXtn_4h uHatPoly16 vPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg2b (ct_pointsTo_split seg2b_ok)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC04 blkLib04 blkTree04 blk04_code_eq blk04_tree_size
  via_placement blkPl04 blkPlaceable04 [0x1884 → 0x1998]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl04_ρ [MlKemPlacement] (sym : String) :
    blkPl04.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp, arm64_norm, wp_norm] private theorem readReg64_orFpsr' (s : State) (fl : BitVec 32) (r : Reg) :
    (s.orFpsr fl).readReg64 r = s.readReg64 r := State.readReg64_orFpsr s fl r
@[simp, arm64_norm, wp_norm] private theorem readVReg128_orFpsr' (s : State) (fl : BitVec 32) (r : BitVec 5) :
    (s.orFpsr fl).readVReg128 r = s.readVReg128 r := State.readVReg128_orFpsr s fl r
@[simp, arm64_norm, wp_norm] private theorem status_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).status = s.status := by cases s; rfl
@[simp, arm64_norm, wp_norm] private theorem pc_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).pc = s.pc := by cases s; rfl
@[simp, arm64_norm, wp_norm] private theorem sp_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).sp = s.sp := by cases s; rfl
@[simp, arm64_norm, wp_norm] private theorem spAligned_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).spAligned = s.spAligned := by cases s; rfl
@[simp, arm64_norm, wp_norm] private theorem pstate_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).pstate = s.pstate := by cases s; rfl
@[simp, arm64_norm, wp_norm] private theorem mem_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).mem = s.mem := by cases s; rfl

private theorem blk25_deserialize4_04 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC04.rebase b (fun _ => none)) (mlkemMpl.base 25)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemDeserialize4RWSpec) :=
  mlkemCall_of_blockOk (blkPC04.rebase b (fun _ => none)) blk25_deserialize4_RW_ok

private theorem deserializeChunkBytes_len_4 (bs : List (BitVec 8)) :
    (deserializeChunkBytes 4 bs).length = 32 := by simp [deserializeChunkBytes]

attribute [local irreducible]
  blkPC04 polyVecNat decompPoly16 dup4hLow deserializeChunkBytes
  simdXtn4h simdShrn16_4h simdUmlal4sLow simdUshr4s simdTrn1_8h

attribute [local wp_norm ↓ high]
  exec_simdMovi_2d_0 exec_simdDup_4h exec_simdMovi_4s_8
  exec_simdXtn_4h exec_simdShrn16_4h exec_simdUmlal_4s_low
  exec_simdUshr_4s_4_op svc_simdTrn1_8h

attribute [local simp] PortableDeserializePurePre

private theorem SepStore128.polyMem {k : Nat} {ea ptr : BitVec 64} {f : Nat → BitVec 128}
    {val : BitVec 128} (hk : k < 32) (ha : ptr + BitVec.ofNat 64 (16 * k) = ea) :
    SepStore128 ea val (PolyMem ptr f) (PolyMem ptr (Function.update f k val)) :=
  SepStore128.vecRange (n := 32) hk ha

private theorem polyMem_congr {ptr : BitVec 64} {f g : Nat → BitVec 128}
    (h : ∀ i, i < 32 → f i = g i) : PolyMem ptr f = PolyMem ptr g :=
  vecRangeMem_congr h

private theorem update2_prefix {f g : Nat → BitVec 128} {k : Nat}
    (hf : ∀ j, j < 2 * k → f j = g j) :
    ∀ j, j < 2 * (k + 1) →
      Function.update (Function.update f (2 * k) (g (2 * k))) (2 * k + 1) (g (2 * k + 1)) j =
        g j := by
  intro j hj
  by_cases h1 : j = 2 * k + 1
  · subst h1; simp
  · rw [Function.update_of_ne h1]
    by_cases h0 : j = 2 * k
    · subst h0; simp
    · rw [Function.update_of_ne h0]; exact hf j (by omega)

private theorem sepWP_elim_polyMem {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ f : Nat → BitVec 128, SepWP prog target s (PolyMem a f ∗ R0) post) :
    SepWP prog target s (memRegion a 512 ∗ R0) post :=
  LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem.SepWP.of_memRegion_vecRangeMem
    (n := 32) (ptr := a) (F := R0) (by decide) rfl h

private theorem of_pointsToBytes_readLE128 {ea ptr : BitVec 64} {bs : List (BitVec 8)}
    {off : Nat} {P F : SepProp}
    (h : P = (ptr ↦ₛ bs) ∗ F) (hoff : off + 16 ≤ bs.length)
    (ha : ptr + BitVec.ofNat 64 off = ea) :
    SepLoad128 ea P (ByteSlice.readLE bs (off + 8) 8 ++ ByteSlice.readLE bs off 8) := by
  refine ⟨?_, ?_⟩
  · rw [show (ByteSlice.readLE bs (off + 8) 8 ++ ByteSlice.readLE bs off 8).extractLsb' 0 64 =
      ByteSlice.readLE bs off 8 by bv_bits]
    exact SepLoad64.of_pointsToBytes_readLE h (by omega) ha
  · rw [show (ByteSlice.readLE bs (off + 8) 8 ++ ByteSlice.readLE bs off 8).extractLsb' 64 64 =
      ByteSlice.readLE bs (off + 8) 8 by bv_bits]
    exact SepLoad64.of_pointsToBytes_readLE h (by omega) (by rw [← ha]; clear * -; bv_omega)

attribute [local irreducible] ByteSlice.readLE

local macro "step_zero_q19168 " k:num : tactic => `(tactic| (
  apply step_strQ128
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · first | rfl | wp_norm_lhs | wp_norm_goal |
      simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, *]
  · wp_norm_lhs
  · wp_norm_lhs
  · apply SepStore128.left
    refine SepStore128.polyMem (k := $k) (by decide) (by clear * -; bv_omega)
  · wp_norm_lhs
  intro _))

private theorem seg2c_init [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + 6276#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + 6432#64) s
      (memRegion (sp + 19168#64) 512 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x20 = sp + 19184#64 ∧
        sf.readReg64 .x21 = 960#64 ∧
        sf.readReg64 .x22 = sp + 3344#64 ∧
        sf.readReg64 .x23 = 3329#64 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        (Pf ⊢ PolyMem (sp + 19168#64) (fun _ => 0#128) ∗ Rest)) := by
  subst hbase; subst hsp
  have hsp_chk : (s.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hspA
  sep_frame_apply (sepWP_elim_polyMem (a := s.sp + 19168#64)); intro f0
  wp_steps 7
  step_zero_q19168 31; step_zero_q19168 30; step_zero_q19168 29; step_zero_q19168 28
  step_zero_q19168 27; step_zero_q19168 26; step_zero_q19168 25; step_zero_q19168 24
  step_zero_q19168 23; step_zero_q19168 22; step_zero_q19168 21; step_zero_q19168 20
  step_zero_q19168 19; step_zero_q19168 18; step_zero_q19168 17; step_zero_q19168 16
  step_zero_q19168 15; step_zero_q19168 14; step_zero_q19168 13; step_zero_q19168 12
  step_zero_q19168 11; step_zero_q19168 10; step_zero_q19168 9; step_zero_q19168 8
  step_zero_q19168 7; step_zero_q19168 6; step_zero_q19168 5; step_zero_q19168 4
  step_zero_q19168 3; step_zero_q19168 2; step_zero_q19168 1; step_zero_q19168 0
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp, spAligned_of_chk (by simp) hsp_chk,
      by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, ?_⟩
  rw [polyMem_congr (g := fun _ => 0#128) (fun i hi => by
    match i with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
    | _ + 32 => omega)]
  sep_frame

private theorem pointsToBytes_chunk8 {ptr : BitVec 64} {bs : List (BitVec 8)} {c : Nat}
    (hbs : bs.length = 128) (hc : c < 16) :
    (ptr ↦ₛ bs) =
      (ptr ↦ₛ bs.take (8 * c)) ∗
      ((ptr + BitVec.ofNat 64 (8 * c)) ↦ₛ (bs.drop (8 * c)).take 8) ∗
      ((ptr + BitVec.ofNat 64 (8 * (c + 1))) ↦ₛ bs.drop (8 * (c + 1))) := by
  have hl1 : (bs.take (8 * c)).length = 8 * c := by simp [hbs]; omega
  have hl2 : ((bs.drop (8 * c)).take 8).length = 8 := by simp [hbs]; omega
  have hdrop : (bs.drop (8 * c)).drop 8 = bs.drop (8 * (c + 1)) := by
    rw [List.drop_drop, show 8 * c + 8 = 8 * (c + 1) by omega]
  have hadd : (ptr + BitVec.ofNat 64 (8 * c)) + BitVec.ofNat 64 8 =
      ptr + BitVec.ofNat 64 (8 * (c + 1)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 8 * c + 8 = 8 * (c + 1) by omega]
  conv_lhs => rw [← List.take_append_drop (8 * c) bs]
  rw [pointsToBytes_append, hl1]
  conv in (bs.drop (8 * c)) => rw [← List.take_append_drop 8 (bs.drop (8 * c))]
  rw [pointsToBytes_append, hl2, hdrop, hadd]

private theorem sepWP_seq_codeLoaded [MlKemPlacement]
    {prog : Program} {mid target : BitVec 64} {s : State} {P : SepProp}
    {post1 post2 : State → SepProp → Prop}
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (h1 : SepWP prog mid s P post1)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      mlkemMultiLib.CodeLoaded mlkemMpl sm.mem → post1 sm Pm → SepWP prog target sm Pm post2) :
    SepWP prog target s P post2 :=
  SepWP.seq
    (SepWP.mono_frozen
      (post' := fun sm Pm => mlkemMultiLib.CodeLoaded mlkemMpl sm.mem ∧ post1 sm Pm)
      (Φ := fun m => mlkemMultiLib.CodeLoaded mlkemMpl m)
      (fun _ _ hc hkf => hc.of_keepsFrozen hkf) hcl h1 (fun _ _ _ _ hc hp1 => ⟨hc, hp1⟩))
    (fun sm Pm hpc hrun ⟨hc, hp1⟩ => h2 sm Pm hpc hrun hc hp1)

private theorem seg2c_cond_eq : ∀ k : Fin 16,
    ConditionHolds .NE (subsPState64 (BitVec.ofNat 64 (960 + 8 * k.val) + 8#64) 1088#64) =
      decide (k.val < 15) := by decide +kernel

private theorem seg2c_loop_tail [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl04 b)
    (s : State) {c : Nat} (hc : c < 16) (P : SepProp)
    (hpc : s.pc = b + 6552#64) (hrun : s.status = .Running)
    (hpst : s.pstate = subsPState64 (BitVec.ofNat 64 (960 + 8 * c) + 8#64) 1088#64) :
    SepWP (blkPC04.rebase b (fun _ => none))
      (if c < 15 then b + 6432#64 else b + 6556#64) s P
      (fun sf Pf => sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧ sf.regs = s.regs ∧ Pf = P) := by
  have _ : b = blkPl04.base := hb
  set off : BitVec 64 := BitVec.ofInt 64 (-120)
  have hf : (blkPC04.rebase b (fun _ => none)).fetch (b + 6552#64) = some (.bCond .NE off) := by wp_norm_lhs
  have hpc_tgt : (b + 6552#64) + off = b + 6432#64 := by dsimp only [off]; clear * -; bv_omega
  have hpc_fall : (b + 6552#64) + 4#64 = b + 6556#64 := by clear * -; bv_omega
  rcases s with ⟨regs, vregs, sp, pc, ps, mem, tpidr, fpsr, brkS, brk, fs, orc, oidx, excls, tr, st, sym, sigA, sigS, sigM, sigP, phys⟩
  dsimp only at hpc hrun hpst ⊢; subst hpc
  let s0 : State := ⟨regs, vregs, sp, b + 6552#64, ps, mem, tpidr, fpsr, brkS, brk, fs, orc, oidx, excls, tr, st, sym, sigA, sigS, sigM, sigP, phys⟩
  have hcond_eq : ConditionHolds .NE ps = decide (c < 15) := by rw [hpst]; exact seg2c_cond_eq ⟨c, hc⟩
  by_cases hc15 : c < 15
  · simp only [hc15, decide_true, ↓reduceIte] at hcond_eq ⊢
    refine SepWP.step_pure (s' := s0.setPC (b + 6432#64)) rfl hrun hf ?_ (by simp [s0, State.setPC]) ?_
    · simp only [s0, Program.evalInst, State.setPC, execInstWithSvc, hcond_eq, ↓reduceIte, hpc_tgt]
    · exact SepWP.done (by simp [s0, State.setPC]) (by simp [s0, State.setPC, hrun]) (by simp [s0, State.setPC, State.spAligned])
  · simp only [hc15, decide_false, ↓reduceIte] at hcond_eq ⊢
    refine SepWP.step_pure (s' := s0.setPC (b + 6556#64)) rfl hrun hf ?_ (by simp [s0, State.setPC]) ?_
    · simp only [s0, Program.evalInst, State.setPC, State.advancePC, execInstWithSvc, hcond_eq, Bool.false_eq_true, ↓reduceIte, hpc_fall]
    · exact SepWP.done (by simp [s0, State.setPC]) (by simp [s0, State.setPC, hrun]) (by simp [s0, State.setPC, State.spAligned])

private theorem seg2c_iter_simd [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl04 b)
    (sp : BitVec 64) (ct2 buf : List (BitVec 8)) (Rest : SepProp)
    (hct2 : ct2.length = 128) {c : Nat} (hc16 : c < 16)
    (hbuf : buf = deserializeChunkBytes 4 ((ct2.drop (8 * c)).take 8))
    (s : State) (f : Nat → BitVec 128)
    (hpc : s.pc = b + 6460#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = sp + BitVec.ofNat 64 (19184 + 32 * c))
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 (960 + 8 * c))
    (hx22 : s.readReg64 .x22 = sp + 3344#64)
    (hx23 : s.readReg64 .x23 = 3329#64)
    (hv0 : s.readVReg128 0#5 = ByteSlice.readLE buf 8 8 ++ ByteSlice.readLE buf 0 8)
    (hv1 : s.readVReg128 1#5 = ByteSlice.readLE buf 24 8 ++ ByteSlice.readLE buf 16 8) :
    SepWP (blkPC04.rebase b (fun _ => none))
      (if c < 15 then b + 6432#64 else b + 6556#64) s
      (PolyMem (sp + 19168#64) f ∗
        (((sp + 11856#64) ↦ₛ buf) ∗ stackAt sp 1136 ∗ ((sp + 4304#64) ↦ₛ ct2) ∗ Rest))
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x20 = sp + BitVec.ofNat 64 (19184 + 32 * (c + 1)) ∧
        sf.readReg64 .x21 = BitVec.ofNat 64 (960 + 8 * (c + 1)) ∧
        sf.readReg64 .x22 = sp + 3344#64 ∧
        sf.readReg64 .x23 = 3329#64 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        (Pf ⊢ stackAt sp 1136 ∗ memRegion (sp + 11856#64) 32 ∗
          ((sp + 4304#64) ↦ₛ ct2) ∗
          PolyMem (sp + 19168#64)
            (Function.update
              (Function.update f (2 * c) (polyVecNat (vPoly16 ct2) (2 * c)))
              (2 * c + 1) (polyVecNat (vPoly16 ct2) (2 * c + 1))) ∗ Rest)) := by
  have _ : b = blkPl04.base := hb
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  have hbuf_len : buf.length = 32 := by rw [hbuf]; exact deserializeChunkBytes_len_4 _
  wp_steps 21
  have ⟨hq0, hq1⟩ := deser4Decomp_chunk_eq ct2 c hc16 hct2
  refine step_stpQ128 (wb := none)
    (ea := sp + 19168#64 + BitVec.ofNat 64 (16 * (2 * c)))
    (ea16 := sp + 19168#64 + BitVec.ofNat 64 (16 * (2 * c + 1)))
    (v1 := polyVecNat (vPoly16 ct2) (2 * c))
    (v2 := polyVecNat (vPoly16 ct2) (2 * c + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx20]; clear * - hc16; bv_omega)
    (by clear * - hc16; bv_omega)
    (by simp; exact hq0) (by simp; exact hq1)
    (SepStore128.left (SepStore128.polyMem (k := 2 * c) (by omega) rfl))
    (SepStore128.left (SepStore128.polyMem (k := 2 * c + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  intro _m'
  have hbuf_reg : ((sp + 11856#64) ↦ₛ buf) ⊢ memRegion (sp + 11856#64) 32 := by
    simpa [hbuf_len] using pointsToBytes_entails_memRegion (sp + 11856#64) buf
  wp_step
  have hrr {s1 s2 : State} (hs : s1.sp = s2.sp) (hr : s1.regs = s2.regs) (r : Reg) :
      s1.readReg64 r = s2.readReg64 r := by cases r <;> simp [State.readReg64, hs, hr]
  refine SepWP.mono (seg2c_loop_tail hb _ hc16 _ (by wp_norm_lhs) (by simp [hrun]) (by simp)) ?_
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hregs_f, rfl⟩
  refine ⟨hsp_f.trans (by simp [hsp]), hspA_f.trans (by simpa [State.spAligned, hsp] using hsp_chk),
    (hrr hsp_f hregs_f .fp).trans (by simp),
    (hrr hsp_f hregs_f .x20).trans (by simp; clear * - hc16; bv_omega),
    (hrr hsp_f hregs_f .x21).trans (by simp; clear * - hc16; bv_omega),
    (hrr hsp_f hregs_f .x22).trans (by simp [hx22]), (hrr hsp_f hregs_f .x23).trans (by simp [hx23]),
    (hrr hsp_f hregs_f .x26).trans (by simp), (hrr hsp_f hregs_f .x27).trans (by simp),
    (hrr hsp_f hregs_f .x28).trans (by simp), entails_sub hbuf_reg (by sep_frame) (by sep_frame)⟩

private theorem seg2c_iter [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (sp : BitVec 64) (ct2 : List (BitVec 8)) (Rest : SepProp)
    (hct2 : ct2.length = 128) {c : Nat} (hc16 : c < 16)
    (s : State) (f : Nat → BitVec 128)
    (hpc : s.pc = b + 6432#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hx20 : s.readReg64 .x20 = sp + BitVec.ofNat 64 (19184 + 32 * c))
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 (960 + 8 * c))
    (hx22 : s.readReg64 .x22 = sp + 3344#64)
    (hx23 : s.readReg64 .x23 = 3329#64) :
    SepWP (blkPC04.rebase b (fun _ => none))
      (if c < 15 then b + 6432#64 else b + 6556#64) s
      (stackAt sp 1136 ∗ memRegion (sp + 11856#64) 32 ∗
        ((sp + 4304#64) ↦ₛ ct2) ∗ PolyMem (sp + 19168#64) f ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x20 = sp + BitVec.ofNat 64 (19184 + 32 * (c + 1)) ∧
        sf.readReg64 .x21 = BitVec.ofNat 64 (960 + 8 * (c + 1)) ∧
        sf.readReg64 .x22 = sp + 3344#64 ∧
        sf.readReg64 .x23 = 3329#64 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        (Pf ⊢ stackAt sp 1136 ∗ memRegion (sp + 11856#64) 32 ∗
          ((sp + 4304#64) ↦ₛ ct2) ∗
          PolyMem (sp + 19168#64)
            (Function.update
              (Function.update f (2 * c) (polyVecNat (vPoly16 ct2) (2 * c)))
              (2 * c + 1) (polyVecNat (vPoly16 ct2) (2 * c + 1))) ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  set chunk := (ct2.drop (8 * c)).take 8
  have hchunk_len : chunk.length = 8 := by simp [chunk, hct2]; omega
  have haddr_out : sp + 8192#64 + 3664#64 = sp + 11856#64 := by clear * -; bv_omega
  have haddr_in : (sp + 3344#64) + BitVec.ofNat 64 (960 + 8 * c) =
      (sp + 4304#64) + BitVec.ofNat 64 (8 * c) := by clear * - hc16; bv_omega
  refine SepWP.weaken_pre
    (show stackAt sp 1136 ∗ memRegion (sp + 11856#64) 32 ∗
        ((sp + 4304#64) ↦ₛ ct2) ∗ PolyMem (sp + 19168#64) f ∗ Rest ⊢
      (memRegion (sp - 1136#64) 1120 ∗ stackAt sp 16) ∗ memRegion (sp + 11856#64) 32 ∗
        (((sp + 4304#64) ↦ₛ ct2.take (8 * c)) ∗
          (((sp + 4304#64) + BitVec.ofNat 64 (8 * c)) ↦ₛ chunk) ∗
          (((sp + 4304#64) + BitVec.ofNat 64 (8 * (c + 1))) ↦ₛ ct2.drop (8 * (c + 1)))) ∗
        PolyMem (sp + 19168#64) f ∗ Rest by
      rw [ProofLib.stackAt_shrink sp 1136 16 (by decide), pointsToBytes_chunk8 hct2 hc16]
      exact Entails.refl _) ?_
  wp_cut_codeLoaded
  wp_steps 4
  apply SepWP.done (by wp_norm_lhs) (by assumption)
  intro _hcl_pre
  wp_call (blk25_deserialize4_04 blkPl04.base)
    (⟨sp + 11856#64, (sp + 4304#64) + BitVec.ofNat 64 (8 * c), chunk⟩ : PortableDeserializeArgs)
  have hsp_sf : sf.sp = sp := by simp [*]
  have hspA_sf : sf.spAligned = true := spAligned_of_chk hsp_sf hsp_chk
  set buf := deserializeChunkBytes 4 chunk
  refine step_ldrQ128 (pc := blkPl04.base + 6452#64) (wb := none) (ea := sp + 11856#64)
    (v := ByteSlice.readLE buf 8 8 ++ ByteSlice.readLE buf 0 8)
    hpc_sf hrun_sf (by wp_norm_lhs)
    (by simpa [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg] using hspA_sf)
    (by simp [evalAddrMode, hsp_sf])
    (of_pointsToBytes_readLE128 (ptr := sp + 11856#64) (bs := buf) (off := 0)
      rfl (by rw [show buf.length = 32 from deserializeChunkBytes_len_4 _]; omega) (by clear * -; bv_omega))
    (by wp_norm_lhs) ?_
  refine step_ldrQ128 (pc := blkPl04.base + 6456#64) (wb := none) (ea := sp + 11872#64)
    (v := ByteSlice.readLE buf 24 8 ++ ByteSlice.readLE buf 16 8)
    (by wp_norm_lhs) (by simp [hrun_sf]) (by wp_norm_lhs)
    (by simpa [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp_sf]
      using hsp_chk)
    (by simp [evalAddrMode, hsp_sf])
    (of_pointsToBytes_readLE128 (ptr := sp + 11856#64) (bs := buf) (off := 16)
      rfl (by rw [show buf.length = 32 from deserializeChunkBytes_len_4 _]) (by clear * -; bv_omega))
    (by wp_norm_lhs) ?_
  refine SepWP.weaken_pre
    (show _ ⊢ PolyMem (sp + 19168#64) f ∗
        (((sp + 11856#64) ↦ₛ buf) ∗ stackAt sp 1136 ∗ ((sp + 4304#64) ↦ₛ ct2) ∗ Rest) by
      rw [ProofLib.stackAt_shrink sp 1136 16 (by decide), pointsToBytes_chunk8 hct2 hc16]
      sep_frame) ?_
  refine SepWP.mono
    (seg2c_iter_simd hb sp ct2 buf Rest hct2 hc16 rfl _ f
      (by wp_norm_lhs) (by simp [hrun_sf]) (by simp [hsp_sf])
      (by simpa [State.spAligned, hsp_sf] using hsp_chk)
      (by simp [*]) (by simp [*]) (by simp [*]) (by simp [*])
      (by simp) (by simp)) ?_
  rintro sf2 Pf2 _ _ ⟨hsp2, hspA2, hfp2, hx20_2, hx21_2, hx22_2, hx23_2, hx26_2, hx27_2, hx28_2, hPf2⟩
  exact ⟨hsp2, hspA2, hfp2.trans (by simp [*]), hx20_2, hx21_2, hx22_2, hx23_2,
    hx26_2.trans (by simp [*]), hx27_2.trans (by simp [*]), hx28_2.trans (by simp [*]), hPf2⟩

private theorem seg2c_loop [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (sp : BitVec 64) (ct2 : List (BitVec 8)) (Rest : SepProp) (hct2 : ct2.length = 128) :
    ∀ (rem c : Nat), c + 1 + rem = 16 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + 6432#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem →
      s.readReg64 .x20 = sp + BitVec.ofNat 64 (19184 + 32 * c) →
      s.readReg64 .x21 = BitVec.ofNat 64 (960 + 8 * c) →
      s.readReg64 .x22 = sp + 3344#64 → s.readReg64 .x23 = 3329#64 →
      (∀ j, j < 2 * c → f j = polyVecNat (vPoly16 ct2) j) →
      SepWP (blkPC04.rebase b (fun _ => none)) (b + 6556#64) s
        (stackAt sp 1136 ∗ memRegion (sp + 11856#64) 32 ∗ ((sp + 4304#64) ↦ₛ ct2) ∗ PolyMem (sp + 19168#64) f ∗ Rest)
        (fun sf Pf => sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = s.readReg64 .fp ∧
          sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
          sf.readReg64 .x28 = s.readReg64 .x28 ∧
          (Pf ⊢ stackAt sp 1136 ∗ memRegion (sp + 11856#64) 32 ∗ ((sp + 4304#64) ↦ₛ ct2) ∗
            PolyMem (sp + 19168#64) (polyVecNat (vPoly16 ct2)) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro c hc15 s f hpc hrun hsp hspA hcl hx20 hx21 hx22 hx23 hf
    have hc : c = 15 := by omega
    subst hc
    have hiter := seg2c_iter hb hbase sp ct2 Rest hct2 (c := 15) (by decide)
      s f hpc hrun hsp hspA hcl hx20 hx21 hx22 hx23
    simp only [Nat.lt_irrefl, ↓reduceIte] at hiter
    refine SepWP.mono hiter ?_
    rintro sf Pf _ _ ⟨hsp_f, hspA_f, hfp_f, _, _, _, _, hx26_f, hx27_f, hx28_f, hPf⟩
    have hf32 := update2_prefix (k := 15) hf
    exact ⟨hsp_f, hspA_f, hfp_f, hx26_f, hx27_f, hx28_f,
      Entails.trans hPf (by rw [polyMem_congr hf32]; exact Entails.refl _)⟩
  | succ rem' ih =>
    intro c hc_rem s f hpc hrun hsp hspA hcl hx20 hx21 hx22 hx23 hf
    have hc15 : c < 15 := by omega
    have hiter := seg2c_iter hb hbase sp ct2 Rest hct2 (c := c) (by omega)
      s f hpc hrun hsp hspA hcl hx20 hx21 hx22 hx23
    simp only [hc15, ↓reduceIte] at hiter
    refine sepWP_seq_codeLoaded hcl hiter ?_
    rintro sm Pm hpc_m hrun_m hcl_m
      ⟨hsp_m, hspA_m, hfp_m, hx20_m, hx21_m, hx22_m, hx23_m, hx26_m, hx27_m, hx28_m, hPm⟩
    refine SepWP.weaken_pre hPm
      (SepWP.mono
        (ih (c + 1) (by omega) sm _ hpc_m hrun_m hsp_m hspA_m hcl_m
          hx20_m hx21_m hx22_m hx23_m (update2_prefix hf)) ?_)
    rintro sf Pf _ _ ⟨hsp_f, hspA_f, hfp_f, hx26_f, hx27_f, hx28_f, hPf⟩
    exact ⟨hsp_f, hspA_f, hfp_f.trans hfp_m, hx26_f.trans hx26_m,
      hx27_f.trans hx27_m, hx28_f.trans hx28_m, hPf⟩

/-- Segment 2c contract (`vPoly` `B25` + `decompress_4`, `+0x1884 → +0x199c`). -/
theorem seg2c_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (ct2 : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 6276#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hct2 : ct2.length = 128) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + 6556#64) s
      (stackAt sp 1136 ∗ memRegion (sp + 11856#64) 32 ∗
        ((sp + 4304#64) ↦ₛ ct2) ∗ memRegion (sp + 19168#64) 512 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        (Pf ⊢ stackAt sp 1136 ∗ memRegion (sp + 11856#64) 32 ∗
          ((sp + 4304#64) ↦ₛ ct2) ∗
          PolyMem (sp + 19168#64) (polyVecNat (vPoly16 ct2)) ∗ Rest)) := by
  have hP0 : stackAt sp 1136 ∗ memRegion (sp + 11856#64) 32 ∗
      ((sp + 4304#64) ↦ₛ ct2) ∗ memRegion (sp + 19168#64) 512 ∗ Rest ⊢
      memRegion (sp + 19168#64) 512 ∗
      (stackAt sp 1136 ∗ memRegion (sp + 11856#64) 32 ∗ ((sp + 4304#64) ↦ₛ ct2) ∗ Rest) := by
    sep_frame
  refine SepWP.weaken_pre hP0 (sepWP_seq_codeLoaded hcl (seg2c_init hb hbase s sp _ hpc hrun hsp hspA) ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 ⟨hsp1, hspA1, hfp1, hx20_1, hx21_1, hx22_1, hx23_1, hx26_1, hx27_1, hx28_1, hP1⟩
  have hP1' : P1 ⊢ stackAt sp 1136 ∗ memRegion (sp + 11856#64) 32 ∗
      ((sp + 4304#64) ↦ₛ ct2) ∗ PolyMem (sp + 19168#64) (fun _ => 0#128) ∗ Rest :=
    Entails.trans hP1 (by sep_frame)
  refine SepWP.weaken_pre hP1'
    (SepWP.mono
      (seg2c_loop hb hbase sp ct2 Rest hct2 15 0 rfl s1 (fun _ => 0#128)
        hpc1 hrun1 hsp1 hspA1 hcl1 hx20_1 hx21_1 hx22_1 hx23_1 (by omega)) ?_)
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hfp_f, hx26_f, hx27_f, hx28_f, hPf⟩
  exact ⟨hsp_f, hspA_f, hfp_f.trans hfp1, hx26_f.trans hx26_1,
    hx27_f.trans hx27_1, hx28_f.trans hx28_1, hPf⟩

@[expose] def Seg2Spatial (s0 : State) (ret dkA ct1A ct2A : BitVec 64)
    (dk ct1 ct2 : List (BitVec 8)) (F : SepProp) : SepProp :=
  let sp := s0.sp - 25824#64
  stackAt sp 1136 ∗ SavedFrame04 s0.sp s0 ∗ memRegion sp 136 ∗ ((sp + 136#64) ↦₆₄ ret) ∗
  memRegion (sp + 144#64) 56 ∗ ((sp + 200#64) ↦₆₄ (sp + 22664#64)) ∗ memRegion (sp + 208#64) 1632 ∗
  ((sp + 1840#64) ↦₆₄ (dkA + 2336#64)) ∗ memRegion (sp + 1848#64) 8 ∗
  ((sp + 1856#64) ↦₆₄ (dkA + 2368#64)) ∗ memRegion (sp + 1864#64) 8 ∗ ((sp + 1872#64) ↦₆₄ dkA) ∗
  memRegion (sp + 1880#64) 8 ∗ ((sp + 1888#64) ↦₆₄ (dkA + 384#64)) ∗ memRegion (sp + 1896#64) 8 ∗
  Vec128At (sp + 1904#64) cst16_3_val ∗ Spill21Mem (sp + 1920#64) uHatZetaSpill21 ∗
  ((sp + 2256#64) ↦ₛ (ct1 ++ ct2)) ∗ ((sp + 3344#64) ↦ₛ (ct1 ++ ct2)) ∗ memRegion (sp + 4432#64) 1248 ∗
  PolyMem (sp + 5680#64) (polyVecNat (uHatPoly16 ct1 0)) ∗
  PolyMem (sp + 6192#64) (polyVecNat (uHatPoly16 ct1 1)) ∗
  PolyMem (sp + 6704#64) (polyVecNat (uHatPoly16 ct1 2)) ∗
  memRegion (sp + 7216#64) 11952 ∗ PolyMem (sp + 19168#64) (polyVecNat (vPoly16 ct2)) ∗
  memRegion (sp + 19680#64) 2720 ∗
  PolyMem (sp + 22400#64) (polyVecNat (tHatPoly16 (dk.take 384))) ∗
  PolyMem (sp + 22912#64) (polyVecNat (tHatPoly16 ((dk.drop 384).take 384))) ∗
  PolyMem (sp + 23424#64) (polyVecNat (tHatPoly16 ((dk.drop 768).take 384))) ∗
  memRegion (sp + 23936#64) 1728 ∗ (dkA ↦ₛ dk) ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ F

private theorem memRegion_17968_seg2_split (sp : BitVec 64) :
    memRegion (sp + 4432#64) 17968 =
      memRegion (sp + 4432#64) 1248 ∗ memRegion (sp + 5680#64) 1536 ∗
      memRegion (sp + 7216#64) 4640 ∗ memRegion (sp + 11856#64) 1536 ∗
      memRegion (sp + 13392#64) 5776 ∗ memRegion (sp + 19168#64) 512 ∗
      memRegion (sp + 19680#64) 2720 := by
  rw [memRegion_split' (b := sp + 4432#64) (b' := sp + 5680#64) (n := 1248) (k := (16720 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 5680#64) (b' := sp + 7216#64) (n := 1536) (k := (15184 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 7216#64) (b' := sp + 11856#64) (n := 4640) (k := (10544 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 11856#64) (b' := sp + 13392#64) (n := 1536) (k := (9008 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 13392#64) (b' := sp + 19168#64) (n := 5776) (k := (3232 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 19168#64) (b' := sp + 19680#64) (n := 512) (k := (2720 : Nat)) rfl (by bv_omega) (by decide)]

private theorem memRegion_11952_seg2_split (sp : BitVec 64) :
    memRegion (sp + 7216#64) 11952 =
      memRegion (sp + 7216#64) 4640 ∗ memRegion (sp + 11856#64) 32 ∗
      memRegion (sp + 11888#64) 1504 ∗ memRegion (sp + 13392#64) 5776 := by
  rw [memRegion_split' (b := sp + 7216#64) (b' := sp + 11856#64) (n := 4640) (k := (7312 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 11856#64) (b' := sp + 11888#64) (n := 32) (k := (7280 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 11888#64) (b' := sp + 13392#64) (n := 1504) (k := (5776 : Nat)) rfl (by bv_omega) (by decide)]

/-- Composed Segments 1–2 contract (`+0x0000 → +0x199c`). -/
theorem seg2_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s0 : State) (ret dkA ct1A ct2A : BitVec 64)
    (dk ct1 ct2 : List (BitVec 8)) (F : SepProp)
    (hpc : s0.pc = b) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s0.mem) (hro : MlKemRoOk mlkemMpl s0.mem)
    (hx0 : s0.readReg64 .x0 = ret) (hx1 : s0.readReg64 .x1 = dkA)
    (hx2 : s0.readReg64 .x2 = ct1A) (hx3 : s0.readReg64 .x3 = ct2A)
    (hdk : dk.length = 2400) (hct1 : ct1.length = 960) (hct2 : ct2.length = 128) :
    let sp := s0.sp - 25824#64
    SepWP (blkPC04.rebase b (fun _ => none)) (b + 6556#64) s0
      (stackAt s0.sp 26960 ∗ (dkA ↦ₛ dk) ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ F)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s0.sp - 96#64 ∧
        sf.readReg64 .x26 = sp + 20704#64 ∧
        sf.readReg64 .x28 = sp + 20968#64 ∧
        (Pf ⊢ Seg2Spatial s0 ret dkA ct1A ct2A dk ct1 ct2 F)) := by
  intro sp
  refine sepWP_seq_env hcl hro
    (seg1_ok hb hbase s0 ret dkA ct1A ct2A dk ct1 ct2 F hpc hrun hsp0 hcl hro hx0 hx1 hx2 hx3 hdk hct1 hct2) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hfp1, hx8_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hv8_1, _, hP1⟩
  set R2b := stackAt sp 1136 ∗ SavedFrame04 s0.sp s0 ∗ memRegion sp 136 ∗ ((sp + 136#64) ↦₆₄ ret) ∗
    memRegion (sp + 144#64) 56 ∗ ((sp + 200#64) ↦₆₄ (sp + 22664#64)) ∗ memRegion (sp + 208#64) 1632 ∗
    ((sp + 1840#64) ↦₆₄ (dkA + 2336#64)) ∗ memRegion (sp + 1848#64) 8 ∗
    ((sp + 1856#64) ↦₆₄ (dkA + 2368#64)) ∗ memRegion (sp + 1864#64) 8 ∗ ((sp + 1872#64) ↦₆₄ dkA) ∗
    memRegion (sp + 1880#64) 8 ∗ ((sp + 1888#64) ↦₆₄ (dkA + 384#64)) ∗ memRegion (sp + 1896#64) 8 ∗
    Vec128At (sp + 1904#64) cst16_3_val ∗ ((sp + 2256#64) ↦ₛ (ct1 ++ ct2)) ∗
    memRegion (sp + 4432#64) 1248 ∗ memRegion (sp + 7216#64) 4640 ∗ memRegion (sp + 13392#64) 5776 ∗
    memRegion (sp + 19168#64) 512 ∗ memRegion (sp + 19680#64) 2720 ∗
    PolyMem (sp + 22400#64) (polyVecNat (tHatPoly16 (dk.take 384))) ∗
    PolyMem (sp + 22912#64) (polyVecNat (tHatPoly16 ((dk.drop 384).take 384))) ∗
    PolyMem (sp + 23424#64) (polyVecNat (tHatPoly16 ((dk.drop 768).take 384))) ∗
    memRegion (sp + 23936#64) 1728 ∗ (dkA ↦ₛ dk) ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ F
  have hP1' : P1 ⊢ Spill21Mem (sp + 1920#64) uHatZetaSpill21 ∗ ((sp + 3344#64) ↦ₛ (ct1 ++ ct2)) ∗
      memRegion (sp + 5680#64) 1536 ∗ memRegion (sp + 11856#64) 1536 ∗ R2b := by
    refine Entails.trans hP1 ?_
    dsimp only [Seg1Spatial, R2b, sp]
    rw [memRegion_17968_seg2_split (s0.sp - 25824#64)]; sep_frame
  refine SepWP.weaken_pre hP1'
    (sepWP_seq_codeLoaded hcl1
      (seg2b_ok hb hbase s1 sp ct1 ct2 R2b hpc1 hrun1 hsp1 hspA1 hcl1 hro1
        hx8_1 hx20_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 (by rw [hv8_1]) hct1) ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 ⟨hsp2, hspA2, hfp2, hx26_2, _, hx28_2, hP2⟩
  have h1536_split : memRegion (sp + 11856#64) 1536 =
      memRegion (sp + 11856#64) 32 ∗ memRegion (sp + 11888#64) 1504 :=
    memRegion_split' (b := sp + 11856#64) (b' := sp + 11888#64) (n := 32) (k := (1504 : Nat)) rfl (by bv_omega) (by decide)
  have hct_3344 : ((sp + 3344#64) ↦ₛ (ct1 ++ ct2)) =
      ((sp + 3344#64) ↦ₛ ct1) ∗ ((sp + 4304#64) ↦ₛ ct2) := by
    rw [pointsToBytes_append, hct1, show (sp + 3344#64) + BitVec.ofNat 64 960 = sp + 4304#64 by clear * -; bv_omega]
  set R2c := SavedFrame04 s0.sp s0 ∗ memRegion sp 136 ∗ ((sp + 136#64) ↦₆₄ ret) ∗
    memRegion (sp + 144#64) 56 ∗ ((sp + 200#64) ↦₆₄ (sp + 22664#64)) ∗ memRegion (sp + 208#64) 1632 ∗
    ((sp + 1840#64) ↦₆₄ (dkA + 2336#64)) ∗ memRegion (sp + 1848#64) 8 ∗
    ((sp + 1856#64) ↦₆₄ (dkA + 2368#64)) ∗ memRegion (sp + 1864#64) 8 ∗ ((sp + 1872#64) ↦₆₄ dkA) ∗
    memRegion (sp + 1880#64) 8 ∗ ((sp + 1888#64) ↦₆₄ (dkA + 384#64)) ∗ memRegion (sp + 1896#64) 8 ∗
    Vec128At (sp + 1904#64) cst16_3_val ∗ Spill21Mem (sp + 1920#64) uHatZetaSpill21 ∗
    ((sp + 2256#64) ↦ₛ (ct1 ++ ct2)) ∗ ((sp + 3344#64) ↦ₛ ct1) ∗
    memRegion (sp + 4432#64) 1248 ∗
    PolyMem (sp + 5680#64) (polyVecNat (uHatPoly16 ct1 0)) ∗
    PolyMem (sp + 6192#64) (polyVecNat (uHatPoly16 ct1 1)) ∗
    PolyMem (sp + 6704#64) (polyVecNat (uHatPoly16 ct1 2)) ∗
    memRegion (sp + 7216#64) 4640 ∗ memRegion (sp + 11888#64) 1504 ∗ memRegion (sp + 13392#64) 5776 ∗
    memRegion (sp + 19680#64) 2720 ∗
    PolyMem (sp + 22400#64) (polyVecNat (tHatPoly16 (dk.take 384))) ∗
    PolyMem (sp + 22912#64) (polyVecNat (tHatPoly16 ((dk.drop 384).take 384))) ∗
    PolyMem (sp + 23424#64) (polyVecNat (tHatPoly16 ((dk.drop 768).take 384))) ∗
    memRegion (sp + 23936#64) 1728 ∗ (dkA ↦ₛ dk) ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ F
  have hP2' : P2 ⊢ stackAt sp 1136 ∗ memRegion (sp + 11856#64) 32 ∗
      ((sp + 4304#64) ↦ₛ ct2) ∗ memRegion (sp + 19168#64) 512 ∗ R2c := by
    refine Entails.trans hP2 ?_
    dsimp only [R2b, R2c]
    rw [h1536_split, hct_3344]; sep_frame
  refine SepWP.weaken_pre hP2'
    (SepWP.mono (seg2c_ok hb hbase s2 sp ct2 R2c hpc2 hrun2 hsp2 hspA2 hcl2 hct2) ?_)
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hfp_f, hx26_f, _, hx28_f, hPf⟩
  refine ⟨hsp_f, hspA_f, hfp_f.trans (hfp2.trans hfp1),
    hx26_f.trans (hx26_2.trans hx26_1), hx28_f.trans (hx28_2.trans hx28_1), ?_⟩
  refine Entails.trans hPf ?_
  dsimp only [Seg2Spatial, R2c, sp]
  rw [memRegion_11952_seg2_split (s0.sp - 25824#64),
    show ((s0.sp - 25824#64 + 3344#64) ↦ₛ (ct1 ++ ct2)) =
      ((s0.sp - 25824#64 + 3344#64) ↦ₛ ct1) ∗ ((s0.sp - 25824#64 + 4304#64) ↦ₛ ct2) from hct_3344]
  sep_frame

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg2c
