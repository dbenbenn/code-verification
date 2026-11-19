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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.DecompressBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.Specs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b

/-!
# `kyber_decapsulate` (`B06`) — `Seg3` `decompress_5` Loop (`+0x1858 .. +0x1970`) with `x23`/`fp`

Strengthens `seg3_decompress5_ok` to also export `sf.readReg64 .x23 = ctA` (consumed at `+0x3bb0`)
and `sf.readReg64 .fp = s.readReg64 .fp` (consumed at `+0xd8b0`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg3DecompressFp

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup4hLow)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (simdTrn1_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.Specs (
  PortableDeserializeArgs PortableDeserializePurePre deserializeChunkBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub spAligned_of_chk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc (
  svc_simdTrn1_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem SepLoad128 SepStore128 polyVecNat step_ldrQ128 step_stpQ128 step_strQ128
  vecRangeMem_congr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blk06_code_eq blk06_tree_size blkLib06 blkPC06 blkPl06 blkPlaceable06 blkTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.DecompressBase (
  SepLoad128.of_pointsToBytes_readLE blk26_deserialize5_06 decompressPoly16
  exec_simdMovi_4s_16 exec_simdShrn16_4h exec_simdUmlal_4s_low
  exec_simdUshr_4s_5 exec_simdXtn_4h
  neonDecompressRaw8h neonDecompress_q0_eq neonDecompress_q1_eq
  simdShrn16_4h simdUmlal4sLow simdUshr4s simdXtn4h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b (exec_simdMovi_2d_0)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06 [0x1858 → 0x196c]
end

abbrev off1858 : BitVec 64 := BitVec.ofNat 64 (4 * 1558)
private abbrev off18f4 : BitVec 64 := BitVec.ofNat 64 (4 * 1597)
abbrev off1970 : BitVec 64 := BitVec.ofNat 64 (4 * 1628)

@[simp, arm64_norm, wp_norm]
private theorem blkPl06_ρ [MlKemPlacement] (sym : String) :
    blkPl06.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

private theorem mask_getElem_16_128 (k : Nat) (_hk : k < 128) :
    (65535#128)[k] = decide (k < 16) := by
  have hm : (65535#128) = (BitVec.allOnes 16).setWidth 128 := rfl
  rw [hm, BitVec.getElem_setWidth]
  by_cases h : k < 16
  · rw [BitVec.getLsbD_eq_getElem h, BitVec.getElem_allOnes, decide_eq_true h]
  · rw [BitVec.getLsbD_of_ge _ _ (by omega), decide_eq_false h]

private theorem zext64_and_ffff_eq (w : BitVec 64) :
    (w.zeroExtend 128) &&& (1#128 <<< 16 - 1#128) = (w.truncate 16).zeroExtend 128 := by
  ext k hk
  simp only [show (1#128 <<< 16 - 1#128 : BitVec 128) = 65535#128 from rfl,
    BitVec.getElem_and, mask_getElem_16_128 k hk]
  rw [BitVec.getElem_setWidth, BitVec.getElem_setWidth]
  simp [Bool.and_comm]

private theorem mapLanes4_zext16_eq_dup4hLow (x : BitVec 16) :
    mapLanes 16 0#128 (fun _ => BitVec.setWidth 128 x) 4 = dup4hLow x := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  have hm : laneMask 16 = 65535#128 := rfl
  have hm_lsb : ∀ k, (65535#128).getLsbD k = decide (k < 16) := by
    intro k
    by_cases hk : k < 128
    · rw [BitVec.getLsbD_eq_getElem hk, mask_getElem_16_128 k hk]
    · rw [BitVec.getLsbD_of_ge _ _ (by omega), decide_eq_false (by omega)]
  by_cases h4 : b < 64
  · simp only [mapLanes, hm, dup4hLow, BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_append,
      BitVec.getLsbD_zero, hm_lsb, hb, decide_true, Bool.true_and]
    by_cases h1 : b < 16
    · simp [h1, hb, show b < 32 by omega, show b < 48 by omega]
    · by_cases h2 : b < 32
      · simp [h1, h2, show b < 48 by omega, show b - 16 < 16 by omega, show b - 16 < 128 by omega]
      · by_cases h3 : b < 48
        · have heq : b - 16 - 16 = b - 32 := by omega
          simp [heq, h1, h2, h3, show ¬ (b - 16 < 16) by omega,
            show b - 32 < 16 by omega, show b - 32 < 128 by omega]
        · have heq : b - 16 - 16 - 16 = b - 48 := by omega
          simp [heq, h1, h2, h3, show ¬ (b - 16 < 16) by omega, show ¬ (b - 32 < 16) by omega,
            show ¬ (b - 16 - 16 < 16) by omega, show b - 48 < 16 by omega,
            show b - 48 < 128 by omega]
  · simp only [mapLanes, hm, dup4hLow, BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_zero,
      hm_lsb, hb, decide_true, Bool.true_and, BitVec.getLsbD_of_ge (x ++ x ++ x ++ x) b (by omega)]
    simp [show ¬ (b < 16) by omega, show ¬ (b < 32) by omega, show ¬ (b < 48) by omega,
      show ¬ (b - 16 < 16) by omega, show ¬ (b - 32 < 16) by omega, show ¬ (b - 48 < 16) by omega]

@[simp, arm64_norm, wp_norm]
private theorem exec_simdDup_4h {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdInsDup false false 0b00010#5 0b0001#4 rn rd) s =
      (s.writeVReg128 rd (dup4hLow ((s.readReg64 (Reg.fromZRBits rn)).truncate 16))).advancePC := by
  have hz := zext64_and_ffff_eq (s.readReg64 (Reg.fromZRBits rn))
  simp [execInstWithSvc] at hz ⊢
  rw [hz, mapLanes4_zext16_eq_dup4hLow]

private theorem deserializeChunkBytes_len_5 (bs : List (BitVec 8)) :
    (deserializeChunkBytes 5 bs).length = 32 := by
  simp [deserializeChunkBytes]

private theorem dup4hLow_3329_lo :
    (dup4hLow 3329#16).truncate 64 = 0x0d010d010d010d01#64 := by decide

attribute [local irreducible]
  blkPC06 polyVecNat decompressPoly16 dup4hLow deserializeChunkBytes
  simdXtn4h simdShrn16_4h simdUmlal4sLow simdUshr4s simdTrn1_8h

attribute [local wp_norm ↓ high]
  exec_simdMovi_2d_0 exec_simdMovi_4s_16 exec_simdDup_4h
  exec_simdXtn_4h exec_simdShrn16_4h exec_simdUmlal_4s_low
  exec_simdUshr_4s_5 svc_simdTrn1_8h

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

local macro "step_zero_q26320 " k:num : tactic => `(tactic| (
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

private theorem sepWP_elim_polyMem {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ f : Nat → BitVec 128, SepWP prog target s (PolyMem a f ∗ R0) post) :
    SepWP prog target s (memRegion a 512 ∗ R0) post :=
  LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem.SepWP.of_memRegion_vecRangeMem
    (n := 32) (ptr := a) (F := R0) (by decide) rfl h

private theorem seg3_decompress5_init [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp ctA : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + off1858) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off18f4) s
      (memRegion (sp + 26320#64) 512 ∗ ((sp + 136#64) ↦₆₄ ctA) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = sp + 26336#64 ∧
        sf.readReg64 .x21 = 1408#64 ∧
        sf.readReg64 .x22 = 3329#64 ∧
        sf.readReg64 .x23 = ctA ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        (Pf ⊢ PolyMem (sp + 26320#64) (fun _ => 0#128) ∗
          ((sp + 136#64) ↦₆₄ ctA) ∗ Rest)) := by
  subst hbase; subst hsp
  have hsp_chk : (s.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hspA
  sep_frame_apply (sepWP_elim_polyMem (a := s.sp + 26320#64)); intro f0
  wp_steps 7
  step_zero_q26320 31; step_zero_q26320 30; step_zero_q26320 29; step_zero_q26320 28
  step_zero_q26320 27; step_zero_q26320 26; step_zero_q26320 25; step_zero_q26320 24
  step_zero_q26320 23; step_zero_q26320 22; step_zero_q26320 21; step_zero_q26320 20
  step_zero_q26320 19; step_zero_q26320 18; step_zero_q26320 17; step_zero_q26320 16
  step_zero_q26320 15; step_zero_q26320 14; step_zero_q26320 13; step_zero_q26320 12
  step_zero_q26320 11; step_zero_q26320 10; step_zero_q26320 9; step_zero_q26320 8
  step_zero_q26320 7; step_zero_q26320 6; step_zero_q26320 5; step_zero_q26320 4
  step_zero_q26320 3; step_zero_q26320 2; step_zero_q26320 1; step_zero_q26320 0
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp, spAligned_of_chk (by simp) hsp_chk,
      by simp, by simp, by simp, by simp, by simp, by simp, by simp, ?_⟩
  have hf_zero : ∀ i, i < 32 →
      (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update f0
        31 0#128) 30 0#128) 29 0#128) 28 0#128)
        27 0#128) 26 0#128) 25 0#128) 24 0#128)
        23 0#128) 22 0#128) 21 0#128) 20 0#128)
        19 0#128) 18 0#128) 17 0#128) 16 0#128)
        15 0#128) 14 0#128) 13 0#128) 12 0#128)
        11 0#128) 10 0#128) 9 0#128) 8 0#128)
        7 0#128) 6 0#128) 5 0#128) 4 0#128)
        3 0#128) 2 0#128) 1 0#128) 0 0#128) i = 0#128 := by
    intro i hi
    match i with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
    | _ + 32 => omega
  rw [polyMem_congr hf_zero]
  sep_frame

private theorem pointsToBytes_chunk10 {ptr : BitVec 64} {bs : List (BitVec 8)} {k : Nat}
    (hbs : bs.length = 160) (hk : k < 16) :
    (ptr ↦ₛ bs) =
      (ptr ↦ₛ bs.take (10 * k)) ∗
      ((ptr + BitVec.ofNat 64 (10 * k)) ↦ₛ (bs.drop (10 * k)).take 10) ∗
      ((ptr + BitVec.ofNat 64 (10 * (k + 1))) ↦ₛ bs.drop (10 * (k + 1))) := by
  have hl1 : (bs.take (10 * k)).length = 10 * k := by simp [hbs]; omega
  have hl2 : ((bs.drop (10 * k)).take 10).length = 10 := by simp [hbs]; omega
  have hdrop : (bs.drop (10 * k)).drop 10 = bs.drop (10 * (k + 1)) := by
    rw [List.drop_drop, show 10 * k + 10 = 10 * (k + 1) by omega]
  have hadd : (ptr + BitVec.ofNat 64 (10 * k)) + BitVec.ofNat 64 10 =
      ptr + BitVec.ofNat 64 (10 * (k + 1)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 10 * k + 10 = 10 * (k + 1) by omega]
  conv_lhs => rw [← List.take_append_drop (10 * k) bs]
  rw [pointsToBytes_append, hl1]
  conv in (bs.drop (10 * k)) => rw [← List.take_append_drop 10 (bs.drop (10 * k))]
  rw [pointsToBytes_append, hl2, hdrop, hadd]

attribute [local simp] PortableDeserializePurePre

private theorem sepWP_seq_codeLoaded {prog : Program} {mid target : BitVec 64} {s : State}
    {P : SepProp} {post1 post2 : State → SepProp → Prop} {mpl : MultiPlacement}
    (hcl : mlkemMultiLib.CodeLoaded mpl s.mem)
    (h1 : SepWP prog mid s P post1)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      mlkemMultiLib.CodeLoaded mpl sm.mem → post1 sm Pm → SepWP prog target sm Pm post2) :
    SepWP prog target s P post2 :=
  SepWP.seq
    (SepWP.mono_frozen
      (post' := fun sm Pm => mlkemMultiLib.CodeLoaded mpl sm.mem ∧ post1 sm Pm)
      (Φ := fun m => mlkemMultiLib.CodeLoaded mpl m)
      (fun _ _ hc hkf => hc.of_keepsFrozen hkf)
      hcl h1
      (fun _ _ _ _ hc hp1 => ⟨hc, hp1⟩))
    (fun sm Pm hpc hrun ⟨hc, hp1⟩ => h2 sm Pm hpc hrun hc hp1)

private abbrev off1908 : BitVec 64 := BitVec.ofNat 64 (4 * 1602)
private abbrev off190c : BitVec 64 := BitVec.ofNat 64 (4 * 1603)

private theorem seg3_decompress5_iter [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (sp ctA : BitVec 64) (ct2 : List (BitVec 8)) (Rest : SepProp)
    (hct2 : ct2.length = 160) {k : Nat} (hk16 : k < 16)
    (s : State) (f : Nat → BitVec 128)
    (hpc : s.pc = b + off18f4) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hx19 : s.readReg64 .x19 = sp + 26336#64 + BitVec.ofNat 64 (32 * k))
    (hx21 : s.readReg64 .x21 = 1408#64 + BitVec.ofNat 64 (10 * k))
    (hx22 : s.readReg64 .x22 = 3329#64)
    (hx23 : s.readReg64 .x23 = ctA) :
    SepWP (blkPC06.rebase b (fun _ => none))
      (if k < 15 then b + off18f4 else b + off1970) s
      (stackAt sp 1136 ∗ memRegion (sp + 14432#64) 32 ∗
        ((ctA + 1408#64) ↦ₛ ct2) ∗ PolyMem (sp + 26320#64) f ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = sp + 26336#64 + BitVec.ofNat 64 (32 * (k + 1)) ∧
        sf.readReg64 .x21 = 1408#64 + BitVec.ofNat 64 (10 * (k + 1)) ∧
        sf.readReg64 .x22 = 3329#64 ∧
        sf.readReg64 .x23 = ctA ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        (Pf ⊢ stackAt sp 1136 ∗ memRegion (sp + 14432#64) 32 ∗
          ((ctA + 1408#64) ↦ₛ ct2) ∗
          PolyMem (sp + 26320#64)
            (Function.update
              (Function.update f (2 * k) (polyVecNat (decompressPoly16 5 ct2) (2 * k)))
              (2 * k + 1) (polyVecNat (decompressPoly16 5 ct2) (2 * k + 1))) ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  set ct2Ptr := ctA + 1408#64
  set chunk := (ct2.drop (10 * k)).take 10
  have hchunk_len : chunk.length = 10 := by simp [chunk, hct2]; omega
  refine SepWP.weaken_pre
    (show stackAt sp 1136 ∗ memRegion (sp + 14432#64) 32 ∗
        (ct2Ptr ↦ₛ ct2) ∗ PolyMem (sp + 26320#64) f ∗ Rest ⊢
      (memRegion (sp - 1136#64) 1120 ∗ stackAt sp 16) ∗ memRegion (sp + 14432#64) 32 ∗
        ((ct2Ptr ↦ₛ ct2.take (10 * k)) ∗ ((ct2Ptr + BitVec.ofNat 64 (10 * k)) ↦ₛ chunk) ∗
          ((ct2Ptr + BitVec.ofNat 64 (10 * (k + 1))) ↦ₛ ct2.drop (10 * (k + 1)))) ∗
        PolyMem (sp + 26320#64) f ∗ Rest by
      rw [ProofLib.stackAt_shrink sp 1136 16 (by decide), pointsToBytes_chunk10 hct2 hk16]
      exact Entails.refl _) ?_
  wp_cut_codeLoaded
  wp_steps 4
  apply SepWP.done (by wp_norm_lhs) (by assumption)
  intro _hcl_pre
  have hx0_eq : ctA + (1408#64 + BitVec.ofNat 64 (10 * k)) = ct2Ptr + BitVec.ofNat 64 (10 * k) := by
    dsimp only [ct2Ptr]; clear * -; bv_omega
  wp_call (blk26_deserialize5_06 blkPl06.base)
    (⟨sp + 14432#64, ct2Ptr + BitVec.ofNat 64 (10 * k), chunk⟩ : PortableDeserializeArgs)
  have hsp_sf : sf.sp = sp := by simp [*]
  have hspA_sf : sf.spAligned = true := spAligned_of_chk hsp_sf hsp_chk
  have hx22_sf : sf.readReg64 .x22 = 3329#64 := by simp [*]
  set buf := deserializeChunkBytes 5 chunk
  have hbuf_len : buf.length = 32 := deserializeChunkBytes_len_5 chunk
  refine step_ldrQ128 (wb := none) (ea := sp + 14432#64)
    (v := ByteSlice.readLE buf 8 8 ++ ByteSlice.readLE buf 0 8)
    hpc_sf hrun_sf (by wp_norm_lhs)
    (by simpa [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg] using hspA_sf)
    (by simp [evalAddrMode, hsp_sf])
    (SepLoad128.of_pointsToBytes_readLE (ptr := sp + 14432#64) (bs := buf) (off := 0)
      rfl (by omega) (by clear * -; bv_omega))
    (by wp_norm_lhs) ?_
  refine step_ldrQ128 (wb := none) (ea := sp + 14448#64)
    (v := ByteSlice.readLE buf 24 8 ++ ByteSlice.readLE buf 16 8)
    (by wp_norm_lhs) (by simp [hrun_sf]) (by wp_norm_lhs)
    (by simpa [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp_sf]
      using hsp_chk)
    (by simp [evalAddrMode, hsp_sf])
    (SepLoad128.of_pointsToBytes_readLE (ptr := sp + 14432#64) (bs := buf) (off := 16)
      rfl (by omega) (by clear * -; bv_omega))
    (by wp_norm_lhs) ?_
  refine SepWP.weaken_pre
    (show _ ⊢ PolyMem (sp + 26320#64) f ∗
        (((sp + 14432#64) ↦ₛ buf) ∗ stackAt sp 1136 ∗ (ct2Ptr ↦ₛ ct2) ∗ Rest) by
      rw [ProofLib.stackAt_shrink sp 1136 16 (by decide), pointsToBytes_chunk10 hct2 hk16]
      sep_frame) ?_
  wp_steps 21
  have hq0 := neonDecompress_q0_eq (d := 5) (fullBs := ct2) (k := k)
    (q3329 := dup4hLow 3329#16) (Or.inl rfl) hk16 (by omega) dup4hLow_3329_lo
  have hq1 := neonDecompress_q1_eq (d := 5) (fullBs := ct2) (k := k)
    (q3329 := dup4hLow 3329#16) (Or.inl rfl) hk16 (by omega) dup4hLow_3329_lo
  refine step_stpQ128 (wb := none)
    (ea := sp + 26320#64 + BitVec.ofNat 64 (16 * (2 * k)))
    (ea16 := sp + 26320#64 + BitVec.ofNat 64 (16 * (2 * k + 1)))
    (v1 := polyVecNat (decompressPoly16 5 ct2) (2 * k))
    (v2 := polyVecNat (decompressPoly16 5 ct2) (2 * k + 1))
    (by wp_norm_lhs) (by simp [hrun_sf]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, *]; clear * - hk16; bv_omega)
    (by clear * - hk16; bv_omega)
    (by simpa [neonDecompressRaw8h, chunk, buf] using hq0)
    (by simpa [neonDecompressRaw8h, chunk, buf] using hq1)
    (SepStore128.left (SepStore128.polyMem (k := 2 * k) (by omega) rfl))
    (SepStore128.left (SepStore128.polyMem (k := 2 * k + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  intro m'
  have hbuf_reg : ((sp + 14432#64) ↦ₛ buf) ⊢ memRegion (sp + 14432#64) 32 := by
    simpa [hbuf_len] using pointsToBytes_entails_memRegion (sp + 14432#64) buf
  wp_steps 2
  wp_if hne
  · have hk15 : k < 15 := by
      by_contra hge
      have hk_eq : k = 15 := by omega
      subst hk_eq; simp [*] at hne
    simp only [hk15, ↓reduceIte]
    refine SepWP.done (by wp_norm_lhs) (by simp [hrun_sf])
      ⟨by simp [hsp_sf], by simpa [State.spAligned, hsp_sf] using hsp_chk,
        by simp [*]; clear * - hk15; bv_omega,
        by simp [*]; clear * - hk15; bv_omega,
        by simp [*], by simp [*], by simp [*], by simp [*], by simp [*], ?_⟩
    exact entails_sub hbuf_reg (by sep_frame) (by sep_frame)
  · have hk15 : ¬ k < 15 := by
      intro hlt
      have hk_eq : k = 15 := by clear * - hne hlt; bv_omega
      omega
    have hk_eq : k = 15 := by omega
    subst hk_eq
    simp only [Nat.lt_irrefl, ↓reduceIte]
    refine SepWP.done (by wp_norm_lhs) (by simp [hrun_sf])
      ⟨by simp [hsp_sf], by simpa [State.spAligned, hsp_sf] using hsp_chk,
        by simp [*], by simp [*], by simp [*], by simp [*], by simp [*], by simp [*], by simp [*], ?_⟩
    exact entails_sub hbuf_reg (by sep_frame) (by sep_frame)

private theorem seg3_decompress5_loop [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (sp ctA : BitVec 64) (ct2 : List (BitVec 8)) (Rest : SepProp)
    (hct2 : ct2.length = 160) :
    ∀ (rem k : Nat), k + 1 + rem = 16 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + off18f4 →
      s.status = .Running →
      s.sp = sp →
      s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem →
      s.readReg64 .x19 = sp + 26336#64 + BitVec.ofNat 64 (32 * k) →
      s.readReg64 .x21 = 1408#64 + BitVec.ofNat 64 (10 * k) →
      s.readReg64 .x22 = 3329#64 →
      s.readReg64 .x23 = ctA →
      (∀ j, j < 2 * k → f j = polyVecNat (decompressPoly16 5 ct2) j) →
      SepWP (blkPC06.rebase b (fun _ => none)) (b + off1970) s
        (stackAt sp 1136 ∗ memRegion (sp + 14432#64) 32 ∗
          ((ctA + 1408#64) ↦ₛ ct2) ∗ PolyMem (sp + 26320#64) f ∗ Rest)
        (fun sf Pf =>
          sf.sp = sp ∧ sf.spAligned = true ∧
          sf.readReg64 .x23 = ctA ∧
          sf.readReg64 .x25 = s.readReg64 .x25 ∧
          sf.readReg64 .x26 = s.readReg64 .x26 ∧
          sf.readReg64 .fp = s.readReg64 .fp ∧
          (Pf ⊢ stackAt sp 1136 ∗ memRegion (sp + 14432#64) 32 ∗
            ((ctA + 1408#64) ↦ₛ ct2) ∗
            PolyMem (sp + 26320#64) (polyVecNat (decompressPoly16 5 ct2)) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro k hk15 s f hpc hrun hsp hspA hcl hx19 hx21 hx22 hx23 hf
    have hk : k = 15 := by omega
    subst hk
    have hiter := seg3_decompress5_iter hb hbase sp ctA ct2 Rest hct2 (k := 15) (by decide)
      s f hpc hrun hsp hspA hcl hx19 hx21 hx22 hx23
    simp only [Nat.lt_irrefl, ↓reduceIte] at hiter
    refine SepWP.mono hiter ?_
    rintro sf Pf _ _ ⟨hsp_f, hspA_f, _, _, _, hx23_f, hx25_f, hx26_f, hfp_f, hPf⟩
    have hf32 := update2_prefix (k := 15) hf
    exact ⟨hsp_f, hspA_f, hx23_f, hx25_f, hx26_f, hfp_f,
      Entails.trans hPf (by rw [polyMem_congr hf32]; exact Entails.refl _)⟩
  | succ rem' ih =>
    intro k hk_rem s f hpc hrun hsp hspA hcl hx19 hx21 hx22 hx23 hf
    have hk15 : k < 15 := by omega
    have hiter := seg3_decompress5_iter hb hbase sp ctA ct2 Rest hct2 (k := k) (by omega)
      s f hpc hrun hsp hspA hcl hx19 hx21 hx22 hx23
    simp only [hk15, ↓reduceIte] at hiter
    refine sepWP_seq_codeLoaded hcl hiter ?_
    rintro sm Pm hpc_m hrun_m hcl_m ⟨hsp_m, hspA_m, hx19_m, hx21_m, hx22_m, hx23_m,
      hx25_m, hx26_m, hfp_m, hPm⟩
    refine SepWP.weaken_pre hPm
      (SepWP.mono
        (ih (k + 1) (by omega) sm _ hpc_m hrun_m hsp_m hspA_m hcl_m
          hx19_m hx21_m hx22_m hx23_m (update2_prefix hf)) ?_)
    rintro sf Pf _ _ ⟨hsp_f, hspA_f, hx23_f, hx25_f, hx26_f, hfp_f, hPf⟩
    exact ⟨hsp_f, hspA_f, hx23_f, hx25_f.trans hx25_m, hx26_f.trans hx26_m, hfp_f.trans hfp_m, hPf⟩

/-- Composed `Seg3` `decompress_5` sub-segment (`+0x1858 → +0x1970`) preserving `x23 = ctA` and `fp`. -/
theorem seg3_decompress5_fp_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp ctA : BitVec 64) (ct2 : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + off1858) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hct2 : ct2.length = 160) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off1970) s
      (stackAt sp 1136 ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
        memRegion (sp + 14432#64) 32 ∗ memRegion (sp + 26320#64) 512 ∗
        ((ctA + 1408#64) ↦ₛ ct2) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x23 = ctA ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        (Pf ⊢ stackAt sp 1136 ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
          memRegion (sp + 14432#64) 32 ∗
          PolyMem (sp + 26320#64) (polyVecNat (decompressPoly16 5 ct2)) ∗
          ((ctA + 1408#64) ↦ₛ ct2) ∗ Rest)) := by
  have hP0 :
      stackAt sp 1136 ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
        memRegion (sp + 14432#64) 32 ∗ memRegion (sp + 26320#64) 512 ∗
        ((ctA + 1408#64) ↦ₛ ct2) ∗ Rest ⊢
      memRegion (sp + 26320#64) 512 ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
        (stackAt sp 1136 ∗ memRegion (sp + 14432#64) 32 ∗ ((ctA + 1408#64) ↦ₛ ct2) ∗ Rest) := by
    sep_frame
  refine SepWP.weaken_pre hP0
    (sepWP_seq_codeLoaded hcl
      (seg3_decompress5_init hb hbase s sp ctA _ hpc hrun hsp hspA) ?_)
  rintro s1 P1 hpc1 hrun1 hcl1
    ⟨hsp1, hspA1, hx19_1, hx21_1, hx22_1, hx23_1, hx25_1, hx26_1, hfp_1, hP1⟩
  have hP1' : P1 ⊢
      stackAt sp 1136 ∗ memRegion (sp + 14432#64) 32 ∗ ((ctA + 1408#64) ↦ₛ ct2) ∗
        PolyMem (sp + 26320#64) (fun _ => 0#128) ∗
        (((sp + 136#64) ↦₆₄ ctA) ∗ Rest) :=
    Entails.trans hP1 (by sep_frame)
  refine SepWP.weaken_pre hP1'
    (SepWP.mono
      (seg3_decompress5_loop hb hbase sp ctA ct2 (((sp + 136#64) ↦₆₄ ctA) ∗ Rest) hct2
        15 0 rfl s1 (fun _ => 0#128)
        hpc1 hrun1 hsp1 hspA1 hcl1 (by simp [hx19_1]) (by simp [hx21_1])
        hx22_1 hx23_1 (by omega)) ?_)
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hx23_f, hx25_f, hx26_f, hfp_f, hPf⟩
  exact ⟨hsp_f, hspA_f, hx23_f, hx25_f.trans hx25_1, hx26_f.trans hx26_1, hfp_f.trans hfp_1,
    Entails.trans hPf (by sep_frame)⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg3DecompressFp
