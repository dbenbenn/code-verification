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
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b

/-!
# `kyber_decapsulate` (`B06`) — `Seg2` `decompress_11` Loop (`+0x05dc .. +0x06f0`)

Proves the 16-iteration `B27 deserialize_11` + NEON `decompress_11` loop inside `Seg2`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg2Decompress

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (simdTrn1_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.PortableDeserialize.Specs (
  PortableDeserializeArgs PortableDeserializePurePre deserializeChunkBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub sepWP_elim_cell8 spAligned_of_chk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc (
  svc_simdTrn1_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem SepLoad128 SepStore128 polyVecNat step_ldrQ128 step_stpQ128 step_strQ128
  vecRangeMem_congr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blk06_code_eq blk06_tree_size blkLib06 blkPC06 blkPl06 blkPlaceable06 blkTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.DecompressBase (
  SepLoad128.of_pointsToBytes_readLE blk27_deserialize11_06 decompressPoly16
  exec_simdMovi_4s_1024 exec_simdMovi_4s_16 exec_simdShrn16_4h exec_simdUmlal_4s_low
  exec_simdUshr_4s_11 exec_simdUshr_4s_5 exec_simdXtn_4h
  neonDecompressRaw8h neonDecompress_q0_eq neonDecompress_q1_eq
  simdShrn16_4h simdUmlal4sLow simdUshr4s simdXtn4h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b (exec_simdMovi_2d_0)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06 [0x05dc → 0x06ec]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl06_ρ [MlKemPlacement] (sym : String) :
    blkPl06.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

attribute [local irreducible]
  blkPC06 polyVecNat decompressPoly16
  simdXtn4h simdShrn16_4h simdUmlal4sLow simdUshr4s simdTrn1_8h

attribute [local wp_norm ↓ high]
  exec_simdMovi_2d_0 exec_simdMovi_4s_1024 exec_simdMovi_4s_16
  exec_simdXtn_4h exec_simdShrn16_4h exec_simdUmlal_4s_low
  exec_simdUshr_4s_11 exec_simdUshr_4s_5 svc_simdTrn1_8h

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

local macro "step_zero_q4160 " k:num : tactic => `(tactic| (
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

private theorem seg2_decompress11_init [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp ctPtr idx : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + 0x05dc#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = ctPtr)
    (hx22 : s.readReg64 .x22 = idx) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x0674#64) s
      (memRegion (sp + 4160#64) 512 ∗ memRegion (sp + 2400#64) 8 ∗
        memRegion (sp + 2416#64) 8 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x0 = ctPtr ∧
        sf.readReg64 .x21 = 0#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x22 = idx ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readVReg128 8#5 = s.readVReg128 8#5 ∧
        (Pf ⊢ PolyMem (sp + 4160#64) (fun _ => 0#128) ∗
          ((sp + 2400#64) ↦₆₄ (idx + 1#64)) ∗
          ((sp + 2416#64) ↦₆₄ (ctPtr + 352#64)) ∗ Rest)) := by
  subst hbase; subst hsp
  have hsp_chk : (s.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hspA
  sep_frame_apply (sepWP_elim_cell8 (a := s.sp + 2400#64)); intro c2400
  sep_frame_apply (sepWP_elim_cell8 (a := s.sp + 2416#64)); intro c2416
  sep_frame_apply (sepWP_elim_polyMem (a := s.sp + 4160#64)); intro f0
  wp_steps 6
  step_zero_q4160 31; step_zero_q4160 30; step_zero_q4160 29; step_zero_q4160 28
  step_zero_q4160 27; step_zero_q4160 26; step_zero_q4160 25; step_zero_q4160 24
  step_zero_q4160 23; step_zero_q4160 22; step_zero_q4160 21; step_zero_q4160 20
  step_zero_q4160 19; step_zero_q4160 18; step_zero_q4160 17; step_zero_q4160 16
  step_zero_q4160 15; step_zero_q4160 14; step_zero_q4160 13; step_zero_q4160 12
  step_zero_q4160 11; step_zero_q4160 10; step_zero_q4160 9; step_zero_q4160 8
  step_zero_q4160 7; step_zero_q4160 6; step_zero_q4160 5; step_zero_q4160 4
  step_zero_q4160 3; step_zero_q4160 2; step_zero_q4160 1; step_zero_q4160 0
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp, spAligned_of_chk (by simp) hsp_chk,
      by simp, by simp [hx0], by simp, by simp, by simp [hx22],
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

private theorem pointsToBytes_chunk22 {ptr : BitVec 64} {bs : List (BitVec 8)} {k : Nat}
    (hbs : bs.length = 352) (hk : k < 16) :
    (ptr ↦ₛ bs) =
      (ptr ↦ₛ bs.take (22 * k)) ∗
      ((ptr + BitVec.ofNat 64 (22 * k)) ↦ₛ (bs.drop (22 * k)).take 22) ∗
      ((ptr + BitVec.ofNat 64 (22 * (k + 1))) ↦ₛ bs.drop (22 * (k + 1))) := by
  have hl1 : (bs.take (22 * k)).length = 22 * k := by simp [hbs]; omega
  have hl2 : ((bs.drop (22 * k)).take 22).length = 22 := by simp [hbs]; omega
  have hdrop : (bs.drop (22 * k)).drop 22 = bs.drop (22 * (k + 1)) := by
    rw [List.drop_drop, show 22 * k + 22 = 22 * (k + 1) by omega]
  have hadd : (ptr + BitVec.ofNat 64 (22 * k)) + BitVec.ofNat 64 22 =
      ptr + BitVec.ofNat 64 (22 * (k + 1)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 22 * k + 22 = 22 * (k + 1) by omega]
  conv_lhs => rw [← List.take_append_drop (22 * k) bs]
  rw [pointsToBytes_append, hl1]
  conv in (bs.drop (22 * k)) => rw [← List.take_append_drop 22 (bs.drop (22 * k))]
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

private theorem seg2_decompress11_iter [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (sp ctPtr : BitVec 64) (ctSlice : List (BitVec 8)) (Rest : SepProp)
    (hct : ctSlice.length = 352) {k : Nat} (hk16 : k < 16)
    (s : State) (f : Nat → BitVec 128)
    (hpc : s.pc = b + 0x0674#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hx0 : s.readReg64 .x0 = ctPtr + BitVec.ofNat 64 (22 * k))
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 (32 * k))
    (hx27 : s.readReg64 .x27 = sp + 4160#64)
    (hv8 : (s.readVReg128 8#5).truncate 64 = 0x0d010d010d010d01#64) :
    SepWP (blkPC06.rebase b (fun _ => none))
      (if k < 15 then b + 0x0674#64 else b + 0x06f0#64) s
      (stackAt sp 1136 ∗ memRegion (sp + 28368#64) 32 ∗
        (ctPtr ↦ₛ ctSlice) ∗ PolyMem (sp + 4160#64) f ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x0 = ctPtr + BitVec.ofNat 64 (22 * (k + 1)) ∧
        sf.readReg64 .x21 = BitVec.ofNat 64 (32 * (k + 1)) ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = sp + 4160#64 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readVReg128 8#5 = s.readVReg128 8#5 ∧
        sf.readVReg128 11#5 = s.readVReg128 11#5 ∧
        (Pf ⊢ stackAt sp 1136 ∗ memRegion (sp + 28368#64) 32 ∗
          (ctPtr ↦ₛ ctSlice) ∗
          PolyMem (sp + 4160#64)
            (Function.update
              (Function.update f (2 * k) (polyVecNat (decompressPoly16 11 ctSlice) (2 * k)))
              (2 * k + 1) (polyVecNat (decompressPoly16 11 ctSlice) (2 * k + 1))) ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  set chunk := (ctSlice.drop (22 * k)).take 22
  have hchunk_len : chunk.length = 22 := by simp [chunk, hct]; omega
  refine SepWP.weaken_pre
    (show stackAt sp 1136 ∗ memRegion (sp + 28368#64) 32 ∗
        (ctPtr ↦ₛ ctSlice) ∗ PolyMem (sp + 4160#64) f ∗ Rest ⊢
      (memRegion (sp - 1136#64) 1120 ∗ stackAt sp 16) ∗ memRegion (sp + 28368#64) 32 ∗
        ((ctPtr ↦ₛ ctSlice.take (22 * k)) ∗ ((ctPtr + BitVec.ofNat 64 (22 * k)) ↦ₛ chunk) ∗
          ((ctPtr + BitVec.ofNat 64 (22 * (k + 1))) ↦ₛ ctSlice.drop (22 * (k + 1)))) ∗
        PolyMem (sp + 4160#64) f ∗ Rest by
      rw [ProofLib.stackAt_shrink sp 1136 16 (by decide), pointsToBytes_chunk22 hct hk16]
      exact Entails.refl _) ?_
  wp_cut_codeLoaded
  wp_steps 4
  apply SepWP.done (by wp_norm_lhs) (by assumption)
  intro _hcl_pre
  wp_call (blk27_deserialize11_06 blkPl06.base)
    (⟨sp + 28368#64, ctPtr + BitVec.ofNat 64 (22 * k), chunk⟩ : PortableDeserializeArgs)
  have hsp_sf : sf.sp = sp := by simp [*]
  have hspA_sf : sf.spAligned = true := spAligned_of_chk hsp_sf hsp_chk
  have hv8_eq : sf.readVReg128 8#5 = s.readVReg128 8#5 := by
    simp [State.readVReg128, hpost, State.writeReg64, State.setPC]
  have hv11_eq : sf.readVReg128 11#5 = s.readVReg128 11#5 := by
    simp [State.readVReg128, hpost, State.writeReg64, State.setPC]
  set buf := deserializeChunkBytes 11 chunk
  have hbuf_len : buf.length = 32 := by simp [buf]
  refine step_ldrQ128 (pc := blkPl06.base + 1672#64) (wb := none) (ea := sp + 28368#64)
    (v := ByteSlice.readLE buf 8 8 ++ ByteSlice.readLE buf 0 8)
    hpc_sf hrun_sf (by wp_norm_lhs)
    (by simpa [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg] using hspA_sf)
    (by simp [evalAddrMode, hsp_sf])
    (SepLoad128.of_pointsToBytes_readLE (ptr := sp + 28368#64) (bs := buf) (off := 0)
      rfl (by omega) (by clear * -; bv_omega))
    (by wp_norm_lhs) ?_
  refine step_ldrQ128 (pc := blkPl06.base + 1676#64) (wb := none) (ea := sp + 28384#64)
    (v := ByteSlice.readLE buf 24 8 ++ ByteSlice.readLE buf 16 8)
    (by wp_norm_lhs) (by simp [hrun_sf]) (by wp_norm_lhs)
    (by simpa [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp_sf]
      using hsp_chk)
    (by simp [evalAddrMode, hsp_sf])
    (SepLoad128.of_pointsToBytes_readLE (ptr := sp + 28368#64) (bs := buf) (off := 16)
      rfl (by omega) (by clear * -; bv_omega))
    (by wp_norm_lhs) ?_
  refine SepWP.weaken_pre
    (show _ ⊢ PolyMem (sp + 4160#64) f ∗
        (((sp + 28368#64) ↦ₛ buf) ∗ stackAt sp 1136 ∗ (ctPtr ↦ₛ ctSlice) ∗ Rest) by
      rw [ProofLib.stackAt_shrink sp 1136 16 (by decide), pointsToBytes_chunk22 hct hk16]
      sep_frame) ?_
  wp_steps 22
  have hq0 := neonDecompress_q0_eq (d := 11) (fullBs := ctSlice) (k := k)
    (q3329 := s.readVReg128 8#5) (Or.inr rfl) hk16 (by omega) hv8
  have hq1 := neonDecompress_q1_eq (d := 11) (fullBs := ctSlice) (k := k)
    (q3329 := s.readVReg128 8#5) (Or.inr rfl) hk16 (by omega) hv8
  refine step_stpQ128 (wb := none)
    (ea := sp + 4160#64 + BitVec.ofNat 64 (16 * (2 * k)))
    (ea16 := sp + 4160#64 + BitVec.ofNat 64 (16 * (2 * k + 1)))
    (v1 := polyVecNat (decompressPoly16 11 ctSlice) (2 * k))
    (v2 := polyVecNat (decompressPoly16 11 ctSlice) (2 * k + 1))
    (by wp_norm_lhs) (by simp [hrun_sf]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, *]; clear * - hk16; bv_omega)
    (by clear * - hk16; bv_omega)
    (by simpa [neonDecompressRaw8h, chunk, buf] using hq0)
    (by simpa [neonDecompressRaw8h, chunk, buf] using hq1)
    (SepStore128.left (SepStore128.polyMem (k := 2 * k) (by omega) rfl))
    (SepStore128.left (SepStore128.polyMem (k := 2 * k + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  intro m'
  have hbuf_reg : ((sp + 28368#64) ↦ₛ buf) ⊢ memRegion (sp + 28368#64) 32 := by
    simpa [hbuf_len] using pointsToBytes_entails_memRegion (sp + 28368#64) buf
  wp_step
  wp_if hne
  · have hk15 : k < 15 := by
      by_contra hge
      have hk_eq : k = 15 := by omega
      subst hk_eq; simp [*] at hne
    simp only [hk15, ↓reduceIte]
    refine SepWP.done (by wp_norm_lhs) (by simp [hrun_sf])
      ⟨by simp [hsp_sf], by simpa [State.spAligned, hsp_sf] using hsp_chk,
        by simp [*],
        by simp [*]; clear * - hk15; bv_omega,
        by simp [*]; clear * - hk15; bv_omega,
        by simp [*], by simp [*], by simp [*], by simp [*],
        by simp [*], by simp [*], by simp [*], by simp [*],
        by simp [hv8_eq], by simp [hv11_eq], ?_⟩
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
        by simp [*],
        by simp [*], by simp [*],
        by simp [*], by simp [*], by simp [*], by simp [*],
        by simp [*], by simp [*], by simp [*], by simp [*],
        by simp [hv8_eq], by simp [hv11_eq], ?_⟩
    exact entails_sub hbuf_reg (by sep_frame) (by sep_frame)

private theorem seg2_decompress11_loop [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (sp ctPtr : BitVec 64) (ctSlice : List (BitVec 8)) (Rest : SepProp)
    (hct : ctSlice.length = 352) :
    ∀ (rem k : Nat), k + 1 + rem = 16 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + 0x0674#64 →
      s.status = .Running →
      s.sp = sp →
      s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem →
      s.readReg64 .x0 = ctPtr + BitVec.ofNat 64 (22 * k) →
      s.readReg64 .x21 = BitVec.ofNat 64 (32 * k) →
      s.readReg64 .x27 = sp + 4160#64 →
      (s.readVReg128 8#5).truncate 64 = 0x0d010d010d010d01#64 →
      (∀ j, j < 2 * k → f j = polyVecNat (decompressPoly16 11 ctSlice) j) →
      SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x06f0#64) s
        (stackAt sp 1136 ∗ memRegion (sp + 28368#64) 32 ∗
          (ctPtr ↦ₛ ctSlice) ∗ PolyMem (sp + 4160#64) f ∗ Rest)
        (fun sf Pf =>
          sf.sp = sp ∧ sf.spAligned = true ∧
          sf.readReg64 .fp = s.readReg64 .fp ∧
          sf.readReg64 .x19 = s.readReg64 .x19 ∧
          sf.readReg64 .x22 = s.readReg64 .x22 ∧
          sf.readReg64 .x23 = s.readReg64 .x23 ∧
          sf.readReg64 .x24 = s.readReg64 .x24 ∧
          sf.readReg64 .x25 = s.readReg64 .x25 ∧
          sf.readReg64 .x26 = s.readReg64 .x26 ∧
          sf.readReg64 .x27 = sp + 4160#64 ∧
          sf.readReg64 .x28 = s.readReg64 .x28 ∧
          sf.readVReg128 8#5 = s.readVReg128 8#5 ∧
          sf.readVReg128 11#5 = s.readVReg128 11#5 ∧
          (Pf ⊢ stackAt sp 1136 ∗ memRegion (sp + 28368#64) 32 ∗
            (ctPtr ↦ₛ ctSlice) ∗
            PolyMem (sp + 4160#64) (polyVecNat (decompressPoly16 11 ctSlice)) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro k hk15 s f hpc hrun hsp hspA hcl hx0 hx21 hx27 hv8 hf
    have hk : k = 15 := by omega
    subst hk
    have hiter := seg2_decompress11_iter hb hbase sp ctPtr ctSlice Rest hct (k := 15) (by decide)
      s f hpc hrun hsp hspA hcl hx0 hx21 hx27 hv8
    simp only [Nat.lt_irrefl, ↓reduceIte] at hiter
    refine SepWP.mono hiter ?_
    rintro sf Pf _ _ ⟨hsp_f, hspA_f, hfp_f, _, _, hx19_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx26_f, hx27_f, hx28_f, hv8_f, hv11_f, hPf⟩
    have hf32 := update2_prefix (k := 15) hf
    exact ⟨hsp_f, hspA_f, hfp_f, hx19_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f,
      hv8_f, hv11_f, Entails.trans hPf (by rw [polyMem_congr hf32]; exact Entails.refl _)⟩
  | succ rem' ih =>
    intro k hk_rem s f hpc hrun hsp hspA hcl hx0 hx21 hx27 hv8 hf
    have hk15 : k < 15 := by omega
    have hiter := seg2_decompress11_iter hb hbase sp ctPtr ctSlice Rest hct (k := k) (by omega)
      s f hpc hrun hsp hspA hcl hx0 hx21 hx27 hv8
    simp only [hk15, ↓reduceIte] at hiter
    refine sepWP_seq_codeLoaded hcl hiter ?_
    rintro sm Pm hpc_m hrun_m hcl_m ⟨hsp_m, hspA_m, hfp_m, hx0_m, hx21_m, hx19_m, hx22_m,
      hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hv8_m, hv11_m, hPm⟩
    refine SepWP.weaken_pre hPm
      (SepWP.mono
        (ih (k + 1) (by omega) sm _ hpc_m hrun_m hsp_m hspA_m hcl_m hx0_m hx21_m hx27_m
          (hv8_m ▸ hv8) (update2_prefix hf)) ?_)
    rintro sf Pf _ _ ⟨hsp_f, hspA_f, hfp_f, hx19_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx26_f, hx27_f, hx28_f, hv8_f, hv11_f, hPf⟩
    exact ⟨hsp_f, hspA_f, hfp_f.trans hfp_m, hx19_f.trans hx19_m, hx22_f.trans hx22_m,
      hx23_f.trans hx23_m, hx24_f.trans hx24_m, hx25_f.trans hx25_m, hx26_f.trans hx26_m,
      hx27_f, hx28_f.trans hx28_m, hv8_f.trans hv8_m, hv11_f.trans hv11_m, hPf⟩

/-- Composed `Seg2` `decompress_11` sub-segment (`+0x05dc → +0x06f0`). -/
theorem seg2_decompress11_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp ctPtr idx : BitVec 64) (ctSlice : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 0x05dc#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hx0 : s.readReg64 .x0 = ctPtr)
    (hx22 : s.readReg64 .x22 = idx)
    (hx27 : s.readReg64 .x27 = sp + 4160#64)
    (hv8 : (s.readVReg128 8#5).truncate 64 = 0x0d010d010d010d01#64)
    (hct : ctSlice.length = 352) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x06f0#64) s
      (stackAt sp 1136 ∗ memRegion (sp + 2400#64) 8 ∗ memRegion (sp + 2416#64) 8 ∗
        memRegion (sp + 4160#64) 512 ∗ memRegion (sp + 28368#64) 32 ∗
        (ctPtr ↦ₛ ctSlice) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x22 = idx ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = sp + 4160#64 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readVReg128 8#5 = s.readVReg128 8#5 ∧
        (Pf ⊢ stackAt sp 1136 ∗ ((sp + 2400#64) ↦₆₄ (idx + 1#64)) ∗
          ((sp + 2416#64) ↦₆₄ (ctPtr + 352#64)) ∗
          PolyMem (sp + 4160#64) (polyVecNat (decompressPoly16 11 ctSlice)) ∗
          memRegion (sp + 28368#64) 32 ∗ (ctPtr ↦ₛ ctSlice) ∗ Rest)) := by
  have hP0 :
      stackAt sp 1136 ∗ memRegion (sp + 2400#64) 8 ∗ memRegion (sp + 2416#64) 8 ∗
        memRegion (sp + 4160#64) 512 ∗ memRegion (sp + 28368#64) 32 ∗
        (ctPtr ↦ₛ ctSlice) ∗ Rest ⊢
      memRegion (sp + 4160#64) 512 ∗ memRegion (sp + 2400#64) 8 ∗ memRegion (sp + 2416#64) 8 ∗
        (stackAt sp 1136 ∗ memRegion (sp + 28368#64) 32 ∗ (ctPtr ↦ₛ ctSlice) ∗ Rest) := by
    sep_frame
  refine SepWP.weaken_pre hP0
    (sepWP_seq_codeLoaded hcl
      (seg2_decompress11_init hb hbase s sp ctPtr idx _ hpc hrun hsp hspA hx0 hx22) ?_)
  rintro s1 P1 hpc1 hrun1 hcl1
    ⟨hsp1, hspA1, hfp_1, hx0_1, hx21_1, hx19_1, hx22_1, hx23_1, hx24_1,
      hx25_1, hx26_1, hx27_1, hx28_1, hv8_1, hP1⟩
  have hP1' : P1 ⊢
      stackAt sp 1136 ∗ memRegion (sp + 28368#64) 32 ∗ (ctPtr ↦ₛ ctSlice) ∗
        PolyMem (sp + 4160#64) (fun _ => 0#128) ∗
        (((sp + 2400#64) ↦₆₄ (idx + 1#64)) ∗ ((sp + 2416#64) ↦₆₄ (ctPtr + 352#64)) ∗ Rest) :=
    Entails.trans hP1 (by sep_frame)
  refine SepWP.weaken_pre hP1'
    (SepWP.mono
      (seg2_decompress11_loop hb hbase sp ctPtr ctSlice _ hct 15 0 rfl s1 (fun _ => 0#128)
        hpc1 hrun1 hsp1 hspA1 hcl1 (by simp [hx0_1]) (by simp [hx21_1])
        (hx27_1.trans hx27) (hv8_1 ▸ hv8) (by omega)) ?_)
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hfp_f, hx19_f, hx22_f, hx23_f, hx24_f,
    hx25_f, hx26_f, hx27_f, hx28_f, hv8_f, _, hPf⟩
  exact ⟨hsp_f, hspA_f, hfp_f.trans hfp_1, hx19_f.trans hx19_1, hx22_f.trans hx22_1,
    hx23_f.trans hx23_1, hx24_f.trans hx24_1, hx25_f.trans hx25_1, hx26_f.trans hx26_1,
    hx27_f, hx28_f.trans hx28_1, hv8_f.trans hv8_1, Entails.trans hPf (by sep_frame)⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg2Decompress
