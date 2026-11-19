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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2Loop
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg3Simd

/-!
# `validate_pk_bytes` (`B21`) — Segment 3 Setup, Dead-Store & `memcpy` Blocks (`Role::Proof`)

Proves the pure `bcmp` ↔ `mlkem768ValidPk` equivalence and steps Setup 1 (`+0x044c → +0x04c8`),
Copy 1 + Setup 2 (`+0x0560 → +0x0604`), and Copy 2 + Setup 3 (`+0x069c → +0x0740`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg3Copy

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement add_off_reloc_cancel add_reloc_cancel add_zero_reloc_cancel mbase
  mlkemBlockPlacement_ρ mlkemCall_of_blockOk mlkemMpl resolve_blk28 seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (mlkemMemcpySpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  byteDecodeRaw mlkem768ValidPk mlkemQ sha3_256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk28_memcpy_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Base (
  blk21_code_eq blk21_tree_size blkLib21 blkPC21 blkPl21 blkPlaceable21 blkTree21
  reencodePoly384 reencodePoly384_eq_iff)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg1 (
  UnspilledSaved entails_sub sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 (
  setPC_setMem_collapse)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2Loop (
  dup8x16_3329 exec_simdDup_8h_gpr exec_simdMovi_2d_0 step_dead_strQ)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg3Simd (
  reencodePolyPrefix_16 reencodePolyPrefix_length)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC21 blkLib21 blkTree21 blk21_code_eq blk21_tree_size
  via_placement blkPl21 blkPlaceable21
  [0x044c → 0x04c4, 0x0560 → 0x0600, 0x069c → 0x073c]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl21_ρ [MlKemPlacement] (sym : String) :
    blkPl21.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl
@[simp, arm64_norm, wp_norm]
private theorem dup8x16_3329_norm :
    dup8x16 ((3329#64 : BitVec 64).truncate 16) = 0x0d010d010d010d010d010d010d010d01#128 := dup8x16_3329

private theorem sepWP_bind_state {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop}
    (h : ∀ s1 : State, s1 = s → SepWP prog target s1 P post) : SepWP prog target s P post := h s rfl
private theorem state_eq_setPC_setMem (s : State) {pc : BitVec 64} (h : s.pc = pc) :
    s = (s.setPC pc).setMem s.mem := by cases s; subst h; rfl

/-! ## 1. Pure `reencodePoly384` Length, `memRegion` Collapse, & `mlkem768ValidPk` Equivalence -/

@[simp] theorem reencodePoly384_length (bs : List (BitVec 8)) :
    (reencodePoly384 bs).length = 384 := by
  rw [← reencodePolyPrefix_16, reencodePolyPrefix_length]

theorem pointsToBytes_reencode_entails_memRegion (a : BitVec 64) (bs : List (BitVec 8)) :
    (a ↦ₛ reencodePoly384 bs) ⊢ memRegion a 384 := by
  simpa [reencodePoly384_length] using pointsToBytes_entails_memRegion a (reencodePoly384 bs)

section
attribute [local irreducible] sha3_256List byteDecodeRaw reencodePoly384

theorem reencode_bcmp_eq_iff_validPk {hdr ek : List (BitVec 8)}
    (hhdr : hdr.length = 64) (hek : ek.length = 1152)
    (hhash : sha3_256List (ek ++ hdr.take 32) = (hdr.drop 32).take 32) :
    ek ++ hdr.take 32 =
      reencodePoly384 (ek.take 384) ++
        reencodePoly384 ((ek.drop 384).take 384) ++
        reencodePoly384 ((ek.drop 768).take 384) ++
        hdr.take 32 ↔
      mlkem768ValidPk hdr ek = true := by
  let bs0 := ek.take 384
  let bs1 := (ek.drop 384).take 384
  let bs2 := (ek.drop 768).take 384
  have hl0 : bs0.length = 384 := by simp [bs0, hek]
  have hl1 : bs1.length = 384 := by simp [bs1, hek]
  have hl2 : bs2.length = 384 := by simp [bs2, hek]
  have hek_eq : ek = bs0 ++ bs1 ++ bs2 := by
    have h1 := (List.take_append_drop 384 ek).symm
    have h2 := (List.take_append_drop 384 (ek.drop 384)).symm
    rw [List.drop_drop] at h2
    have h3 : bs2 = ek.drop 768 := List.take_of_length_le (by simp [hek])
    dsimp only [bs0, bs1]; rw [h3, List.append_assoc]
    exact h1.trans (congrArg (ek.take 384 ++ ·) h2)
  have hlhs :
      (ek ++ hdr.take 32 =
        reencodePoly384 bs0 ++ reencodePoly384 bs1 ++ reencodePoly384 bs2 ++ hdr.take 32) ↔
      (reencodePoly384 bs0 = bs0 ∧ reencodePoly384 bs1 = bs1 ∧ reencodePoly384 bs2 = bs2) := by
    constructor
    · intro h
      conv at h => lhs; arg 1; rw [hek_eq]
      have ⟨h012, _⟩ := List.append_inj h (by simp [hl0, hl1, hl2])
      have ⟨h01, h2⟩ := List.append_inj h012 (by simp [hl0, hl1])
      have ⟨h0, h1⟩ := List.append_inj h01 (by simp [hl0])
      exact ⟨h0.symm, h1.symm, h2.symm⟩
    · rintro ⟨h0, h1, h2⟩
      rw [h0, h1, h2, ← hek_eq]
  rw [hlhs, reencodePoly384_eq_iff hl0, reencodePoly384_eq_iff hl1, reencodePoly384_eq_iff hl2]
  unfold mlkem768ValidPk
  have hr3 : List.range 3 = [0, 1, 2] := by decide
  simp only [hhdr, hek, bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ite_false, hhash,
    beq_self_eq_true, Bool.true_and, hr3, List.all_cons, List.all_nil, Bool.and_true, Nat.mul_zero,
    List.drop_zero, Nat.mul_one, show 384 * 2 = 768 from rfl, Bool.and_eq_true]
  rfl
end

/-! ## 2. `CodeLoaded` Sequencing, Unrolled Dead-Store Macro, & Setup / Copy Blocks -/

theorem sepWP_seq_cl {prog : Program} {mid target : BitVec 64} {s : State}
    {P : SepProp} {post1 post2 : State → SepProp → Prop} {mpl : MultiPlacement}
    (hcl : mlkemMultiLib.CodeLoaded mpl s.mem)
    (h1 : SepWP prog mid s P post1)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      mlkemMultiLib.CodeLoaded mpl sm.mem → post1 sm Pm → SepWP prog target sm Pm post2) :
    SepWP prog target s P post2 :=
  SepWP.seq
    (SepWP.mono_frozen
      (post' := fun sm Pm => mlkemMultiLib.CodeLoaded mpl sm.mem ∧ post1 sm Pm)
      (Φ := mlkemMultiLib.CodeLoaded mpl)
      (fun _ _ hc hkf => hc.of_keepsFrozen hkf)
      hcl h1 (fun _ _ _ _ hc hp1 => ⟨hc, hp1⟩))
    (fun sm Pm hpc hrun ⟨hc, hp1⟩ => h2 sm Pm hpc hrun hc hp1)

attribute [local irreducible] reencodePoly384

local macro "dead_strQ1 " bo:num tot:num pc:num sp:num : tactic =>
  `(tactic| (
    intro m_cur
    refine step_dead_strQ (m := m_cur) $bo $tot ($pc : Nat) (($pc : Nat) + 4) ($sp : Nat)
      (($sp : Nat) - $bo) 1#5 ‹_› ‹_› (by simp only [BitVec.ofNat_eq_ofNat, arm64_norm])
      (by omega) (by omega) (by omega) (by omega) fun m_nxt => ?_
    clear m_cur; revert m_nxt))

theorem seg3_setup1 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl21 b) (_hbase : blkPl21.base = b)
    (s0 s : State) (sp : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + 0x044c#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : (sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = sp + 1168#64)
    (hx20 : s.readReg64 .x20 = sp + 2736#64)
    (hx21 : s.readReg64 .x21 = sp + 1200#64)
    (hus : UnspilledSaved s0 s) :
    SepWP (blkPC21.rebase b (fun _ => none)) (b + 0x04c8#64) s
      (memRegion (sp + 4304#64) 384 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.readReg64 .x8 = BitVec.ofNat 64 (24 * 0) ∧
        sf.readReg64 .x9 = (sp + 1200#64) + BitVec.ofNat 64 (32 * 0) + 16#64 ∧
        sf.readReg64 .x10 = sp + 4304#64 ∧
        sf.readReg64 .x19 = sp + 1168#64 ∧ sf.readReg64 .x20 = sp + 2736#64 ∧
        sf.readReg64 .x21 = sp + 1200#64 ∧ UnspilledSaved s0 sf ∧
        Pf = (memRegion (sp + 4304#64) 384 ∗ Rest)) := by
  have hsp_align : s.spAligned = true := by rw [State.spAligned, hsp]; exact hspA
  wp_steps 7; refine sepWP_bind_state fun s1 hs1 => ?_
  have hrun1 : s1.status = .Running := by simp [hs1, hrun]
  have hspA1 : s1.spAligned = true := by simp [hs1, State.spAligned] at hsp_align ⊢; exact hsp_align
  have hsp1 : s1.sp = sp := by simp [hs1, hsp]
  conv => arg 3; rw [state_eq_setPC_setMem s1 (pc := b + BitVec.ofNat 64 0x0468) (by simp [hs1, wp_norm, arm64_norm])]
  conv => arg 4; arg 1; rw [← hsp1, show (4304#64 : BitVec 64) = BitVec.ofNat 64 4304 from rfl]
  generalize s1.mem = m; revert m
  dead_strQ1 4304 384 0x0468 4672; dead_strQ1 4304 384 0x046c 4656; dead_strQ1 4304 384 0x0470 4640; dead_strQ1 4304 384 0x0474 4624; dead_strQ1 4304 384 0x0478 4608; dead_strQ1 4304 384 0x047c 4592; dead_strQ1 4304 384 0x0480 4576; dead_strQ1 4304 384 0x0484 4560
  dead_strQ1 4304 384 0x0488 4544; dead_strQ1 4304 384 0x048c 4528; dead_strQ1 4304 384 0x0490 4512; dead_strQ1 4304 384 0x0494 4496; dead_strQ1 4304 384 0x0498 4480; dead_strQ1 4304 384 0x049c 4464; dead_strQ1 4304 384 0x04a0 4448; dead_strQ1 4304 384 0x04a4 4432
  dead_strQ1 4304 384 0x04a8 4416; dead_strQ1 4304 384 0x04ac 4400; dead_strQ1 4304 384 0x04b0 4384; dead_strQ1 4304 384 0x04b4 4368; dead_strQ1 4304 384 0x04b8 4352; dead_strQ1 4304 384 0x04bc 4336; dead_strQ1 4304 384 0x04c0 4320; dead_strQ1 4304 384 0x04c4 4304
  intro _
  apply SepWP.done (by simp) (by simp [hrun1])
  exact ⟨by simp [hsp1], by simp [hs1], by simp [hs1], by simp [hs1],
    by simp [hs1, hx19], by simp [hs1, hx20], by simp [hs1, hx21],
    ⟨by simp [hs1, hus.1], by simp [hs1, hus.2.1], by simp [hs1, hus.2.2.1],
      by simp [hs1, hus.2.2.2.1], by simp [hs1, calleeSavedVRegs, hus.2.2.2.2]⟩,
    by rw [hsp1, show BitVec.ofNat 64 4304 = 4304#64 from rfl]⟩

private theorem seg3_copy1a [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl21 b) (_hbase : blkPl21.base = b)
    (s0 s : State) (sp : BitVec 64) (bs0 : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 0x0560#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : (sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = sp + 1168#64) (hx20 : s.readReg64 .x20 = sp + 2736#64)
    (hus : UnspilledSaved s0 s) (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC21.rebase b (fun _ => none)) (b + 0x057c#64) s
      (memRegion (sp + 3920#64) 384 ∗ ((sp + 4304#64) ↦ₛ reencodePoly384 bs0) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.readReg64 .x19 = sp + 1168#64 ∧ sf.readReg64 .x20 = sp + 2736#64 ∧
        sf.readReg64 .x21 = sp + 4304#64 ∧ UnspilledSaved s0 sf ∧
        (Pf ⊢ ((sp + 3920#64) ↦ₛ reencodePoly384 bs0) ∗ ((sp + 4304#64) ↦ₛ reencodePoly384 bs0) ∗ Rest)) := by
  have hsp_align : s.spAligned = true := by rw [State.spAligned, hsp]; exact hspA
  have ha4304 : sp + 4096#64 + 208#64 = sp + 4304#64 := by bv_omega
  have hlen : (reencodePoly384 bs0).length = 384 := reencodePoly384_length bs0
  rw [show memRegion (sp + 3920#64) 384 = memRegion (sp + 3920#64) (reencodePoly384 bs0).length by rw [hlen]]
  wp_cut_codeLoaded; wp_steps
  wp_mlkem_call blk28_memcpy_ok (sp + 3920#64, sp + 4304#64, reencodePoly384 bs0)
  refine SepWP.done hpc_sf hrun_sf
    ⟨hsp_sf.trans hsp, h.trans hx19, h_1.trans hx20, h_2.trans (by simp),
      ⟨h_5.trans hus.1, h_6.trans hus.2.1, h_7.trans hus.2.2.1, h_8.trans hus.2.2.2.1, hvregs.trans hus.2.2.2.2⟩,
      by sep_frame⟩

theorem seg3_copy1_setup2 [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl21 b) (hbase : blkPl21.base = b)
    (s0 s : State) (sp : BitVec 64) (bs0 : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 0x0560#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : (sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = sp + 1168#64) (hx20 : s.readReg64 .x20 = sp + 2736#64)
    (hus : UnspilledSaved s0 s) (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC21.rebase b (fun _ => none)) (b + 0x0604#64) s
      (memRegion (sp + 2736#64) 384 ∗ memRegion (sp + 3920#64) 384 ∗
        ((sp + 4304#64) ↦ₛ reencodePoly384 bs0) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.readReg64 .x8 = BitVec.ofNat 64 (24 * 0) ∧
        sf.readReg64 .x9 = (sp + 1712#64) + BitVec.ofNat 64 (32 * 0) + 16#64 ∧
        sf.readReg64 .x19 = sp + 1168#64 ∧ sf.readReg64 .x20 = sp + 2736#64 ∧
        sf.readReg64 .x21 = sp + 4304#64 ∧ UnspilledSaved s0 sf ∧
        (Pf ⊢ ((sp + 2736#64) ↦ₛ reencodePoly384 bs0) ∗ memRegion (sp + 3920#64) 384 ∗
          memRegion (sp + 4304#64) 384 ∗ Rest)) := by
  refine sepWP_seq_cl hcl
    (SepWP.weaken_pre (by sep_frame)
      (seg3_copy1a hb hbase s0 s sp bs0 (memRegion (sp + 2736#64) 384 ∗ Rest)
        hpc hrun hsp hspA hx19 hx20 hus hcl)) ?_
  rintro sm Pm hpcm hrunm hclm ⟨hspm, hx19m, hx20m, hx21m, husm, hPm⟩
  refine SepWP.weaken_pre hPm ?_
  have hsp_align : sm.spAligned = true := by rw [State.spAligned, hspm]; exact hspA
  have hlen : (reencodePoly384 bs0).length = 384 := reencodePoly384_length bs0
  rw [show memRegion (sp + 2736#64) 384 = memRegion (sp + 2736#64) (reencodePoly384 bs0).length by rw [hlen]]
  wp_cut_codeLoaded; wp_steps
  wp_mlkem_call blk28_memcpy_ok (sp + 2736#64, sp + 3920#64, reencodePoly384 bs0)
  have hus_sf : UnspilledSaved s0 sf :=
    ⟨h_5.trans husm.1, h_6.trans husm.2.1, h_7.trans husm.2.2.1, h_8.trans husm.2.2.2.1, hvregs.trans husm.2.2.2.2⟩
  have hsp_sf' : sf.sp = sp := hsp_sf.trans hspm
  have hspA_sf : sf.spAligned = true := by rw [State.spAligned, hsp_sf']; exact hspA
  refine SepWP.weaken_pre
    (entails_sub (pointsToBytes_reencode_entails_memRegion (sp + 3920#64) bs0) (by sep_frame)
      (entails_sub (pointsToBytes_reencode_entails_memRegion (sp + 4304#64) bs0) (by sep_frame)
        (show memRegion (sp + 4304#64) 384 ∗ _ ⊢
          memRegion (sp + 4304#64) 384 ∗
            (((sp + 2736#64) ↦ₛ reencodePoly384 bs0) ∗ memRegion (sp + 3920#64) 384 ∗ Rest) by
          sep_frame))) ?_
  wp_steps 6; refine sepWP_bind_state fun s1 hs1 => ?_
  have hrun1 : s1.status = .Running := by simp [hs1, hrun_sf]
  have hspA1 : s1.spAligned = true := by simp [hs1, State.spAligned] at hspA_sf ⊢; exact hspA_sf
  have hsp1 : s1.sp = sp := by simp [hs1, hsp_sf']
  conv => arg 3; rw [state_eq_setPC_setMem s1 (pc := b + BitVec.ofNat 64 0x05a4) (by simp [hs1, wp_norm, arm64_norm])]
  conv => arg 4; arg 1; rw [← hsp1, show (4304#64 : BitVec 64) = BitVec.ofNat 64 4304 from rfl]
  generalize s1.mem = m; revert m
  dead_strQ1 4304 384 0x05a4 4672; dead_strQ1 4304 384 0x05a8 4656; dead_strQ1 4304 384 0x05ac 4640; dead_strQ1 4304 384 0x05b0 4624; dead_strQ1 4304 384 0x05b4 4608; dead_strQ1 4304 384 0x05b8 4592; dead_strQ1 4304 384 0x05bc 4576; dead_strQ1 4304 384 0x05c0 4560
  dead_strQ1 4304 384 0x05c4 4544; dead_strQ1 4304 384 0x05c8 4528; dead_strQ1 4304 384 0x05cc 4512; dead_strQ1 4304 384 0x05d0 4496; dead_strQ1 4304 384 0x05d4 4480; dead_strQ1 4304 384 0x05d8 4464; dead_strQ1 4304 384 0x05dc 4448; dead_strQ1 4304 384 0x05e0 4432
  dead_strQ1 4304 384 0x05e4 4416; dead_strQ1 4304 384 0x05e8 4400; dead_strQ1 4304 384 0x05ec 4384; dead_strQ1 4304 384 0x05f0 4368; dead_strQ1 4304 384 0x05f4 4352; dead_strQ1 4304 384 0x05f8 4336; dead_strQ1 4304 384 0x05fc 4320; dead_strQ1 4304 384 0x0600 4304
  intro _
  apply SepWP.done (by simp) (by simp [hrun1])
  refine ⟨by simp [hsp1], by simp [hs1], by simp [hs1],
    by simp [hs1, h, hx19m], by simp [hs1, h_1, hx20m], by simp [hs1, h_2, hx21m],
    ⟨by simp [hs1, hus_sf.1], by simp [hs1, hus_sf.2.1], by simp [hs1, hus_sf.2.2.1],
      by simp [hs1, hus_sf.2.2.2.1], by simp [hs1, calleeSavedVRegs, hus_sf.2.2.2.2]⟩, ?_⟩
  rw [hsp1, show BitVec.ofNat 64 4304 = 4304#64 from rfl]; sep_frame

private theorem seg3_copy2a [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl21 b) (_hbase : blkPl21.base = b)
    (s0 s : State) (sp : BitVec 64) (bs1 : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 0x069c#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : (sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = sp + 1168#64) (hx20 : s.readReg64 .x20 = sp + 2736#64)
    (hus : UnspilledSaved s0 s) (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC21.rebase b (fun _ => none)) (b + 0x06b8#64) s
      (memRegion (sp + 3920#64) 384 ∗ ((sp + 4304#64) ↦ₛ reencodePoly384 bs1) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.readReg64 .x19 = sp + 1168#64 ∧ sf.readReg64 .x20 = sp + 2736#64 ∧
        sf.readReg64 .x21 = sp + 4304#64 ∧ UnspilledSaved s0 sf ∧
        (Pf ⊢ ((sp + 3920#64) ↦ₛ reencodePoly384 bs1) ∗ ((sp + 4304#64) ↦ₛ reencodePoly384 bs1) ∗ Rest)) := by
  have hsp_align : s.spAligned = true := by rw [State.spAligned, hsp]; exact hspA
  have ha4304 : sp + 4096#64 + 208#64 = sp + 4304#64 := by bv_omega
  have hlen : (reencodePoly384 bs1).length = 384 := reencodePoly384_length bs1
  rw [show memRegion (sp + 3920#64) 384 = memRegion (sp + 3920#64) (reencodePoly384 bs1).length by rw [hlen]]
  wp_cut_codeLoaded; wp_steps
  wp_mlkem_call blk28_memcpy_ok (sp + 3920#64, sp + 4304#64, reencodePoly384 bs1)
  refine SepWP.done hpc_sf hrun_sf
    ⟨hsp_sf.trans hsp, h.trans hx19, h_1.trans hx20, h_2.trans (by simp),
      ⟨h_5.trans hus.1, h_6.trans hus.2.1, h_7.trans hus.2.2.1, h_8.trans hus.2.2.2.1, hvregs.trans hus.2.2.2.2⟩,
      by sep_frame⟩

theorem seg3_copy2_setup3 [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl21 b) (hbase : blkPl21.base = b)
    (s0 s : State) (sp : BitVec 64) (bs1 : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 0x069c#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : (sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = sp + 1168#64) (hx20 : s.readReg64 .x20 = sp + 2736#64)
    (hus : UnspilledSaved s0 s) (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC21.rebase b (fun _ => none)) (b + 0x0740#64) s
      (memRegion (sp + 3120#64) 384 ∗ memRegion (sp + 3920#64) 384 ∗
        ((sp + 4304#64) ↦ₛ reencodePoly384 bs1) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.readReg64 .x8 = BitVec.ofNat 64 (24 * 0) ∧
        sf.readReg64 .x9 = (sp + 2224#64) + BitVec.ofNat 64 (32 * 0) + 16#64 ∧
        sf.readReg64 .x19 = sp + 1168#64 ∧ sf.readReg64 .x20 = sp + 2736#64 ∧
        sf.readReg64 .x21 = sp + 4304#64 ∧ UnspilledSaved s0 sf ∧
        (Pf ⊢ ((sp + 3120#64) ↦ₛ reencodePoly384 bs1) ∗ memRegion (sp + 3920#64) 384 ∗
          memRegion (sp + 4304#64) 384 ∗ Rest)) := by
  refine sepWP_seq_cl hcl
    (SepWP.weaken_pre (by sep_frame)
      (seg3_copy2a hb hbase s0 s sp bs1 (memRegion (sp + 3120#64) 384 ∗ Rest)
        hpc hrun hsp hspA hx19 hx20 hus hcl)) ?_
  rintro sm Pm hpcm hrunm hclm ⟨hspm, hx19m, hx20m, hx21m, husm, hPm⟩
  refine SepWP.weaken_pre hPm ?_
  have hsp_align : sm.spAligned = true := by rw [State.spAligned, hspm]; exact hspA
  have ha3120 : sp + 2736#64 + 384#64 = sp + 3120#64 := by bv_omega
  have hlen : (reencodePoly384 bs1).length = 384 := reencodePoly384_length bs1
  rw [show memRegion (sp + 3120#64) 384 = memRegion (sp + 3120#64) (reencodePoly384 bs1).length by rw [hlen]]
  wp_cut_codeLoaded; wp_steps
  wp_mlkem_call blk28_memcpy_ok (sp + 3120#64, sp + 3920#64, reencodePoly384 bs1)
  have hus_sf : UnspilledSaved s0 sf :=
    ⟨h_5.trans husm.1, h_6.trans husm.2.1, h_7.trans husm.2.2.1, h_8.trans husm.2.2.2.1, hvregs.trans husm.2.2.2.2⟩
  have hsp_sf' : sf.sp = sp := hsp_sf.trans hspm
  have hspA_sf : sf.spAligned = true := by rw [State.spAligned, hsp_sf']; exact hspA
  refine SepWP.weaken_pre
    (entails_sub (pointsToBytes_reencode_entails_memRegion (sp + 3920#64) bs1) (by sep_frame)
      (entails_sub (pointsToBytes_reencode_entails_memRegion (sp + 4304#64) bs1) (by sep_frame)
        (show memRegion (sp + 4304#64) 384 ∗ _ ⊢
          memRegion (sp + 4304#64) 384 ∗
            (((sp + 3120#64) ↦ₛ reencodePoly384 bs1) ∗ memRegion (sp + 3920#64) 384 ∗ Rest) by
          sep_frame))) ?_
  wp_steps 6; refine sepWP_bind_state fun s1 hs1 => ?_
  have hrun1 : s1.status = .Running := by simp [hs1, hrun_sf]
  have hspA1 : s1.spAligned = true := by simp [hs1, State.spAligned] at hspA_sf ⊢; exact hspA_sf
  have hsp1 : s1.sp = sp := by simp [hs1, hsp_sf']
  conv => arg 3; rw [state_eq_setPC_setMem s1 (pc := b + BitVec.ofNat 64 0x06e0) (by simp [hs1, wp_norm, arm64_norm])]
  conv => arg 4; arg 1; rw [← hsp1, show (4304#64 : BitVec 64) = BitVec.ofNat 64 4304 from rfl]
  generalize s1.mem = m; revert m
  dead_strQ1 4304 384 0x06e0 4672; dead_strQ1 4304 384 0x06e4 4656; dead_strQ1 4304 384 0x06e8 4640; dead_strQ1 4304 384 0x06ec 4624; dead_strQ1 4304 384 0x06f0 4608; dead_strQ1 4304 384 0x06f4 4592; dead_strQ1 4304 384 0x06f8 4576; dead_strQ1 4304 384 0x06fc 4560
  dead_strQ1 4304 384 0x0700 4544; dead_strQ1 4304 384 0x0704 4528; dead_strQ1 4304 384 0x0708 4512; dead_strQ1 4304 384 0x070c 4496; dead_strQ1 4304 384 0x0710 4480; dead_strQ1 4304 384 0x0714 4464; dead_strQ1 4304 384 0x0718 4448; dead_strQ1 4304 384 0x071c 4432
  dead_strQ1 4304 384 0x0720 4416; dead_strQ1 4304 384 0x0724 4400; dead_strQ1 4304 384 0x0728 4384; dead_strQ1 4304 384 0x072c 4368; dead_strQ1 4304 384 0x0730 4352; dead_strQ1 4304 384 0x0734 4336; dead_strQ1 4304 384 0x0738 4320; dead_strQ1 4304 384 0x073c 4304
  intro _
  apply SepWP.done (by simp) (by simp [hrun1])
  refine ⟨by simp [hsp1], by simp [hs1], by simp [hs1],
    by simp [hs1, h, hx19m], by simp [hs1, h_1, hx20m], by simp [hs1, h_2, hx21m],
    ⟨by simp [hs1, hus_sf.1], by simp [hs1, hus_sf.2.1], by simp [hs1, hus_sf.2.2.1],
      by simp [hs1, hus_sf.2.2.2.1], by simp [hs1, calleeSavedVRegs, hus_sf.2.2.2.2]⟩, ?_⟩
  rw [hsp1, show BitVec.ofNat 64 4304 = 4304#64 from rfl]; sep_frame

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg3Copy
