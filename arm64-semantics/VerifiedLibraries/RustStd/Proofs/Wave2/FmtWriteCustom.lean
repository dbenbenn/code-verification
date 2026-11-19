/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Spec
public import VerifiedLibraries.RustStd.Proofs.Wave2.FmtWriteOps

/-!
# `core::fmt::write` Custom Placeholders (`0xc1..0xff`)

Proves compositional join-point lemmas verifying the bitmask placeholder decoder
(`+0x074 .. +0x158`) for opcodes `0xc1 .. 0xff` (`cwStep_customArg`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj Arm64.Process ProofLib

/-! ## Bit, decoder, and slice-focusing helpers -/

private theorem cw_u8_zeroExtend64_getLsbD (n : BitVec 8) {k : Nat} (_hk : k < 8) :
    (n.zeroExtend 64).getLsbD k = n.getLsbD k := by
  simp only [BitVec.getLsbD, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans n.isLt (show 2 ^ 8 < 2 ^ 64 by omega))]

private theorem cw_setWidth32_setWidth64 (v : BitVec 32) :
    (BitVec.setWidth 64 v).setWidth 32 = v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := v.isLt; omega

private theorem cw_setWidth16_setWidth64 (v : BitVec 16) :
    (BitVec.setWidth 64 v).setWidth 16 = v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := v.isLt; omega

private theorem cw_u16_w32_ext (v : BitVec 16) :
    ((v.zeroExtend 64).setWidth 32).setWidth 64 = BitVec.setWidth 64 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.zeroExtend, BitVec.toNat_setWidth]
  have := v.isLt; omega

private theorem cw_u16_shl4_eq_mul16 (v : BitVec 16) :
    (BitVec.setWidth 64 v) <<< 4 = BitVec.ofNat 64 (16 * v.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have := v.isLt; omega

private theorem cw_leBytesNat_take2_lt {r : List (BitVec 8)} (h : 2 ≤ r.length) :
    leBytesNat (r.take 2) < 65536 := by
  match r with
  | b0 :: b1 :: _ => exact leBytesNat_pair_lt b0 b1

private theorem cw_tpl_focus_u16 (tplPtr : BitVec 64) (tpl : List (BitVec 8))
    (off : Nat) (r : List (BitVec 8))
    (hdrop : tpl.drop off = r) (hle : off ≤ tpl.length) (hr : 2 ≤ r.length) :
    (tplPtr ↦ᵣ tpl) =
      ((tplPtr + BitVec.ofNat 64 off) ↦₁₆ᵣ BitVec.ofNat 16 (leBytesNat (r.take 2))) ∗
      ((tplPtr ↦ᵣ tpl.take off) ∗ ((tplPtr + BitVec.ofNat 64 (off + 2)) ↦ᵣ r.drop 2)) := by
  match r with
  | b0 :: b1 :: suf =>
    have hf := tpl_focus_sublist tplPtr tpl off [b0, b1] suf hdrop hle
    simp only [List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero,
      List.drop_succ_cons, List.drop_zero] at hf ⊢
    rw [hf, pointsToBytesRO_pair_eq_le16]

private theorem cw_tpl_focus_u32 (tplPtr : BitVec 64) (tpl : List (BitVec 8))
    (off : Nat) (r : List (BitVec 8))
    (hdrop : tpl.drop off = r) (hle : off ≤ tpl.length) (hr : 4 ≤ r.length) :
    (tplPtr ↦ᵣ tpl) =
      ((tplPtr + BitVec.ofNat 64 off) ↦₃₂ᵣ BitVec.ofNat 32 (leBytesNat (r.take 4))) ∗
      ((tplPtr ↦ᵣ tpl.take off) ∗ ((tplPtr + BitVec.ofNat 64 (off + 4)) ↦ᵣ r.drop 4)) := by
  match r with
  | b0 :: b1 :: b2 :: b3 :: suf =>
    have hf := tpl_focus_sublist tplPtr tpl off [b0, b1, b2, b3] suf hdrop hle
    simp only [List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero,
      List.drop_succ_cons, List.drop_zero] at hf ⊢
    rw [hf, pointsToBytesRO_quad_eq_le32]

private theorem cwLoopMemFmt_transport {σ : Type} (C : CwCtx σ) {st : σ} {pad : BitVec 64}
    {opts : FmtOptions} {s1 s2 : State}
    (htrans : ∀ (st : σ) (s1 s2 : State), FmtWriteFrame s1 s2 → C.W st s1 ⊢ C.W st s2)
    (hframe : FmtWriteFrame s1 s2) :
    CwLoopMemFmt C st pad opts s1 ⊢ CwLoopMemFmt C st pad opts s2 :=
  sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (htrans st s1 s2 hframe)))

theorem decodeFmtPlaceholder_inv {n : BitVec 8} {rest : List (BitVec 8)}
    {args : List (BitVec 64 × BitVec 64)} {ai : Nat}
    {opts : FmtOptions} {idx ai' k : Nat}
    (h : decodeFmtPlaceholder n rest args ai = some (opts, idx, ai', k)) :
    let lf := if n.getLsbD 0 then 4 else 0
    let lw := if n.getLsbD 1 then 2 else 0
    let lp := if n.getLsbD 2 then 2 else 0
    let li := if n.getLsbD 3 then 2 else 0
    let r1 := rest.drop lf
    let r2 := r1.drop lw
    let r3 := r2.drop lp
    let flags := if n.getLsbD 0 then BitVec.ofNat 32 (leBytesNat (rest.take 4)) else 0x60000020#32
    let width0 := if n.getLsbD 1 then BitVec.ofNat 16 (leBytesNat (r1.take 2)) else 0#16
    let prec0 := if n.getLsbD 2 then BitVec.ofNat 16 (leBytesNat (r2.take 2)) else 0#16
    lf + lw + lp + li ≤ rest.length ∧
    k = lf + lw + lp + li ∧
    idx = (if n.getLsbD 3 then leBytesNat (r3.take 2) else ai) ∧
    ai' = idx + 1 ∧
    opts.flags = flags ∧
    (if n.getLsbD 4 then fmtCountAt args width0.toNat else some width0) = some opts.width ∧
    (if n.getLsbD 5 then fmtCountAt args prec0.toNat else some prec0) = some opts.precision := by
  unfold decodeFmtPlaceholder at h
  by_cases hlen : rest.length <
      (if n.getLsbD 0 then 4 else 0) + (if n.getLsbD 1 then 2 else 0) +
      (if n.getLsbD 2 then 2 else 0) + (if n.getLsbD 3 then 2 else 0)
  · simp only [hlen, ↓reduceIte] at h; cases h
  · simp only [hlen, ↓reduceIte] at h
    have hle := Nat.le_of_not_lt hlen
    generalize hw : (if n.getLsbD 4 then
      fmtCountAt args (if n.getLsbD 1 then BitVec.ofNat 16 (leBytesNat ((rest.drop (if n.getLsbD 0 then 4 else 0)).take 2)) else 0#16).toNat
      else some (if n.getLsbD 1 then BitVec.ofNat 16 (leBytesNat ((rest.drop (if n.getLsbD 0 then 4 else 0)).take 2)) else 0#16)) = w? at h
    generalize hp : (if n.getLsbD 5 then
      fmtCountAt args (if n.getLsbD 2 then BitVec.ofNat 16 (leBytesNat (((rest.drop (if n.getLsbD 0 then 4 else 0)).drop (if n.getLsbD 1 then 2 else 0)).take 2)) else 0#16).toNat
      else some (if n.getLsbD 2 then BitVec.ofNat 16 (leBytesNat (((rest.drop (if n.getLsbD 0 then 4 else 0)).drop (if n.getLsbD 1 then 2 else 0)).take 2)) else 0#16)) = p? at h
    match w?, p? with
    | none, _ => cases h
    | some _, none => cases h
    | some width, some prec =>
      dsimp only at h
      injection h with h
      rcases Prod.mk.inj h with ⟨hopts, hrest_eq⟩
      rcases Prod.mk.inj hrest_eq with ⟨hidx, hrest_eq2⟩
      rcases Prod.mk.inj hrest_eq2 with ⟨hai', hk⟩
      subst hopts; subst hidx; subst hai'; subst hk
      exact ⟨hle, rfl, rfl, rfl, rfl, hw, hp⟩

/-! ## Join-point stepping lemmas (`0xc1 .. 0xff`) -/

section
arm64_proof_prelude

private theorem cwCustom_d1 [CoreFmtWritePl] {σ : Type} (C : CwCtx σ)
    (hext_blk : ∀ off : Nat, off < 436 →
      C.P.externAt? (coreFmtMpl.base 0 + BitVec.ofNat 64 off) = none)
    {pos : Nat} {n : BitVec 8} {rest : List (BitVec 8)} {cs : List FmtCall}
    {st : σ} {pad : BitVec 64} {s : State}
    (hcl : coreMultiLib.CodeLoaded coreFmtMpl s.mem)
    (hdrop1 : C.tpl.drop (pos + 1) = rest)
    (hpos1_le : pos + 1 ≤ C.tpl.length)
    (hn_ge : ¬ n.toNat < 0x80) (hne80 : n ≠ 0x80#8) (hnec0 : n ≠ 0xc0#8)
    (hlf_le : (if n.getLsbD 0 then 4 else 0) ≤ rest.length)
    (htrans : ∀ (st : σ) (s1 s2 : State), FmtWriteFrame s1 s2 → C.W st s1 ⊢ C.W st s2)
    (hpc : s.pc = cwPl0.base + 116#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = C.s0.sp - 112#64)
    (hsp_al : s.spAligned = true)
    (hx2 : s.readReg64 (.gpr 2#5) = C.tplPtr + BitVec.ofNat 64 pos)
    (hx8 : s.readReg64 (.gpr 8#5) = n.zeroExtend 64)
    (hcont : ∀ sm : State,
      coreMultiLib.CodeLoaded coreFmtMpl sm.mem →
      sm.pc = (if n.getLsbD 1 then cwPl0.base + 188#64 else cwPl0.base + 256#64) →
      sm.status = .Running →
      sm.sp = C.s0.sp - 112#64 →
      sm.spAligned = true →
      sm.readReg64 (.gpr 8#5) = n.zeroExtend 64 →
      sm.readReg64 (.gpr 9#5) =
        BitVec.setWidth 64 (if n.getLsbD 0 then BitVec.ofNat 32 (leBytesNat (rest.take 4)) else 0x60000020#32) →
      sm.readReg64 (.gpr 22#5) = C.tplPtr + BitVec.ofNat 64 (pos + 1 + if n.getLsbD 0 then 4 else 0) →
      (∀ r : BitVec 5, r ≠ 2#5 → r ≠ 8#5 → r ≠ 9#5 → r ≠ 22#5 →
        sm.readReg64 (.gpr r) = s.readReg64 (.gpr r)) →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      SepWPp C.P C.ret_pc sm (CwLoopMem C st pad sm) (CwQ C cs st) (CwQp C cs st) (CwOom C cs st)) :
    SepWPp C.P C.ret_pc s (CwLoopMem C st pad s) (CwQ C cs st) (CwQp C cs st) (CwOom C cs st) := by
  rcases u8_ne_0x80_ne_0xc0_bit7 hn_ge hne80 hnec0 with ⟨hb7, hne80_w, hnec0_w⟩
  have hb0_ext : (n.zeroExtend 64).getLsbD 0 = n.getLsbD 0 := cw_u8_zeroExtend64_getLsbD n (by omega)
  have hb1_ext : (n.zeroExtend 64).getLsbD 1 = n.getLsbD 1 := cw_u8_zeroExtend64_getLsbD n (by omega)
  cases hb0 : n.getLsbD 0
  ·
    rw [hb0] at hb0_ext
    cases hb1 : n.getLsbD 1 <;> {
      rw [hb1] at hb1_ext
      simp only [hb0, hb1, ↓reduceIte, Bool.false_eq_true, Nat.add_zero] at hcont
      apply sepWPp_seg_coreFmt_pure hext_blk hcl
        (mid := if n.getLsbD 1 then cwPl0.base + 188#64 else cwPl0.base + 256#64)
      intro s' hcpu_in
      have hpc' : s'.pc = cwPl0.base + 116#64 := hcpu_in.pc_eq.trans hpc
      have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
      have hsp' : s'.sp = C.s0.sp - 112#64 := hcpu_in.sp_eq.trans hsp
      have hsp_al' : s'.spAligned = true := hcpu_in.spAligned.trans hsp_al
      have hx2' : s'.readReg64 (.gpr 2#5) = C.tplPtr + BitVec.ofNat 64 pos := (hcpu_in.readReg64 _).trans hx2
      have hx8' : s'.readReg64 (.gpr 8#5) = n.zeroExtend 64 := (hcpu_in.readReg64 _).trans hx8
      simp only [hb1, ↓reduceIte, Bool.false_eq_true]
      clear hpc
      wp_sym_steps
      refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
        fun sm hcpu_out hcl_sm hnsp hsig htp horc hsym => ?_
      have hframe : FmtWriteFrame s sm := fmtWriteFrame_of_seg hnsp hsig htp horc hsym
      refine SepWPp.weaken_pre (cwLoopMem_transport C htrans hframe) ?_
      refine hcont sm hcl_sm
        (by rw [hcpu_out.pc_eq]; simp [arm64_norm])
        (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
        (by rw [hcpu_out.sp_eq]; simp [arm64_norm, hsp'])
        (by simp [arm64_norm] at hsp_al'; rw [hcpu_out.spAligned]; simpa [arm64_norm] using hsp_al')
        (by rw [hcpu_out.readReg64]; simp [arm64_norm, hx8'])
        (by rw [hcpu_out.readReg64]; simp [arm64_norm])
        (by rw [hcpu_out.readReg64]; simp [arm64_norm, BitVec.add_assoc, ← bv64_add_ofNat])
        (fun r _hr2 _hr8 hr9 hr22 => by
          rw [hcpu_out.readReg64]
          simp [arm64_norm, hr9, hr22, hcpu_in.readReg64])
        (by rw [hcpu_out.calleeSavedVRegs]; simp [arm64_norm, hcpu_in.calleeSavedVRegs])
    }
  ·
    rw [hb0] at hb0_ext hlf_le
    simp only [↓reduceIte] at hlf_le
    have htpl_u32 : (C.tplPtr ↦ᵣ C.tpl) =
        ((C.tplPtr + BitVec.ofNat 64 pos + 1#64) ↦₃₂ᵣ BitVec.ofNat 32 (leBytesNat (rest.take 4))) ∗
        ((C.tplPtr ↦ᵣ C.tpl.take (pos + 1)) ∗
         ((C.tplPtr + BitVec.ofNat 64 (pos + 1 + 4)) ↦ᵣ rest.drop 4)) := by
      rw [cw_tpl_focus_u32 C.tplPtr C.tpl (pos + 1) rest hdrop1 hpos1_le hlf_le]
      have ha : C.tplPtr + BitVec.ofNat 64 (pos + 1) = C.tplPtr + BitVec.ofNat 64 pos + 1#64 := by
        rw [BitVec.add_assoc, ← bv64_add_ofNat]
      rw [ha]
    cases hb1 : n.getLsbD 1 <;> {
      rw [hb1] at hb1_ext
      simp only [hb0, hb1, ↓reduceIte, Bool.false_eq_true] at hcont
      apply sepWPp_seg_coreFmt_pure hext_blk hcl
        (mid := if n.getLsbD 1 then cwPl0.base + 188#64 else cwPl0.base + 256#64)
      intro s' hcpu_in
      have hpc' : s'.pc = cwPl0.base + 116#64 := hcpu_in.pc_eq.trans hpc
      have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
      have hsp' : s'.sp = C.s0.sp - 112#64 := hcpu_in.sp_eq.trans hsp
      have hsp_al' : s'.spAligned = true := hcpu_in.spAligned.trans hsp_al
      have hx2' : s'.readReg64 (.gpr 2#5) = C.tplPtr + BitVec.ofNat 64 pos := (hcpu_in.readReg64 _).trans hx2
      have hx8' : s'.readReg64 (.gpr 8#5) = n.zeroExtend 64 := (hcpu_in.readReg64 _).trans hx8
      simp only [hb1, ↓reduceIte, Bool.false_eq_true]
      wp_conv_pre =>
        dsimp only [CwLoopMem, fmtArgumentsAt]
        rw [htpl_u32]
        simp only [sepConj_assoc]
      clear hpc
      wp_sym_steps
      refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
        fun sm hcpu_out hcl_sm hnsp hsig htp horc hsym => ?_
      have hframe : FmtWriteFrame s sm := fmtWriteFrame_of_seg hnsp hsig htp horc hsym
      refine SepWPp.weaken_pre (P' := CwLoopMem C st pad sm)
        (Entails.trans (Q := CwLoopMem C st pad s) (Entails.of_eq ?_)
          (cwLoopMem_transport C htrans hframe)) ?_
      · dsimp only [CwLoopMem, fmtArgumentsAt]
        rw [htpl_u32]
        ac_rfl
      · refine hcont sm hcl_sm
          (by rw [hcpu_out.pc_eq]; simp [arm64_norm])
          (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
          (by rw [hcpu_out.sp_eq]; simp [arm64_norm, hsp'])
          (by simp [arm64_norm] at hsp_al'; rw [hcpu_out.spAligned]; simpa [arm64_norm] using hsp_al')
          (by rw [hcpu_out.readReg64]; simp [arm64_norm, hx8'])
          (by rw [hcpu_out.readReg64]; simp [arm64_norm])
          (by rw [hcpu_out.readReg64]; simp [arm64_norm, BitVec.add_assoc, ← bv64_add_ofNat])
          (fun r _hr2 _hr8 hr9 hr22 => by
            rw [hcpu_out.readReg64]
            simp [arm64_norm, hr9, hr22, hcpu_in.readReg64])
          (by rw [hcpu_out.calleeSavedVRegs]; simp [arm64_norm, hcpu_in.calleeSavedVRegs])
    }

private theorem cwCustom_d2 [CoreFmtWritePl] {σ : Type} (C : CwCtx σ)
    (hext_blk : ∀ off : Nat, off < 436 →
      C.P.externAt? (coreFmtMpl.base 0 + BitVec.ofNat 64 off) = none)
    {off1 : Nat} {n : BitVec 8} {r1 : List (BitVec 8)} {cs : List FmtCall}
    {st : σ} {pad : BitVec 64} {s : State}
    (hcl : coreMultiLib.CodeLoaded coreFmtMpl s.mem)
    (hdrop : C.tpl.drop off1 = r1)
    (hoff1_le : off1 ≤ C.tpl.length)
    (hlw_le : (if n.getLsbD 1 then 2 else 0) ≤ r1.length)
    (htrans : ∀ (st : σ) (s1 s2 : State), FmtWriteFrame s1 s2 → C.W st s1 ⊢ C.W st s2)
    (hpc : s.pc = (if n.getLsbD 1 then cwPl0.base + 188#64 else cwPl0.base + 256#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = C.s0.sp - 112#64)
    (hsp_al : s.spAligned = true)
    (hx8 : s.readReg64 (.gpr 8#5) = n.zeroExtend 64)
    (hx22 : s.readReg64 (.gpr 22#5) = C.tplPtr + BitVec.ofNat 64 off1)
    (hcont : ∀ sm : State,
      coreMultiLib.CodeLoaded coreFmtMpl sm.mem →
      sm.pc = (if n.getLsbD 2 then cwPl0.base + 196#64 else cwPl0.base + 264#64) →
      sm.status = .Running →
      sm.sp = C.s0.sp - 112#64 →
      sm.spAligned = true →
      sm.readReg64 (.gpr 8#5) = n.zeroExtend 64 →
      sm.readReg64 (.gpr 10#5) =
        BitVec.setWidth 64 (if n.getLsbD 1 then BitVec.ofNat 16 (leBytesNat (r1.take 2)) else 0#16) →
      sm.readReg64 (.gpr 22#5) = C.tplPtr + BitVec.ofNat 64 (off1 + if n.getLsbD 1 then 2 else 0) →
      (∀ r : BitVec 5, r ≠ 8#5 → r ≠ 10#5 → r ≠ 22#5 →
        sm.readReg64 (.gpr r) = s.readReg64 (.gpr r)) →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      SepWPp C.P C.ret_pc sm (CwLoopMem C st pad sm) (CwQ C cs st) (CwQp C cs st) (CwOom C cs st)) :
    SepWPp C.P C.ret_pc s (CwLoopMem C st pad s) (CwQ C cs st) (CwQp C cs st) (CwOom C cs st) := by
  have hb2_ext : (n.zeroExtend 64).getLsbD 2 = n.getLsbD 2 := cw_u8_zeroExtend64_getLsbD n (by omega)
  cases hb1 : n.getLsbD 1
  ·
    rw [hb1] at hpc
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc
    cases hb2 : n.getLsbD 2 <;> {
      rw [hb2] at hb2_ext
      simp only [hb1, hb2, ↓reduceIte, Bool.false_eq_true, Nat.add_zero] at hcont
      apply sepWPp_seg_coreFmt_pure hext_blk hcl
        (mid := if n.getLsbD 2 then cwPl0.base + 196#64 else cwPl0.base + 264#64)
      intro s' hcpu_in
      have hpc' : s'.pc = cwPl0.base + 256#64 := hcpu_in.pc_eq.trans hpc
      have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
      have hsp' : s'.sp = C.s0.sp - 112#64 := hcpu_in.sp_eq.trans hsp
      have hsp_al' : s'.spAligned = true := hcpu_in.spAligned.trans hsp_al
      have hx8' : s'.readReg64 (.gpr 8#5) = n.zeroExtend 64 := (hcpu_in.readReg64 _).trans hx8
      have hx22' : s'.readReg64 (.gpr 22#5) = C.tplPtr + BitVec.ofNat 64 off1 := (hcpu_in.readReg64 _).trans hx22
      simp only [hb2, ↓reduceIte, Bool.false_eq_true]
      clear hpc
      wp_sym_steps
      refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
        fun sm hcpu_out hcl_sm hnsp hsig htp horc hsym => ?_
      have hframe : FmtWriteFrame s sm := fmtWriteFrame_of_seg hnsp hsig htp horc hsym
      refine SepWPp.weaken_pre (cwLoopMem_transport C htrans hframe) ?_
      refine hcont sm hcl_sm
        (by rw [hcpu_out.pc_eq]; simp [arm64_norm])
        (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
        (by rw [hcpu_out.sp_eq]; simp [arm64_norm, hsp'])
        (by simp [arm64_norm] at hsp_al'; rw [hcpu_out.spAligned]; simpa [arm64_norm] using hsp_al')
        (by rw [hcpu_out.readReg64]; simp [arm64_norm, hx8'])
        (by rw [hcpu_out.readReg64]; simp [arm64_norm])
        (by rw [hcpu_out.readReg64]; simp [arm64_norm, hx22'])
        (fun r _hr8 hr10 _hr22 => by
          rw [hcpu_out.readReg64]
          simp [arm64_norm, hr10, hcpu_in.readReg64])
        (by rw [hcpu_out.calleeSavedVRegs]; simp [arm64_norm, hcpu_in.calleeSavedVRegs])
    }
  ·
    rw [hb1] at hpc hlw_le
    simp only [↓reduceIte] at hpc hlw_le
    have htpl_u16 := cw_tpl_focus_u16 C.tplPtr C.tpl off1 r1 hdrop hoff1_le hlw_le
    cases hb2 : n.getLsbD 2 <;> {
      rw [hb2] at hb2_ext
      simp only [hb1, hb2, ↓reduceIte, Bool.false_eq_true] at hcont
      apply sepWPp_seg_coreFmt_pure hext_blk hcl
        (mid := if n.getLsbD 2 then cwPl0.base + 196#64 else cwPl0.base + 264#64)
      intro s' hcpu_in
      have hpc' : s'.pc = cwPl0.base + 188#64 := hcpu_in.pc_eq.trans hpc
      have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
      have hsp' : s'.sp = C.s0.sp - 112#64 := hcpu_in.sp_eq.trans hsp
      have hsp_al' : s'.spAligned = true := hcpu_in.spAligned.trans hsp_al
      have hx8' : s'.readReg64 (.gpr 8#5) = n.zeroExtend 64 := (hcpu_in.readReg64 _).trans hx8
      have hx22' : s'.readReg64 (.gpr 22#5) = C.tplPtr + BitVec.ofNat 64 off1 := (hcpu_in.readReg64 _).trans hx22
      simp only [hb2, ↓reduceIte, Bool.false_eq_true]
      wp_conv_pre =>
        dsimp only [CwLoopMem, fmtArgumentsAt]
        rw [htpl_u16]
        simp only [sepConj_assoc]
      clear hpc
      wp_sym_steps
      refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
        fun sm hcpu_out hcl_sm hnsp hsig htp horc hsym => ?_
      have hframe : FmtWriteFrame s sm := fmtWriteFrame_of_seg hnsp hsig htp horc hsym
      refine SepWPp.weaken_pre (P' := CwLoopMem C st pad sm)
        (Entails.trans (Q := CwLoopMem C st pad s) (Entails.of_eq ?_)
          (cwLoopMem_transport C htrans hframe)) ?_
      · dsimp only [CwLoopMem, fmtArgumentsAt]
        rw [htpl_u16]
        ac_rfl
      · refine hcont sm hcl_sm
          (by rw [hcpu_out.pc_eq]; simp [arm64_norm])
          (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
          (by rw [hcpu_out.sp_eq]; simp [arm64_norm, hsp'])
          (by simp [arm64_norm] at hsp_al'; rw [hcpu_out.spAligned]; simpa [arm64_norm] using hsp_al')
          (by rw [hcpu_out.readReg64]; simp [arm64_norm, hx8'])
          (by rw [hcpu_out.readReg64]; simp [arm64_norm])
          (by rw [hcpu_out.readReg64]; simp [arm64_norm, BitVec.add_assoc, ← bv64_add_ofNat])
          (fun r _hr8 hr10 hr22 => by
            rw [hcpu_out.readReg64]
            simp [arm64_norm, hr10, hr22, hcpu_in.readReg64])
          (by rw [hcpu_out.calleeSavedVRegs]; simp [arm64_norm, hcpu_in.calleeSavedVRegs])
    }

private theorem cwCustom_d3 [CoreFmtWritePl] {σ : Type} (C : CwCtx σ)
    (hext_blk : ∀ off : Nat, off < 436 →
      C.P.externAt? (coreFmtMpl.base 0 + BitVec.ofNat 64 off) = none)
    {off2 : Nat} {n : BitVec 8} {r2 : List (BitVec 8)} {cs : List FmtCall}
    {st : σ} {pad : BitVec 64} {s : State}
    (hcl : coreMultiLib.CodeLoaded coreFmtMpl s.mem)
    (hdrop : C.tpl.drop off2 = r2)
    (hoff2_le : off2 ≤ C.tpl.length)
    (hlp_le : (if n.getLsbD 2 then 2 else 0) ≤ r2.length)
    (htrans : ∀ (st : σ) (s1 s2 : State), FmtWriteFrame s1 s2 → C.W st s1 ⊢ C.W st s2)
    (hpc : s.pc = (if n.getLsbD 2 then cwPl0.base + 196#64 else cwPl0.base + 264#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = C.s0.sp - 112#64)
    (hsp_al : s.spAligned = true)
    (hx8 : s.readReg64 (.gpr 8#5) = n.zeroExtend 64)
    (hx22 : s.readReg64 (.gpr 22#5) = C.tplPtr + BitVec.ofNat 64 off2)
    (hcont : ∀ sm : State,
      coreMultiLib.CodeLoaded coreFmtMpl sm.mem →
      sm.pc = (if n.getLsbD 3 then cwPl0.base + 272#64 else cwPl0.base + 276#64) →
      sm.status = .Running →
      sm.sp = C.s0.sp - 112#64 →
      sm.spAligned = true →
      sm.readReg64 (.gpr 8#5) = n.zeroExtend 64 →
      sm.readReg64 (.gpr 11#5) =
        BitVec.setWidth 64 (if n.getLsbD 2 then BitVec.ofNat 16 (leBytesNat (r2.take 2)) else 0#16) →
      sm.readReg64 (.gpr 22#5) = C.tplPtr + BitVec.ofNat 64 (off2 + if n.getLsbD 2 then 2 else 0) →
      (∀ r : BitVec 5, r ≠ 8#5 → r ≠ 11#5 → r ≠ 22#5 →
        sm.readReg64 (.gpr r) = s.readReg64 (.gpr r)) →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      SepWPp C.P C.ret_pc sm (CwLoopMem C st pad sm) (CwQ C cs st) (CwQp C cs st) (CwOom C cs st)) :
    SepWPp C.P C.ret_pc s (CwLoopMem C st pad s) (CwQ C cs st) (CwQp C cs st) (CwOom C cs st) := by
  have hb3_ext : (n.zeroExtend 64).getLsbD 3 = n.getLsbD 3 := cw_u8_zeroExtend64_getLsbD n (by omega)
  cases hb2 : n.getLsbD 2
  ·
    rw [hb2] at hpc
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc
    cases hb3 : n.getLsbD 3 <;> {
      rw [hb3] at hb3_ext
      simp only [hb2, hb3, ↓reduceIte, Bool.false_eq_true, Nat.add_zero] at hcont
      apply sepWPp_seg_coreFmt_pure hext_blk hcl
        (mid := if n.getLsbD 3 then cwPl0.base + 272#64 else cwPl0.base + 276#64)
      intro s' hcpu_in
      have hpc' : s'.pc = cwPl0.base + 264#64 := hcpu_in.pc_eq.trans hpc
      have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
      have hsp' : s'.sp = C.s0.sp - 112#64 := hcpu_in.sp_eq.trans hsp
      have hsp_al' : s'.spAligned = true := hcpu_in.spAligned.trans hsp_al
      have hx8' : s'.readReg64 (.gpr 8#5) = n.zeroExtend 64 := (hcpu_in.readReg64 _).trans hx8
      have hx22' : s'.readReg64 (.gpr 22#5) = C.tplPtr + BitVec.ofNat 64 off2 := (hcpu_in.readReg64 _).trans hx22
      simp only [hb3, ↓reduceIte, Bool.false_eq_true]
      clear hpc
      wp_sym_steps
      refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
        fun sm hcpu_out hcl_sm hnsp hsig htp horc hsym => ?_
      have hframe : FmtWriteFrame s sm := fmtWriteFrame_of_seg hnsp hsig htp horc hsym
      refine SepWPp.weaken_pre (cwLoopMem_transport C htrans hframe) ?_
      refine hcont sm hcl_sm
        (by rw [hcpu_out.pc_eq]; simp [arm64_norm])
        (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
        (by rw [hcpu_out.sp_eq]; simp [arm64_norm, hsp'])
        (by simp [arm64_norm] at hsp_al'; rw [hcpu_out.spAligned]; simpa [arm64_norm] using hsp_al')
        (by rw [hcpu_out.readReg64]; simp [arm64_norm, hx8'])
        (by rw [hcpu_out.readReg64]; simp [arm64_norm])
        (by rw [hcpu_out.readReg64]; simp [arm64_norm, hx22'])
        (fun r _hr8 hr11 _hr22 => by
          rw [hcpu_out.readReg64]
          simp [arm64_norm, hr11, hcpu_in.readReg64])
        (by rw [hcpu_out.calleeSavedVRegs]; simp [arm64_norm, hcpu_in.calleeSavedVRegs])
    }
  ·
    rw [hb2] at hpc hlp_le
    simp only [↓reduceIte] at hpc hlp_le
    have htpl_u16 := cw_tpl_focus_u16 C.tplPtr C.tpl off2 r2 hdrop hoff2_le hlp_le
    cases hb3 : n.getLsbD 3 <;> {
      rw [hb3] at hb3_ext
      simp only [hb2, hb3, ↓reduceIte, Bool.false_eq_true] at hcont
      apply sepWPp_seg_coreFmt_pure hext_blk hcl
        (mid := if n.getLsbD 3 then cwPl0.base + 272#64 else cwPl0.base + 276#64)
      intro s' hcpu_in
      have hpc' : s'.pc = cwPl0.base + 196#64 := hcpu_in.pc_eq.trans hpc
      have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
      have hsp' : s'.sp = C.s0.sp - 112#64 := hcpu_in.sp_eq.trans hsp
      have hsp_al' : s'.spAligned = true := hcpu_in.spAligned.trans hsp_al
      have hx8' : s'.readReg64 (.gpr 8#5) = n.zeroExtend 64 := (hcpu_in.readReg64 _).trans hx8
      have hx22' : s'.readReg64 (.gpr 22#5) = C.tplPtr + BitVec.ofNat 64 off2 := (hcpu_in.readReg64 _).trans hx22
      simp only [hb3, ↓reduceIte, Bool.false_eq_true]
      wp_conv_pre =>
        dsimp only [CwLoopMem, fmtArgumentsAt]
        rw [htpl_u16]
        simp only [sepConj_assoc]
      clear hpc
      wp_sym_steps
      refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
        fun sm hcpu_out hcl_sm hnsp hsig htp horc hsym => ?_
      have hframe : FmtWriteFrame s sm := fmtWriteFrame_of_seg hnsp hsig htp horc hsym
      refine SepWPp.weaken_pre (P' := CwLoopMem C st pad sm)
        (Entails.trans (Q := CwLoopMem C st pad s) (Entails.of_eq ?_)
          (cwLoopMem_transport C htrans hframe)) ?_
      · dsimp only [CwLoopMem, fmtArgumentsAt]
        rw [htpl_u16]
        ac_rfl
      · refine hcont sm hcl_sm
          (by rw [hcpu_out.pc_eq]; simp [arm64_norm])
          (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
          (by rw [hcpu_out.sp_eq]; simp [arm64_norm, hsp'])
          (by simp [arm64_norm] at hsp_al'; rw [hcpu_out.spAligned]; simpa [arm64_norm] using hsp_al')
          (by rw [hcpu_out.readReg64]; simp [arm64_norm, hx8'])
          (by rw [hcpu_out.readReg64]; simp [arm64_norm])
          (by rw [hcpu_out.readReg64]; simp [arm64_norm, BitVec.add_assoc, ← bv64_add_ofNat])
          (fun r _hr8 hr11 hr22 => by
            rw [hcpu_out.readReg64]
            simp [arm64_norm, hr11, hr22, hcpu_in.readReg64])
          (by rw [hcpu_out.calleeSavedVRegs]; simp [arm64_norm, hcpu_in.calleeSavedVRegs])
    }

private theorem cwCustom_d4 [CoreFmtWritePl] {σ : Type} (C : CwCtx σ)
    (hext_blk : ∀ off : Nat, off < 436 →
      C.P.externAt? (coreFmtMpl.base 0 + BitVec.ofNat 64 off) = none)
    {off3 ai : Nat} {n : BitVec 8} {r3 : List (BitVec 8)} {cs : List FmtCall}
    {st : σ} {pad : BitVec 64} {s : State}
    (hcl : coreMultiLib.CodeLoaded coreFmtMpl s.mem)
    (hdrop : C.tpl.drop off3 = r3)
    (hoff3_le : off3 ≤ C.tpl.length)
    (hli_le : (if n.getLsbD 3 then 2 else 0) ≤ r3.length)
    (htrans : ∀ (st : σ) (s1 s2 : State), FmtWriteFrame s1 s2 → C.W st s1 ⊢ C.W st s2)
    (hpc : s.pc = (if n.getLsbD 3 then cwPl0.base + 272#64 else cwPl0.base + 276#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = C.s0.sp - 112#64)
    (hsp_al : s.spAligned = true)
    (hx22 : s.readReg64 (.gpr 22#5) = C.tplPtr + BitVec.ofNat 64 off3)
    (hx25 : s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 ai)
    (hcont : ∀ sm : State,
      coreMultiLib.CodeLoaded coreFmtMpl sm.mem →
      sm.pc = cwPl0.base + 276#64 →
      sm.status = .Running →
      sm.sp = C.s0.sp - 112#64 →
      sm.spAligned = true →
      sm.readReg64 (.gpr 22#5) = C.tplPtr + BitVec.ofNat 64 (off3 + if n.getLsbD 3 then 2 else 0) →
      sm.readReg64 (.gpr 25#5) =
        BitVec.ofNat 64 (if n.getLsbD 3 then leBytesNat (r3.take 2) else ai) →
      (∀ r : BitVec 5, r ≠ 22#5 → r ≠ 25#5 →
        sm.readReg64 (.gpr r) = s.readReg64 (.gpr r)) →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      SepWPp C.P C.ret_pc sm (CwLoopMem C st pad sm) (CwQ C cs st) (CwQp C cs st) (CwOom C cs st)) :
    SepWPp C.P C.ret_pc s (CwLoopMem C st pad s) (CwQ C cs st) (CwQp C cs st) (CwOom C cs st) := by
  cases hb3 : n.getLsbD 3
  · rw [hb3] at hpc
    simp only [hb3, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hpc hcont
    exact hcont s hcl hpc hrun hsp hsp_al hx22 hx25 (fun _ _ _ => rfl) rfl
  · rw [hb3] at hpc hli_le
    simp only [hb3, ↓reduceIte] at hpc hli_le hcont
    have htpl_u16 := cw_tpl_focus_u16 C.tplPtr C.tpl off3 r3 hdrop hoff3_le hli_le
    have hlt16 : leBytesNat (r3.take 2) < 65536 := cw_leBytesNat_take2_lt hli_le
    apply sepWPp_seg_coreFmt_pure hext_blk hcl (mid := cwPl0.base + 276#64)
    intro s' hcpu_in
    have hpc' : s'.pc = cwPl0.base + 272#64 := hcpu_in.pc_eq.trans hpc
    have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
    have hsp' : s'.sp = C.s0.sp - 112#64 := hcpu_in.sp_eq.trans hsp
    have hsp_al' : s'.spAligned = true := hcpu_in.spAligned.trans hsp_al
    have hx22' : s'.readReg64 (.gpr 22#5) = C.tplPtr + BitVec.ofNat 64 off3 := (hcpu_in.readReg64 _).trans hx22
    wp_conv_pre =>
      dsimp only [CwLoopMem, fmtArgumentsAt]
      rw [htpl_u16]
      simp only [sepConj_assoc]
    clear hpc
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
      fun sm hcpu_out hcl_sm hnsp hsig htp horc hsym => ?_
    have hframe : FmtWriteFrame s sm := fmtWriteFrame_of_seg hnsp hsig htp horc hsym
    refine SepWPp.weaken_pre (P' := CwLoopMem C st pad sm)
      (Entails.trans (Q := CwLoopMem C st pad s) (Entails.of_eq ?_)
        (cwLoopMem_transport C htrans hframe)) ?_
    · dsimp only [CwLoopMem, fmtArgumentsAt]
      rw [htpl_u16]
      ac_rfl
    · have hx25_sm : sm.readReg64 (.gpr 25#5) = BitVec.ofNat 64 (leBytesNat (r3.take 2)) := by
        have hraw : sm.readReg64 (.gpr 25#5) = BitVec.setWidth 64 (BitVec.ofNat 16 (leBytesNat (r3.take 2))) := by
          rw [hcpu_out.readReg64]; simp [arm64_norm]
        rw [hraw, u16_ofNat_zeroExtend64 hlt16]
      refine hcont sm hcl_sm
        (by rw [hcpu_out.pc_eq]; simp [arm64_norm])
        (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
        (by rw [hcpu_out.sp_eq]; simp [arm64_norm, hsp'])
        (by simp [arm64_norm] at hsp_al'; rw [hcpu_out.spAligned]; simpa [arm64_norm] using hsp_al')
        (by rw [hcpu_out.readReg64]; simp [arm64_norm, BitVec.add_assoc, ← bv64_add_ofNat])
        hx25_sm
        (fun r hr22 hr25 => by
          rw [hcpu_out.readReg64]
          simp [arm64_norm, hr22, hr25, hcpu_in.readReg64])
        (by rw [hcpu_out.calleeSavedVRegs]; simp [arm64_norm, hcpu_in.calleeSavedVRegs])

private theorem cwCustom_d5a [CoreFmtWritePl] {σ : Type} (C : CwCtx σ)
    (hext_blk : ∀ off : Nat, off < 436 →
      C.P.externAt? (coreFmtMpl.base 0 + BitVec.ofNat 64 off) = none)
    {n : BitVec 8} {width0 width : BitVec 16} {cs : List FmtCall}
    {st : σ} {pad : BitVec 64} {s : State}
    (hcl : coreMultiLib.CodeLoaded coreFmtMpl s.mem)
    (heven : C.argsPtr.getLsbD 0 = false)
    (hw_res : (if n.getLsbD 4 then fmtCountAt C.args width0.toNat else some width0) = some width)
    (htrans : ∀ (st : σ) (s1 s2 : State), FmtWriteFrame s1 s2 → C.W st s1 ⊢ C.W st s2)
    (hpc : s.pc = cwPl0.base + 276#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = C.s0.sp - 112#64)
    (hsp_al : s.spAligned = true)
    (hx8 : s.readReg64 (.gpr 8#5) = n.zeroExtend 64)
    (hx10 : s.readReg64 (.gpr 10#5) = BitVec.setWidth 64 width0)
    (hx19 : s.readReg64 (.gpr 19#5) = C.argsPtr)
    (hcont : ∀ sm : State,
      coreMultiLib.CodeLoaded coreFmtMpl sm.mem →
      sm.pc = (if n.getLsbD 5 then cwPl0.base + 284#64 else cwPl0.base + 292#64) →
      sm.status = .Running →
      sm.sp = C.s0.sp - 112#64 →
      sm.spAligned = true →
      sm.readReg64 (.gpr 10#5) = BitVec.setWidth 64 width →
      (∀ r : BitVec 5, r ≠ 8#5 → r ≠ 10#5 →
        sm.readReg64 (.gpr r) = s.readReg64 (.gpr r)) →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      SepWPp C.P C.ret_pc sm (CwLoopMem C st pad sm) (CwQ C cs st) (CwQp C cs st) (CwOom C cs st)) :
    SepWPp C.P C.ret_pc s (CwLoopMem C st pad s) (CwQ C cs st) (CwQp C cs st) (CwOom C cs st) := by
  have hb4_ext : (n.zeroExtend 64).getLsbD 4 = n.getLsbD 4 := cw_u8_zeroExtend64_getLsbD n (by omega)
  have hb5_ext : (n.zeroExtend 64).getLsbD 5 = n.getLsbD 5 := cw_u8_zeroExtend64_getLsbD n (by omega)
  cases hb4 : n.getLsbD 4
  · rw [hb4] at hb4_ext hw_res
    simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hw_res
    subst hw_res
    cases hb5 : n.getLsbD 5 <;> {
      rw [hb5] at hb5_ext
      simp only [hb5, ↓reduceIte, Bool.false_eq_true] at hcont
      apply sepWPp_seg_coreFmt_pure hext_blk hcl
        (mid := if n.getLsbD 5 then cwPl0.base + 284#64 else cwPl0.base + 292#64)
      intro s' hcpu_in
      have hpc' : s'.pc = cwPl0.base + 276#64 := hcpu_in.pc_eq.trans hpc
      have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
      have hsp' : s'.sp = C.s0.sp - 112#64 := hcpu_in.sp_eq.trans hsp
      have hsp_al' : s'.spAligned = true := hcpu_in.spAligned.trans hsp_al
      have hx8' : s'.readReg64 (.gpr 8#5) = n.zeroExtend 64 := (hcpu_in.readReg64 _).trans hx8
      have hx10' : s'.readReg64 (.gpr 10#5) = BitVec.setWidth 64 width0 := (hcpu_in.readReg64 _).trans hx10
      simp only [hb5, ↓reduceIte, Bool.false_eq_true]
      clear hpc
      wp_sym_steps
      refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
        fun sm hcpu_out hcl_sm hnsp hsig htp horc hsym => ?_
      have hframe : FmtWriteFrame s sm := fmtWriteFrame_of_seg hnsp hsig htp horc hsym
      refine SepWPp.weaken_pre (cwLoopMem_transport C htrans hframe) ?_
      refine hcont sm hcl_sm
        (by rw [hcpu_out.pc_eq]; simp [arm64_norm])
        (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
        (by rw [hcpu_out.sp_eq]; simp [arm64_norm, hsp'])
        (by simp [arm64_norm] at hsp_al'; rw [hcpu_out.spAligned]; simpa [arm64_norm] using hsp_al')
        (by rw [hcpu_out.readReg64]; simp [arm64_norm, hx10'])
        (fun r _hr8 _hr10 => by
          rw [hcpu_out.readReg64]
          simp [arm64_norm, hcpu_in.readReg64])
        (by rw [hcpu_out.calleeSavedVRegs]; simp [arm64_norm, hcpu_in.calleeSavedVRegs])
    }
  · rw [hb4] at hb4_ext hw_res
    simp only [↓reduceIte] at hw_res
    rcases fmtCountAt_eq_some_iff.mp hw_res with ⟨cval, cword2, hcarg, hcwidth⟩
    have hshl : C.argsPtr + (BitVec.setWidth 64 width0) <<< 4 =
        C.argsPtr + BitVec.ofNat 64 (16 * width0.toNat) := by
      rw [cw_u16_shl4_eq_mul16]
    have hfocus := fmtArgEntriesAt_focus C.argsRo C.argsPtr C.args hcarg
    rw [fmtArgElemAt_splitCount16, hcwidth] at hfocus
    cases hro : C.argsRo <;> cases hb5 : n.getLsbD 5 <;> {
      rw [hb5] at hb5_ext
      rw [hro] at hfocus
      simp only [Bool.false_eq_true, ↓reduceIte] at hfocus
      simp only [hb5, ↓reduceIte, Bool.false_eq_true] at hcont
      apply sepWPp_seg_coreFmt_pure hext_blk hcl
        (mid := if n.getLsbD 5 then cwPl0.base + 284#64 else cwPl0.base + 292#64)
      intro s' hcpu_in
      have hpc' : s'.pc = cwPl0.base + 276#64 := hcpu_in.pc_eq.trans hpc
      have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
      have hsp' : s'.sp = C.s0.sp - 112#64 := hcpu_in.sp_eq.trans hsp
      have hsp_al' : s'.spAligned = true := hcpu_in.spAligned.trans hsp_al
      have hx8' : s'.readReg64 (.gpr 8#5) = n.zeroExtend 64 := (hcpu_in.readReg64 _).trans hx8
      have hx10' : s'.readReg64 (.gpr 10#5) = BitVec.setWidth 64 width0 := (hcpu_in.readReg64 _).trans hx10
      have hx19' : s'.readReg64 (.gpr 19#5) = C.argsPtr := (hcpu_in.readReg64 _).trans hx19
      simp only [hb5, ↓reduceIte, Bool.false_eq_true]
      wp_conv_pre =>
        dsimp only [CwLoopMem, fmtArgumentsAt]
        simp only [heven, Bool.false_eq_true, ↓reduceIte, hro]
        rw [hfocus, ← hshl]
        simp only [sepConj_assoc]
      clear hpc
      wp_sym_steps
      apply SepWP.step_ldr16 (pc := cwPl0.base + 336#64) (rt := .gpr 10#5)
        (addr := .Offset (.gpr 10#5) 8#64)
        (ea := C.argsPtr + BitVec.setWidth 64 width0 <<< 4 + 8#64) (wb := none)
        rfl (by simpa [arm64_norm] using hrun')
        (by simp [arm64_norm]) rfl (by simp [evalAddrMode, arm64_norm])
        (SepLoad16.right (SepLoad16.right (SepLoad16.left
          (by first | exact SepLoad16.here rfl | exact SepLoad16.here_ro rfl)))) rfl
      conv => arg 3; simp [applyWriteback, State.writeReg, cw_u16_w32_ext, arm64_norm]
      wp_sym_steps
      refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
        fun sm hcpu_out hcl_sm hnsp hsig htp horc hsym => ?_
      have hframe : FmtWriteFrame s sm := fmtWriteFrame_of_seg hnsp hsig htp horc hsym
      refine SepWPp.weaken_pre (P' := CwLoopMem C st pad sm)
        (Entails.trans (Q := CwLoopMem C st pad s) (Entails.of_eq ?_)
          (cwLoopMem_transport C htrans hframe)) ?_
      · dsimp only [CwLoopMem, fmtArgumentsAt]
        simp only [heven, Bool.false_eq_true, ↓reduceIte, hro, hshl]
        rw [hfocus]
        ac_rfl
      · refine hcont sm hcl_sm
          (by rw [hcpu_out.pc_eq]; simp [arm64_norm])
          (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
          (by rw [hcpu_out.sp_eq]; simp [arm64_norm, hsp'])
          (by simp [arm64_norm] at hsp_al'; rw [hcpu_out.spAligned]; simpa [arm64_norm] using hsp_al')
          (by rw [hcpu_out.readReg64]; simp [arm64_norm])
          (fun r _hr8 hr10 => by
            rw [hcpu_out.readReg64]
            simp [arm64_norm, hr10, hcpu_in.readReg64])
          (by rw [hcpu_out.calleeSavedVRegs]; simp [arm64_norm, hcpu_in.calleeSavedVRegs])
    }

private theorem cwCustom_d5b [CoreFmtWritePl] {σ : Type} (C : CwCtx σ)
    (hext_blk : ∀ off : Nat, off < 436 →
      C.P.externAt? (coreFmtMpl.base 0 + BitVec.ofNat 64 off) = none)
    {n : BitVec 8} {prec0 prec : BitVec 16} {cs : List FmtCall}
    {st : σ} {pad : BitVec 64} {s : State}
    (hcl : coreMultiLib.CodeLoaded coreFmtMpl s.mem)
    (heven : C.argsPtr.getLsbD 0 = false)
    (hp_res : (if n.getLsbD 5 then fmtCountAt C.args prec0.toNat else some prec0) = some prec)
    (htrans : ∀ (st : σ) (s1 s2 : State), FmtWriteFrame s1 s2 → C.W st s1 ⊢ C.W st s2)
    (hpc : s.pc = (if n.getLsbD 5 then cwPl0.base + 284#64 else cwPl0.base + 292#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = C.s0.sp - 112#64)
    (hsp_al : s.spAligned = true)
    (hx11 : s.readReg64 (.gpr 11#5) = BitVec.setWidth 64 prec0)
    (hx19 : s.readReg64 (.gpr 19#5) = C.argsPtr)
    (hcont : ∀ sm : State,
      coreMultiLib.CodeLoaded coreFmtMpl sm.mem →
      sm.pc = cwPl0.base + 292#64 →
      sm.status = .Running →
      sm.sp = C.s0.sp - 112#64 →
      sm.spAligned = true →
      sm.readReg64 (.gpr 11#5) = BitVec.setWidth 64 prec →
      (∀ r : BitVec 5, r ≠ 8#5 → r ≠ 11#5 →
        sm.readReg64 (.gpr r) = s.readReg64 (.gpr r)) →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      SepWPp C.P C.ret_pc sm (CwLoopMem C st pad sm) (CwQ C cs st) (CwQp C cs st) (CwOom C cs st)) :
    SepWPp C.P C.ret_pc s (CwLoopMem C st pad s) (CwQ C cs st) (CwQp C cs st) (CwOom C cs st) := by
  cases hb5 : n.getLsbD 5
  · rw [hb5] at hpc hp_res
    simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hpc hp_res
    subst hp_res
    exact hcont s hcl hpc hrun hsp hsp_al hx11 (fun _ _ _ => rfl) rfl
  · rw [hb5] at hpc hp_res
    simp only [↓reduceIte] at hpc hp_res
    rcases fmtCountAt_eq_some_iff.mp hp_res with ⟨cval, cword2, hcarg, hcprec⟩
    have hshl : C.argsPtr + (BitVec.setWidth 64 prec0) <<< 4 =
        C.argsPtr + BitVec.ofNat 64 (16 * prec0.toNat) := by
      rw [cw_u16_shl4_eq_mul16]
    have hfocus := fmtArgEntriesAt_focus C.argsRo C.argsPtr C.args hcarg
    rw [fmtArgElemAt_splitCount16, hcprec] at hfocus
    cases hro : C.argsRo <;> {
      rw [hro] at hfocus
      simp only [Bool.false_eq_true, ↓reduceIte] at hfocus
      apply sepWPp_seg_coreFmt_pure hext_blk hcl (mid := cwPl0.base + 292#64)
      intro s' hcpu_in
      have hpc' : s'.pc = cwPl0.base + 284#64 := hcpu_in.pc_eq.trans hpc
      have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
      have hsp' : s'.sp = C.s0.sp - 112#64 := hcpu_in.sp_eq.trans hsp
      have hsp_al' : s'.spAligned = true := hcpu_in.spAligned.trans hsp_al
      have hx11' : s'.readReg64 (.gpr 11#5) = BitVec.setWidth 64 prec0 := (hcpu_in.readReg64 _).trans hx11
      have hx19' : s'.readReg64 (.gpr 19#5) = C.argsPtr := (hcpu_in.readReg64 _).trans hx19
      wp_conv_pre =>
        dsimp only [CwLoopMem, fmtArgumentsAt]
        simp only [heven, Bool.false_eq_true, ↓reduceIte, hro]
        rw [hfocus, ← hshl]
        simp only [sepConj_assoc]
      clear hpc
      wp_sym_steps
      apply SepWP.step_ldr16 (pc := cwPl0.base + 288#64) (rt := .gpr 11#5)
        (addr := .Offset (.gpr 8#5) 8#64)
        (ea := C.argsPtr + BitVec.setWidth 64 prec0 <<< 4 + 8#64) (wb := none)
        rfl (by simpa [arm64_norm] using hrun')
        (by simp [arm64_norm]) rfl (by simp [evalAddrMode, arm64_norm])
        (SepLoad16.right (SepLoad16.right (SepLoad16.left
          (by first | exact SepLoad16.here rfl | exact SepLoad16.here_ro rfl)))) rfl
      conv => arg 3; simp [applyWriteback, State.writeReg, cw_u16_w32_ext, arm64_norm]
      refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
        fun sm hcpu_out hcl_sm hnsp hsig htp horc hsym => ?_
      have hframe : FmtWriteFrame s sm := fmtWriteFrame_of_seg hnsp hsig htp horc hsym
      refine SepWPp.weaken_pre (P' := CwLoopMem C st pad sm)
        (Entails.trans (Q := CwLoopMem C st pad s) (Entails.of_eq ?_)
          (cwLoopMem_transport C htrans hframe)) ?_
      · dsimp only [CwLoopMem, fmtArgumentsAt]
        simp only [heven, Bool.false_eq_true, ↓reduceIte, hro, hshl]
        rw [hfocus]
        ac_rfl
      · refine hcont sm hcl_sm
          (by rw [hcpu_out.pc_eq]; simp [arm64_norm])
          (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
          (by rw [hcpu_out.sp_eq]; simp [arm64_norm, hsp'])
          (by simp [arm64_norm] at hsp_al'; rw [hcpu_out.spAligned]; simpa [arm64_norm] using hsp_al')
          (by rw [hcpu_out.readReg64]; simp [arm64_norm])
          (fun r hr8 hr11 => by
            rw [hcpu_out.readReg64]
            simp [arm64_norm, hr8, hr11, hcpu_in.readReg64])
          (by rw [hcpu_out.calleeSavedVRegs]; simp [arm64_norm, hcpu_in.calleeSavedVRegs])
    }

private theorem cwCustom_d6_preCall [CoreFmtWritePl] {σ : Type} (C : CwCtx σ)
    (hext_blk : ∀ off : Nat, off < 436 →
      C.P.externAt? (coreFmtMpl.base 0 + BitVec.ofNat 64 off) = none)
    {nextPos idx : Nat} {opts : FmtOptions} {value fmtFn : BitVec 64} {cs : List FmtCall}
    {st : σ} {pad : BitVec 64} {s : State}
    (hcl : coreMultiLib.CodeLoaded coreFmtMpl s.mem)
    (heven : C.argsPtr.getLsbD 0 = false)
    (harg : C.args[idx]? = some (value, fmtFn))
    (htrans : ∀ (st : σ) (s1 s2 : State), FmtWriteFrame s1 s2 → C.W st s1 ⊢ C.W st s2)
    (hpc : s.pc = cwPl0.base + 292#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = C.s0.sp - 112#64)
    (hsp_al : s.spAligned = true)
    (hx9 : s.readReg64 (.gpr 9#5) = BitVec.setWidth 64 opts.flags)
    (hx10 : s.readReg64 (.gpr 10#5) = BitVec.setWidth 64 opts.width)
    (hx11 : s.readReg64 (.gpr 11#5) = BitVec.setWidth 64 opts.precision)
    (hx19 : s.readReg64 (.gpr 19#5) = C.argsPtr)
    (hx20 : s.readReg64 (.gpr 20#5) = C.out)
    (hx21 : s.readReg64 (.gpr 21#5) = C.vt)
    (hx22 : s.readReg64 (.gpr 22#5) = C.tplPtr + BitVec.ofNat 64 nextPos)
    (hx24 : s.readReg64 (.gpr 24#5) = C.writeStrFn)
    (hx25 : s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 idx)
    (hx26 : s.readReg64 (.gpr 26#5) = 0x60000020#64)
    (hx27 : s.readReg64 (.gpr 27#5) = C.s0.readReg64 (.gpr 27#5))
    (hx28 : s.readReg64 (.gpr 28#5) = C.s0.readReg64 (.gpr 28#5))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs C.s0)
    (hcont : ∀ sm : State,
      coreMultiLib.CodeLoaded coreFmtMpl sm.mem →
      sm.pc = fmtFn →
      sm.status = .Running →
      sm.sp = C.s0.sp - 112#64 →
      sm.spAligned = true →
      sm.readReg64 Reg.lr = cwPl0.base + 324#64 →
      sm.readReg64 .x0 = value →
      sm.readReg64 .x1 = C.s0.sp - 104#64 →
      sm.readReg64 (.gpr 19#5) = C.argsPtr →
      sm.readReg64 (.gpr 20#5) = C.out →
      sm.readReg64 (.gpr 21#5) = C.vt →
      sm.readReg64 (.gpr 22#5) = C.tplPtr + BitVec.ofNat 64 nextPos →
      sm.readReg64 (.gpr 24#5) = C.writeStrFn →
      sm.readReg64 (.gpr 25#5) = BitVec.ofNat 64 idx →
      sm.readReg64 (.gpr 26#5) = 0x60000020#64 →
      sm.readReg64 (.gpr 27#5) = C.s0.readReg64 (.gpr 27#5) →
      sm.readReg64 (.gpr 28#5) = C.s0.readReg64 (.gpr 28#5) →
      calleeSavedVRegs sm = calleeSavedVRegs C.s0 →
      SepWPp C.P C.ret_pc sm (CwLoopMemFmt C st pad opts sm)
        (CwQ C cs st) (CwQp C cs st) (CwOom C cs st)) :
    SepWPp C.P C.ret_pc s (CwLoopMem C st pad s)
      (CwQ C cs st) (CwQp C cs st) (CwOom C cs st) := by
  have hunpack : CwLoopMem C st pad s =
      (∃∗ w0, ∃∗ w1, ∃∗ fl, ∃∗ wd, ∃∗ pr,
        ((C.s0.sp - 104#64) ↦₆₄ w0) ∗
        ((C.s0.sp - 104#64 + 8#64) ↦₆₄ w1) ∗
        ((C.s0.sp - 104#64 + 16#64) ↦₃₂ fl) ∗
        ((C.s0.sp - 104#64 + 20#64) ↦₁₆ wd) ∗
        ((C.s0.sp - 104#64 + 22#64) ↦₁₆ pr)) ∗
      (((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
       fmtArgumentsAt C.argsRo C.tplPtr C.argsPtr C.tpl C.args ∗
       C.W st s ∗
       stackFrameAt (C.s0.sp - 112#64) C.stackBytes ∗
       (((C.s0.sp - 112#64) ↦₆₄ pad) ∗ cwSavedSlots C.s0.sp C.s0 C.ret_pc)) := by
    dsimp only [CwLoopMem]
    rw [memRegion24_eq_exists_fmtFields (C.s0.sp - 104#64)]
    ac_rfl
  rw [hunpack]
  apply sepWPp_sepExists_left; intro w0
  apply sepWPp_sepExists_left; intro w1
  apply sepWPp_sepExists_left; intro fl
  apply sepWPp_sepExists_left; intro wd
  apply sepWPp_sepExists_left; intro pr
  have hfocus := fmtArgEntriesAt_focus C.argsRo C.argsPtr C.args harg
  have hshl : C.argsPtr + (BitVec.ofNat 64 idx) <<< 4 = C.argsPtr + BitVec.ofNat 64 (16 * idx) := by
    rw [bv64_shl4_eq_mul16]
  have hf_sp0 : C.s0.sp - 112#64 + 8#64 = C.s0.sp - 104#64 := by bv_omega
  have hf_sp16 : C.s0.sp - 112#64 + 16#64 = C.s0.sp - 104#64 + 8#64 := by bv_omega
  have hf_sp24 : C.s0.sp - 112#64 + 24#64 = C.s0.sp - 104#64 + 16#64 := by bv_omega
  have hf_sp28 : C.s0.sp - 112#64 + 28#64 = C.s0.sp - 104#64 + 20#64 := by bv_omega
  have hf_sp30 : C.s0.sp - 112#64 + 30#64 = C.s0.sp - 104#64 + 22#64 := by bv_omega
  cases hro : C.argsRo <;> {
    rw [hro] at hfocus
    dsimp only [fmtArgElemAt] at hfocus
    simp only [Bool.false_eq_true, ↓reduceIte] at hfocus
    apply sepWPp_seg_coreFmt_pure hext_blk hcl (mid := fmtFn)
    intro s' hcpu_in
    have hpc' : s'.pc = cwPl0.base + 292#64 := hcpu_in.pc_eq.trans hpc
    have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
    have hsp' : s'.sp = C.s0.sp - 112#64 := hcpu_in.sp_eq.trans hsp
    have hsp_al' : s'.spAligned = true := hcpu_in.spAligned.trans hsp_al
    have hx9' : s'.readReg64 (.gpr 9#5) = BitVec.setWidth 64 opts.flags := (hcpu_in.readReg64 _).trans hx9
    have hx10' : s'.readReg64 (.gpr 10#5) = BitVec.setWidth 64 opts.width := (hcpu_in.readReg64 _).trans hx10
    have hx11' : s'.readReg64 (.gpr 11#5) = BitVec.setWidth 64 opts.precision := (hcpu_in.readReg64 _).trans hx11
    have hx19' : s'.readReg64 (.gpr 19#5) = C.argsPtr := (hcpu_in.readReg64 _).trans hx19
    have hx20' : s'.readReg64 (.gpr 20#5) = C.out := (hcpu_in.readReg64 _).trans hx20
    have hx21' : s'.readReg64 (.gpr 21#5) = C.vt := (hcpu_in.readReg64 _).trans hx21
    have hx25' : s'.readReg64 (.gpr 25#5) = BitVec.ofNat 64 idx := (hcpu_in.readReg64 _).trans hx25
    wp_conv_pre =>
      dsimp only [fmtArgumentsAt]
      simp only [heven, Bool.false_eq_true, ↓reduceIte, hro]
      rw [hfocus, ← hshl, ← hf_sp16, ← hf_sp24, ← hf_sp28, ← hf_sp30, ← hf_sp0]
      simp only [sepConj_assoc]
    clear hpc
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
      fun sm hcpu_out hcl_sm hnsp hsig htp horc hsym => ?_
    have hframe : FmtWriteFrame s sm := fmtWriteFrame_of_seg hnsp hsig htp horc hsym
    refine SepWPp.weaken_pre (P' := CwLoopMemFmt C st pad opts sm)
      (Entails.trans (Q := CwLoopMemFmt C st pad opts s) (Entails.of_eq ?_)
        (cwLoopMemFmt_transport C htrans hframe)) ?_
    · dsimp only [CwLoopMemFmt, formatterAt, fmtArgumentsAt]
      simp only [heven, Bool.false_eq_true, ↓reduceIte, hro,
        hf_sp0, hf_sp16, hf_sp24, hf_sp28, hf_sp30, hshl]
      rw [hfocus]
      ac_rfl
    · exact hcont sm hcl_sm
        (by rw [hcpu_out.pc_eq]; simp [arm64_norm])
        (by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun')
        (by rw [hcpu_out.sp_eq]; simp [arm64_norm, hsp'])
        (by simp [arm64_norm] at hsp_al'; rw [hcpu_out.spAligned]; simpa [arm64_norm] using hsp_al')
        (by rw [hcpu_out.readReg64]; simp [arm64_norm])
        (by rw [hcpu_out.readReg64]; simp [arm64_norm])
        (by rw [hcpu_out.readReg64]; simp [arm64_norm])
        (by rw [hcpu_out.readReg64]; simp [arm64_norm, hx19'])
        (by rw [hcpu_out.readReg64]; simp [arm64_norm, hx20'])
        (by rw [hcpu_out.readReg64]; simp [arm64_norm, hx21'])
        (by rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx22])
        (by rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx24])
        (by rw [hcpu_out.readReg64]; simp [arm64_norm, hx25'])
        (by rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx26])
        (by rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx27])
        (by rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx28])
        (by rw [hcpu_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu_in.calleeSavedVRegs] using hvregs)
  }

/-! ## Custom placeholder step (`0xc1..0xff`) -/

/-- Custom placeholder step (`0xc1 .. 0xff`, `+0x074 .. +0x158`). -/
theorem cwStep_customArg [CoreFmtWritePl] {σ : Type} (C : CwCtx σ)
    (hext_blk : ∀ off : Nat, off < 436 →
      C.P.externAt? (coreFmtMpl.base 0 + BitVec.ofNat 64 off) = none)
    {pos ai idx ai' k : Nat} {n : BitVec 8} {rest : List (BitVec 8)}
    {opts : FmtOptions} {value fmtFn : BitVec 64} {cs' : List FmtCall}
    {st : σ} {pad : BitVec 64} {s : State}
    (hcl : coreMultiLib.CodeLoaded coreFmtMpl s.mem)
    (heven : C.argsPtr.getLsbD 0 = false)
    (hdrop : C.tpl.drop pos = n :: rest)
    (hpos_lt : pos < C.tpl.length)
    (hn_ge : ¬ n.toNat < 0x80) (hne80 : n ≠ 0x80#8) (hnec0 : n ≠ 0xc0#8)
    (hph : decodeFmtPlaceholder n rest C.args ai = some (opts, idx, ai', k))
    (harg : C.args[idx]? = some (value, fmtFn))
    (hcb : FmtCallbacks C.P C.W C.Step C.Panic C.Oom C.stackBytes C.out C.vt C.writeStrFn
      (FmtCall.fmtArg idx value fmtFn opts :: cs'))
    (ih_loop : CwLoopCont C (pos + 1 + k) ai' cs')
    (hpc : s.pc = cwPl0.base + 116#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = C.s0.sp - 112#64)
    (hsp_al : s.spAligned = true)
    (hx2 : s.readReg64 (.gpr 2#5) = C.tplPtr + BitVec.ofNat 64 pos)
    (hx8 : s.readReg64 (.gpr 8#5) = n.zeroExtend 64)
    (hx19 : s.readReg64 (.gpr 19#5) = C.argsPtr)
    (hx20 : s.readReg64 (.gpr 20#5) = C.out)
    (hx21 : s.readReg64 (.gpr 21#5) = C.vt)
    (hx24 : s.readReg64 (.gpr 24#5) = C.writeStrFn)
    (hx25 : s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 ai)
    (hx26 : s.readReg64 (.gpr 26#5) = 0x60000020#64)
    (hx27 : s.readReg64 (.gpr 27#5) = C.s0.readReg64 (.gpr 27#5))
    (hx28 : s.readReg64 (.gpr 28#5) = C.s0.readReg64 (.gpr 28#5))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs C.s0) :
    SepWPp C.P C.ret_pc s (CwLoopMem C st pad s)
      (CwQ C (FmtCall.fmtArg idx value fmtFn opts :: cs') st)
      (CwQp C (FmtCall.fmtArg idx value fmtFn opts :: cs') st)
      (CwOom C (FmtCall.fmtArg idx value fmtFn opts :: cs') st) := by
  rcases decodeFmtPlaceholder_inv hph with ⟨hk_le, hk_eq, hidx_eq, hai'_eq, hfl_eq, hw_res, hp_res⟩
  let lf := if n.getLsbD 0 then 4 else 0
  let lw := if n.getLsbD 1 then 2 else 0
  let lp := if n.getLsbD 2 then 2 else 0
  let li := if n.getLsbD 3 then 2 else 0
  let r1 := rest.drop lf
  let r2 := r1.drop lw
  let r3 := r2.drop lp
  let width0 := if n.getLsbD 1 then BitVec.ofNat 16 (leBytesNat (r1.take 2)) else 0#16
  let prec0 := if n.getLsbD 2 then BitVec.ofNat 16 (leBytesNat (r2.take 2)) else 0#16
  have hdrop1 : C.tpl.drop (pos + 1) = rest := by rw [← List.drop_drop, hdrop]; rfl
  have hdrop_r1 : C.tpl.drop (pos + 1 + lf) = r1 := by rw [← List.drop_drop, hdrop1]
  have hdrop_r2 : C.tpl.drop (pos + 1 + lf + lw) = r2 := by rw [← List.drop_drop, hdrop_r1]
  have hdrop_r3 : C.tpl.drop (pos + 1 + lf + lw + lp) = r3 := by rw [← List.drop_drop, hdrop_r2]
  have hlen_tpl : rest.length = C.tpl.length - (pos + 1) := by
    have hdl : (C.tpl.drop pos).length = C.tpl.length - pos := List.length_drop
    rw [hdrop, List.length_cons] at hdl; omega
  have hr1_len : r1.length = rest.length - lf := List.length_drop
  have hr2_len : r2.length = r1.length - lw := List.length_drop
  have hr3_len : r3.length = r2.length - lp := List.length_drop
  refine cwCustom_d1 C hext_blk hcl hdrop1 (by omega) hn_ge hne80 hnec0 (by omega)
    hcb.transport hpc hrun hsp hsp_al hx2 hx8 ?_
  intro s1 hcl1 hpc1 hrun1 hsp1 hsp_al1 hx8_1 hx9_1 hx22_1 hgpr1 hv1
  refine cwCustom_d2 C hext_blk hcl1 hdrop_r1 (by omega) (by omega)
    hcb.transport hpc1 hrun1 hsp1 hsp_al1 hx8_1 hx22_1 ?_
  intro s2 hcl2 hpc2 hrun2 hsp2 hsp_al2 hx8_2 hx10_2 hx22_2 hgpr2 hv2
  refine cwCustom_d3 C hext_blk hcl2 hdrop_r2 (by omega) (by omega)
    hcb.transport hpc2 hrun2 hsp2 hsp_al2 hx8_2 hx22_2 ?_
  intro s3 hcl3 hpc3 hrun3 hsp3 hsp_al3 hx8_3 hx11_3 hx22_3 hgpr3 hv3
  have hx25_3 : s3.readReg64 (.gpr 25#5) = BitVec.ofNat 64 ai := by
    rw [hgpr3 25#5 (by decide) (by decide) (by decide),
        hgpr2 25#5 (by decide) (by decide) (by decide),
        hgpr1 25#5 (by decide) (by decide) (by decide) (by decide), hx25]
  refine cwCustom_d4 C hext_blk hcl3 hdrop_r3 (by omega) (by omega)
    hcb.transport hpc3 hrun3 hsp3 hsp_al3 hx22_3 hx25_3 ?_
  intro s4 hcl4 hpc4 hrun4 hsp4 hsp_al4 hx22_4 hx25_4 hgpr4 hv4
  have hx8_4 : s4.readReg64 (.gpr 8#5) = n.zeroExtend 64 := by
    rw [hgpr4 8#5 (by decide) (by decide), hx8_3]
  have hx19_4 : s4.readReg64 (.gpr 19#5) = C.argsPtr := by
    rw [hgpr4 19#5 (by decide) (by decide),
        hgpr3 19#5 (by decide) (by decide) (by decide),
        hgpr2 19#5 (by decide) (by decide) (by decide),
        hgpr1 19#5 (by decide) (by decide) (by decide) (by decide), hx19]
  have hx10_4 : s4.readReg64 (.gpr 10#5) = BitVec.setWidth 64 width0 := by
    rw [hgpr4 10#5 (by decide) (by decide),
        hgpr3 10#5 (by decide) (by decide) (by decide), hx10_2]
  refine cwCustom_d5a C hext_blk hcl4 heven hw_res hcb.transport
    hpc4 hrun4 hsp4 hsp_al4 hx8_4 hx10_4 hx19_4 ?_
  intro s5 hcl5 hpc5 hrun5 hsp5 hsp_al5 hx10_5 hgpr5 hv5
  have hx11_5 : s5.readReg64 (.gpr 11#5) = BitVec.setWidth 64 prec0 := by
    rw [hgpr5 11#5 (by decide) (by decide),
        hgpr4 11#5 (by decide) (by decide), hx11_3]
  have hx19_5 : s5.readReg64 (.gpr 19#5) = C.argsPtr := by
    rw [hgpr5 19#5 (by decide) (by decide), hx19_4]
  refine cwCustom_d5b C hext_blk hcl5 heven hp_res hcb.transport
    hpc5 hrun5 hsp5 hsp_al5 hx11_5 hx19_5 ?_
  intro s6 hcl6 hpc6 hrun6 hsp6 hsp_al6 hx11_6 hgpr6 hv6
  have hx9_6 : s6.readReg64 (.gpr 9#5) = BitVec.setWidth 64 opts.flags := by
    rw [hgpr6 9#5 (by decide) (by decide),
        hgpr5 9#5 (by decide) (by decide),
        hgpr4 9#5 (by decide) (by decide),
        hgpr3 9#5 (by decide) (by decide) (by decide),
        hgpr2 9#5 (by decide) (by decide) (by decide), hx9_1, ← hfl_eq]
  have hx10_6 : s6.readReg64 (.gpr 10#5) = BitVec.setWidth 64 opts.width := by
    rw [hgpr6 10#5 (by decide) (by decide), hx10_5]
  have hx19_6 : s6.readReg64 (.gpr 19#5) = C.argsPtr := by
    rw [hgpr6 19#5 (by decide) (by decide), hx19_5]
  have hx20_6 : s6.readReg64 (.gpr 20#5) = C.out := by
    rw [hgpr6 20#5 (by decide) (by decide), hgpr5 20#5 (by decide) (by decide),
        hgpr4 20#5 (by decide) (by decide), hgpr3 20#5 (by decide) (by decide) (by decide),
        hgpr2 20#5 (by decide) (by decide) (by decide),
        hgpr1 20#5 (by decide) (by decide) (by decide) (by decide), hx20]
  have hx21_6 : s6.readReg64 (.gpr 21#5) = C.vt := by
    rw [hgpr6 21#5 (by decide) (by decide), hgpr5 21#5 (by decide) (by decide),
        hgpr4 21#5 (by decide) (by decide), hgpr3 21#5 (by decide) (by decide) (by decide),
        hgpr2 21#5 (by decide) (by decide) (by decide),
        hgpr1 21#5 (by decide) (by decide) (by decide) (by decide), hx21]
  have hx22_6 : s6.readReg64 (.gpr 22#5) = C.tplPtr + BitVec.ofNat 64 (pos + 1 + k) := by
    have hp_k : pos + 1 + lf + lw + lp + li = pos + 1 + k := by omega
    rw [hgpr6 22#5 (by decide) (by decide), hgpr5 22#5 (by decide) (by decide), hx22_4]
    simp only [lf, lw, lp, li, hp_k]
  have hx24_6 : s6.readReg64 (.gpr 24#5) = C.writeStrFn := by
    rw [hgpr6 24#5 (by decide) (by decide), hgpr5 24#5 (by decide) (by decide),
        hgpr4 24#5 (by decide) (by decide), hgpr3 24#5 (by decide) (by decide) (by decide),
        hgpr2 24#5 (by decide) (by decide) (by decide),
        hgpr1 24#5 (by decide) (by decide) (by decide) (by decide), hx24]
  have hx25_6 : s6.readReg64 (.gpr 25#5) = BitVec.ofNat 64 idx := by
    rw [hgpr6 25#5 (by decide) (by decide), hgpr5 25#5 (by decide) (by decide), hx25_4, ← hidx_eq]
  have hx26_6 : s6.readReg64 (.gpr 26#5) = 0x60000020#64 := by
    rw [hgpr6 26#5 (by decide) (by decide), hgpr5 26#5 (by decide) (by decide),
        hgpr4 26#5 (by decide) (by decide), hgpr3 26#5 (by decide) (by decide) (by decide),
        hgpr2 26#5 (by decide) (by decide) (by decide),
        hgpr1 26#5 (by decide) (by decide) (by decide) (by decide), hx26]
  have hx27_6 : s6.readReg64 (.gpr 27#5) = C.s0.readReg64 (.gpr 27#5) := by
    rw [hgpr6 27#5 (by decide) (by decide), hgpr5 27#5 (by decide) (by decide),
        hgpr4 27#5 (by decide) (by decide), hgpr3 27#5 (by decide) (by decide) (by decide),
        hgpr2 27#5 (by decide) (by decide) (by decide),
        hgpr1 27#5 (by decide) (by decide) (by decide) (by decide), hx27]
  have hx28_6 : s6.readReg64 (.gpr 28#5) = C.s0.readReg64 (.gpr 28#5) := by
    rw [hgpr6 28#5 (by decide) (by decide), hgpr5 28#5 (by decide) (by decide),
        hgpr4 28#5 (by decide) (by decide), hgpr3 28#5 (by decide) (by decide) (by decide),
        hgpr2 28#5 (by decide) (by decide) (by decide),
        hgpr1 28#5 (by decide) (by decide) (by decide) (by decide), hx28]
  have hv_6 : calleeSavedVRegs s6 = calleeSavedVRegs C.s0 := by
    rw [hv6, hv5, hv4, hv3, hv2, hv1, hvregs]
  refine cwCustom_d6_preCall C hext_blk hcl6 heven harg hcb.transport
    hpc6 hrun6 hsp6 hsp_al6 hx9_6 hx10_6 hx11_6 hx19_6 hx20_6 hx21_6 hx22_6
    hx24_6 hx25_6 hx26_6 hx27_6 hx28_6 hv_6 ?_
  intro sm hcl_sm hpc_sm hrun_sm hsp_sm hsp_al_sm hlr_sm hx0_sm hx1_sm
    hx19_sm hx20_sm hx21_sm hx22_sm hx24_sm hx25_sm hx26_sm hx27_sm hx28_sm hvregs_sm
  refine cwCallFmtArg_wpp C hcl_sm hcb hpc_sm hrun_sm hsp_sm hsp_al_sm hlr_sm hx0_sm hx1_sm
    fun sf ok st' hpcf hrunf hsp_sf hsp_al_sf hcs_sf hcl_sf hw0f hstep => ?_
  rw [CalleeSavedPreserved.iff_regs] at hcs_sf
  rcases hcs_sf with ⟨h19f, h20f, h21f, h22f, _, h24f, h25f, h26f, h27f, h28f, _, hvrf⟩
  have hbit0_sf : (sf.readReg64 (.gpr 0#5)).getLsbD 0 = !ok :=
    w0_bit0_of_and1_ite (by simpa [arm64_norm] using hw0f)
  cases ok
  ·
    apply sepWPp_seg_coreFmt_pure hext_blk hcl_sf (mid := cwPl0.base + 404#64)
    intro sp2 hcpu2
    have hpc2 : sp2.pc = cwPl0.base + 324#64 := hcpu2.pc_eq.trans hpcf
    have hrun2 : sp2.status = .Running := hcpu2.status_eq.trans hrunf
    have hsp_al2 : sp2.spAligned = true := hcpu2.spAligned.trans hsp_al_sf
    have hbit0_2 : (sp2.readReg64 (.gpr 0#5)).getLsbD 0 = true := by
      rw [hcpu2.readReg64]; simpa using hbit0_sf
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun2)
      fun sm2 hcpu2_out hcl_sm2 hnsp2 hsig2 htp2 horc2 hsym2 => ?_
    have hframe2 : FmtWriteFrame sf sm2 := fmtWriteFrame_of_seg hnsp2 hsig2 htp2 horc2 hsym2
    refine SepWPp.weaken_pre (cwLoopMem_transport C hcb.transport hframe2) ?_
    exact cwExitErr_wpp C hext_blk hcl_sm2
      (by rw [hcpu2_out.pc_eq]; simp [arm64_norm])
      (by rw [hcpu2_out.status_eq]; simpa [arm64_norm] using hrun2)
      (by rw [hcpu2_out.sp_eq]; simp [arm64_norm, hcpu2.sp_eq, hsp_sf])
      (by simp [arm64_norm] at hsp_al2; rw [hcpu2_out.spAligned]; simpa [arm64_norm] using hsp_al2)
      (by rw [hcpu2_out.readReg64]; simp [arm64_norm, hcpu2.readReg64, h27f, hx27_sm])
      (by rw [hcpu2_out.readReg64]; simp [arm64_norm, hcpu2.readReg64, h28f, hx28_sm])
      (by rw [hcpu2_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu2.calleeSavedVRegs, hvrf] using hvregs_sm)
      (.cons_err hstep) hcb.transport
  ·
    apply cw_step_ok_conseq C hstep
    apply sepWPp_seg_coreFmt_pure hext_blk hcl_sf (mid := cwPl0.base + 104#64)
    intro sp2 hcpu2
    have hpc2 : sp2.pc = cwPl0.base + 324#64 := hcpu2.pc_eq.trans hpcf
    have hrun2 : sp2.status = .Running := hcpu2.status_eq.trans hrunf
    have hsp_al2 : sp2.spAligned = true := hcpu2.spAligned.trans hsp_al_sf
    have hbit0_2 : (sp2.readReg64 (.gpr 0#5)).getLsbD 0 = false := by
      rw [hcpu2.readReg64]; simpa using hbit0_sf
    have hx25_2 : sp2.readReg64 (.gpr 25#5) = BitVec.ofNat 64 idx := by
      rw [hcpu2.readReg64, h25f, hx25_sm]
    clear hidx_eq
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun2)
      fun sm2 hcpu2_out hcl_sm2 hnsp2 hsig2 htp2 horc2 hsym2 => ?_
    have hframe2 : FmtWriteFrame sf sm2 := fmtWriteFrame_of_seg hnsp2 hsig2 htp2 horc2 hsym2
    refine SepWPp.weaken_pre (cwLoopMem_transport C hcb.transport hframe2) ?_
    subst hai'_eq
    refine ih_loop st' pad sm2 hcl_sm2 (fmtCallbacks_cons_inv hcb)
      (by rw [hcpu2_out.pc_eq]; simp [arm64_norm])
      (by rw [hcpu2_out.status_eq]; simpa [arm64_norm] using hrun2)
      (by rw [hcpu2_out.sp_eq]; simp [arm64_norm, hcpu2.sp_eq, hsp_sf])
      (by simp [arm64_norm] at hsp_al2; rw [hcpu2_out.spAligned]; simpa [arm64_norm] using hsp_al2)
      (by rw [hcpu2_out.readReg64]; simp [arm64_norm, hcpu2.readReg64, h19f, hx19_sm])
      (by rw [hcpu2_out.readReg64]; simp [arm64_norm, hcpu2.readReg64, h20f, hx20_sm])
      (by rw [hcpu2_out.readReg64]; simp [arm64_norm, hcpu2.readReg64, h21f, hx21_sm])
      (by rw [hcpu2_out.readReg64]; simp [arm64_norm, hcpu2.readReg64, h22f, hx22_sm])
      (by rw [hcpu2_out.readReg64]; simp [arm64_norm, hcpu2.readReg64, h24f, hx24_sm])
      (by rw [hcpu2_out.readReg64]; simp [arm64_norm, ← bv64_add_ofNat])
      (by rw [hcpu2_out.readReg64]; simp [arm64_norm, hcpu2.readReg64, h26f, hx26_sm])
      (by rw [hcpu2_out.readReg64]; simp [arm64_norm, hcpu2.readReg64, h27f, hx27_sm])
      (by rw [hcpu2_out.readReg64]; simp [arm64_norm, hcpu2.readReg64, h28f, hx28_sm])
      (by rw [hcpu2_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu2.calleeSavedVRegs, hvrf] using hvregs_sm)

end

end VerifiedLibraries.RustStd
