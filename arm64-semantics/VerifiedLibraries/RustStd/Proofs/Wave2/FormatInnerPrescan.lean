/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Spec
public import VerifiedLibraries.RustStd.Proofs.Wave2.FormatInnerLemmas

/-!
# Pre-Scan Loop Verification for `alloc::fmt::format::format_inner`

Defines the accumulator `prescanRun` and register-preservation bundle `PrescanKeep`, and verifies
`format_inner`'s template pre-scan step, loop, and entry wrapper.
-/

@[expose] public section

set_option autoImplicit false

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj ProofLib

/-! ## Pure Accumulator `prescanRun` -/

/-- Tail-recursive accumulator mirroring `format_inner`'s `+0x04c .. +0x0b0` loop registers
    `(x8 = lit, w9 = swp)`. -/
def prescanRun : Nat → Bool → List FmtCall → Nat × Bool
  | lit, swp, [] => (lit, swp)
  | lit, swp, .writeStr _ bs :: cs => prescanRun (lit + bs.length) swp cs
  | lit, swp, .fmtArg .. :: cs => prescanRun lit (decide (lit = 0) || swp) cs

theorem prescanRun_fst (cs : List FmtCall) :
    ∀ (lit : Nat) (swp : Bool), (prescanRun lit swp cs).1 = lit + fmtLiteralLen cs := by
  induction cs with
  | nil => intro lit swp; simp [prescanRun, fmtLiteralLen]
  | cons c cs' ih =>
    intro lit swp
    cases c with
    | writeStr ptr bs =>
      simp only [prescanRun, fmtLiteralLen, ih]
      omega
    | fmtArg idx value fmtFn opts =>
      simp only [prescanRun, fmtLiteralLen, ih]

theorem prescanRun_snd (cs : List FmtCall) :
    ∀ (lit : Nat) (swp : Bool),
      (prescanRun lit swp cs).2 = (swp || (decide (lit = 0) && fmtStartsWithPlaceholder cs)) := by
  induction cs with
  | nil => intro lit swp; simp [prescanRun, fmtStartsWithPlaceholder]
  | cons c cs' ih =>
    intro lit swp
    cases c with
    | writeStr ptr bs =>
      simp only [prescanRun, fmtStartsWithPlaceholder, ih]
      cases bs <;> simp [List.isEmpty]
    | fmtArg idx value fmtFn opts =>
      simp only [prescanRun, fmtStartsWithPlaceholder, ih]
      cases h0 : decide (lit = 0) <;> cases swp <;> simp

theorem prescanRun_zero (cs : List FmtCall) :
    prescanRun 0 false cs = (fmtLiteralLen cs, fmtStartsWithPlaceholder cs) := by
  apply Prod.ext
  · simpa using prescanRun_fst cs 0 false
  · simpa using prescanRun_snd cs 0 false

/-! ## Register Preservation Bundle and Byte-Slice Helpers -/

/-- Registers untouched by `format_inner`'s pre-scan (`+0x028 .. +0x0e0`). -/
structure PrescanKeep (s s' : State) : Prop where
  sp : s'.sp = s.sp
  x19 : s'.readReg64 .x19 = s.readReg64 .x19
  x20 : s'.readReg64 .x20 = s.readReg64 .x20
  x21 : s'.readReg64 .x21 = s.readReg64 .x21
  x24 : s'.readReg64 .x24 = s.readReg64 .x24
  x25 : s'.readReg64 .x25 = s.readReg64 .x25
  x26 : s'.readReg64 .x26 = s.readReg64 .x26
  x27 : s'.readReg64 .x27 = s.readReg64 .x27
  x28 : s'.readReg64 .x28 = s.readReg64 .x28
  x29 : s'.readReg64 .x29 = s.readReg64 .x29
  vregs : calleeSavedVRegs s' = calleeSavedVRegs s
  tpidr : s'.tpidrEl0 = s.tpidrEl0
  sigActions : s'.sigActions = s.sigActions

theorem PrescanKeep.refl (s : State) : PrescanKeep s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem PrescanKeep.trans {s0 s1 s2 : State}
    (h01 : PrescanKeep s0 s1) (h12 : PrescanKeep s1 s2) : PrescanKeep s0 s2 :=
  ⟨h12.sp.trans h01.sp, h12.x19.trans h01.x19, h12.x20.trans h01.x20, h12.x21.trans h01.x21,
   h12.x24.trans h01.x24, h12.x25.trans h01.x25, h12.x26.trans h01.x26, h12.x27.trans h01.x27,
   h12.x28.trans h01.x28, h12.x29.trans h01.x29, h12.vregs.trans h01.vregs,
   h12.tpidr.trans h01.tpidr, h12.sigActions.trans h01.sigActions⟩

private theorem sepWP_seq {prog : Program} {mid_pc target_pc : BitVec 64}
    {s : State} {P : SepProp} {mid_post post : State → SepProp → Prop}
    (h1 : SepWP prog mid_pc s P mid_post)
    (h2 : ∀ sm Pm, sm.pc = mid_pc → sm.status = .Running → mid_post sm Pm →
      SepWP prog target_pc sm Pm post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at h1 ⊢
  intro R hm hL
  obtain ⟨sm, hs1, ⟨hpc_m, hrun_m, Pm, hmm, hmp⟩ | ⟨ho, hmo⟩⟩ := h1 R hm hL
  · have h2' := h2 sm Pm hpc_m hrun_m hmp
    unfold SepWP at h2'
    obtain ⟨sf, hs2, hout2⟩ := h2' R hmm (hs1.codeLoaded hL)
    exact ⟨sf, hs1.trans hs2, hout2⟩
  · exact ⟨sm, hs1, Or.inr ⟨ho, hmo⟩⟩

private theorem sepWP_frame_left {prog : Program} {target_pc : BitVec 64}
    {s : State} {F P : SepProp} {post : State → SepProp → Prop}
    (h : SepWP prog target_pc s P (fun sf Pf => post sf (F ∗ Pf))) :
    SepWP prog target_pc s (F ∗ P) post := by
  unfold SepWP at h ⊢
  intro R hm
  have hm' : s.mem ⊨ P ∗ (F ∗ R) := by revert hm; intro hm; sep_frame
  refine reaches_pc_mono (h (F ∗ R) hm') ?_
    (fun _ _ ho => False.elim (not_satisfies_false_sepConj ho))
  rintro sf _ _ ⟨Pf, hmf, hp⟩
  have hmf' : sf.mem ⊨ (F ∗ Pf) ∗ R := by revert hmf; intro hmf; sep_frame
  exact ⟨F ∗ Pf, hmf', hp⟩

private theorem leBytesNat2_bv (b0 b1 : BitVec 8) :
    ((b1 ++ b0 : BitVec 16).zeroExtend 64) = BitVec.ofNat 64 (leBytesNat [b0, b1]) := by
  apply BitVec.eq_of_toNat_eq
  have hb0 := b0.isLt
  have hb1 := b1.isLt
  have happ : (b1 ++ b0 : BitVec 16).toNat = (b1.toNat <<< 8) + b0.toNat := by
    rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt hb0]
  have hze : ((b1 ++ b0 : BitVec 16).zeroExtend 64).toNat = (b1 ++ b0 : BitVec 16).toNat :=
    BitVec.toNat_setWidth_of_le (by omega)
  rw [hze, happ]
  simp only [leBytesNat, List.foldr, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

private theorem pointsToBytesRO_split_at (base : BitVec 64) (pos skip : Nat)
    (bs : List (BitVec 8)) (hskip : skip ≤ bs.length) :
    ((base + BitVec.ofNat 64 pos) ↦ᵣ bs) =
      (((base + BitVec.ofNat 64 pos) ↦ᵣ bs.take skip) ∗
       ((base + BitVec.ofNat 64 (pos + skip)) ↦ᵣ bs.drop skip)) := by
  have hlen : (bs.take skip).length = skip := List.length_take_of_le hskip
  have haddr : base + BitVec.ofNat 64 pos + BitVec.ofNat 64 skip =
      base + BitVec.ofNat 64 (pos + skip) := by
    bv_omega
  conv => lhs; rw [← List.take_append_drop skip bs]
  rw [pointsToBytesRO_append, hlen, haddr]

private theorem pointsToBytesRO_header3 (a : BitVec 64) (n b0 b1 : BitVec 8) (r : List (BitVec 8)) :
    (a ↦ᵣ (n :: b0 :: b1 :: r)) =
      ((a ↦₈ᵣ n) ∗ ((a + 1#64) ↦₁₆ᵣ (b1 ++ b0)) ∗ ((a + 3#64) ↦ᵣ r)) := by
  have hsplit : (n :: b0 :: b1 :: r) = [n] ++ ([b0, b1] ++ r) := rfl
  have ha12 : a + 1#64 + 2#64 = a + 3#64 := by bv_arith
  rw [hsplit, pointsToBytesRO_append, pointsToBytesRO_append]
  have hl1 : ([n] : List (BitVec 8)).length = 1 := rfl
  have hl2 : ([b0, b1] : List (BitVec 8)).length = 2 := rfl
  rw [hl1, hl2, pointsToBytesRO2_eq_pointsTo16RO, pointsToBytesRO_cons, pointsToBytesRO_nil,
    sepConj_emp, ha12]

set_option maxRecDepth 200000 in
private theorem byte_lt_80_tbz (n : BitVec 8) (h : n.toNat < 0x80) :
    (((n.zeroExtend 64 : BitVec 64).setWidth 32 &&& (1#32 <<< 7)) == 0#32) = true := by
  revert h n; decide

set_option maxRecDepth 200000 in
private theorem byte_ge_c0_flags (n : BitVec 8) (h : ¬ n.toNat < 0xc0) :
    (((n.zeroExtend 64 : BitVec 64).setWidth 32 &&& (1#32 <<< 7)) != 0#32) = true ∧
    (((n.zeroExtend 64 : BitVec 64).setWidth 32 &&& 0xff#32) != 0x80#32) = true := by
  revert h n; decide

set_option maxRecDepth 200000 in
private theorem reverseBits32_of_lt4 {x : BitVec 32} (hx : x.toNat < 4) :
    reverseBits x = x.reverse := by
  have hfold : ∀ y : BitVec 32,
      reverseBits y =
        (List.range' 0 32 1).foldl
          (fun s i => if y.getLsbD i = true then s ||| 1#32 <<< (32 - 1 - i) else s) 0#32 := by
    intro y
    simp only [Arm64.reverseBits, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
    have h : ∀ i (s : BitVec 32),
        (if y.getLsbD i = true then (pure (ForInStep.yield (s ||| 1#32 <<< (32 - 1 - i))) : Id _)
          else pure (ForInStep.yield s)) =
        pure (ForInStep.yield (if y.getLsbD i = true then s ||| 1#32 <<< (32 - 1 - i) else s)) := by
      intro i s; split <;> rfl
    simp only [h, List.forIn_pure_yield_eq_foldl, bind_pure, Id.run_pure]
    rfl
  rw [hfold]
  have h4 : x = 0#32 ∨ x = 1#32 ∨ x = 2#32 ∨ x = 3#32 := by bv_omega
  rcases h4 with rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 200000 in
private theorem byte_placeholder_skip_norm (base : BitVec 64) (n : BitVec 8) :
    base +
    (BitVec.zeroExtend 64 (n >>> 1) &&& 8589934594#64) +
    (BitVec.zeroExtend 64 (n >>> 2) &&& 8589934594#64) +
    BitVec.setWidth 64
      (BitVec.setWidth 32
        (BitVec.setWidth 64
          (reverseBits (BitVec.setWidth 32 (BitVec.zeroExtend 64 n &&& 12884901891#64))) >>> 29)) =
    base + BitVec.ofNat 64
      ((if n.getLsbD 0 then 4 else 0) + (if n.getLsbD 1 then 2 else 0) +
       (if n.getLsbD 2 then 2 else 0) + (if n.getLsbD 3 then 2 else 0)) := by
  have hx_lt4 : (BitVec.setWidth 32 (BitVec.zeroExtend 64 n &&& 12884901891#64)).toNat < 4 := by
    revert n; decide
  have hconst :
      (BitVec.zeroExtend 64 (n >>> 1) &&& 8589934594#64) +
      (BitVec.zeroExtend 64 (n >>> 2) &&& 8589934594#64) +
      BitVec.setWidth 64
        (BitVec.setWidth 32
          (BitVec.setWidth 64
            ((BitVec.setWidth 32 (BitVec.zeroExtend 64 n &&& 12884901891#64)).reverse) >>> 29)) =
      BitVec.ofNat 64
        ((if n.getLsbD 0 then 4 else 0) + (if n.getLsbD 1 then 2 else 0) +
         (if n.getLsbD 2 then 2 else 0) + (if n.getLsbD 3 then 2 else 0)) := by
    revert n; decide
  rw [reverseBits32_of_lt4 hx_lt4, BitVec.add_assoc base, BitVec.add_assoc base, hconst]

/-! ## One Non-Zero Opcode Step (`+0x054` to `+0x04c`) -/

section PrescanWP
variable [FormatInnerPlacement]

theorem formatInner_prescan_step_054
    {target_pc tplPtr : BitVec 64} {args : List (BitVec 64 × BitVec 64)}
    {fuel pos ai lit : Nat} {swp : Bool}
    {n : BitVec 8} {rest : List (BitVec 8)} {cs : List FmtCall}
    {s : State} {post : State → SepProp → Prop}
    (hpc : s.pc = allocPl03.base + 84#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 lit)
    (hx9 : s.readReg64 .x9 = if swp then 1#64 else 0#64)
    (hx10 : s.readReg64 .x10 = n.zeroExtend 64)
    (hx11 : s.readReg64 .x11 = tplPtr + BitVec.ofNat 64 pos)
    (hn0 : n ≠ 0#8)
    (hdec : decodeFmtTemplate tplPtr args (fuel + 1) pos ai (n :: rest) = some cs)
    (hlit_lt : lit + fmtLiteralLen cs < 2 ^ 64)
    (hnext : ∀ (skip ai' lit' : Nat) (swp' : Bool) (cs' : List FmtCall) (s1 : State),
      skip ≤ (n :: rest).length →
      decodeFmtTemplate tplPtr args fuel (pos + skip) ai' ((n :: rest).drop skip) = some cs' →
      prescanRun lit swp cs = prescanRun lit' swp' cs' →
      lit' + fmtLiteralLen cs' = lit + fmtLiteralLen cs →
      s1.pc = allocPl03.base + 76#64 →
      s1.status = .Running →
      s1.spAligned = true →
      PrescanKeep s s1 →
      s1.readReg64 .x8 = BitVec.ofNat 64 lit' →
      s1.readReg64 .x9 = (if swp' then 1#64 else 0#64) →
      s1.readReg64 .x11 = tplPtr + BitVec.ofNat 64 (pos + skip) →
      SepWP (allocPC03.rebase allocPl03.base (fun _ => none)) target_pc s1
        ((tplPtr + BitVec.ofNat 64 pos) ↦ᵣ (n :: rest)) post) :
    SepWP (allocPC03.rebase allocPl03.base (fun _ => none)) target_pc s
      ((tplPtr + BitVec.ofNat 64 pos) ↦ᵣ (n :: rest)) post := by
  simp only [decodeFmtTemplate, hn0, ↓reduceIte] at hdec
  by_cases hn80 : n.toNat < 0x80
  ·
    simp only [hn80, ↓reduceIte] at hdec
    by_cases hrlen : rest.length < n.toNat
    · simp [hrlen] at hdec
    · simp only [hrlen, ↓reduceIte, Option.map_eq_some_iff] at hdec
      rcases hdec with ⟨cs', hrec, rfl⟩
      have htake_len : (rest.take n.toNat).length = n.toNat :=
        List.length_take_of_le (Nat.le_of_not_lt hrlen)
      have hdrop : (n :: rest).drop (1 + n.toNat) = rest.drop n.toNat := by
        rw [Nat.add_comm 1, List.drop_succ_cons]
      have hrec' : decodeFmtTemplate tplPtr args fuel (pos + (1 + n.toNat)) ai
          ((n :: rest).drop (1 + n.toNat)) = some cs' := by
        simpa [hdrop, Nat.add_assoc] using hrec
      have hpr_eq : prescanRun lit swp
          (.writeStr (tplPtr + BitVec.ofNat 64 (pos + 1)) (rest.take n.toNat) :: cs') =
          prescanRun (lit + n.toNat) swp cs' := by
        simp [prescanRun, htake_len]
      have hlit_eq : (lit + n.toNat) + fmtLiteralLen cs' =
          lit + fmtLiteralLen (.writeStr (tplPtr + BitVec.ofNat 64 (pos + 1)) (rest.take n.toNat) :: cs') := by
        simp only [fmtLiteralLen, htake_len]; omega
      have htbz := byte_lt_80_tbz n hn80
      clear hrec
      wp_sym_steps
      refine hnext (1 + n.toNat) ai (lit + n.toNat) swp cs' _
        (by simp; omega) hrec' hpr_eq hlit_eq
        (by simp [wp_norm, arm64_norm])
        (by simpa [wp_norm, arm64_norm] using hrun)
        (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp)
        ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
         by simp [wp_norm, arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
        ?_ (by simpa [wp_norm, arm64_norm] using hx9) ?_
      · simp only [wp_norm, arm64_norm]
        bv_omega
      · simp only [wp_norm, arm64_norm]
        bv_omega
  ·
    simp only [hn80, ↓reduceIte] at hdec
    by_cases heq80 : n = 0x80#8
    ·
      subst heq80
      simp only [↓reduceIte] at hdec
      by_cases hr2 : rest.length < 2
      · simp [hr2] at hdec
      · simp only [hr2, ↓reduceIte] at hdec
        rcases rest with _ | ⟨b0, _ | ⟨b1, r⟩⟩
        · simp at hr2
        · simp at hr2
        · dsimp only [List.take, List.drop] at hdec
          let len := leBytesNat [b0, b1]
          by_cases hrlen : r.length < leBytesNat [b0, b1]
          · simp only [hrlen, ↓reduceIte] at hdec; cases hdec
          · simp only [hrlen, ↓reduceIte, Option.map_eq_some_iff] at hdec
            rcases hdec with ⟨cs', hrec, rfl⟩
            have htake_len : (r.take len).length = len :=
              List.length_take_of_le (Nat.le_of_not_lt hrlen)
            have hdrop : (0x80#8 :: b0 :: b1 :: r).drop (3 + len) = r.drop len := by
              rw [Nat.add_comm 3 len]; rfl
            have hrec' : decodeFmtTemplate tplPtr args fuel (pos + (3 + len)) ai
                ((0x80#8 :: b0 :: b1 :: r).drop (3 + len)) = some cs' := by
              simpa [hdrop, Nat.add_assoc] using hrec
            have hpr_eq : prescanRun lit swp
                (.writeStr (tplPtr + BitVec.ofNat 64 (pos + 3)) (r.take len) :: cs') =
                prescanRun (lit + len) swp cs' := by
              simp [prescanRun, htake_len, len]
            have hlit_eq : (lit + len) + fmtLiteralLen cs' =
                lit + fmtLiteralLen (.writeStr (tplPtr + BitVec.ofNat 64 (pos + 3)) (r.take len) :: cs') := by
              simp only [fmtLiteralLen, htake_len, len]; omega
            wp_conv_pre => rw [pointsToBytesRO_header3]
            clear hrec
            wp_sym_steps
            wp_conv_pre => rw [← pointsToBytesRO_header3]
            refine hnext (3 + len) ai (lit + len) swp cs' _
              (by simp; omega) hrec' hpr_eq hlit_eq
              (by simp [wp_norm, arm64_norm])
              (by simpa [wp_norm, arm64_norm] using hrun)
              (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp)
              ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
               by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
               by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
               by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
               by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
               by simp [wp_norm, arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
              ?_ (by simpa [wp_norm, arm64_norm] using hx9) ?_
            · simp only [wp_norm, arm64_norm]
              dsimp only [len]
              rw [leBytesNat2_bv]
              bv_omega
            · simp only [wp_norm, arm64_norm]
              dsimp only [len]
              rw [leBytesNat2_bv]
              bv_omega
    ·
      simp only [heq80, ↓reduceIte] at hdec
      by_cases hnc0 : n.toNat < 0xc0
      · simp [hnc0] at hdec
      · simp only [hnc0, ↓reduceIte] at hdec
        cases hph : decodeFmtPlaceholder n rest args ai with
        | none => simp [hph] at hdec
        | some val =>
          rcases val with ⟨opts, idx, ai', k⟩
          simp only [hph] at hdec
          cases harg : args[idx]? with
          | none => simp [harg] at hdec
          | some vf =>
            rcases vf with ⟨value, fmtFn⟩
            simp only [harg, Option.map_eq_some_iff] at hdec
            rcases hdec with ⟨cs', hrec, rfl⟩
            obtain ⟨hk_eq, hk_le⟩ := decodeFmtPlaceholder_skip_eq hph
            have hdrop : (n :: rest).drop (1 + k) = rest.drop k := by
              rw [Nat.add_comm 1, List.drop_succ_cons]
            have hrec' : decodeFmtTemplate tplPtr args fuel (pos + (1 + k)) ai'
                ((n :: rest).drop (1 + k)) = some cs' := by
              simpa [hdrop, Nat.add_assoc] using hrec
            have hpr_eq : prescanRun lit swp (.fmtArg idx value fmtFn opts :: cs') =
                prescanRun lit (decide (lit = 0) || swp) cs' := by
              simp [prescanRun]
            have hlit_eq : lit + fmtLiteralLen cs' =
                lit + fmtLiteralLen (.fmtArg idx value fmtFn opts :: cs') := by
              simp [fmtLiteralLen]
            obtain ⟨hbit7, hne80_32⟩ := byte_ge_c0_flags n hnc0
            clear hrec hph harg
            wp_sym_steps
            refine hnext (1 + k) ai' lit (decide (lit = 0) || swp) cs' _
              (by simp; omega) hrec' hpr_eq hlit_eq
              (by simp [wp_norm, arm64_norm])
              (by simpa [wp_norm, arm64_norm] using hrun)
              (by simpa [State.spAligned, wp_norm, arm64_norm] using hsp)
              ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
               by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
               by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
               by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
               by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
               by simp [wp_norm, arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
              (by simpa [wp_norm, arm64_norm] using hx8) ?_ ?_
            · have hlit_lt' : lit < 2 ^ 64 := by simp [fmtLiteralLen] at hlit_lt; omega
              by_cases hlit0 : lit = 0
              · subst hlit0
                cases swp <;> simp [wp_norm, arm64_norm]
              · have hbv_ne : BitVec.ofNat 64 lit ≠ 0#64 := by bv_omega
                cases swp <;> simp [wp_norm, arm64_norm, hlit0, hbv_ne]
            · simp only [wp_norm, arm64_norm]
              rw [byte_placeholder_skip_norm _ n, ← hk_eq]
              bv_omega

/-! ## Pre-Scan Loop (`+0x04c` to `+0x0bc`) and Entry (`+0x054` to `+0x0bc`) -/

theorem formatInner_prescan_loop_04c
    {tplPtr : BitVec 64} {args : List (BitVec 64 × BitVec 64)} :
    ∀ (fuel pos ai lit : Nat) (swp : Bool) (bs : List (BitVec 8)) (cs : List FmtCall)
      (s : State),
      s.pc = allocPl03.base + 76#64 →
      s.status = .Running →
      s.spAligned = true →
      s.readReg64 .x8 = BitVec.ofNat 64 lit →
      s.readReg64 .x9 = (if swp then 1#64 else 0#64) →
      s.readReg64 .x11 = tplPtr + BitVec.ofNat 64 pos →
      decodeFmtTemplate tplPtr args fuel pos ai bs = some cs →
      lit + fmtLiteralLen cs < 2 ^ 64 →
      SepWP (allocPC03.rebase allocPl03.base (fun _ => none)) (allocPl03.base + 188#64) s
        ((tplPtr + BitVec.ofNat 64 pos) ↦ᵣ bs)
        (fun sf Pf =>
          Pf = ((tplPtr + BitVec.ofNat 64 pos) ↦ᵣ bs) ∧
          sf.spAligned = true ∧
          PrescanKeep s sf ∧
          sf.readReg64 .x8 = BitVec.ofNat 64 (prescanRun lit swp cs).1 ∧
          sf.readReg64 .x9 = (if (prescanRun lit swp cs).2 then 1#64 else 0#64))
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, hdec, _ => by
    simp [decodeFmtTemplate] at hdec
  | _ + 1, _, _, _, _, [], _, _, _, _, _, _, _, _, hdec, _ => by
    simp [decodeFmtTemplate] at hdec
  | fuel + 1, pos, ai, lit, swp, n :: rest, cs, s,
      hpc, hrun, hsp, hx8, hx9, hx11, hdec, hlit_lt => by
    by_cases hn0 : n = 0#8
    ·
      subst hn0
      have hdec0 := hdec
      simp only [decodeFmtTemplate, ↓reduceIte] at hdec0
      by_cases hr0 : rest = []
      · subst hr0
        simp only [↓reduceIte, Option.some.injEq] at hdec0
        subst hdec0
        wp_conv_pre => rw [pointsToBytesRO_cons, pointsToBytesRO_nil, sepConj_emp]
        wp_sym_steps
        wp_conv_pre => rw [← sepConj_emp (_ ↦₈ᵣ 0#8),
          ← pointsToBytesRO_nil (tplPtr + BitVec.ofNat 64 pos + 1#64),
          ← pointsToBytesRO_cons]
        apply SepWP.done
          (by simp [wp_norm, arm64_norm])
          (by simpa [wp_norm, arm64_norm] using hrun)
        refine ⟨rfl, by simpa [State.spAligned, wp_norm, arm64_norm] using hsp,
          ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
           by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
           by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
           by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
           by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
           by simp [wp_norm, arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩,
          by simpa [prescanRun, wp_norm, arm64_norm] using hx8,
          by simp only [prescanRun, wp_norm, arm64_norm]; exact hx9⟩
      · simp [hr0] at hdec0
    ·
      have hnz32 : (n.zeroExtend 32 : BitVec 32) ≠ 0#32 := by bv_omega
      apply sepWP_seq (mid_pc := allocPl03.base + 84#64)
        (mid_post := fun s054 P054 =>
          P054 = ((tplPtr + BitVec.ofNat 64 pos) ↦ᵣ (n :: rest)) ∧
          s054.spAligned = true ∧
          PrescanKeep s s054 ∧
          s054.readReg64 .x8 = BitVec.ofNat 64 lit ∧
          s054.readReg64 .x9 = (if swp then 1#64 else 0#64) ∧
          s054.readReg64 .x10 = n.zeroExtend 64 ∧
          s054.readReg64 .x11 = tplPtr + BitVec.ofNat 64 pos)
      · wp_conv_pre => rw [pointsToBytesRO_cons]
        wp_sym_steps
        wp_conv_pre => rw [← pointsToBytesRO_cons]
        apply SepWP.done
          (by simp [wp_norm, arm64_norm])
          (by simpa [wp_norm, arm64_norm] using hrun)
        refine ⟨rfl, by simpa [State.spAligned, wp_norm, arm64_norm] using hsp,
          ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
           by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
           by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
           by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
           by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
           by simp [wp_norm, arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩,
          by simp only [wp_norm, arm64_norm]; exact hx8,
          by simp only [wp_norm, arm64_norm]; exact hx9,
          by simp [wp_norm, arm64_norm],
          by simp only [wp_norm, arm64_norm]; exact hx11⟩
      · rintro s054 _ hpc054 hrun054 ⟨rfl, hsp054, hkeep0, hx8_054, hx9_054, hx10_054, hx11_054⟩
        refine formatInner_prescan_step_054
          hpc054 hrun054 hsp054 hx8_054 hx9_054 hx10_054 hx11_054 hn0 hdec hlit_lt ?_
        intro skip ai' lit' swp' cs' s1 hskip_le hdec_next hpr_eq hlit_eq
          hpc1 hrun1 hsp1 hkeep1 hx8_1 hx9_1 hx11_1
        rw [pointsToBytesRO_split_at tplPtr pos skip (n :: rest) hskip_le]
        apply sepWP_frame_left
        refine SepWP.mono
          (formatInner_prescan_loop_04c fuel (pos + skip) ai' lit' swp'
            ((n :: rest).drop skip) cs' s1 hpc1 hrun1 hsp1 hx8_1 hx9_1 hx11_1
            hdec_next (hlit_eq.symm ▸ hlit_lt)) ?_
        rintro sf _ _ _ ⟨rfl, hspf, hkeep2, hx8_f, hx9_f⟩
        rw [← pointsToBytesRO_split_at tplPtr pos skip (n :: rest) hskip_le]
        rw [← hpr_eq] at hx8_f hx9_f
        exact ⟨rfl, hspf, hkeep0.trans (hkeep1.trans hkeep2), hx8_f, hx9_f⟩

theorem formatInner_prescan_from_054
    {tplPtr : BitVec 64} {args : List (BitVec 64 × BitVec 64)}
    {n : BitVec 8} {rest : List (BitVec 8)} {cs : List FmtCall}
    {s : State}
    (hpc : s.pc = allocPl03.base + 84#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = 0#64)
    (hx9 : s.readReg64 .x9 = 0#64)
    (hx10 : s.readReg64 .x10 = n.zeroExtend 64)
    (hx11 : s.readReg64 .x11 = tplPtr)
    (hn0 : n ≠ 0#8)
    (hdec : decodeFmtTemplate tplPtr args (rest.length + 1) 0 0 (n :: rest) = some cs)
    (hlit_lt : fmtLiteralLen cs < 2 ^ 64) :
    SepWP (allocPC03.rebase allocPl03.base (fun _ => none)) (allocPl03.base + 188#64) s
      (tplPtr ↦ᵣ (n :: rest))
      (fun sf Pf =>
        Pf = (tplPtr ↦ᵣ (n :: rest)) ∧
        sf.spAligned = true ∧
        PrescanKeep s sf ∧
        sf.readReg64 .x8 = BitVec.ofNat 64 (fmtLiteralLen cs) ∧
        sf.readReg64 .x9 = (if fmtStartsWithPlaceholder cs then 1#64 else 0#64)) := by
  have hx11' : s.readReg64 .x11 = tplPtr + BitVec.ofNat 64 0 := by simpa using hx11
  have hpre_eq : (tplPtr ↦ᵣ (n :: rest)) = ((tplPtr + BitVec.ofNat 64 0) ↦ᵣ (n :: rest)) := by
    simp
  rw [hpre_eq]
  refine formatInner_prescan_step_054 (lit := 0) (swp := false)
    hpc hrun hsp hx8 hx9 hx10 hx11' hn0 hdec (by omega) ?_
  intro skip ai' lit' swp' cs' s1 hskip_le hdec_next hpr_eq hlit_eq
    hpc1 hrun1 hsp1 hkeep1 hx8_1 hx9_1 hx11_1
  rw [pointsToBytesRO_split_at tplPtr 0 skip (n :: rest) hskip_le]
  apply sepWP_frame_left
  refine SepWP.mono
    (formatInner_prescan_loop_04c rest.length (0 + skip) ai' lit' swp'
      ((n :: rest).drop skip) cs' s1 hpc1 hrun1 hsp1 hx8_1 hx9_1 hx11_1
      hdec_next (by omega)) ?_
  rintro sf _ _ _ ⟨rfl, hspf, hkeep2, hx8_f, hx9_f⟩
  rw [← pointsToBytesRO_split_at tplPtr 0 skip (n :: rest) hskip_le, ← hpre_eq]
  rw [← hpr_eq, prescanRun_zero] at hx8_f hx9_f
  exact ⟨rfl, hspf, hkeep1.trans hkeep2, hx8_f, hx9_f⟩

end PrescanWP

end VerifiedLibraries.RustStd
