/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Spec
public import VerifiedLibraries.RustStd.Proofs.Wave2.FmtWriteLoop

/-!
# `core::fmt::write`: Callback Combinators and Literal/Default Opcodes

Defines the loop spatial invariant (`CwLoopMem`) and header continuation (`CwLoopCont`), proves
the `write_str` and `fmtArg` callback combinators, and steps the short-literal (`0x01..0x7f`),
long-literal (`0x80`), and default-argument (`0xc0`) opcodes.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj Arm64.Process ProofLib

/-! ## Arithmetic and Bit-Extraction Lemmas -/

theorem bv64_shl4_eq_mul16 (i : Nat) :
    (BitVec.ofNat 64 i) <<< 4 = BitVec.ofNat 64 (16 * i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem bv64_add_ofNat (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem u8_zeroExtend64_eq_ofNat (b : BitVec 8) :
    BitVec.setWidth 64 b = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

theorem u16_ofNat_zeroExtend64 {n : Nat} (hn : n < 65536) :
    BitVec.setWidth 64 (BitVec.ofNat 16 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem leBytesNat_pair_lt (b0 b1 : BitVec 8) :
    leBytesNat [b0, b1] < 65536 := by
  simp only [leBytesNat, List.foldr_cons, List.foldr_nil, Nat.mul_zero, Nat.add_zero]
  have := b0.isLt
  have := b1.isLt
  omega

theorem u8_bit7_false_of_lt_0x80 {n : BitVec 8} (h : n.toNat < 0x80) :
    (n.zeroExtend 64).getLsbD 7 = false := by
  simp only [BitVec.getLsbD, Nat.testBit, BitVec.toNat_setWidth,
    Nat.shiftRight_eq_div_pow, Nat.and_comm 1, Nat.and_one_is_mod, bne_eq_false_iff_eq]
  have := n.isLt
  omega

theorem u8_ne_0x80_ne_0xc0_bit7 {n : BitVec 8} (hge : ¬ n.toNat < 0x80)
    (hne80 : n ≠ 0x80#8) (hnec0 : n ≠ 0xc0#8) :
    (n.zeroExtend 64).getLsbD 7 = true ∧
    (n.zeroExtend 32 == 0x80#32) = false ∧
    (n.zeroExtend 32 == 0xc0#32) = false := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [BitVec.getLsbD, Nat.testBit, BitVec.toNat_setWidth,
      Nat.shiftRight_eq_div_pow, Nat.and_comm 1, Nat.and_one_is_mod, bne_iff_ne, ne_eq]
    have := n.isLt
    omega
  · rw [beq_eq_false_iff_ne]
    intro heq
    apply hne80
    apply BitVec.eq_of_toNat_eq
    have ht := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at ht ⊢
    have := n.isLt
    omega
  · rw [beq_eq_false_iff_ne]
    intro heq
    apply hnec0
    apply BitVec.eq_of_toNat_eq
    have ht := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at ht ⊢
    have := n.isLt
    omega

theorem w0_bit0_of_eq_ite {x0 : BitVec 64} {ok : Bool}
    (h : x0.setWidth 32 = if ok then 0#32 else 1#32) :
    x0.getLsbD 0 = !ok := by
  have ht := congrArg BitVec.toNat h
  simp only [BitVec.toNat_setWidth] at ht
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, BitVec.toNat_ofNat,
      BitVec.getLsbD, Nat.testBit, Nat.shiftRight_zero, Nat.and_comm 1, Nat.and_one_is_mod,
      bne_iff_ne, ne_eq] at ht ⊢
    omega
  · simp only [↓reduceIte, Bool.not_true, BitVec.toNat_ofNat,
      BitVec.getLsbD, Nat.testBit, Nat.shiftRight_zero, Nat.and_comm 1, Nat.and_one_is_mod,
      bne_eq_false_iff_eq] at ht ⊢
    omega

theorem w0_bit0_of_and1_ite {x0 : BitVec 64} {ok : Bool}
    (h : x0.setWidth 32 &&& 1#32 = if ok then 0#32 else 1#32) :
    x0.getLsbD 0 = !ok := by
  have ht := congrArg BitVec.toNat h
  have hand : (x0.setWidth 32 &&& 1#32).toNat = (x0.setWidth 32).toNat % 2 :=
    Nat.and_two_pow_sub_one_eq_mod (x0.setWidth 32).toNat 1
  rw [hand, BitVec.toNat_setWidth] at ht
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, BitVec.toNat_ofNat,
      BitVec.getLsbD, Nat.testBit, Nat.shiftRight_zero, Nat.and_comm 1, Nat.and_one_is_mod,
      bne_iff_ne, ne_eq] at ht ⊢
    omega
  · simp only [↓reduceIte, Bool.not_true, BitVec.toNat_ofNat,
      BitVec.getLsbD, Nat.testBit, Nat.shiftRight_zero, Nat.and_comm 1, Nat.and_one_is_mod,
      bne_eq_false_iff_eq] at ht ⊢
    omega

theorem tpl_focus_sublist (tplPtr : BitVec 64) (tpl : List (BitVec 8))
    (off : Nat) (mid suf : List (BitVec 8))
    (hdrop : tpl.drop off = mid ++ suf) (hle : off ≤ tpl.length) :
    (tplPtr ↦ᵣ tpl) =
      ((tplPtr + BitVec.ofNat 64 off) ↦ᵣ mid) ∗
      ((tplPtr ↦ᵣ tpl.take off) ∗
       ((tplPtr + BitVec.ofNat 64 (off + mid.length)) ↦ᵣ suf)) := by
  have hsplit : tpl = tpl.take off ++ (mid ++ suf) := by
    rw [← hdrop, List.take_append_drop]
  have htl : (tpl.take off).length = off := List.length_take_of_le hle
  conv => lhs; rw [hsplit]
  rw [pointsToBytesRO_append, pointsToBytesRO_append, htl]
  have ha : tplPtr + BitVec.ofNat 64 off + BitVec.ofNat 64 mid.length =
      tplPtr + BitVec.ofNat 64 (off + mid.length) := by
    rw [BitVec.add_assoc, bv64_add_ofNat]
  rw [ha]
  ac_rfl

/-! ## Loop Invariant, Continuation, and Call Combinators -/

/-- Standard loop spatial invariant for `core::fmt::write` (`sp = C.s0.sp - 112`). -/
def CwLoopMem {σ : Type} (C : CwCtx σ) (st : σ) (pad : BitVec 64) (s : State) : SepProp :=
  ((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
  fmtArgumentsAt C.argsRo C.tplPtr C.argsPtr C.tpl C.args ∗
  C.W st s ∗
  stackFrameAt (C.s0.sp - 112#64) C.stackBytes ∗
  (((C.s0.sp - 112#64) ↦₆₄ pad) ∗ memRegion (C.s0.sp - 104#64) 24 ∗
   cwSavedSlots C.s0.sp C.s0 C.ret_pc)

/-- Loop spatial invariant right before `blr x8` (`fmtArg`), with `formatterAt` built at `sp + 8`. -/
def CwLoopMemFmt {σ : Type} (C : CwCtx σ) (st : σ) (pad : BitVec 64)
    (opts : FmtOptions) (s : State) : SepProp :=
  ((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
  fmtArgumentsAt C.argsRo C.tplPtr C.argsPtr C.tpl C.args ∗
  C.W st s ∗
  stackFrameAt (C.s0.sp - 112#64) C.stackBytes ∗
  (((C.s0.sp - 112#64) ↦₆₄ pad) ∗
   formatterAt (C.s0.sp - 104#64) C.out C.vt opts ∗
   cwSavedSlots C.s0.sp C.s0 C.ret_pc)

theorem cwLoopMem_transport {σ : Type} (C : CwCtx σ) {st : σ} {pad : BitVec 64} {s1 s2 : State}
    (htrans : ∀ (st : σ) (s1 s2 : State), FmtWriteFrame s1 s2 → C.W st s1 ⊢ C.W st s2)
    (hframe : FmtWriteFrame s1 s2) :
    CwLoopMem C st pad s1 ⊢ CwLoopMem C st pad s2 :=
  sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (htrans st s1 s2 hframe)))

/-- Continuation contract at loop header `+0x068` for template offset `pos`, running index `ai`,
    and remaining calls `cs`. -/
def CwLoopCont [CoreFmtWritePl] {σ : Type} (C : CwCtx σ)
    (pos ai : Nat) (cs : List FmtCall) : Prop :=
  ∀ (st : σ) (pad : BitVec 64) (s : State),
    coreMultiLib.CodeLoaded coreFmtMpl s.mem →
    FmtCallbacks C.P C.W C.Step C.Panic C.Oom C.stackBytes C.out C.vt C.writeStrFn cs →
    s.pc = cwPl0.base + 104#64 →
    s.status = .Running →
    s.sp = C.s0.sp - 112#64 →
    s.spAligned = true →
    s.readReg64 (.gpr 19#5) = C.argsPtr →
    s.readReg64 (.gpr 20#5) = C.out →
    s.readReg64 (.gpr 21#5) = C.vt →
    s.readReg64 (.gpr 22#5) = C.tplPtr + BitVec.ofNat 64 pos →
    s.readReg64 (.gpr 24#5) = C.writeStrFn →
    s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 ai →
    s.readReg64 (.gpr 26#5) = 0x60000020#64 →
    s.readReg64 (.gpr 27#5) = C.s0.readReg64 (.gpr 27#5) →
    s.readReg64 (.gpr 28#5) = C.s0.readReg64 (.gpr 28#5) →
    calleeSavedVRegs s = calleeSavedVRegs C.s0 →
    SepWPp C.P C.ret_pc s (CwLoopMem C st pad s) (CwQ C cs st) (CwQp C cs st) (CwOom C cs st)

/-- Reusable `SepWPp` rule for `blr x24` (`write_str`) inside the loop (`+0x08c` and `+0x0e4`). -/
theorem cwCallWriteStr_wpp [CoreFmtWritePl] {σ : Type} (C : CwCtx σ)
    {slicePos len : Nat} {cs : List FmtCall} {st : σ} {pad ret_pc_call : BitVec 64} {sm : State}
    (hcl_sm : coreMultiLib.CodeLoaded coreFmtMpl sm.mem)
    (hle : slicePos + len ≤ C.tpl.length)
    (hcb : FmtCallbacks C.P C.W C.Step C.Panic C.Oom C.stackBytes C.out C.vt C.writeStrFn
      (FmtCall.writeStr (C.tplPtr + BitVec.ofNat 64 slicePos) ((C.tpl.drop slicePos).take len) :: cs))
    (hpc_sm : sm.pc = C.writeStrFn)
    (hrun_sm : sm.status = .Running)
    (hsp_sm : sm.sp = C.s0.sp - 112#64)
    (hsp_al_sm : sm.spAligned = true)
    (hlr_sm : sm.readReg64 Reg.lr = ret_pc_call)
    (hx0_sm : sm.readReg64 .x0 = C.out)
    (hx1_sm : sm.readReg64 .x1 = C.tplPtr + BitVec.ofNat 64 slicePos)
    (hx2_sm : (sm.readReg64 .x2).toNat = ((C.tpl.drop slicePos).take len).length)
    (hnext : ∀ (sf : State) (ok : Bool) (st' : σ),
      sf.pc = ret_pc_call →
      sf.status = .Running →
      sf.sp = C.s0.sp - 112#64 →
      sf.spAligned = true →
      CalleeSavedPreserved sm sf →
      coreMultiLib.CodeLoaded coreFmtMpl sf.mem →
      sf.readReg32 .x0 = (if ok then 0#32 else 1#32) →
      C.Step (FmtCall.writeStr (C.tplPtr + BitVec.ofNat 64 slicePos) ((C.tpl.drop slicePos).take len)) st ok st' →
      SepWPp C.P C.ret_pc sf (CwLoopMem C st' pad sf)
        (CwQ C (FmtCall.writeStr (C.tplPtr + BitVec.ofNat 64 slicePos) ((C.tpl.drop slicePos).take len) :: cs) st)
        (CwQp C (FmtCall.writeStr (C.tplPtr + BitVec.ofNat 64 slicePos) ((C.tpl.drop slicePos).take len) :: cs) st)
        (CwOom C (FmtCall.writeStr (C.tplPtr + BitVec.ofNat 64 slicePos) ((C.tpl.drop slicePos).take len) :: cs) st)) :
    SepWPp C.P C.ret_pc sm (CwLoopMem C st pad sm)
      (CwQ C (FmtCall.writeStr (C.tplPtr + BitVec.ofNat 64 slicePos) ((C.tpl.drop slicePos).take len) :: cs) st)
      (CwQp C (FmtCall.writeStr (C.tplPtr + BitVec.ofNat 64 slicePos) ((C.tpl.drop slicePos).take len) :: cs) st)
      (CwOom C (FmtCall.writeStr (C.tplPtr + BitVec.ofNat 64 slicePos) ((C.tpl.drop slicePos).take len) :: cs) st) := by
  let ptr := C.tplPtr + BitVec.ofNat 64 slicePos
  let bs := (C.tpl.drop slicePos).take len
  let F_call : SepProp :=
    ((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
    fmtArgumentsAt C.argsRo C.tplPtr C.argsPtr C.tpl C.args ∗
    (((C.s0.sp - 112#64) ↦₆₄ pad) ∗ memRegion (C.s0.sp - 104#64) 24 ∗
     cwSavedSlots C.s0.sp C.s0 C.ret_pc)
  refine call_wpp_coreFmt (x := st) (F := F_call) (ret_pc := ret_pc_call)
    (hcb.write_str ptr bs (.head _)) hcl_sm hpc_sm hrun_sm hsp_al_sm hlr_sm
    (fun R' hm => ?_)
    (fun _ _ _ _ hex => by
      dsimp only [fmtWriteStrCallSpec] at hex
      rw [satisfies_pure_sepConj] at hex; exact hex.1)
    (fun sf _ ⟨R', hpan⟩ hm_pan => ?_)
    (fun sf hpcf hrunf hspf hcs_sf hcl_sf => ?_)
    (fun sf R' _ hoom => ?_)
  · have hent_pre :
        CwLoopMem C st pad sm ⊢
          (fmtWriteStrCallSpec C.W C.Step C.Panic C.Oom C.stackBytes C.out ptr bs).pre st sm ∗ F_call := by
      dsimp only [CwLoopMem, fmtWriteStrCallSpec, F_call, fmtArgumentsAt, ptr, bs]
      rw [← hsp_sm]
      conv => rhs; rw [sepConj_assoc]
      refine Entails.pure_right ⟨hx0_sm, hx1_sm, hx2_sm⟩ ?_
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono_left (sepConj_mono_left
          (tpl_dup_slice C.tplPtr C.tpl slicePos len hle)))) ?_
      have hac :
          ((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
            ((((C.tplPtr + BitVec.ofNat 64 slicePos) ↦ᵣ ((C.tpl.drop slicePos).take len) ∗ (C.tplPtr ↦ᵣ C.tpl)) ∗
              (if C.argsPtr.getLsbD 0 then emp else fmtArgEntriesAt C.argsRo C.argsPtr C.args)) ∗
             (C.W st sm ∗
              (stackFrameAt sm.sp C.stackBytes ∗
               ((sm.sp ↦₆₄ pad) ∗ memRegion (C.s0.sp - 104#64) 24 ∗
                cwSavedSlots C.s0.sp C.s0 C.ret_pc)))) =
          (((C.tplPtr + BitVec.ofNat 64 slicePos) ↦ᵣ ((C.tpl.drop slicePos).take len)) ∗
            C.W st sm ∗ stackFrameAt sm.sp C.stackBytes) ∗
          (((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
            ((C.tplPtr ↦ᵣ C.tpl) ∗
             (if C.argsPtr.getLsbD 0 then emp else fmtArgEntriesAt C.argsRo C.argsPtr C.args)) ∗
            ((sm.sp ↦₆₄ pad) ∗ memRegion (C.s0.sp - 104#64) 24 ∗
             cwSavedSlots C.s0.sp C.s0 C.ret_pc)) := by
        ac_rfl
      rw [hac]
      exact Entails.refl _
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hent_pre) hm
  · dsimp only [fmtWriteStrCallSpec] at hpan hm_pan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨FmtCall.writeStr ptr bs, st, fmtReaches_head _ cs st, hpan.1⟩,
      Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm_pan⟩
  · dsimp only [fmtWriteStrCallSpec]
    apply sepWPp_sepExists_left; intro ok
    apply sepWPp_sepExists_left; intro st'
    rw [sepConj_assoc]
    apply sepWPp_pure_left; rintro ⟨hw0f, hstep⟩
    have hsp_sf : sf.sp = C.s0.sp - 112#64 := hspf.trans hsp_sm
    have hsp_al_sf : sf.spAligned = true := by
      unfold State.spAligned at hsp_al_sm ⊢; rwa [hspf]
    have hmem_eq :
        (C.W st' sf ∗ stackFrameAt sm.sp C.stackBytes) ∗ F_call = CwLoopMem C st' pad sf := by
      dsimp only [F_call, CwLoopMem]
      rw [hsp_sm]
      ac_rfl
    rw [hmem_eq]
    exact hnext sf ok st' hpcf hrunf hsp_sf hsp_al_sf hcs_sf hcl_sf hw0f hstep
  · dsimp only [fmtWriteStrCallSpec, CwOom] at hoom ⊢
    rw [satisfies_pure_sepConj] at hoom
    rw [satisfies_pure_sepConj]
    exact ⟨⟨FmtCall.writeStr ptr bs, st, fmtReaches_head _ cs st, hoom.1⟩,
      Satisfies.drop_left hoom.2⟩

/-- Reusable `SepWPp` rule for `blr x8` (`fmtArg`) inside the loop (`+0x05c` and `+0x140`). -/
theorem cwCallFmtArg_wpp [CoreFmtWritePl] {σ : Type} (C : CwCtx σ)
    {idx : Nat} {value fmtFn : BitVec 64} {opts : FmtOptions}
    {cs : List FmtCall} {st : σ} {pad ret_pc_call : BitVec 64} {sm : State}
    (hcl_sm : coreMultiLib.CodeLoaded coreFmtMpl sm.mem)
    (hcb : FmtCallbacks C.P C.W C.Step C.Panic C.Oom C.stackBytes C.out C.vt C.writeStrFn
      (FmtCall.fmtArg idx value fmtFn opts :: cs))
    (hpc_sm : sm.pc = fmtFn)
    (hrun_sm : sm.status = .Running)
    (hsp_sm : sm.sp = C.s0.sp - 112#64)
    (hsp_al_sm : sm.spAligned = true)
    (hlr_sm : sm.readReg64 Reg.lr = ret_pc_call)
    (hx0_sm : sm.readReg64 .x0 = value)
    (hx1_sm : sm.readReg64 .x1 = C.s0.sp - 104#64)
    (hnext : ∀ (sf : State) (ok : Bool) (st' : σ),
      sf.pc = ret_pc_call →
      sf.status = .Running →
      sf.sp = C.s0.sp - 112#64 →
      sf.spAligned = true →
      CalleeSavedPreserved sm sf →
      coreMultiLib.CodeLoaded coreFmtMpl sf.mem →
      sf.readReg32 .x0 &&& 1#32 = (if ok then 0#32 else 1#32) →
      C.Step (FmtCall.fmtArg idx value fmtFn opts) st ok st' →
      SepWPp C.P C.ret_pc sf (CwLoopMem C st' pad sf)
        (CwQ C (FmtCall.fmtArg idx value fmtFn opts :: cs) st)
        (CwQp C (FmtCall.fmtArg idx value fmtFn opts :: cs) st)
        (CwOom C (FmtCall.fmtArg idx value fmtFn opts :: cs) st)) :
    SepWPp C.P C.ret_pc sm (CwLoopMemFmt C st pad opts sm)
      (CwQ C (FmtCall.fmtArg idx value fmtFn opts :: cs) st)
      (CwQp C (FmtCall.fmtArg idx value fmtFn opts :: cs) st)
      (CwOom C (FmtCall.fmtArg idx value fmtFn opts :: cs) st) := by
  let f := C.s0.sp - 104#64
  let F_call : SepProp :=
    ((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
    fmtArgumentsAt C.argsRo C.tplPtr C.argsPtr C.tpl C.args ∗
    (((C.s0.sp - 112#64) ↦₆₄ pad) ∗ cwSavedSlots C.s0.sp C.s0 C.ret_pc)
  refine call_wpp_coreFmt (x := (st, f)) (F := F_call) (ret_pc := ret_pc_call)
    (hcb.fmt_arg idx value fmtFn opts (.head _)) hcl_sm hpc_sm hrun_sm hsp_al_sm hlr_sm
    (fun R' hm => ?_)
    (fun _ _ _ _ hex => by
      dsimp only [fmtArgCallSpec] at hex
      rw [satisfies_pure_sepConj] at hex; exact hex.1)
    (fun sf _ ⟨R', hpan⟩ hm_pan => ?_)
    (fun sf hpcf hrunf hspf hcs_sf hcl_sf => ?_)
    (fun sf R' _ hoom => ?_)
  · have hent_pre :
        CwLoopMemFmt C st pad opts sm ⊢
          (fmtArgCallSpec C.W C.Step C.Panic C.Oom C.stackBytes C.out C.vt idx value fmtFn opts).pre (st, f) sm ∗ F_call := by
      dsimp only [CwLoopMemFmt, fmtArgCallSpec, F_call, f]
      rw [← hsp_sm]
      conv => rhs; rw [sepConj_assoc]
      refine Entails.pure_right ⟨hx0_sm, hx1_sm⟩ ?_
      have hac :
          ((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
            (fmtArgumentsAt C.argsRo C.tplPtr C.argsPtr C.tpl C.args ∗
             (C.W st sm ∗
              (stackFrameAt sm.sp C.stackBytes ∗
               ((sm.sp ↦₆₄ pad) ∗
                (formatterAt (C.s0.sp - 104#64) C.out C.vt opts ∗
                 cwSavedSlots C.s0.sp C.s0 C.ret_pc))))) =
          (formatterAt (C.s0.sp - 104#64) C.out C.vt opts ∗
            C.W st sm ∗ stackFrameAt sm.sp C.stackBytes) ∗
          (((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
            (fmtArgumentsAt C.argsRo C.tplPtr C.argsPtr C.tpl C.args ∗
             ((sm.sp ↦₆₄ pad) ∗ cwSavedSlots C.s0.sp C.s0 C.ret_pc))) := by
        ac_rfl
      rw [hac]
      exact Entails.refl _
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hent_pre) hm
  · dsimp only [fmtArgCallSpec] at hpan hm_pan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨FmtCall.fmtArg idx value fmtFn opts, st, fmtReaches_head _ cs st, hpan.1⟩,
      Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm_pan⟩
  · dsimp only [fmtArgCallSpec]
    apply sepWPp_sepExists_left; intro ok
    apply sepWPp_sepExists_left; intro st'
    rw [sepConj_assoc]
    apply sepWPp_pure_left; rintro ⟨hw0f, hstep⟩
    have hsp_sf : sf.sp = C.s0.sp - 112#64 := hspf.trans hsp_sm
    have hsp_al_sf : sf.spAligned = true := by
      unfold State.spAligned at hsp_al_sm ⊢; rwa [hspf]
    have hmem_eq :
        (memRegion f 24 ∗ C.W st' sf ∗ stackFrameAt sm.sp C.stackBytes) ∗ F_call =
          CwLoopMem C st' pad sf := by
      dsimp only [F_call, CwLoopMem, f]
      rw [hsp_sm]
      ac_rfl
    rw [hmem_eq]
    exact hnext sf ok st' hpcf hrunf hsp_sf hsp_al_sf hcs_sf hcl_sf hw0f hstep
  · dsimp only [fmtArgCallSpec, CwOom] at hoom ⊢
    rw [satisfies_pure_sepConj] at hoom
    rw [satisfies_pure_sepConj]
    exact ⟨⟨FmtCall.fmtArg idx value fmtFn opts, st, fmtReaches_head _ cs st, hoom.1⟩,
      Satisfies.drop_left hoom.2⟩

/-! ## Short-Literal, Long-Literal, and Default-Argument Opcodes -/

section
arm64_proof_prelude
set_option linter.literalFetch false

/-- Short literal step (`0x01 .. 0x7f`, `+0x074 .. +0x098`). -/
theorem cwStep_shortLit [CoreFmtWritePl] {σ : Type} (C : CwCtx σ)
    (hext_blk : ∀ off : Nat, off < 436 →
      C.P.externAt? (coreFmtMpl.base 0 + BitVec.ofNat 64 off) = none)
    {pos ai : Nat} {n : BitVec 8} {rest : List (BitVec 8)} {cs' : List FmtCall}
    {st : σ} {pad : BitVec 64} {s : State}
    (hcl : coreMultiLib.CodeLoaded coreFmtMpl s.mem)
    (hdrop : C.tpl.drop pos = n :: rest)
    (hpos_lt : pos < C.tpl.length)
    (hn_lt : n.toNat < 0x80)
    (hlen_ok : n.toNat ≤ rest.length)
    (hcb : FmtCallbacks C.P C.W C.Step C.Panic C.Oom C.stackBytes C.out C.vt C.writeStrFn
      (FmtCall.writeStr (C.tplPtr + BitVec.ofNat 64 (pos + 1)) (rest.take n.toNat) :: cs'))
    (ih_loop : CwLoopCont C (pos + 1 + n.toNat) ai cs')
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
      (CwQ C (FmtCall.writeStr (C.tplPtr + BitVec.ofNat 64 (pos + 1)) (rest.take n.toNat) :: cs') st)
      (CwQp C (FmtCall.writeStr (C.tplPtr + BitVec.ofNat 64 (pos + 1)) (rest.take n.toNat) :: cs') st)
      (CwOom C (FmtCall.writeStr (C.tplPtr + BitVec.ofNat 64 (pos + 1)) (rest.take n.toNat) :: cs') st) := by
  have hbit7 : (n.zeroExtend 64).getLsbD 7 = false := u8_bit7_false_of_lt_0x80 hn_lt
  have hdrop1 : C.tpl.drop (pos + 1) = rest := by
    rw [← List.drop_drop, hdrop]; rfl
  have hslice_le : (pos + 1) + n.toNat ≤ C.tpl.length := by
    have hdl : (C.tpl.drop pos).length = C.tpl.length - pos := List.length_drop
    rw [hdrop, List.length_cons] at hdl
    omega
  apply sepWPp_seg_coreFmt_pure hext_blk hcl (mid := C.writeStrFn)
  intro s' hcpu_in
  have hpc' : s'.pc = cwPl0.base + 116#64 := hcpu_in.pc_eq.trans hpc
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
  have hsp' : s'.sp = C.s0.sp - 112#64 := hcpu_in.sp_eq.trans hsp
  have hsp_al' : s'.spAligned = true := hcpu_in.spAligned.trans hsp_al
  have hx2' : s'.readReg64 (.gpr 2#5) = C.tplPtr + BitVec.ofNat 64 pos := (hcpu_in.readReg64 _).trans hx2
  have hx8' : s'.readReg64 (.gpr 8#5) = n.zeroExtend 64 := (hcpu_in.readReg64 _).trans hx8
  have hx20' : s'.readReg64 (.gpr 20#5) = C.out := (hcpu_in.readReg64 _).trans hx20
  have hx24' : s'.readReg64 (.gpr 24#5) = C.writeStrFn := (hcpu_in.readReg64 _).trans hx24
  clear hpc
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
    fun sm hcpu_out hcl_sm hnsp hsig htp horc hsym => ?_
  have hframe : FmtWriteFrame s sm := fmtWriteFrame_of_seg hnsp hsig htp horc hsym
  refine SepWPp.weaken_pre (cwLoopMem_transport C hcb.transport hframe) ?_
  have hpc_sm : sm.pc = C.writeStrFn := by rw [hcpu_out.pc_eq]; simp [arm64_norm]
  have hrun_sm : sm.status = .Running := by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun'
  have hsp_sm : sm.sp = C.s0.sp - 112#64 := by rw [hcpu_out.sp_eq]; simp [arm64_norm, hsp']
  have hsp_al_sm : sm.spAligned = true := by
    simp [arm64_norm] at hsp_al'; rw [hcpu_out.spAligned]; simpa [arm64_norm] using hsp_al'
  have hlr_sm : sm.readReg64 Reg.lr = cwPl0.base + 144#64 := by
    rw [hcpu_out.readReg64]; simp [arm64_norm]
  have hx0_sm : sm.readReg64 .x0 = C.out := by
    rw [hcpu_out.readReg64]; simp [arm64_norm]
  have hx1_sm : sm.readReg64 .x1 = C.tplPtr + BitVec.ofNat 64 (pos + 1) := by
    rw [hcpu_out.readReg64]; simp [arm64_norm, BitVec.add_assoc, ← bv64_add_ofNat]
  have hx2_sm : (sm.readReg64 .x2).toNat = ((C.tpl.drop (pos + 1)).take n.toNat).length := by
    have hx2_raw : sm.readReg64 .x2 = BitVec.setWidth 64 n := by
      rw [hcpu_out.readReg64]; simp [arm64_norm]
    rw [hx2_raw, u8_zeroExtend64_eq_ofNat, hdrop1, List.length_take_of_le hlen_ok, BitVec.toNat_ofNat]
    have := n.isLt; omega
  have hx22_sm : sm.readReg64 (.gpr 22#5) = C.tplPtr + BitVec.ofNat 64 (pos + 1) := by
    rw [hcpu_out.readReg64]; simp [arm64_norm, BitVec.add_assoc, ← bv64_add_ofNat]
  have hx23_sm : sm.readReg64 (.gpr 23#5) = n.zeroExtend 64 := by
    rw [hcpu_out.readReg64]; simp [arm64_norm]
  have hx19_sm : sm.readReg64 (.gpr 19#5) = C.argsPtr := by
    rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx19]
  have hx20_sm : sm.readReg64 (.gpr 20#5) = C.out := by
    rw [hcpu_out.readReg64]; simp [arm64_norm, hx20']
  have hx21_sm : sm.readReg64 (.gpr 21#5) = C.vt := by
    rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx21]
  have hx24_sm : sm.readReg64 (.gpr 24#5) = C.writeStrFn := by
    rw [hcpu_out.readReg64]; simp [arm64_norm, hx24']
  have hx25_sm : sm.readReg64 (.gpr 25#5) = BitVec.ofNat 64 ai := by
    rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx25]
  have hx26_sm : sm.readReg64 (.gpr 26#5) = 0x60000020#64 := by
    rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx26]
  have hx27_sm : sm.readReg64 (.gpr 27#5) = C.s0.readReg64 (.gpr 27#5) := by
    rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx27]
  have hx28_sm : sm.readReg64 (.gpr 28#5) = C.s0.readReg64 (.gpr 28#5) := by
    rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx28]
  have hvregs_sm : calleeSavedVRegs sm = calleeSavedVRegs C.s0 := by
    rw [hcpu_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu_in.calleeSavedVRegs] using hvregs
  have hcb_eq : (C.tpl.drop (pos + 1)).take n.toNat = rest.take n.toNat := by rw [hdrop1]
  rw [← hcb_eq] at hcb ⊢
  refine cwCallWriteStr_wpp C hcl_sm hslice_le hcb hpc_sm hrun_sm hsp_sm hsp_al_sm
    hlr_sm hx0_sm hx1_sm hx2_sm fun sf ok st' hpcf hrunf hsp_sf hsp_al_sf hcs_sf hcl_sf hw0f hstep => ?_
  rw [CalleeSavedPreserved.iff_regs] at hcs_sf
  rcases hcs_sf with ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, _, hvrf⟩
  have hbit0_sf : (sf.readReg64 (.gpr 0#5)).getLsbD 0 = !ok :=
    w0_bit0_of_eq_ite (by simpa [arm64_norm] using hw0f)
  cases ok
  ·
    apply sepWPp_seg_coreFmt_pure hext_blk hcl_sf (mid := cwPl0.base + 404#64)
    intro s2 hcpu2
    have hpc2 : s2.pc = cwPl0.base + 144#64 := hcpu2.pc_eq.trans hpcf
    have hrun2 : s2.status = .Running := hcpu2.status_eq.trans hrunf
    have hsp_al2 : s2.spAligned = true := hcpu2.spAligned.trans hsp_al_sf
    have hbit0_2 : (s2.readReg64 (.gpr 0#5)).getLsbD 0 = true := by
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
    intro s2 hcpu2
    have hpc2 : s2.pc = cwPl0.base + 144#64 := hcpu2.pc_eq.trans hpcf
    have hrun2 : s2.status = .Running := hcpu2.status_eq.trans hrunf
    have hsp_al2 : s2.spAligned = true := hcpu2.spAligned.trans hsp_al_sf
    have hbit0_2 : (s2.readReg64 (.gpr 0#5)).getLsbD 0 = false := by
      rw [hcpu2.readReg64]; simpa using hbit0_sf
    have hx22_2 : s2.readReg64 (.gpr 22#5) = C.tplPtr + BitVec.ofNat 64 (pos + 1) := by
      rw [hcpu2.readReg64, h22f, hx22_sm]
    have hx23_2 : s2.readReg64 (.gpr 23#5) = n.zeroExtend 64 := by
      rw [hcpu2.readReg64, h23f, hx23_sm]
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun2)
      fun sm2 hcpu2_out hcl_sm2 hnsp2 hsig2 htp2 horc2 hsym2 => ?_
    have hframe2 : FmtWriteFrame sf sm2 := fmtWriteFrame_of_seg hnsp2 hsig2 htp2 horc2 hsym2
    refine SepWPp.weaken_pre (cwLoopMem_transport C hcb.transport hframe2) ?_
    refine ih_loop st' pad sm2 hcl_sm2 (fmtCallbacks_cons_inv hcb)
      (by rw [hcpu2_out.pc_eq]; simp [arm64_norm])
      (by rw [hcpu2_out.status_eq]; simpa [arm64_norm] using hrun2)
      (by rw [hcpu2_out.sp_eq]; simp [arm64_norm, hcpu2.sp_eq, hsp_sf])
      (by simp [arm64_norm] at hsp_al2; rw [hcpu2_out.spAligned]; simpa [arm64_norm] using hsp_al2)
      (by rw [hcpu2_out.readReg64]; simp [arm64_norm, hcpu2.readReg64, h19f, hx19_sm])
      (by rw [hcpu2_out.readReg64]; simp [arm64_norm, hcpu2.readReg64, h20f, hx20_sm])
      (by rw [hcpu2_out.readReg64]; simp [arm64_norm, hcpu2.readReg64, h21f, hx21_sm])
      (by
        have hx22_out : sm2.readReg64 (.gpr 22#5) = C.tplPtr + BitVec.ofNat 64 (pos + 1) + BitVec.setWidth 64 n := by
          rw [hcpu2_out.readReg64]; simp [arm64_norm]
        rw [hx22_out, u8_zeroExtend64_eq_ofNat, BitVec.add_assoc, bv64_add_ofNat])
      (by rw [hcpu2_out.readReg64]; simp [arm64_norm, hcpu2.readReg64, h24f, hx24_sm])
      (by rw [hcpu2_out.readReg64]; simp [arm64_norm, hcpu2.readReg64, h25f, hx25_sm])
      (by rw [hcpu2_out.readReg64]; simp [arm64_norm, hcpu2.readReg64, h26f, hx26_sm])
      (by rw [hcpu2_out.readReg64]; simp [arm64_norm, hcpu2.readReg64, h27f, hx27_sm])
      (by rw [hcpu2_out.readReg64]; simp [arm64_norm, hcpu2.readReg64, h28f, hx28_sm])
      (by rw [hcpu2_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu2.calleeSavedVRegs, hvrf] using hvregs_sm)

/-- Long literal step (`0x80`, `+0x074 .. +0x0a0`, `+0x0d0 .. +0x0f0`). -/
theorem cwStep_longLit [CoreFmtWritePl] {σ : Type} (C : CwCtx σ)
    (hext_blk : ∀ off : Nat, off < 436 →
      C.P.externAt? (coreFmtMpl.base 0 + BitVec.ofNat 64 off) = none)
    {pos ai : Nat} {b0 b1 : BitVec 8} {r : List (BitVec 8)} {cs' : List FmtCall}
    {st : σ} {pad : BitVec 64} {s : State}
    (hcl : coreMultiLib.CodeLoaded coreFmtMpl s.mem)
    (hdrop : C.tpl.drop pos = 0x80#8 :: b0 :: b1 :: r)
    (hpos_lt : pos < C.tpl.length)
    (hlen_ok : leBytesNat [b0, b1] ≤ r.length)
    (hcb : FmtCallbacks C.P C.W C.Step C.Panic C.Oom C.stackBytes C.out C.vt C.writeStrFn
      (FmtCall.writeStr (C.tplPtr + BitVec.ofNat 64 (pos + 3)) (r.take (leBytesNat [b0, b1])) :: cs'))
    (ih_loop : CwLoopCont C (pos + 3 + leBytesNat [b0, b1]) ai cs')
    (hpc : s.pc = cwPl0.base + 116#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = C.s0.sp - 112#64)
    (hsp_al : s.spAligned = true)
    (hx2 : s.readReg64 (.gpr 2#5) = C.tplPtr + BitVec.ofNat 64 pos)
    (hx8 : s.readReg64 (.gpr 8#5) = (0x80#8).zeroExtend 64)
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
      (CwQ C (FmtCall.writeStr (C.tplPtr + BitVec.ofNat 64 (pos + 3)) (r.take (leBytesNat [b0, b1])) :: cs') st)
      (CwQp C (FmtCall.writeStr (C.tplPtr + BitVec.ofNat 64 (pos + 3)) (r.take (leBytesNat [b0, b1])) :: cs') st)
      (CwOom C (FmtCall.writeStr (C.tplPtr + BitVec.ofNat 64 (pos + 3)) (r.take (leBytesNat [b0, b1])) :: cs') st) := by
  let len := leBytesNat [b0, b1]
  have hlen_lt : len < 65536 := leBytesNat_pair_lt b0 b1
  have hdrop1 : C.tpl.drop (pos + 1) = [b0, b1] ++ r := by
    rw [← List.drop_drop, hdrop]; rfl
  have hdrop3 : C.tpl.drop (pos + 3) = r := by
    have hp3 : pos + 3 = pos + (1 + 2) := by omega
    rw [hp3, ← List.drop_drop, hdrop]; rfl
  have hpos1_le : pos + 1 ≤ C.tpl.length := by omega
  have hslice_le : (pos + 3) + len ≤ C.tpl.length := by
    have hdl : (C.tpl.drop pos).length = C.tpl.length - pos := List.length_drop
    rw [hdrop, List.length_cons, List.length_cons, List.length_cons] at hdl
    omega
  have htpl_u16 : (C.tplPtr ↦ᵣ C.tpl) =
      ((C.tplPtr + BitVec.ofNat 64 pos + 1#64) ↦₁₆ᵣ BitVec.ofNat 16 len) ∗
      ((C.tplPtr ↦ᵣ C.tpl.take (pos + 1)) ∗
       ((C.tplPtr + BitVec.ofNat 64 (pos + 1 + 2)) ↦ᵣ r)) := by
    have hf := tpl_focus_sublist C.tplPtr C.tpl (pos + 1) [b0, b1] r hdrop1 hpos1_le
    simp only [List.length_cons, List.length_nil] at hf
    rw [hf, pointsToBytesRO_pair_eq_le16]
    have ha : C.tplPtr + BitVec.ofNat 64 (pos + 1) = C.tplPtr + BitVec.ofNat 64 pos + 1#64 := by
      rw [BitVec.add_assoc, ← bv64_add_ofNat]
    rw [ha]
  apply sepWPp_seg_coreFmt_pure hext_blk hcl (mid := C.writeStrFn)
  intro s' hcpu_in
  have hpc' : s'.pc = cwPl0.base + 116#64 := hcpu_in.pc_eq.trans hpc
  have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
  have hsp' : s'.sp = C.s0.sp - 112#64 := hcpu_in.sp_eq.trans hsp
  have hsp_al' : s'.spAligned = true := hcpu_in.spAligned.trans hsp_al
  have hx2' : s'.readReg64 (.gpr 2#5) = C.tplPtr + BitVec.ofNat 64 pos := (hcpu_in.readReg64 _).trans hx2
  have hx8' : s'.readReg64 (.gpr 8#5) = 0x80#64 := (hcpu_in.readReg64 _).trans hx8
  have hx20' : s'.readReg64 (.gpr 20#5) = C.out := (hcpu_in.readReg64 _).trans hx20
  have hx24' : s'.readReg64 (.gpr 24#5) = C.writeStrFn := (hcpu_in.readReg64 _).trans hx24
  wp_conv_pre =>
    dsimp only [CwLoopMem, fmtArgumentsAt]
    rw [htpl_u16]
    simp only [sepConj_assoc]
  clear hpc
  wp_sym_steps
  refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
    fun sm hcpu_out hcl_sm hnsp hsig htp horc hsym => ?_
  have hmem_fold :
      (((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
       (((C.tplPtr + BitVec.ofNat 64 pos + 1#64) ↦₁₆ᵣ BitVec.ofNat 16 len) ∗
        ((C.tplPtr ↦ᵣ C.tpl.take (pos + 1)) ∗
         (((C.tplPtr + BitVec.ofNat 64 (pos + 1 + 2)) ↦ᵣ r) ∗
          ((if C.argsPtr.getLsbD 0 then emp else fmtArgEntriesAt C.argsRo C.argsPtr C.args) ∗
           (C.W st s ∗
            (stackFrameAt (C.s0.sp - 112#64) C.stackBytes ∗
             (((C.s0.sp - 112#64) ↦₆₄ pad) ∗
              (memRegion (C.s0.sp - 104#64) 24 ∗ cwSavedSlots C.s0.sp C.s0 C.ret_pc))))))))) =
      CwLoopMem C st pad s := by
    dsimp only [CwLoopMem, fmtArgumentsAt]
    rw [htpl_u16]
    ac_rfl
  rw [hmem_fold]
  have hframe : FmtWriteFrame s sm := fmtWriteFrame_of_seg hnsp hsig htp horc hsym
  refine SepWPp.weaken_pre (cwLoopMem_transport C hcb.transport hframe) ?_
  have hpc_sm : sm.pc = C.writeStrFn := by rw [hcpu_out.pc_eq]; simp [arm64_norm]
  have hrun_sm : sm.status = .Running := by rw [hcpu_out.status_eq]; simpa [arm64_norm] using hrun'
  have hsp_sm : sm.sp = C.s0.sp - 112#64 := by rw [hcpu_out.sp_eq]; simp [arm64_norm, hsp']
  have hsp_al_sm : sm.spAligned = true := by
    simp [arm64_norm] at hsp_al'; rw [hcpu_out.spAligned]; simpa [arm64_norm] using hsp_al'
  have hlr_sm : sm.readReg64 Reg.lr = cwPl0.base + 232#64 := by
    rw [hcpu_out.readReg64]; simp [arm64_norm]
  have hx0_sm : sm.readReg64 .x0 = C.out := by
    rw [hcpu_out.readReg64]; simp [arm64_norm]
  have hx1_sm : sm.readReg64 .x1 = C.tplPtr + BitVec.ofNat 64 (pos + 3) := by
    rw [hcpu_out.readReg64]; simp [arm64_norm, BitVec.add_assoc, ← bv64_add_ofNat]
  have hx2_sm : (sm.readReg64 .x2).toNat = ((C.tpl.drop (pos + 3)).take len).length := by
    rw [hcpu_out.readReg64, hdrop3, List.length_take_of_le hlen_ok]
    simp [arm64_norm, u16_ofNat_zeroExtend64 hlen_lt]
    omega
  have hx22_sm : sm.readReg64 (.gpr 22#5) = BitVec.ofNat 64 len := by
    rw [hcpu_out.readReg64]; simp [arm64_norm, u16_ofNat_zeroExtend64 hlen_lt]
  have hx23_sm : sm.readReg64 (.gpr 23#5) = C.tplPtr + BitVec.ofNat 64 (pos + 3) := by
    rw [hcpu_out.readReg64]; simp [arm64_norm, BitVec.add_assoc, ← bv64_add_ofNat]
  have hx19_sm : sm.readReg64 (.gpr 19#5) = C.argsPtr := by
    rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx19]
  have hx20_sm : sm.readReg64 (.gpr 20#5) = C.out := by
    rw [hcpu_out.readReg64]; simp [arm64_norm, hx20']
  have hx21_sm : sm.readReg64 (.gpr 21#5) = C.vt := by
    rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx21]
  have hx24_sm : sm.readReg64 (.gpr 24#5) = C.writeStrFn := by
    rw [hcpu_out.readReg64]; simp [arm64_norm, hx24']
  have hx25_sm : sm.readReg64 (.gpr 25#5) = BitVec.ofNat 64 ai := by
    rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx25]
  have hx26_sm : sm.readReg64 (.gpr 26#5) = 0x60000020#64 := by
    rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx26]
  have hx27_sm : sm.readReg64 (.gpr 27#5) = C.s0.readReg64 (.gpr 27#5) := by
    rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx27]
  have hx28_sm : sm.readReg64 (.gpr 28#5) = C.s0.readReg64 (.gpr 28#5) := by
    rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx28]
  have hvregs_sm : calleeSavedVRegs sm = calleeSavedVRegs C.s0 := by
    rw [hcpu_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu_in.calleeSavedVRegs] using hvregs
  have hcb_eq : (C.tpl.drop (pos + 3)).take len = r.take len := by rw [hdrop3]
  rw [← hcb_eq] at hcb ⊢
  refine cwCallWriteStr_wpp C hcl_sm hslice_le hcb hpc_sm hrun_sm hsp_sm hsp_al_sm
    hlr_sm hx0_sm hx1_sm hx2_sm fun sf ok st' hpcf hrunf hsp_sf hsp_al_sf hcs_sf hcl_sf hw0f hstep => ?_
  rw [CalleeSavedPreserved.iff_regs] at hcs_sf
  rcases hcs_sf with ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, _, hvrf⟩
  have hbit0_sf : (sf.readReg64 (.gpr 0#5)).getLsbD 0 = !ok :=
    w0_bit0_of_eq_ite (by simpa [arm64_norm] using hw0f)
  cases ok
  · apply sepWPp_seg_coreFmt_pure hext_blk hcl_sf (mid := cwPl0.base + 404#64)
    intro s2 hcpu2
    have hpc2 : s2.pc = cwPl0.base + 232#64 := hcpu2.pc_eq.trans hpcf
    have hrun2 : s2.status = .Running := hcpu2.status_eq.trans hrunf
    have hsp_al2 : s2.spAligned = true := hcpu2.spAligned.trans hsp_al_sf
    have hbit0_2 : (s2.readReg64 (.gpr 0#5)).getLsbD 0 = true := by
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
  · apply cw_step_ok_conseq C hstep
    apply sepWPp_seg_coreFmt_pure hext_blk hcl_sf (mid := cwPl0.base + 104#64)
    intro s2 hcpu2
    have hpc2 : s2.pc = cwPl0.base + 232#64 := hcpu2.pc_eq.trans hpcf
    have hrun2 : s2.status = .Running := hcpu2.status_eq.trans hrunf
    have hsp_al2 : s2.spAligned = true := hcpu2.spAligned.trans hsp_al_sf
    have hbit0_2 : (s2.readReg64 (.gpr 0#5)).getLsbD 0 = false := by
      rw [hcpu2.readReg64]; simpa using hbit0_sf
    have hx22_2 : s2.readReg64 (.gpr 22#5) = BitVec.ofNat 64 len := by
      rw [hcpu2.readReg64, h22f, hx22_sm]
    have hx23_2 : s2.readReg64 (.gpr 23#5) = C.tplPtr + BitVec.ofNat 64 (pos + 3) := by
      rw [hcpu2.readReg64, h23f, hx23_sm]
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun2)
      fun sm2 hcpu2_out hcl_sm2 hnsp2 hsig2 htp2 horc2 hsym2 => ?_
    have hframe2 : FmtWriteFrame sf sm2 := fmtWriteFrame_of_seg hnsp2 hsig2 htp2 horc2 hsym2
    refine SepWPp.weaken_pre (cwLoopMem_transport C hcb.transport hframe2) ?_
    refine ih_loop st' pad sm2 hcl_sm2 (fmtCallbacks_cons_inv hcb)
      (by rw [hcpu2_out.pc_eq]; simp [arm64_norm])
      (by rw [hcpu2_out.status_eq]; simpa [arm64_norm] using hrun2)
      (by rw [hcpu2_out.sp_eq]; simp [arm64_norm, hcpu2.sp_eq, hsp_sf])
      (by simp [arm64_norm] at hsp_al2; rw [hcpu2_out.spAligned]; simpa [arm64_norm] using hsp_al2)
      (by rw [hcpu2_out.readReg64]; simp [arm64_norm, hcpu2.readReg64, h19f, hx19_sm])
      (by rw [hcpu2_out.readReg64]; simp [arm64_norm, hcpu2.readReg64, h20f, hx20_sm])
      (by rw [hcpu2_out.readReg64]; simp [arm64_norm, hcpu2.readReg64, h21f, hx21_sm])
      (by rw [hcpu2_out.readReg64]; simp [arm64_norm, BitVec.add_assoc, bv64_add_ofNat])
      (by rw [hcpu2_out.readReg64]; simp [arm64_norm, hcpu2.readReg64, h24f, hx24_sm])
      (by rw [hcpu2_out.readReg64]; simp [arm64_norm, hcpu2.readReg64, h25f, hx25_sm])
      (by rw [hcpu2_out.readReg64]; simp [arm64_norm, hcpu2.readReg64, h26f, hx26_sm])
      (by rw [hcpu2_out.readReg64]; simp [arm64_norm, hcpu2.readReg64, h27f, hx27_sm])
      (by rw [hcpu2_out.readReg64]; simp [arm64_norm, hcpu2.readReg64, h28f, hx28_sm])
      (by rw [hcpu2_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu2.calleeSavedVRegs, hvrf] using hvregs_sm)

private theorem cwStep_defaultArg_preCall [CoreFmtWritePl] {σ : Type} (C : CwCtx σ)
    (hext_blk : ∀ off : Nat, off < 436 →
      C.P.externAt? (coreFmtMpl.base 0 + BitVec.ofNat 64 off) = none)
    {pos ai : Nat} {value fmtFn : BitVec 64} {cs : List FmtCall}
    {st : σ} {pad : BitVec 64} {s : State}
    (hcl : coreMultiLib.CodeLoaded coreFmtMpl s.mem)
    (heven : C.argsPtr.getLsbD 0 = false)
    (harg : C.args[ai]? = some (value, fmtFn))
    (htrans : ∀ (st : σ) (s1 s2 : State), FmtWriteFrame s1 s2 → C.W st s1 ⊢ C.W st s2)
    (hpc : s.pc = cwPl0.base + 116#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = C.s0.sp - 112#64)
    (hsp_al : s.spAligned = true)
    (hx2 : s.readReg64 (.gpr 2#5) = C.tplPtr + BitVec.ofNat 64 pos)
    (hx8 : s.readReg64 (.gpr 8#5) = (0xc0#8).zeroExtend 64)
    (hx19 : s.readReg64 (.gpr 19#5) = C.argsPtr)
    (hx20 : s.readReg64 (.gpr 20#5) = C.out)
    (hx21 : s.readReg64 (.gpr 21#5) = C.vt)
    (hx24 : s.readReg64 (.gpr 24#5) = C.writeStrFn)
    (hx25 : s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 ai)
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
      sm.readReg64 Reg.lr = cwPl0.base + 96#64 →
      sm.readReg64 .x0 = value →
      sm.readReg64 .x1 = C.s0.sp - 104#64 →
      sm.readReg64 (.gpr 19#5) = C.argsPtr →
      sm.readReg64 (.gpr 20#5) = C.out →
      sm.readReg64 (.gpr 21#5) = C.vt →
      sm.readReg64 (.gpr 22#5) = C.tplPtr + BitVec.ofNat 64 (pos + 1) →
      sm.readReg64 (.gpr 24#5) = C.writeStrFn →
      sm.readReg64 (.gpr 25#5) = BitVec.ofNat 64 ai →
      sm.readReg64 (.gpr 26#5) = 0x60000020#64 →
      sm.readReg64 (.gpr 27#5) = C.s0.readReg64 (.gpr 27#5) →
      sm.readReg64 (.gpr 28#5) = C.s0.readReg64 (.gpr 28#5) →
      calleeSavedVRegs sm = calleeSavedVRegs C.s0 →
      SepWPp C.P C.ret_pc sm (CwLoopMemFmt C st pad defaultFmtOptions sm)
        (CwQ C cs st) (CwQp C cs st) (CwOom C cs st)) :
    SepWPp C.P C.ret_pc s (CwLoopMem C st pad s)
      (CwQ C cs st) (CwQp C cs st) (CwOom C cs st) := by
  have hunpack : CwLoopMem C st pad s =
      (∃∗ w0, ∃∗ w1, ∃∗ w2,
        ((C.s0.sp - 104#64) ↦₆₄ w0) ∗
        ((C.s0.sp - 104#64 + 8#64) ↦₆₄ w1) ∗
        ((C.s0.sp - 104#64 + 16#64) ↦₆₄ w2)) ∗
      (((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
       fmtArgumentsAt C.argsRo C.tplPtr C.argsPtr C.tpl C.args ∗
       C.W st s ∗
       stackFrameAt (C.s0.sp - 112#64) C.stackBytes ∗
       (((C.s0.sp - 112#64) ↦₆₄ pad) ∗ cwSavedSlots C.s0.sp C.s0 C.ret_pc)) := by
    dsimp only [CwLoopMem]
    rw [memRegion24_eq_exists_triple64 (C.s0.sp - 104#64)]
    ac_rfl
  rw [hunpack]
  apply sepWPp_sepExists_left; intro w0
  apply sepWPp_sepExists_left; intro w1
  apply sepWPp_sepExists_left; intro w2
  have hfocus := fmtArgEntriesAt_focus C.argsRo C.argsPtr C.args harg
  have hshl : C.argsPtr + (BitVec.ofNat 64 ai) <<< 4 = C.argsPtr + BitVec.ofNat 64 (16 * ai) := by
    rw [bv64_shl4_eq_mul16]
  have hf_sp1 : C.s0.sp - 112#64 + 16#64 = C.s0.sp - 104#64 + 8#64 := by bv_omega
  have hf_sp2 : C.s0.sp - 112#64 + 24#64 = C.s0.sp - 104#64 + 16#64 := by bv_omega
  have hf_sp0 : C.s0.sp - 112#64 + 8#64 = C.s0.sp - 104#64 := by bv_omega
  cases hro : C.argsRo
  ·
    apply sepWPp_seg_coreFmt_pure hext_blk hcl (mid := fmtFn)
    intro s' hcpu_in
    have hpc' : s'.pc = cwPl0.base + 116#64 := hcpu_in.pc_eq.trans hpc
    have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
    have hsp' : s'.sp = C.s0.sp - 112#64 := hcpu_in.sp_eq.trans hsp
    have hsp_al' : s'.spAligned = true := hcpu_in.spAligned.trans hsp_al
    have hx2' : s'.readReg64 (.gpr 2#5) = C.tplPtr + BitVec.ofNat 64 pos := (hcpu_in.readReg64 _).trans hx2
    have hx8' : s'.readReg64 (.gpr 8#5) = 0xc0#64 := (hcpu_in.readReg64 _).trans hx8
    have hx19' : s'.readReg64 (.gpr 19#5) = C.argsPtr := (hcpu_in.readReg64 _).trans hx19
    have hx20' : s'.readReg64 (.gpr 20#5) = C.out := (hcpu_in.readReg64 _).trans hx20
    have hx21' : s'.readReg64 (.gpr 21#5) = C.vt := (hcpu_in.readReg64 _).trans hx21
    have hx25' : s'.readReg64 (.gpr 25#5) = BitVec.ofNat 64 ai := (hcpu_in.readReg64 _).trans hx25
    have hx26' : s'.readReg64 (.gpr 26#5) = 0x60000020#64 := (hcpu_in.readReg64 _).trans hx26
    wp_conv_pre =>
      dsimp only [fmtArgumentsAt]
      simp only [heven, Bool.false_eq_true, ↓reduceIte, hro]
      rw [show fmtArgEntriesAt false C.argsPtr C.args =
          fmtArgElemAt false (C.argsPtr + (BitVec.ofNat 64 ai) <<< 4) value fmtFn ∗
          fmtArgEntriesRest false C.argsPtr C.args ai by
            rw [hshl]; simpa [hro] using hfocus]
      dsimp only [fmtArgElemAt]
      simp only [Bool.false_eq_true, ↓reduceIte, ← hf_sp0, ← hf_sp1, ← hf_sp2, sepConj_assoc]
    clear hpc
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
      fun sm hcpu_out hcl_sm hnsp hsig htp horc hsym => ?_
    have hframe : FmtWriteFrame s sm := fmtWriteFrame_of_seg hnsp hsig htp horc hsym
    have hent_post :
        (((C.s0.sp - 112#64 + 8#64) ↦₆₄ C.out) ∗
         (((C.s0.sp - 112#64 + 8#64 + 8#64) ↦₆₄ C.vt) ∗
          (((C.s0.sp - 112#64 + 8#64 + 16#64) ↦₆₄ 0x60000020#64) ∗
           (((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
            ((C.tplPtr ↦ᵣ C.tpl) ∗
             (((C.argsPtr + (BitVec.ofNat 64 ai) <<< 4) ↦₆₄ value) ∗
              (((C.argsPtr + (BitVec.ofNat 64 ai) <<< 4 + 8#64) ↦₆₄ fmtFn) ∗
               (fmtArgEntriesRest false C.argsPtr C.args ai ∗
                (C.W st s ∗
                 (stackFrameAt (C.s0.sp - 112#64) C.stackBytes ∗
                  (((C.s0.sp - 112#64) ↦₆₄ pad) ∗ cwSavedSlots C.s0.sp C.s0 C.ret_pc))))))))))) ⊢
        CwLoopMemFmt C st pad defaultFmtOptions sm := by
      dsimp only [CwLoopMemFmt, fmtArgumentsAt]
      simp only [heven, Bool.false_eq_true, ↓reduceIte, hro, hf_sp0, hshl]
      rw [formatterAt_default_eq_stp (C.s0.sp - 104#64) C.out C.vt]
      have harg_back : fmtArgEntriesAt false C.argsPtr C.args =
          ((C.argsPtr + BitVec.ofNat 64 (16 * ai)) ↦₆₄ value) ∗
          ((C.argsPtr + BitVec.ofNat 64 (16 * ai) + 8#64) ↦₆₄ fmtFn) ∗
          fmtArgEntriesRest false C.argsPtr C.args ai := by
        simpa [hro, fmtArgElemAt] using hfocus
      rw [harg_back]
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left (htrans st s sm hframe)))))))))) ?_
      have hac :
          ((C.s0.sp - 104#64) ↦₆₄ C.out) ∗
            (((C.s0.sp - 104#64 + 8#64) ↦₆₄ C.vt) ∗
             (((C.s0.sp - 104#64 + 16#64) ↦₆₄ 0x60000020#64) ∗
              (((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
               ((C.tplPtr ↦ᵣ C.tpl) ∗
                (((C.argsPtr + BitVec.ofNat 64 (16 * ai)) ↦₆₄ value) ∗
                 (((C.argsPtr + BitVec.ofNat 64 (16 * ai) + 8#64) ↦₆₄ fmtFn) ∗
                  (fmtArgEntriesRest false C.argsPtr C.args ai ∗
                   (C.W st sm ∗
                    (stackFrameAt (C.s0.sp - 112#64) C.stackBytes ∗
                     (((C.s0.sp - 112#64) ↦₆₄ pad) ∗ cwSavedSlots C.s0.sp C.s0 C.ret_pc)))))))))) =
          ((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
            (((C.tplPtr ↦ᵣ C.tpl) ∗
              (((C.argsPtr + BitVec.ofNat 64 (16 * ai)) ↦₆₄ value) ∗
               ((C.argsPtr + BitVec.ofNat 64 (16 * ai) + 8#64) ↦₆₄ fmtFn) ∗
               fmtArgEntriesRest false C.argsPtr C.args ai)) ∗
             (C.W st sm ∗
              (stackFrameAt (C.s0.sp - 112#64) C.stackBytes ∗
               (((C.s0.sp - 112#64) ↦₆₄ pad) ∗
                ((((C.s0.sp - 104#64) ↦₆₄ C.out) ∗
                  ((C.s0.sp - 104#64 + 8#64) ↦₆₄ C.vt) ∗
                  ((C.s0.sp - 104#64 + 16#64) ↦₆₄ 0x60000020#64)) ∗
                 cwSavedSlots C.s0.sp C.s0 C.ret_pc))))) := by
        ac_rfl
      rw [hac]
      exact Entails.refl _
    refine SepWPp.weaken_pre hent_post ?_
    exact hcont sm hcl_sm
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
      (by rw [hcpu_out.readReg64]; simp [arm64_norm, BitVec.add_assoc, ← bv64_add_ofNat])
      (by rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx24])
      (by rw [hcpu_out.readReg64]; simp [arm64_norm, hx25'])
      (by rw [hcpu_out.readReg64]; simp [arm64_norm, hx26'])
      (by rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx27])
      (by rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx28])
      (by rw [hcpu_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu_in.calleeSavedVRegs] using hvregs)
  ·
    apply sepWPp_seg_coreFmt_pure hext_blk hcl (mid := fmtFn)
    intro s' hcpu_in
    have hpc' : s'.pc = cwPl0.base + 116#64 := hcpu_in.pc_eq.trans hpc
    have hrun' : s'.status = .Running := hcpu_in.status_eq.trans hrun
    have hsp' : s'.sp = C.s0.sp - 112#64 := hcpu_in.sp_eq.trans hsp
    have hsp_al' : s'.spAligned = true := hcpu_in.spAligned.trans hsp_al
    have hx2' : s'.readReg64 (.gpr 2#5) = C.tplPtr + BitVec.ofNat 64 pos := (hcpu_in.readReg64 _).trans hx2
    have hx8' : s'.readReg64 (.gpr 8#5) = 0xc0#64 := (hcpu_in.readReg64 _).trans hx8
    have hx19' : s'.readReg64 (.gpr 19#5) = C.argsPtr := (hcpu_in.readReg64 _).trans hx19
    have hx20' : s'.readReg64 (.gpr 20#5) = C.out := (hcpu_in.readReg64 _).trans hx20
    have hx21' : s'.readReg64 (.gpr 21#5) = C.vt := (hcpu_in.readReg64 _).trans hx21
    have hx25' : s'.readReg64 (.gpr 25#5) = BitVec.ofNat 64 ai := (hcpu_in.readReg64 _).trans hx25
    have hx26' : s'.readReg64 (.gpr 26#5) = 0x60000020#64 := (hcpu_in.readReg64 _).trans hx26
    wp_conv_pre =>
      dsimp only [fmtArgumentsAt]
      simp only [heven, Bool.false_eq_true, ↓reduceIte, hro]
      rw [show fmtArgEntriesAt true C.argsPtr C.args =
          fmtArgElemAt true (C.argsPtr + (BitVec.ofNat 64 ai) <<< 4) value fmtFn ∗
          fmtArgEntriesRest true C.argsPtr C.args ai by
            rw [hshl]; simpa [hro] using hfocus]
      dsimp only [fmtArgElemAt]
      simp only [↓reduceIte, ← hf_sp0, ← hf_sp1, ← hf_sp2, sepConj_assoc]
    clear hpc
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun')
      fun sm hcpu_out hcl_sm hnsp hsig htp horc hsym => ?_
    have hframe : FmtWriteFrame s sm := fmtWriteFrame_of_seg hnsp hsig htp horc hsym
    have hent_post :
        (((C.s0.sp - 112#64 + 8#64) ↦₆₄ C.out) ∗
         (((C.s0.sp - 112#64 + 8#64 + 8#64) ↦₆₄ C.vt) ∗
          (((C.s0.sp - 112#64 + 8#64 + 16#64) ↦₆₄ 0x60000020#64) ∗
           (((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
            ((C.tplPtr ↦ᵣ C.tpl) ∗
             (((C.argsPtr + (BitVec.ofNat 64 ai) <<< 4) ↦₆₄ᵣ value) ∗
              (((C.argsPtr + (BitVec.ofNat 64 ai) <<< 4 + 8#64) ↦₆₄ᵣ fmtFn) ∗
               (fmtArgEntriesRest true C.argsPtr C.args ai ∗
                (C.W st s ∗
                 (stackFrameAt (C.s0.sp - 112#64) C.stackBytes ∗
                  (((C.s0.sp - 112#64) ↦₆₄ pad) ∗ cwSavedSlots C.s0.sp C.s0 C.ret_pc))))))))))) ⊢
        CwLoopMemFmt C st pad defaultFmtOptions sm := by
      dsimp only [CwLoopMemFmt, fmtArgumentsAt]
      simp only [heven, Bool.false_eq_true, ↓reduceIte, hro, hf_sp0, hshl]
      rw [formatterAt_default_eq_stp (C.s0.sp - 104#64) C.out C.vt]
      have harg_back : fmtArgEntriesAt true C.argsPtr C.args =
          ((C.argsPtr + BitVec.ofNat 64 (16 * ai)) ↦₆₄ᵣ value) ∗
          ((C.argsPtr + BitVec.ofNat 64 (16 * ai) + 8#64) ↦₆₄ᵣ fmtFn) ∗
          fmtArgEntriesRest true C.argsPtr C.args ai := by
        simpa [hro, fmtArgElemAt] using hfocus
      rw [harg_back]
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left (htrans st s sm hframe)))))))))) ?_
      have hac :
          ((C.s0.sp - 104#64) ↦₆₄ C.out) ∗
            (((C.s0.sp - 104#64 + 8#64) ↦₆₄ C.vt) ∗
             (((C.s0.sp - 104#64 + 16#64) ↦₆₄ 0x60000020#64) ∗
              (((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
               ((C.tplPtr ↦ᵣ C.tpl) ∗
                (((C.argsPtr + BitVec.ofNat 64 (16 * ai)) ↦₆₄ᵣ value) ∗
                 (((C.argsPtr + BitVec.ofNat 64 (16 * ai) + 8#64) ↦₆₄ᵣ fmtFn) ∗
                  (fmtArgEntriesRest true C.argsPtr C.args ai ∗
                   (C.W st sm ∗
                    (stackFrameAt (C.s0.sp - 112#64) C.stackBytes ∗
                     (((C.s0.sp - 112#64) ↦₆₄ pad) ∗ cwSavedSlots C.s0.sp C.s0 C.ret_pc)))))))))) =
          ((C.vt + 0x18#64) ↦₆₄ᵣ C.writeStrFn) ∗
            (((C.tplPtr ↦ᵣ C.tpl) ∗
              (((C.argsPtr + BitVec.ofNat 64 (16 * ai)) ↦₆₄ᵣ value) ∗
               ((C.argsPtr + BitVec.ofNat 64 (16 * ai) + 8#64) ↦₆₄ᵣ fmtFn) ∗
               fmtArgEntriesRest true C.argsPtr C.args ai)) ∗
             (C.W st sm ∗
              (stackFrameAt (C.s0.sp - 112#64) C.stackBytes ∗
               (((C.s0.sp - 112#64) ↦₆₄ pad) ∗
                ((((C.s0.sp - 104#64) ↦₆₄ C.out) ∗
                  ((C.s0.sp - 104#64 + 8#64) ↦₆₄ C.vt) ∗
                  ((C.s0.sp - 104#64 + 16#64) ↦₆₄ 0x60000020#64)) ∗
                 cwSavedSlots C.s0.sp C.s0 C.ret_pc))))) := by
        ac_rfl
      rw [hac]
      exact Entails.refl _
    refine SepWPp.weaken_pre hent_post ?_
    exact hcont sm hcl_sm
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
      (by rw [hcpu_out.readReg64]; simp [arm64_norm, BitVec.add_assoc, ← bv64_add_ofNat])
      (by rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx24])
      (by rw [hcpu_out.readReg64]; simp [arm64_norm, hx25'])
      (by rw [hcpu_out.readReg64]; simp [arm64_norm, hx26'])
      (by rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx27])
      (by rw [hcpu_out.readReg64]; simp [arm64_norm, hcpu_in.readReg64, hx28])
      (by rw [hcpu_out.calleeSavedVRegs]; simpa [arm64_norm, hcpu_in.calleeSavedVRegs] using hvregs)

/-- Default placeholder step (`0xc0`, `+0x074 .. +0x0a8`, `+0x048 .. +0x064`). -/
theorem cwStep_defaultArg [CoreFmtWritePl] {σ : Type} (C : CwCtx σ)
    (hext_blk : ∀ off : Nat, off < 436 →
      C.P.externAt? (coreFmtMpl.base 0 + BitVec.ofNat 64 off) = none)
    {pos ai : Nat} {value fmtFn : BitVec 64} {cs' : List FmtCall}
    {st : σ} {pad : BitVec 64} {s : State}
    (hcl : coreMultiLib.CodeLoaded coreFmtMpl s.mem)
    (heven : C.argsPtr.getLsbD 0 = false)
    (harg : C.args[ai]? = some (value, fmtFn))
    (hcb : FmtCallbacks C.P C.W C.Step C.Panic C.Oom C.stackBytes C.out C.vt C.writeStrFn
      (FmtCall.fmtArg ai value fmtFn defaultFmtOptions :: cs'))
    (ih_loop : CwLoopCont C (pos + 1) (ai + 1) cs')
    (hpc : s.pc = cwPl0.base + 116#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = C.s0.sp - 112#64)
    (hsp_al : s.spAligned = true)
    (hx2 : s.readReg64 (.gpr 2#5) = C.tplPtr + BitVec.ofNat 64 pos)
    (hx8 : s.readReg64 (.gpr 8#5) = (0xc0#8).zeroExtend 64)
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
      (CwQ C (FmtCall.fmtArg ai value fmtFn defaultFmtOptions :: cs') st)
      (CwQp C (FmtCall.fmtArg ai value fmtFn defaultFmtOptions :: cs') st)
      (CwOom C (FmtCall.fmtArg ai value fmtFn defaultFmtOptions :: cs') st) := by
  refine cwStep_defaultArg_preCall C hext_blk hcl heven harg hcb.transport
    hpc hrun hsp hsp_al hx2 hx8 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hvregs ?_
  intro sm hcl_sm hpc_sm hrun_sm hsp_sm hsp_al_sm hlr_sm hx0_sm hx1_sm
    hx19_sm hx20_sm hx21_sm hx22_sm hx24_sm hx25_sm hx26_sm hx27_sm hx28_sm hvregs_sm
  refine cwCallFmtArg_wpp C hcl_sm hcb hpc_sm hrun_sm hsp_sm hsp_al_sm hlr_sm hx0_sm hx1_sm
    fun sf ok st' hpcf hrunf hsp_sf hsp_al_sf hcs_sf hcl_sf hw0f hstep => ?_
  rw [CalleeSavedPreserved.iff_regs] at hcs_sf
  rcases hcs_sf with ⟨h19f, h20f, h21f, h22f, _, h24f, h25f, h26f, h27f, h28f, _, hvrf⟩
  have hbit0_sf : (sf.readReg64 (.gpr 0#5)).getLsbD 0 = !ok :=
    w0_bit0_of_and1_ite (by simpa [arm64_norm] using hw0f)
  cases ok
  · apply sepWPp_seg_coreFmt_pure hext_blk hcl_sf (mid := cwPl0.base + 404#64)
    intro s2 hcpu2
    have hpc2 : s2.pc = cwPl0.base + 96#64 := hcpu2.pc_eq.trans hpcf
    have hrun2 : s2.status = .Running := hcpu2.status_eq.trans hrunf
    have hsp_al2 : s2.spAligned = true := hcpu2.spAligned.trans hsp_al_sf
    have hbit0_2 : (s2.readReg64 (.gpr 0#5)).getLsbD 0 = true := by
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
  · apply cw_step_ok_conseq C hstep
    apply sepWPp_seg_coreFmt_pure hext_blk hcl_sf (mid := cwPl0.base + 104#64)
    intro s2 hcpu2
    have hpc2 : s2.pc = cwPl0.base + 96#64 := hcpu2.pc_eq.trans hpcf
    have hrun2 : s2.status = .Running := hcpu2.status_eq.trans hrunf
    have hsp_al2 : s2.spAligned = true := hcpu2.spAligned.trans hsp_al_sf
    have hbit0_2 : (s2.readReg64 (.gpr 0#5)).getLsbD 0 = false := by
      rw [hcpu2.readReg64]; simpa using hbit0_sf
    have hx25_2 : s2.readReg64 (.gpr 25#5) = BitVec.ofNat 64 ai := by
      rw [hcpu2.readReg64, h25f, hx25_sm]
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun2)
      fun sm2 hcpu2_out hcl_sm2 hnsp2 hsig2 htp2 horc2 hsym2 => ?_
    have hframe2 : FmtWriteFrame sf sm2 := fmtWriteFrame_of_seg hnsp2 hsig2 htp2 horc2 hsym2
    refine SepWPp.weaken_pre (cwLoopMem_transport C hcb.transport hframe2) ?_
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
