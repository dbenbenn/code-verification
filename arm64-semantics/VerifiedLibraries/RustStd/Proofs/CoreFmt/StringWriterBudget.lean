/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Proofs.CoreFmt.StringWriteStrBudget
public meta import ProofLib.ProgramReflection

/-!
# Budget-Threaded `<String as core::fmt::Write>` Proofs

Verifies `<alloc::string::String as core::fmt::Write>::write_char` against `fmtWriterCharSpec`
(`budgetWriteChar_fmtWriterChar_ok`) and assembles the `FmtWriterOk` bundle
`stringBudgetFmtWriterOk` over `fmtInnerBudgetW`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj Arm64.Process ProofLib
  ProofLib.ProgramReflection ProofLib.GenPlacedFetches ProofLib.StdStartup
open VerifiedLibraries.Mallocng (AllocEvent)
open VerifiedLibraries.RustStd.CoreFmt
  (LibBlockNoExtern LibKeepNoExtern PureSegPreserved
   sepWP_seg_lib_block_pureWhere sepWPp_seg_lib_block_pureWhere)

section WriterHelpers
arm64_proof_prelude

/-! ## `<String as fmt::Write>::write_char` and `FmtWriterOk` -/

private abbrev allocDoReserveCallSym :=
  "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [rust_alloc]"

private theorem budgetWriteChar_reserve_pc [AllocPlacement] :
    allocPl06.base + (reloc_call_off% allocLib06.text.relocs
        "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [rust_alloc]") +
      (allocPl06.ρ allocDoReserveSym - allocPl06.base -
        (reloc_call_off% allocLib06.text.relocs
          "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [rust_alloc]")) =
      allocMultiLib.resolve AllocPlacement.mpl allocDoReserveSym := by
  change allocPl06.base + _ + (allocMultiLib.resolve AllocPlacement.mpl allocDoReserveSym - allocPl06.base - _) = _
  bv_lin

private theorem charUtf8Len_bounds (c : BitVec 32) :
    1 ≤ charUtf8Len c ∧ charUtf8Len c ≤ 4 := by
  unfold charUtf8Len
  repeat' (split <;> try omega)

private theorem memRegion_two_bytes (a : BitVec 64) :
    memRegion a 2 = ∃∗ b0 : BitVec 8, ∃∗ b1 : BitVec 8, (a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) := by
  rw [show (2 : Nat) = 1 + 1 from rfl, memRegion_split a 1 1 (by decide),
    memRegion_one, memRegion_one, sepExists_sepConj_left]
  exact sepExists_congr fun _ => sepExists_sepConj_right _ _

private theorem memRegion_three_bytes (a : BitVec 64) :
    memRegion a 3 = ∃∗ b0 : BitVec 8, ∃∗ b1 : BitVec 8, ∃∗ b2 : BitVec 8,
      (a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) := by
  rw [show (3 : Nat) = 2 + 1 from rfl, memRegion_split a 2 1 (by decide),
    memRegion_two_bytes, memRegion_one, sepExists_sepConj_left]
  refine sepExists_congr fun _ => ?_
  rw [sepExists_sepConj_left]
  refine sepExists_congr fun _ => ?_
  rw [sepExists_sepConj_right]
  exact sepExists_congr fun _ => by simp only [sepConj_assoc, bv_lin_norm]

private theorem memRegion_four_bytes (a : BitVec 64) :
    memRegion a 4 = ∃∗ b0 : BitVec 8, ∃∗ b1 : BitVec 8, ∃∗ b2 : BitVec 8, ∃∗ b3 : BitVec 8,
      (a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₈ b3) := by
  rw [show (4 : Nat) = 3 + 1 from rfl, memRegion_split a 3 1 (by decide),
    memRegion_three_bytes, memRegion_one, sepExists_sepConj_left]
  refine sepExists_congr fun _ => ?_
  rw [sepExists_sepConj_left]
  refine sepExists_congr fun _ => ?_
  rw [sepExists_sepConj_left]
  refine sepExists_congr fun _ => ?_
  rw [sepExists_sepConj_right]
  exact sepExists_congr fun _ => by simp only [sepConj_assoc, bv_lin_norm]

private theorem pointsToBytes_of_bytes1 {a : BitVec 64} {v0 e0 : BitVec 8} (h0 : v0 = e0) :
    (a ↦₈ v0) ⊢ (a ↦ₛ [e0]) := by
  subst h0; rw [pointsToBytes_singleton]; exact Entails.refl _

private theorem pointsToBytes_of_bytes2 {a : BitVec 64} {v0 v1 e0 e1 : BitVec 8}
    (h0 : v0 = e0) (h1 : v1 = e1) :
    (a ↦₈ v0) ∗ ((a + 1#64) ↦₈ v1) ⊢ (a ↦ₛ [e0, e1]) := by
  subst h0 h1; rw [pointsToBytes_cons, pointsToBytes_singleton]; exact Entails.refl _

private theorem pointsToBytes_of_bytes3 {a : BitVec 64} {v0 v1 v2 e0 e1 e2 : BitVec 8}
    (h0 : v0 = e0) (h1 : v1 = e1) (h2 : v2 = e2) :
    (a ↦₈ v0) ∗ ((a + 1#64) ↦₈ v1) ∗ ((a + 2#64) ↦₈ v2) ⊢ (a ↦ₛ [e0, e1, e2]) := by
  subst h0 h1 h2
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, bv_lin_norm]
  exact Entails.refl _

private theorem pointsToBytes_of_bytes4 {a : BitVec 64} {v0 v1 v2 v3 e0 e1 e2 e3 : BitVec 8}
    (h0 : v0 = e0) (h1 : v1 = e1) (h2 : v2 = e2) (h3 : v3 = e3) :
    (a ↦₈ v0) ∗ ((a + 1#64) ↦₈ v1) ∗ ((a + 2#64) ↦₈ v2) ∗ ((a + 3#64) ↦₈ v3) ⊢
      (a ↦ₛ [e0, e1, e2, e3]) := by
  subst h0 h1 h2 h3
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, bv_lin_norm]
  exact Entails.refl _

private theorem char_ult_iff {c : BitVec 32} {k : Nat} (hk : k < 2 ^ 32) :
    c.ult (BitVec.ofNat 32 k) = decide (c.toNat < k) := by
  simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

private theorem char_ule_iff {c : BitVec 32} {k : Nat} (hk : k < 2 ^ 32) :
    (BitVec.ofNat 32 k).ule c = decide (k ≤ c.toNat) := by
  simp [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

private theorem char_shr16_eq_zero_iff (c : BitVec 32) :
    (c >>> 16 == 0#32) = decide (c.toNat < 65536) := by
  by_cases h : c.toNat < 65536
  · rw [decide_eq_true h, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.zero_mod,
      Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (by omega)
  · rw [decide_eq_false h]
    refine beq_false_of_ne fun heq => h ?_
    have h0 := congrArg BitVec.toNat heq
    simp at h0
    omega

theorem fmtInnerBudgetW_transport (A : RustAllocBudget) (st0 : A.σ) (va : StringWriteAddrs)
    (R : SepProp) (t0 : State) (out : BitVec 64) (st : FmtBuf) (s s' : State)
    (hf : FmtWriteFrame s s') :
    fmtInnerBudgetW A st0 va R t0 out st s ⊢ fmtInnerBudgetW A st0 va R t0 out st s' := by
  dsimp only [fmtInnerBudgetW]
  rw [← A.pool_of_fmtWriteFrame _ hf]
  refine Entails.pure_left fun hio => ?_
  rw [pure_sepConj_of_true (budgetIoCall_of_acp hio (allocCallPreserved_of_fmtWriteFrame hf))]
  exact Entails.refl _

private theorem budget_dup_slots {a b c p v f q r : SepProp} (ha : a ∗ a = a) (hb : b ∗ b = b) :
    p ∗ v ∗ f ∗ q ∗ (a ∗ b ∗ c) ∗ r = a ∗ b ∗ p ∗ v ∗ f ∗ q ∗ (a ∗ b ∗ c) ∗ r :=
  calc _ = p ∗ v ∗ f ∗ q ∗ ((a ∗ a) ∗ (b ∗ b) ∗ c) ∗ r := by rw [ha, hb]
    _ = _ := by ac_rfl

theorem fmtInnerBudgetW_slots (A : RustAllocBudget) (st0 : A.σ) (va : StringWriteAddrs)
    (R : SepProp) (t0 : State) (out : BitVec 64) (st : FmtBuf) (s : State) :
    fmtInnerBudgetW A st0 va R t0 out st s =
      ((va.vtable + 0x18#64) ↦₆₄ᵣ va.writeStr) ∗ ((va.vtable + 0x20#64) ↦₆₄ᵣ va.writeChar) ∗
        fmtInnerBudgetW A st0 va R t0 out st s := by
  dsimp only [fmtInnerBudgetW, stringWriteVtableAt]
  exact budget_dup_slots (pointsTo64RO_dup _ _) (pointsTo64RO_dup _ _)

private theorem budgetWriteChar_fold_buf (A : RustAllocBudget)
    {out cap' ptr' : BitVec 64} {bs : List (BitVec 8)} {c : BitVec 32} {k : Nat}
    {Cells Rest : SepProp}
    (hk : charUtf8Len c = k)
    (hcap'_ne0 : cap' ≠ 0#64) (hcap'_lt : cap'.toNat < 2 ^ 63) (hptr'_ne : ptr' ≠ 0#64)
    (hfit : charUtf8Len c ≤ cap'.toNat - bs.length)
    (hcells : Cells ⊢ (ptr' + BitVec.ofNat 64 bs.length) ↦ₛ encodeUtf8Char c) :
    ((out ↦₆₄ cap') ∗ ((out + 8#64) ↦₆₄ ptr') ∗
      ((out + 16#64) ↦₆₄ (BitVec.ofNat 64 k + BitVec.ofNat 64 bs.length)) ∗
      A.live ptr' cap'.toNat 1 ∗ (ptr' ↦ₛ bs) ∗ Cells ∗
      memRegion (ptr' + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 k)
        (cap'.toNat - bs.length - k)) ∗ Rest ⊢
      (vecHeader out cap' ptr' (BitVec.ofNat 64 (bs ++ encodeUtf8Char c).length) ∗
        fmtBufVecAt A cap' ptr' (bs ++ encodeUtf8Char c)) ∗ Rest := by
  refine sepConj_mono_left ?_
  have hk_pos : 1 ≤ k := hk ▸ (charUtf8Len_bounds c).1
  have hlen_app : (bs ++ encodeUtf8Char c).length = bs.length + k := by
    rw [List.length_append, encodeUtf8Char_length, hk]
  dsimp only [vecHeader, fmtBufVecAt]
  simp only [hcap'_ne0, ↓reduceIte, hlen_app]
  rw [pure_sepConj_of_true ⟨by omega, hcap'_lt, hptr'_ne⟩,
    pointsToBytes_append (a := ptr'),
    show ptr' + BitVec.ofNat 64 (bs.length + k) =
      ptr' + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 k by
      rw [BitVec.ofNat_add, BitVec.add_assoc],
    show BitVec.ofNat 64 (bs.length + k) = BitVec.ofNat 64 k + BitVec.ofNat 64 bs.length by
      rw [Nat.add_comm, BitVec.ofNat_add],
    show cap'.toNat - (bs.length + k) = cap'.toNat - bs.length - k by omega]
  exact Entails.trans
    (Q := Cells ∗ ((out ↦₆₄ cap' ∗ (out + 8#64) ↦₆₄ ptr' ∗
        (out + 16#64) ↦₆₄ (BitVec.ofNat 64 k + BitVec.ofNat 64 bs.length)) ∗
      A.live ptr' cap'.toNat 1 ∗ (ptr' ↦ₛ bs) ∗
      memRegion (ptr' + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 k) (cap'.toNat - bs.length - k)))
    (by sep_entail) (Entails.trans (sepConj_mono_left hcells) (by sep_entail))

private theorem budgetWriteChar_fold_all (A : RustAllocBudget)
    {out cap' ptr' : BitVec 64} {bs : List (BitVec 8)} {c : BitVec 32} {k : Nat}
    {s0 : State} {ev_p Frame : SepProp} (Cells : SepProp) {Pre_end : SepProp}
    (hk : charUtf8Len c = k)
    (hcap'_ne0 : cap' ≠ 0#64) (hcap'_lt : cap'.toNat < 2 ^ 63) (hptr'_ne : ptr' ≠ 0#64)
    (hfit : charUtf8Len c ≤ cap'.toNat - bs.length)
    (hperm : Pre_end ⊢
      (((out ↦₆₄ cap') ∗ ((out + 8#64) ↦₆₄ ptr') ∗
        ((out + 16#64) ↦₆₄ (BitVec.ofNat 64 k + BitVec.ofNat 64 bs.length)) ∗
        A.live ptr' cap'.toNat 1 ∗ (ptr' ↦ₛ bs) ∗ Cells ∗
        memRegion (ptr' + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 k)
          (cap'.toNat - bs.length - k)) ∗
       (stackAt (s0.sp - 48#64) defaultAllocReserveStack ∗ budgetWriterSavedSlots s0) ∗
       ev_p ∗ Frame))
    (hcells : Cells ⊢ (ptr' + BitVec.ofNat 64 bs.length) ↦ₛ encodeUtf8Char c) :
    Pre_end ⊢
      vecHeader out cap' ptr' (BitVec.ofNat 64 (bs ++ encodeUtf8Char c).length) ∗
        fmtBufVecAt A cap' ptr' (bs ++ encodeUtf8Char c) ∗
        stackAt s0.sp (48 + defaultAllocReserveStack) ∗ ev_p ∗ Frame := by
  have hstk := budgetWriter_stack_refold s0.sp
    (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5)) (s0.readReg64 (.gpr 22#5))
    (s0.readReg64 (.gpr 21#5)) (s0.readReg64 (.gpr 20#5)) (s0.readReg64 (.gpr 19#5))
  refine Entails.trans hperm ?_
  refine Entails.trans (budgetWriteChar_fold_buf A hk hcap'_ne0 hcap'_lt hptr'_ne hfit hcells) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hstk)) ?_
  sep_entail

private theorem budgetWriteChar_close_seg [AllocPlacement] (A : RustAllocBudget)
    {P : Program} {ev_st : A.σ} {out cap' ptr' : BitVec 64} {bs : List (BitVec 8)} {c : BitVec 32}
    {Frame Pre_end : SepProp} {s0 s_in s_in' s_end : State} {post : State → SepProp → Prop}
    (hcpu_in : SameCpuState s_in' s_in)
    (hgprs_in : BudgetWriterHighGprs s0 s_in)
    (hvregs_in : calleeSavedVRegs s_in = calleeSavedVRegs s0)
    (hpc : s_end.pc = s0.readReg64 .lr) (hrun : s_end.status = .Running)
    (hsp : s_end.sp = s0.sp) (hx0 : s_end.readReg64 .x0 = 0#64)
    (hx19 : s_end.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5))
    (hx20 : s_end.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5))
    (hx21 : s_end.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5))
    (hx22 : s_end.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5))
    (hx29 : s_end.readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5))
    (hgprs_end : BudgetWriterHighGprs s_in' s_end)
    (hvregs_end : calleeSavedVRegs s_end = calleeSavedVRegs s_in')
    (hsig : s_end.sigActions = s_in'.sigActions) (htp : s_end.tpidrEl0 = s_in'.tpidrEl0)
    (hfold : Pre_end ⊢
      vecHeader out cap' ptr' (BitVec.ofNat 64 (bs ++ encodeUtf8Char c).length) ∗
        fmtBufVecAt A cap' ptr' (bs ++ encodeUtf8Char c) ∗
        stackAt s0.sp (48 + defaultAllocReserveStack) ∗ A.pool ev_st s_in ∗ Frame)
    {Cld : Memory → Prop}
    (hcont : ∀ sf : State, sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      AllocCallPreserved s_in sf → sf.readReg64 .x0 = 0#64 →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ vecHeader out cap' ptr' (BitVec.ofNat 64 (bs ++ encodeUtf8Char c).length) ∗
          fmtBufVecAt A cap' ptr' (bs ++ encodeUtf8Char c) ∗
          stackAt s0.sp (48 + defaultAllocReserveStack) ∗ A.pool ev_st sf ∗ Frame) →
        post sf Pre_f) :
    SepWP (allocPC06.rebase allocPl06.base (fun _ => none)) (s0.readReg64 .lr) s_end Pre_end
      fun s_mid Pre_mid =>
        ∀ sf, SameCpuState sf s_mid →
          Cld sf.mem → PureSegPreserved s_in sf →
            SepWP P (s0.readReg64 .lr) sf Pre_mid post := by
  refine SepWP.done hpc hrun fun sf hcpu_f _ hseg_f => ?_
  have ⟨hacp, hvm⟩ := allocCall_vm_of_pureSeg hcpu_in hcpu_f hseg_f hsig htp
  have hpool_eq : A.pool ev_st s_in = A.pool ev_st sf := (A.pool_transport _ s_in sf hvm).symm
  have hg_in' : BudgetWriterHighGprs s0 s_in' :=
    ⟨(hcpu_in.readReg64 _).trans hgprs_in.1, (hcpu_in.readReg64 _).trans hgprs_in.2.1,
     (hcpu_in.readReg64 _).trans hgprs_in.2.2.1, (hcpu_in.readReg64 _).trans hgprs_in.2.2.2.1,
     (hcpu_in.readReg64 _).trans hgprs_in.2.2.2.2.1, (hcpu_in.readReg64 _).trans hgprs_in.2.2.2.2.2⟩
  have hg_end := hg_in'.trans hgprs_end
  have hcs_f : CalleeSavedPreserved s0 sf := by
    rw [CalleeSavedPreserved.iff_regs]
    exact ⟨(hcpu_f.readReg64 _).trans hx19, (hcpu_f.readReg64 _).trans hx20,
      (hcpu_f.readReg64 _).trans hx21, (hcpu_f.readReg64 _).trans hx22,
      (hcpu_f.readReg64 _).trans hg_end.1, (hcpu_f.readReg64 _).trans hg_end.2.1,
      (hcpu_f.readReg64 _).trans hg_end.2.2.1, (hcpu_f.readReg64 _).trans hg_end.2.2.2.1,
      (hcpu_f.readReg64 _).trans hg_end.2.2.2.2.1, (hcpu_f.readReg64 _).trans hg_end.2.2.2.2.2,
      (hcpu_f.readReg64 _).trans hx29,
      hcpu_f.calleeSavedVRegs.trans (hvregs_end.trans (hcpu_in.calleeSavedVRegs.trans hvregs_in))⟩
  refine SepWP.done (hcpu_f.pc_eq.trans hpc) (hcpu_f.status_eq.trans hrun)
    (hcont sf (hcpu_f.sp_eq.trans hsp) hcs_f hacp ((hcpu_f.readReg64 .x0).trans hx0) ?_)
  rwa [← hpool_eq]

set_option maxHeartbeats 1200000 in
private theorem budgetWriteChar_slow_tail [AllocPlacement] (A : RustAllocBudget)
    {keep : Nat → Bool} (hk6 : keep 6 = true) {P : Program}
    {ev_st : A.σ} {out cap' ptr' : BitVec 64} {bs : List (BitVec 8)} {c : BitVec 32}
    {Frame : SepProp} {s0 sj : State} {post : State → SepProp → Prop}
    (hext6 : LibBlockNoExtern allocMultiLib AllocPlacement.mpl P 6)
    (hcl_j : allocMultiLib.CodeLoadedWhere keep AllocPlacement.mpl sj.mem)
    (hpc_j : sj.pc = allocPl06.base +
      (reloc_call_off% allocLib06.text.relocs
        "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [rust_alloc]" + 4#64))
    (hrun_j : sj.status = .Running) (hsp0 : s0.spAligned = true)
    (hsp_j : sj.sp = s0.sp - 48#64)
    (hx19_j : sj.readReg64 (.gpr 19#5) = out)
    (hx20_j : sj.readReg64 (.gpr 20#5) = BitVec.ofNat 64 bs.length)
    (hx21_j : sj.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (charUtf8Len c))
    (hx22_j : sj.readReg64 (.gpr 22#5) = c.zeroExtend 64)
    (hgprs_j : BudgetWriterHighGprs s0 sj)
    (hvregs_j : calleeSavedVRegs sj = calleeSavedVRegs s0)
    (hcap'_lt : cap'.toNat < 2 ^ 63) (hptr'_ne : ptr' ≠ 0#64)
    (hfit : charUtf8Len c ≤ cap'.toNat - bs.length)
    (hcont : ∀ sf : State, sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      AllocCallPreserved sj sf → sf.readReg64 .x0 = 0#64 →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ vecHeader out cap' ptr' (BitVec.ofNat 64 (bs ++ encodeUtf8Char c).length) ∗
          fmtBufVecAt A cap' ptr' (bs ++ encodeUtf8Char c) ∗
          stackAt s0.sp (48 + defaultAllocReserveStack) ∗ A.pool ev_st sf ∗ Frame) →
        post sf Pre_f) :
    SepWP P (s0.readReg64 .lr) sj
      (stackAt (s0.sp - 48#64) defaultAllocReserveStack ∗ budgetWriterSavedSlots s0 ∗
        vecHeader out cap' ptr' (BitVec.ofNat 64 bs.length) ∗
        A.live ptr' cap'.toNat 1 ∗ (ptr' ↦ₛ bs) ∗
        memRegion (ptr' + BitVec.ofNat 64 bs.length) (cap'.toNat - bs.length) ∗
        A.pool ev_st sj ∗ Frame) post := by
  have hcap'_pos : 0 < cap'.toNat := by have := (charUtf8Len_bounds c).1; omega
  have hcap'_ne0 : cap' ≠ 0#64 := by rintro rfl; simp at hcap'_pos
  apply sepWP_seg_lib_block_pureWhere (lib := allocMultiLib) 6 ⟨by decide, hk6⟩ hext6 allocBlockNoSvc0_06 hcl_j
    (mid := s0.readReg64 .lr)
  intro sj' hcpu_j
  change SepWP (allocPC06.rebase allocPl06.base (fun _ => none)) _ _ _ _
  have hpc_j' := hcpu_j.pc_eq.trans hpc_j
  simp only [BitVec.reduceAdd] at hpc_j'
  have hrun_j' : sj'.status = .Running := hcpu_j.status_eq.trans hrun_j
  have hsp_j_in : sj'.sp = s0.sp - 48#64 := hcpu_j.sp_eq.trans hsp_j
  have hsp_j' : sj'.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_j_in]; exact s0.spAligned_sub 48#64 hsp0
  have hx19_j' : sj'.readReg64 (.gpr 19#5) = out := (hcpu_j.readReg64 _).trans hx19_j
  have hx20_j' : sj'.readReg64 (.gpr 20#5) = BitVec.ofNat 64 bs.length := (hcpu_j.readReg64 _).trans hx20_j
  have hx21_j' : sj'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (charUtf8Len c) := (hcpu_j.readReg64 _).trans hx21_j
  have hx22_j' : sj'.readReg64 (.gpr 22#5) = c.zeroExtend 64 := (hcpu_j.readReg64 _).trans hx22_j
  refine SepWP.weaken_pre (P' :=
      memRegion (ptr' + BitVec.ofNat 64 bs.length) (charUtf8Len c) ∗
        (memRegion (ptr' + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 (charUtf8Len c))
          (cap'.toNat - bs.length - charUtf8Len c) ∗
         stackAt sj'.sp defaultAllocReserveStack ∗
         ((sj'.sp ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗ ((sj'.sp + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
           ((sj'.sp + 16#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗ ((sj'.sp + 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
           ((sj'.sp + 32#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗ ((sj'.sp + 40#64) ↦₆₄ s0.readReg64 (.gpr 19#5))) ∗
         (out ↦₆₄ cap') ∗ ((out + 8#64) ↦₆₄ ptr') ∗ ((out + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
         A.live ptr' cap'.toNat 1 ∗ (ptr' ↦ₛ bs) ∗ A.pool ev_st sj ∗ Frame))
    (by
      rw [memRegion_split_le (ptr' + BitVec.ofNat 64 bs.length) (charUtf8Len c)
        (cap'.toNat - bs.length) hfit (by omega)]
      dsimp only [vecHeader, budgetWriterSavedSlots]
      simp only [hsp_j_in, bv_lin_norm]
      sep_entail) ?_
  let dst := ptr' + BitVec.ofNat 64 bs.length
  by_cases hc1 : c.toNat < 128
  · have hlen : charUtf8Len c = 1 := by simp [charUtf8Len, hc1]
    have hult128 : c.ult 128#32 = true := by rw [char_ult_iff (by decide)]; exact decide_eq_true hc1
    wp_conv_pre => rw [hlen, memRegion_one]; simp only [sepExists_sepConj_left]
    refine SepWP.exists_elim fun b0 => ?_
    wp_sym_steps
    refine budgetWriteChar_close_seg A hcpu_j hgprs_j hvregs_j (by simp [arm64_norm])
      (by simpa [arm64_norm] using hrun_j') (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
        by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) ?_ hcont
    exact budgetWriteChar_fold_all A (dst ↦₈ _) hlen hcap'_ne0 hcap'_lt hptr'_ne hfit
      (by dsimp only [budgetWriterSavedSlots, dst]; simp only [hsp_j_in, bv_lin_norm]; sep_entail)
      (by unfold encodeUtf8Char; simp only [hc1, ↓reduceIte]
          exact pointsToBytes_of_bytes1 rfl)
  · have hult128 : c.ult 128#32 = false := by rw [char_ult_iff (by decide)]; exact decide_eq_false hc1
    by_cases hc2 : c.toNat < 2048
    · have hlen : charUtf8Len c = 2 := by simp [charUtf8Len, hc1, hc2]
      have hule2048 : (2048#32).ule c = false := by
        rw [char_ule_iff (by decide)]; exact decide_eq_false (by omega)
      wp_conv_pre => rw [hlen, memRegion_two_bytes]; simp only [sepExists_sepConj_left]
      refine SepWP.exists_elim fun b0 => SepWP.exists_elim fun b1 => ?_
      wp_sym_steps
      refine budgetWriteChar_close_seg A hcpu_j hgprs_j hvregs_j (by simp [arm64_norm])
        (by simpa [arm64_norm] using hrun_j') (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
          by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) ?_ hcont
      exact budgetWriteChar_fold_all A ((dst ↦₈ _) ∗ ((dst + 1#64) ↦₈ _)) hlen hcap'_ne0 hcap'_lt hptr'_ne hfit
        (by dsimp only [budgetWriterSavedSlots, dst]; simp only [hsp_j_in, bv_lin_norm]; sep_entail)
        (by unfold encodeUtf8Char; simp only [hc1, hc2, ↓reduceIte]
            exact pointsToBytes_of_bytes2 (by bv_robdd) (by bv_robdd))
    · have hule2048 : (2048#32).ule c = true := by
        rw [char_ule_iff (by decide)]; exact decide_eq_true (by omega)
      by_cases hc3 : c.toNat < 65536
      · have hlen : charUtf8Len c = 3 := by simp [charUtf8Len, hc1, hc2, hc3]
        have hshr16 : (c >>> 16 == 0#32) = true := by rw [char_shr16_eq_zero_iff]; exact decide_eq_true hc3
        have hshr16_ne : (c >>> 16 != 0#32) = false := by simp [bne, hshr16]
        wp_conv_pre => rw [hlen, memRegion_three_bytes]; simp only [sepExists_sepConj_left]
        refine SepWP.exists_elim fun b0 => SepWP.exists_elim fun b1 => SepWP.exists_elim fun b2 => ?_
        wp_sym_steps
        refine budgetWriteChar_close_seg A hcpu_j hgprs_j hvregs_j (by simp [arm64_norm])
          (by simpa [arm64_norm] using hrun_j') (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
            by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) ?_ hcont
        exact budgetWriteChar_fold_all A ((dst ↦₈ _) ∗ ((dst + 1#64) ↦₈ _) ∗ ((dst + 2#64) ↦₈ _))
          hlen hcap'_ne0 hcap'_lt hptr'_ne hfit
          (by dsimp only [budgetWriterSavedSlots, dst]; simp only [hsp_j_in, bv_lin_norm]; sep_entail)
          (by unfold encodeUtf8Char; simp only [hc1, hc2, hc3, ↓reduceIte]
              exact pointsToBytes_of_bytes3
                (by bv_robdd) (by bv_robdd) (by bv_robdd))
      · have hlen : charUtf8Len c = 4 := by simp [charUtf8Len, hc1, hc2, hc3]
        have hshr16 : (c >>> 16 == 0#32) = false := by rw [char_shr16_eq_zero_iff]; exact decide_eq_false hc3
        have hshr16_ne : (c >>> 16 != 0#32) = true := by simp [bne, hshr16]
        wp_conv_pre => rw [hlen, memRegion_four_bytes]; simp only [sepExists_sepConj_left]
        refine SepWP.exists_elim fun b0 => SepWP.exists_elim fun b1 =>
          SepWP.exists_elim fun b2 => SepWP.exists_elim fun b3 => ?_
        wp_sym_steps
        refine budgetWriteChar_close_seg A hcpu_j hgprs_j hvregs_j (by simp [arm64_norm])
          (by simpa [arm64_norm] using hrun_j') (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
            by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) ?_ hcont
        exact budgetWriteChar_fold_all A
          ((dst ↦₈ _) ∗ ((dst + 1#64) ↦₈ _) ∗ ((dst + 2#64) ↦₈ _) ∗ ((dst + 3#64) ↦₈ _))
          hlen hcap'_ne0 hcap'_lt hptr'_ne hfit
          (by dsimp only [budgetWriterSavedSlots, dst]; simp only [hsp_j_in, bv_lin_norm]; sep_entail)
          (by unfold encodeUtf8Char; simp only [hc1, hc2, hc3, ↓reduceIte]
              exact pointsToBytes_of_bytes4
                (by bv_robdd) (by bv_robdd)
                (by bv_robdd) (by bv_robdd))

private theorem budgetWriteChar_bhi_cond {cap : BitVec 64} {len k : Nat}
    (hlen : len ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63) (hk : k < 2 ^ 64) :
    ((cap - BitVec.ofNat 64 len).ult (BitVec.ofNat 64 k)) = decide (cap.toNat - len < k) := by
  have hlen_bv : (BitVec.ofNat 64 len).toNat = len := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : len < 2 ^ 64)]
  have hsub : (cap - BitVec.ofNat 64 len).toNat = cap.toNat - len := by
    rw [BitVec.toNat_sub_of_le]; · omega
    · rw [BitVec.le_def, hlen_bv]; exact hlen
  simp [BitVec.ult, hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

set_option hygiene false in
local macro "wc_fast_close" : tactic => `(tactic| (
  refine budgetWriteChar_close_seg A hcpu1 ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl
    (by simpa [arm64_norm] using hlr_1') (by simpa [arm64_norm] using hrun1')
    (by simp [arm64_norm]) (by simp [arm64_norm])
    (by simpa [arm64_norm] using hcpu1.readReg64 (.gpr 19#5))
    (by simpa [arm64_norm] using hcpu1.readReg64 (.gpr 20#5))
    (by simpa [arm64_norm] using hcpu1.readReg64 (.gpr 21#5))
    (by simpa [arm64_norm] using hcpu1.readReg64 (.gpr 22#5))
    (by simpa [arm64_norm] using hcpu1.readReg64 (.gpr 29#5))
    ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
    (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) ?_ hcont))

set_option linter.unnecessarySimpa false in
set_option maxHeartbeats 1200000 in
private theorem budgetWriteChar_fast [AllocPlacement] (A : RustAllocBudget)
    {keep : Nat → Bool} (hk6 : keep 6 = true) {P : Program}
    {ev_st : A.σ} {out cap ptr : BitVec 64} {bs : List (BitVec 8)} {c : BitVec 32}
    {Frame : SepProp} {s0 : State} {post : State → SepProp → Prop}
    (hext6 : LibBlockNoExtern allocMultiLib AllocPlacement.mpl P 6)
    (hcl0 : allocMultiLib.CodeLoadedWhere keep AllocPlacement.mpl s0.mem)
    (hpc : s0.pc = allocPl06.base) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = out) (hx1 : s0.readReg32 .x1 = c)
    (hbs_le : bs.length ≤ cap.toNat) (hcap_lt : cap.toNat < 2 ^ 63) (hptr_ne : ptr ≠ 0#64)
    (hfit : charUtf8Len c ≤ cap.toNat - bs.length)
    (hcont : ∀ sf : State, sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      AllocCallPreserved s0 sf → sf.readReg64 .x0 = 0#64 →
      ∀ {Pre_f : SepProp},
        (Pre_f ⊢ vecHeader out cap ptr (BitVec.ofNat 64 (bs ++ encodeUtf8Char c).length) ∗
          fmtBufVecAt A cap ptr (bs ++ encodeUtf8Char c) ∗
          stackAt s0.sp (48 + defaultAllocReserveStack) ∗ A.pool ev_st sf ∗ Frame) →
        post sf Pre_f)
    {w0 w1 w2 w3 w4 w5 : BitVec 64} :
    SepWP P (s0.readReg64 .lr) s0
      (stackAt (s0.sp - 48#64) defaultAllocReserveStack ∗
        (((s0.sp - 48#64) ↦₆₄ w0) ∗ ((s0.sp - 40#64) ↦₆₄ w1) ∗ ((s0.sp - 32#64) ↦₆₄ w2) ∗
          ((s0.sp - 24#64) ↦₆₄ w3) ∗ ((s0.sp - 16#64) ↦₆₄ w4) ∗ ((s0.sp - 8#64) ↦₆₄ w5)) ∗
        vecHeader out cap ptr (BitVec.ofNat 64 bs.length) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
        A.pool ev_st s0 ∗ Frame) post := by
  have hk4 := charUtf8Len_bounds c
  have hcap_pos : 0 < cap.toNat := by omega
  have hcap_ne0 : cap ≠ 0#64 := by rintro rfl; simp at hcap_pos
  have hbhi : ((cap - BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 (charUtf8Len c))) = false := by
    rw [budgetWriteChar_bhi_cond hbs_le hcap_lt (by omega)]; exact decide_eq_false (by omega)
  apply sepWP_seg_lib_block_pureWhere (lib := allocMultiLib) 6 ⟨by decide, hk6⟩ hext6 allocBlockNoSvc0_06 hcl0
    (mid := s0.readReg64 .lr)
  intro s1' hcpu1
  change SepWP (allocPC06.rebase allocPl06.base (fun _ => none)) _ _ _ _
  have hpc1' : s1'.pc = allocPl06.base := hcpu1.pc_eq.trans hpc
  have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun
  have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
  have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
  have hx0_1' : s1'.readReg64 (.gpr 0#5) = out := (hcpu1.readReg64 .x0).trans hx0
  have hx1s : BitVec.setWidth 32 (s1'.readReg64 (.gpr 1#5)) = c := by
    rw [hcpu1.readReg64 .x1]; exact hx1
  have hx1t : (s1'.readReg64 (.gpr 1#5)).truncate 32 = c := hx1s
  refine SepWP.weaken_pre (P' :=
      memRegion (ptr + BitVec.ofNat 64 bs.length) (charUtf8Len c) ∗
        (memRegion (ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 (charUtf8Len c))
          (cap.toNat - bs.length - charUtf8Len c) ∗
         stackAt (s1'.sp - 48#64) defaultAllocReserveStack ∗
         (((s1'.sp - 48#64) ↦₆₄ w0) ∗ ((s1'.sp - 40#64) ↦₆₄ w1) ∗ ((s1'.sp - 32#64) ↦₆₄ w2) ∗
           ((s1'.sp - 24#64) ↦₆₄ w3) ∗ ((s1'.sp - 16#64) ↦₆₄ w4) ∗ ((s1'.sp - 8#64) ↦₆₄ w5)) ∗
         (out ↦₆₄ cap) ∗ ((out + 8#64) ↦₆₄ ptr) ∗ ((out + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
         A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗ A.pool ev_st s0 ∗ Frame))
    (by
      rw [memRegion_split_le (ptr + BitVec.ofNat 64 bs.length) (charUtf8Len c)
        (cap.toNat - bs.length) hfit (by omega)]
      dsimp only [vecHeader]
      simp only [hsp1_in]
      sep_entail) ?_
  have hlr_1' : s1'.readReg64 (.gpr 30#5) = s0.readReg64 .lr := hcpu1.readReg64 .lr
  have hbhi' : ∀ k : Nat, charUtf8Len c = k →
      ((cap - BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 k)) = false := fun _ h => h ▸ hbhi
  let dst := ptr + BitVec.ofNat 64 bs.length
  by_cases hc1 : c.toNat < 128
  · have hlen : charUtf8Len c = 1 := by simp [charUtf8Len, hc1]
    have hult128 : c.ult 128#32 = true := by rw [char_ult_iff (by decide)]; exact decide_eq_true hc1
    have hule128 : (128#32).ule c = false := by rw [char_ule_iff (by decide)]; exact decide_eq_false (by omega)
    have hbhi1 := hbhi' 1 hlen
    wp_conv_pre => rw [hlen, memRegion_one]; simp only [sepExists_sepConj_left]
    refine SepWP.exists_elim fun b0 => ?_
    wp_sym_steps
    wc_fast_close
    exact budgetWriteChar_fold_all A (dst ↦₈ _) hlen hcap_ne0 hcap_lt hptr_ne hfit
      (by dsimp only [budgetWriterSavedSlots, dst]; simp only [hsp1_in, hcpu1.readReg64, bv_lin_norm]; sep_entail)
      (by unfold encodeUtf8Char; simp only [hc1, ↓reduceIte]
          exact pointsToBytes_of_bytes1 rfl)
  · have hult128 : c.ult 128#32 = false := by rw [char_ult_iff (by decide)]; exact decide_eq_false hc1
    have hule128 : (128#32).ule c = true := by rw [char_ule_iff (by decide)]; exact decide_eq_true (by omega)
    by_cases hc2 : c.toNat < 2048
    · have hlen : charUtf8Len c = 2 := by simp [charUtf8Len, hc1, hc2]
      have hule2048 : (2048#32).ule c = false := by
        rw [char_ule_iff (by decide)]; exact decide_eq_false (by omega)
      have hult2048 : c.ult 2048#32 = true := by rw [char_ult_iff (by decide)]; exact decide_eq_true hc2
      have hbhi2 := hbhi' 2 hlen
      wp_conv_pre => rw [hlen, memRegion_two_bytes]; simp only [sepExists_sepConj_left]
      refine SepWP.exists_elim fun b0 => SepWP.exists_elim fun b1 => ?_
      wp_sym_steps
      wc_fast_close
      exact budgetWriteChar_fold_all A ((dst ↦₈ _) ∗ ((dst + 1#64) ↦₈ _)) hlen hcap_ne0 hcap_lt hptr_ne hfit
        (by dsimp only [budgetWriterSavedSlots, dst]; simp only [hsp1_in, hcpu1.readReg64, bv_lin_norm]; sep_entail)
        (by unfold encodeUtf8Char; simp only [hc1, hc2, ↓reduceIte]
            exact pointsToBytes_of_bytes2 (by bv_robdd) (by bv_robdd))
    · have hule2048 : (2048#32).ule c = true := by
        rw [char_ule_iff (by decide)]; exact decide_eq_true (by omega)
      have hult2048 : c.ult 2048#32 = false := by rw [char_ult_iff (by decide)]; exact decide_eq_false hc2
      by_cases hc3 : c.toNat < 65536
      · have hlen : charUtf8Len c = 3 := by simp [charUtf8Len, hc1, hc2, hc3]
        have hshr16 : (c >>> 16 == 0#32) = true := by rw [char_shr16_eq_zero_iff]; exact decide_eq_true hc3
        have hshr16_ne : (c >>> 16 != 0#32) = false := by simp [bne, hshr16]
        have hule65536 : (65536#32).ule c = false := by
          rw [char_ule_iff (by decide)]; exact decide_eq_false (by omega)
        have hult65536 : c.ult 65536#32 = true := by rw [char_ult_iff (by decide)]; exact decide_eq_true hc3
        have hbhi3 := hbhi' 3 hlen
        wp_conv_pre => rw [hlen, memRegion_three_bytes]; simp only [sepExists_sepConj_left]
        refine SepWP.exists_elim fun b0 => SepWP.exists_elim fun b1 => SepWP.exists_elim fun b2 => ?_
        wp_sym_steps
        wc_fast_close
        exact budgetWriteChar_fold_all A ((dst ↦₈ _) ∗ ((dst + 1#64) ↦₈ _) ∗ ((dst + 2#64) ↦₈ _))
          hlen hcap_ne0 hcap_lt hptr_ne hfit
          (by dsimp only [budgetWriterSavedSlots, dst]; simp only [hsp1_in, hcpu1.readReg64, bv_lin_norm]; sep_entail)
          (by unfold encodeUtf8Char; simp only [hc1, hc2, hc3, ↓reduceIte]
              exact pointsToBytes_of_bytes3 (by bv_robdd) (by bv_robdd) (by bv_robdd))
      · have hlen : charUtf8Len c = 4 := by simp [charUtf8Len, hc1, hc2, hc3]
        have hshr16 : (c >>> 16 == 0#32) = false := by rw [char_shr16_eq_zero_iff]; exact decide_eq_false hc3
        have hshr16_ne : (c >>> 16 != 0#32) = true := by simp [bne, hshr16]
        have hule65536 : (65536#32).ule c = true := by
          rw [char_ule_iff (by decide)]; exact decide_eq_true (by omega)
        have hult65536 : c.ult 65536#32 = false := by rw [char_ult_iff (by decide)]; exact decide_eq_false hc3
        have hbhi4 := hbhi' 4 hlen
        wp_conv_pre => rw [hlen, memRegion_four_bytes]; simp only [sepExists_sepConj_left]
        refine SepWP.exists_elim fun b0 => SepWP.exists_elim fun b1 =>
          SepWP.exists_elim fun b2 => SepWP.exists_elim fun b3 => ?_
        wp_sym_steps
        wc_fast_close
        exact budgetWriteChar_fold_all A
          ((dst ↦₈ _) ∗ ((dst + 1#64) ↦₈ _) ∗ ((dst + 2#64) ↦₈ _) ∗ ((dst + 3#64) ↦₈ _))
          hlen hcap_ne0 hcap_lt hptr_ne hfit
          (by dsimp only [budgetWriterSavedSlots, dst]; simp only [hsp1_in, hcpu1.readReg64, bv_lin_norm]; sep_entail)
          (by unfold encodeUtf8Char; simp only [hc1, hc2, hc3, ↓reduceIte]
              exact pointsToBytes_of_bytes4 (by bv_robdd) (by bv_robdd) (by bv_robdd) (by bv_robdd))

set_option hygiene false in
local macro "wc_slow_close" : tactic => `(tactic| (
  refine SepWP.done budgetWriteChar_reserve_pc (by simpa [arm64_norm] using hrun1')
    fun sm hcpu_m hcl_m hseg_m => ?_
  have ⟨hacp_m, hvm_m⟩ :=
    allocCall_vm_of_pureSeg hcpu1 hcpu_m hseg_m (by simp [arm64_norm]) (by simp [arm64_norm])
  refine SepWPp.weaken_pre ?_ (hcont sm (hcpu_m.pc_eq.trans budgetWriteChar_reserve_pc)
    (hcpu_m.status_eq.trans (by simpa [arm64_norm] using hrun1'))
    (hcpu_m.sp_eq.trans (by simp [arm64_norm, hsp1_in]))
    (by rw [hcpu_m.readReg64 .lr]; simp [arm64_norm])
    (by rw [hcpu_m.readReg64 .x0]; simp [arm64_norm])
    (by rw [hcpu_m.readReg64 .x1]; simp [arm64_norm])
    (by rw [hcpu_m.readReg64 .x2]; simp [arm64_norm])
    (by rw [hcpu_m.readReg64]; simp [arm64_norm])
    (by rw [hcpu_m.readReg64]; simp [arm64_norm])
    (by rw [hcpu_m.readReg64]; simp [arm64_norm])
    (by rw [hcpu_m.readReg64]; simp [arm64_norm])
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        · rw [hcpu_m.readReg64]; simpa [arm64_norm] using hcpu1.readReg64 _)
    (hcpu_m.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs s1').trans
      hcpu1.calleeSavedVRegs))
    hacp_m hcl_m)
  rw [← A.pool_transport _ s0 sm hvm_m]
  dsimp only [budgetWriterSavedSlots]
  simp only [hsp1_in, hcpu1.readReg64, bv_lin_norm]
  sep_entail))

set_option maxHeartbeats 1200000 in
private theorem budgetWriteChar_slow_entry [AllocPlacement] (A : RustAllocBudget)
    {keep : Nat → Bool} (hk6 : keep 6 = true) {P : Program}
    {ev_st : A.σ} {out cap : BitVec 64} {len : Nat} {c : BitVec 32}
    {F : SepProp} {s0 : State} {ret : BitVec 64}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hext6 : LibBlockNoExtern allocMultiLib AllocPlacement.mpl P 6)
    (hcl0 : allocMultiLib.CodeLoadedWhere keep AllocPlacement.mpl s0.mem)
    (hpc : s0.pc = allocPl06.base) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = out) (hx1 : s0.readReg32 .x1 = c)
    (hlen_le : len ≤ cap.toNat) (hcap_lt : cap.toNat < 2 ^ 63)
    (hgt : cap.toNat - len < charUtf8Len c)
    {w0 w1 w2 w3 w4 w5 : BitVec 64}
    (hcont : ∀ sm : State,
      sm.pc = allocMultiLib.resolve AllocPlacement.mpl allocDoReserveSym →
      sm.status = .Running → sm.sp = s0.sp - 48#64 →
      sm.readReg64 .lr = allocPl06.base + (reloc_call_off% allocLib06.text.relocs
        "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [rust_alloc]" + 4#64) →
      sm.readReg64 .x0 = out → sm.readReg64 .x1 = BitVec.ofNat 64 len →
      sm.readReg64 .x2 = BitVec.ofNat 64 (charUtf8Len c) →
      sm.readReg64 (.gpr 19#5) = out → sm.readReg64 (.gpr 20#5) = BitVec.ofNat 64 len →
      sm.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (charUtf8Len c) →
      sm.readReg64 (.gpr 22#5) = c.zeroExtend 64 →
      BudgetWriterHighGprs s0 sm → calleeSavedVRegs sm = calleeSavedVRegs s0 →
      AllocCallPreserved s0 sm →
      allocMultiLib.CodeLoadedWhere keep AllocPlacement.mpl sm.mem →
      SepWPp P ret sm
        (stackAt (s0.sp - 48#64) defaultAllocReserveStack ∗ budgetWriterSavedSlots s0 ∗
          (out ↦₆₄ cap) ∗ ((out + 16#64) ↦₆₄ BitVec.ofNat 64 len) ∗ A.pool ev_st sm ∗ F)
        Q Qp oom) :
    SepWPp P ret s0
      (stackAt (s0.sp - 48#64) defaultAllocReserveStack ∗
        (((s0.sp - 48#64) ↦₆₄ w0) ∗ ((s0.sp - 40#64) ↦₆₄ w1) ∗ ((s0.sp - 32#64) ↦₆₄ w2) ∗
          ((s0.sp - 24#64) ↦₆₄ w3) ∗ ((s0.sp - 16#64) ↦₆₄ w4) ∗ ((s0.sp - 8#64) ↦₆₄ w5)) ∗
        (out ↦₆₄ cap) ∗ ((out + 16#64) ↦₆₄ BitVec.ofNat 64 len) ∗ A.pool ev_st s0 ∗ F)
      Q Qp oom := by
  have hk4 := charUtf8Len_bounds c
  have hbhi : ((cap - BitVec.ofNat 64 len).ult (BitVec.ofNat 64 (charUtf8Len c))) = true := by
    rw [budgetWriteChar_bhi_cond hlen_le hcap_lt (by omega)]; exact decide_eq_true hgt
  apply sepWPp_seg_lib_block_pureWhere (lib := allocMultiLib) 6 ⟨by decide, hk6⟩ hext6 allocBlockNoSvc0_06 hcl0
    (mid := allocMultiLib.resolve AllocPlacement.mpl allocDoReserveSym)
  intro s1' hcpu1
  change SepWP (allocPC06.rebase allocPl06.base (fun _ => none)) _ _ _ _
  have hpc1' : s1'.pc = allocPl06.base := hcpu1.pc_eq.trans hpc
  have hrun1' : s1'.status = .Running := hcpu1.status_eq.trans hrun
  have hsp1_in : s1'.sp = s0.sp := hcpu1.sp_eq
  have hsp1' : s1'.spAligned = true := by rw [hcpu1.spAligned]; exact hsp0
  have hx0_1' : s1'.readReg64 (.gpr 0#5) = out := (hcpu1.readReg64 .x0).trans hx0
  have hx1s : BitVec.setWidth 32 (s1'.readReg64 (.gpr 1#5)) = c := by
    rw [hcpu1.readReg64 .x1]; exact hx1
  have hx1t : (s1'.readReg64 (.gpr 1#5)).truncate 32 = c := hx1s
  have hbhi' : ∀ k : Nat, charUtf8Len c = k →
      ((cap - BitVec.ofNat 64 len).ult (BitVec.ofNat 64 k)) = true := fun _ h => h ▸ hbhi
  wp_conv_pre => simp only [← hsp1_in]
  by_cases hc1 : c.toNat < 128
  · have hlen : charUtf8Len c = 1 := by simp [charUtf8Len, hc1]
    have hult128 : c.ult 128#32 = true := by rw [char_ult_iff (by decide)]; exact decide_eq_true hc1
    have hule128 : (128#32).ule c = false := by rw [char_ule_iff (by decide)]; exact decide_eq_false (by omega)
    have hbhi1 := hbhi' 1 hlen
    rw [hlen] at hcont
    wp_sym_steps
    wc_slow_close
  · have hult128 : c.ult 128#32 = false := by rw [char_ult_iff (by decide)]; exact decide_eq_false hc1
    have hule128 : (128#32).ule c = true := by rw [char_ule_iff (by decide)]; exact decide_eq_true (by omega)
    by_cases hc2 : c.toNat < 2048
    · have hlen : charUtf8Len c = 2 := by simp [charUtf8Len, hc1, hc2]
      have hule2048 : (2048#32).ule c = false := by
        rw [char_ule_iff (by decide)]; exact decide_eq_false (by omega)
      have hult2048 : c.ult 2048#32 = true := by rw [char_ult_iff (by decide)]; exact decide_eq_true hc2
      have hbhi2 := hbhi' 2 hlen
      rw [hlen] at hcont
      wp_sym_steps
      wc_slow_close
    · have hule2048 : (2048#32).ule c = true := by
        rw [char_ule_iff (by decide)]; exact decide_eq_true (by omega)
      have hult2048 : c.ult 2048#32 = false := by rw [char_ult_iff (by decide)]; exact decide_eq_false hc2
      by_cases hc3 : c.toNat < 65536
      · have hlen : charUtf8Len c = 3 := by simp [charUtf8Len, hc1, hc2, hc3]
        have hule65536 : (65536#32).ule c = false := by
          rw [char_ule_iff (by decide)]; exact decide_eq_false (by omega)
        have hult65536 : c.ult 65536#32 = true := by rw [char_ult_iff (by decide)]; exact decide_eq_true hc3
        have hbhi3 := hbhi' 3 hlen
        rw [hlen] at hcont
        wp_sym_steps
        wc_slow_close
      · have hlen : charUtf8Len c = 4 := by simp [charUtf8Len, hc1, hc2, hc3]
        have hule65536 : (65536#32).ule c = true := by
          rw [char_ule_iff (by decide)]; exact decide_eq_true (by omega)
        have hult65536 : c.ult 65536#32 = false := by rw [char_ult_iff (by decide)]; exact decide_eq_false hc3
        have hbhi4 := hbhi' 4 hlen
        rw [hlen] at hcont
        wp_sym_steps
        wc_slow_close

private theorem wcAppendEvents_of_gt {st : FmtBuf} {n : Nat}
    (hgt : ¬ st.bytes.length + n ≤ st.cap.toNat) :
    stringAppendEvents st n =
      st.evs ++ stringGrowStepEvents st.cap (stringGrowCap st.cap.toNat st.bytes.length n) := by
  simp [stringAppendEvents, stringGrowStepEvents, hgt]

private theorem wcReadReg32_x0_zero {s : State} (h : s.readReg64 .x0 = 0#64) :
    s.readReg32 .x0 = 0#32 := by
  simp [State.readReg32, State.readReg64] at h ⊢; rw [h]; rfl

set_option maxHeartbeats 1200000 in
/-- Budgeted `<String as fmt::Write>::write_char` (`allocBlocks[6]`) meets `fmtWriterCharSpec`
    over `fmtInnerBudgetW A st0 va R t0 out`. -/
theorem budgetWriteChar_fmtWriterChar_ok (A : RustAllocBudget)
    {keep : Nat → Bool} (hk1 : keep 1 = true) (hk2 : keep 2 = true) (hk6 : keep 6 = true)
    {mpl : MultiPlacement} (hpl : allocMultiLib.Placeable mpl) {P : Program}
    (st0 : A.σ) (va : StringWriteAddrs) (R : SepProp) (t0 : State)
    (stackBytes : Nat) (out : BitVec 64) (c : BitVec 32)
    (hext6 : LibBlockNoExtern allocMultiLib mpl P 6)
    (hext1 : LibBlockNoExtern allocMultiLib mpl P 1)
    (hext2 : LibBlockNoExtern allocMultiLib mpl P 2)
    (hstk : stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hpanic : P.externAt? (allocMultiLib.resolve mpl allocBudgetHandleErrorSym) = some Rust.panicked)
    (hshim : subroutine_ok P (allocMultiLib.resolve mpl allocRustNoAllocShimSym) budgetAllocShimSpec)
    (halloc : subroutine_ok P (allocMultiLib.resolve mpl allocRustAllocSym) (rustBudgetAllocSpec A))
    (hrealloc : subroutine_ok P (allocMultiLib.resolve mpl allocRustReallocSym)
      (rustBudgetReallocSpec A)) :
    subroutine_ok P (allocMultiLib.resolve mpl allocStringWriteCharSym)
      (allocMultiLib.withCodeLoadedWhere keep mpl
        (fmtWriterCharSpec (fmtInnerBudgetW A st0 va R t0 out)
          StringBufCharStep (StringBufWriterPanic t0) (StringBufWriterOom A st0)
          stackBytes out c)) := by
  letI : AllocPlacement := ⟨mpl, hpl⟩
  rw [allocResolve_eq_base hpl 6 allocStringWriteCharSym (by decide) allocWriteChar_lookup]
  apply subroutine_ok_of_sepWPp_init
  intro st R₀ s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoadedWhere, fmtWriterCharSpec, fmtInnerBudgetW] at hpre ⊢
  rw [sepConj_comm _ ⌜allocMultiLib.CodeLoadedWhere keep mpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hpre⟩
  have hpure0 : s0.mem ⊨ ⌜IoCallFrame t0 s0 ∧ s0.fs = t0.fs ∧ s0.trace = t0.trace⌝ ∗
      (vecHeader out st.cap st.ptr (BitVec.ofNat 64 st.bytes.length) ∗
        fmtBufVecAt A st.cap st.ptr st.bytes ∗ A.pool (A.stepEvents st.evs st0) s0 ∗
        stringWriteVtableAt va ∗ R ∗ stackFrameAt s0.sp stackBytes ∗ R₀) :=
    Satisfies.mono (by sep_entail) hpre
  rw [satisfies_pure_sepConj] at hpure0
  rcases hpure0 with ⟨hio0, hmem⟩
  have ⟨hbs_le, hcap_lt, hptr_ne⟩ :
      st.bytes.length ≤ st.cap.toNat ∧ st.cap.toNat < 2 ^ 63 ∧ st.ptr ≠ 0#64 :=
    satisfies_fmtBufVecAt_bounds (m := s0.mem)
    (R := vecHeader out st.cap st.ptr (BitVec.ofNat 64 st.bytes.length) ∗
      A.pool (A.stepEvents st.evs st0) s0 ∗ stringWriteVtableAt va ∗ R ∗
      stackFrameAt s0.sp stackBytes ∗ R₀)
    (Satisfies.mono (by sep_entail) hmem)
  let stkRem : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 stackBytes) (stackBytes - stringWriterStack)
  let Frame : SepProp := stringWriteVtableAt va ∗ R ∗ stkRem
  have hmem' : s0.mem ⊨
      (stackAt s0.sp (48 + defaultAllocReserveStack) ∗
        vecHeader out st.cap st.ptr (BitVec.ofNat 64 st.bytes.length) ∗
        fmtBufVecAt A st.cap st.ptr st.bytes ∗
        A.pool (A.stepEvents st.evs st0) s0 ∗ Frame) ∗ R₀ := by
    rw [← stackAt_eq_stackFrameAt s0.sp stackBytes hstk.2,
      stackAt_shrink s0.sp stackBytes stringWriterStack hstk.1 hstk.2] at hmem
    exact Satisfies.mono (by dsimp only [Frame, stkRem, stringWriterStack]; sep_entail) hmem
  refine ⟨_, hmem', ?_⟩
  conv => arg 4; rw [budgetWriter_stack_split s0.sp]; simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 => SepWPp.exists_elim fun w2 =>
    SepWPp.exists_elim fun w3 => SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun w5 => ?_
  have hk4 := charUtf8Len_bounds c
  by_cases hgt : st.cap.toNat - st.bytes.length < charUtf8Len c
  · have hnle : ¬ st.bytes.length + charUtf8Len c ≤ st.cap.toNat := by omega
    refine SepWPp.weaken_pre (P' :=
        stackAt (s0.sp - 48#64) defaultAllocReserveStack ∗
        (((s0.sp - 48#64) ↦₆₄ w0) ∗ ((s0.sp - 40#64) ↦₆₄ w1) ∗ ((s0.sp - 32#64) ↦₆₄ w2) ∗
          ((s0.sp - 24#64) ↦₆₄ w3) ∗ ((s0.sp - 16#64) ↦₆₄ w4) ∗ ((s0.sp - 8#64) ↦₆₄ w5)) ∗
        (out ↦₆₄ st.cap) ∗ ((out + 16#64) ↦₆₄ BitVec.ofNat 64 st.bytes.length) ∗
        A.pool (A.stepEvents st.evs st0) s0 ∗
        (((out + 8#64) ↦₆₄ st.ptr) ∗ fmtBufVecAt A st.cap st.ptr st.bytes ∗ Frame))
      (by dsimp only [vecHeader]; sep_entail) ?_
    refine budgetWriteChar_slow_entry A hk6 hext6 hcl0 hpc hrun hsp0 hx0 hx1 hbs_le hcap_lt hgt ?_
    intro sm hpc_m hrun_m hsp_m hlr_m hx0_m hx1_m hx2_m hx19_m hx20_m hx21_m hx22_m hgprs_m hvregs_m
      hacp_0m hcl_m
    have hsp_m' : sm.spAligned = true := by
      simp only [State.spAligned]; rw [hsp_m]; exact s0.spAligned_sub 48#64 hsp0
    have hres := budgetDoReserveAndHandle_ok A hk1 hk2 hpl hext1 hext2 ⟨Nat.le_refl _, by decide⟩
      hpanic hshim halloc hrealloc
    refine SepWPp.weaken_pre (P' :=
        stackAt sm.sp defaultAllocReserveStack ∗
        (out ↦₆₄ st.cap) ∗ ((out + 8#64) ↦₆₄ st.ptr) ∗
        fmtBufVecAt A st.cap st.ptr st.bytes ∗ A.pool (A.stepEvents st.evs st0) sm ∗
        budgetWriterSavedSlots s0 ∗ ((out + 16#64) ↦₆₄ BitVec.ofNat 64 st.bytes.length) ∗ Frame)
      (by rw [hsp_m]; sep_entail) ?_
    apply (SepWPp.call_wpp hres
      (x := (out, st.ptr, st.cap, st.bytes, charUtf8Len c, A.stepEvents st.evs st0))
      hpc_m hrun_m hsp_m' hlr_m
      (hoom := fun sf_oom R' _ hm_oom => by
        have hm' := Satisfies.drop_mid hm_oom
        dsimp only [allocWithCodeLoadedWhere, MultiPlacedLib.withCodeLoadedWhere, budgetDoReserveSpec] at hm'
        rw [satisfies_pure_sepConj] at hm' ⊢
        refine ⟨fun hfit => hm'.1.1 ?_, hm'.2⟩
        rw [wcAppendEvents_of_gt hnle, A.fitsEvents_append] at hfit
        exact hfit.2))
    · intro R' hm'
      dsimp only [allocWithCodeLoadedWhere, MultiPlacedLib.withCodeLoadedWhere, budgetDoReserveSpec]
      rw [sepConj_comm _ ⌜allocMultiLib.CodeLoadedWhere keep mpl sm.mem⌝, sepConj_assoc,
        satisfies_pure_sepConj]
      refine ⟨hcl_m, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0_m, hx1_m, hx2_m, by omega, hgt⟩, Satisfies.mono (by sep_frame) hm'⟩
    · intro _ _ _ _ h; exact not_satisfies_false_sepConj h
    · intro sf_pan _ _ hm_pan
      dsimp only [allocWithCodeLoadedWhere, MultiPlacedLib.withCodeLoadedWhere, budgetDoReserveSpec] at hm_pan
      exact allowPanic_frame
        (fun ⟨hfs, htr, hp⟩ => ⟨hfs.trans (hacp_0m.1.trans hio0.2.1),
          htr.trans (hacp_0m.2.1.trans hio0.2.2), by omega, hp⟩) hm_pan
    · intro sf_res hpc_sfres hrun_sfres hsp_sfres hcs_sfres
      apply SepWPp.of_sepWP_ret
      dsimp only [allocWithCodeLoadedWhere, MultiPlacedLib.withCodeLoadedWhere, budgetDoReserveSpec]
      wp_conv_pre => simp only [sepConj_assoc]
      apply SepWP.pure_elim; intro hcl_sfres
      wp_conv_pre => rw [sepExists_sepConj_left]
      refine SepWP.exists_elim fun newPtr => ?_
      wp_conv_pre => simp only [sepConj_assoc]
      apply SepWP.pure_elim; rintro ⟨hacp_res, hgrow_lt63⟩
      generalize hgc : stringGrowCap st.cap.toNat st.bytes.length (charUtf8Len c) = growCap at hgrow_lt63 ⊢
      have hgrow_toNat : (BitVec.ofNat 64 growCap).toNat = growCap := by
        simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : growCap < 2 ^ 64)]
      have hfit_grow : charUtf8Len c ≤ (BitVec.ofNat 64 growCap).toNat - st.bytes.length := by
        have : st.bytes.length + charUtf8Len c ≤ growCap := by rw [← hgc]; unfold stringGrowCap; omega
        rw [hgrow_toNat]; omega
      have hgrow_ne0 : BitVec.ofNat 64 growCap ≠ 0#64 := by
        intro h; rw [h] at hfit_grow; simp at hfit_grow; omega
      have hcap'_lt : (BitVec.ofNat 64 growCap).toNat < 2 ^ 63 := by rw [hgrow_toNat]; exact hgrow_lt63
      wp_conv_pre => simp only [fmtBufVecAt, hgrow_ne0, ↓reduceIte, sepConj_assoc, sepConj_pure_left_comm]
      apply SepWP.pure_elim; rintro ⟨-, -, hnew_ne⟩
      have hsp_sfres_eq : sf_res.sp = s0.sp - 48#64 := hsp_sfres.trans hsp_m
      have hx19_sfres := hcs_sfres.readReg64_x19.trans hx19_m
      have hx20_sfres := hcs_sfres.readReg64_x20.trans hx20_m
      have hx21_sfres := hcs_sfres.readReg64_x21.trans hx21_m
      have hx22_sfres := hcs_sfres.readReg64_x22.trans hx22_m
      have hgprs_sfres := hgprs_m.trans (BudgetWriterHighGprs.of_calleeSaved hcs_sfres)
      have hvregs_sfres := hcs_sfres.vregs.trans hvregs_m
      have hev_eq : A.stepEvents (stringGrowStepEvents st.cap growCap) (A.stepEvents st.evs st0) =
          A.stepEvents (stringAppendEvents st (charUtf8Len c)) st0 := by
        rw [wcAppendEvents_of_gt hnle, A.stepEvents_append, hgc]
      refine SepWP.mono (oom := fun _ => ⌜False⌝) ?_ (fun _ _ _ _ h => h)
      refine SepWP.weaken_pre (by
          rw [hsp_m, hev_eq]; dsimp only [vecHeader, budgetWriterSavedSlots, Frame, stkRem]
          sep_entail) <|
        budgetWriteChar_slow_tail (Frame := Frame)
          (ev_st := A.stepEvents (stringAppendEvents st (charUtf8Len c)) st0)
          (out := out) (cap' := BitVec.ofNat 64 growCap) (ptr' := newPtr) (bs := st.bytes) (c := c)
          A hk6 hext6 hcl_sfres hpc_sfres hrun_sfres hsp0 hsp_sfres_eq hx19_sfres hx20_sfres
          hx21_sfres hx22_sfres hgprs_sfres hvregs_sfres hcap'_lt hnew_ne hfit_grow ?_
      intro sf hsp_f hcs_f hacp_jf hx0_f _Pre_f hent
      refine ⟨fun hm_out => Satisfies.mono (sepConj_mono_left (Entails.trans hent ?_)) hm_out, hsp_f, hcs_f⟩
      let st' : FmtBuf :=
        { bytes := st.bytes ++ encodeUtf8Char c, cap := BitVec.ofNat 64 growCap,
          ptr := newPtr, evs := stringAppendEvents st (charUtf8Len c) }
      have happ : StringBufCharStep st c true st' :=
        ⟨rfl, rfl, by simp [st', stringNextCap, hnle, hgc], by simp [st'],
          fun h => by rw [encodeUtf8Char_length] at h; exact absurd h hnle⟩
      have hx0r : sf.readReg32 .x0 = (if true = true then 0#32 else 1#32) := by
        exact wcReadReg32_x0_zero hx0_f
      refine Entails.sepExists_right true (Entails.sepExists_right st' ?_)
      dsimp only [st']
      rw [pure_sepConj_of_true (And.intro hx0r happ),
        pure_sepConj_of_true (budgetIoCall_of_acp hio0
          (allocCallPreserved_trans hacp_0m (allocCallPreserved_trans hacp_res hacp_jf))),
        ← stackAt_eq_stackFrameAt s0.sp stackBytes hstk.2,
        stackAt_shrink s0.sp stackBytes stringWriterStack hstk.1 hstk.2]
      dsimp only [Frame, stkRem, stringWriterStack]
      sep_entail
  · have hfit : charUtf8Len c ≤ st.cap.toNat - st.bytes.length := Nat.le_of_not_lt hgt
    have hle_sum : st.bytes.length + charUtf8Len c ≤ st.cap.toNat := by omega
    have hcap_ne0 : st.cap ≠ 0#64 := by
      intro h; rw [h] at hle_sum; simp at hle_sum; omega
    apply SepWPp.of_sepWP_ret
    refine SepWP.mono (oom := fun _ => ⌜False⌝) ?_ (fun _ _ _ _ h => h)
    refine SepWP.weaken_pre (P' :=
        stackAt (s0.sp - 48#64) defaultAllocReserveStack ∗
        (((s0.sp - 48#64) ↦₆₄ w0) ∗ ((s0.sp - 40#64) ↦₆₄ w1) ∗ ((s0.sp - 32#64) ↦₆₄ w2) ∗
          ((s0.sp - 24#64) ↦₆₄ w3) ∗ ((s0.sp - 16#64) ↦₆₄ w4) ∗ ((s0.sp - 8#64) ↦₆₄ w5)) ∗
        vecHeader out st.cap st.ptr (BitVec.ofNat 64 st.bytes.length) ∗
        A.live st.ptr st.cap.toNat 1 ∗ (st.ptr ↦ₛ st.bytes) ∗
        memRegion (st.ptr + BitVec.ofNat 64 st.bytes.length) (st.cap.toNat - st.bytes.length) ∗
        A.pool (A.stepEvents st.evs st0) s0 ∗ Frame)
      (by
        simp only [fmtBufVecAt, hcap_ne0, ↓reduceIte,
          pure_sepConj_of_true (And.intro hbs_le (And.intro hcap_lt hptr_ne))]
        sep_entail) ?_
    refine budgetWriteChar_fast A hk6 hext6 hcl0 hpc hrun hsp0 hx0 hx1 hbs_le hcap_lt hptr_ne hfit ?_
    intro sf hsp_f hcs_f hacp_f hx0_f _Pre_f hent
    refine ⟨fun hm_out => Satisfies.mono (sepConj_mono_left (Entails.trans hent ?_)) hm_out, hsp_f, hcs_f⟩
    let st' : FmtBuf :=
      { bytes := st.bytes ++ encodeUtf8Char c, cap := st.cap, ptr := st.ptr, evs := st.evs }
    have happ : StringBufCharStep st c true st' :=
      ⟨rfl, rfl, by simp [st', stringNextCap, hle_sum, BitVec.ofNat_toNat, BitVec.setWidth_eq],
        by simp [st', stringAppendEvents, hle_sum], fun _ => rfl⟩
    have hx0r : sf.readReg32 .x0 = (if true = true then 0#32 else 1#32) := by
      exact wcReadReg32_x0_zero hx0_f
    refine Entails.sepExists_right true (Entails.sepExists_right st' ?_)
    dsimp only [st']
    rw [pure_sepConj_of_true (And.intro hx0r happ),
      pure_sepConj_of_true (budgetIoCall_of_acp hio0 hacp_f),
      ← stackAt_eq_stackFrameAt s0.sp stackBytes hstk.2,
      stackAt_shrink s0.sp stackBytes stringWriterStack hstk.1 hstk.2]
    dsimp only [Frame, stkRem, stringWriterStack]
    sep_entail

theorem stringBudgetFmtWriterOk (A : RustAllocBudget)
    {keep : Nat → Bool} (hk1 : keep 1 = true) (hk2 : keep 2 = true)
    (hk6 : keep 6 = true) (hk7 : keep 7 = true)
    {mpl : MultiPlacement} (hpl : allocMultiLib.Placeable mpl) {P : Program}
    (hcl : ∀ m, P.CodeLoaded m → allocMultiLib.CodeLoadedWhere keep mpl m)
    (st0 : A.σ) (va : StringWriteAddrs) (R : SepProp) (t0 : State)
    (stackBytes : Nat) (out : BitVec 64)
    (hws : va.writeStr = allocMultiLib.resolve mpl allocStringWriteStrSym)
    (hwc : va.writeChar = allocMultiLib.resolve mpl allocStringWriteCharSym)
    (hext6 : LibBlockNoExtern allocMultiLib mpl P 6)
    (hext7 : LibBlockNoExtern allocMultiLib mpl P 7)
    (hext1 : LibBlockNoExtern allocMultiLib mpl P 1)
    (hext2 : LibBlockNoExtern allocMultiLib mpl P 2)
    (hstk : stringWriterStack ≤ stackBytes ∧ stackBytes ≤ 2 ^ 64)
    (hpanic : P.externAt? (allocMultiLib.resolve mpl allocBudgetHandleErrorSym) = some Rust.panicked)
    (hmemcpy : ∀ ro, subroutine_ok P (allocMultiLib.resolve mpl "memcpy") (budgetMemcpySpec ro))
    (hshim : subroutine_ok P (allocMultiLib.resolve mpl allocRustNoAllocShimSym) budgetAllocShimSpec)
    (halloc : subroutine_ok P (allocMultiLib.resolve mpl allocRustAllocSym) (rustBudgetAllocSpec A))
    (hrealloc : subroutine_ok P (allocMultiLib.resolve mpl allocRustReallocSym)
      (rustBudgetReallocSpec A)) :
    FmtWriterOk P (fmtInnerBudgetW A st0 va R t0 out) StringBufStrStep StringBufCharStep
      (StringBufWriterPanic t0) (StringBufWriterOom A st0)
      stackBytes out va.vtable va.writeStr va.writeChar where
  transport st s s' hf := fmtInnerBudgetW_transport A st0 va R t0 out st s s' hf
  slots st s := fmtInnerBudgetW_slots A st0 va R t0 out st s
  write_str ro ptr bs := hws ▸ subroutine_ok_of_withCodeLoadedWhere_imp hcl
    (budgetWriteStr_fmtWriterStr_ok A hk1 hk2 hk7 hpl st0 va R t0 stackBytes out ro ptr bs
      hext7 hext1 hext2 hstk hpanic (hmemcpy ro) hshim halloc hrealloc)
  write_char c := hwc ▸ subroutine_ok_of_withCodeLoadedWhere_imp hcl
    (budgetWriteChar_fmtWriterChar_ok A hk1 hk2 hk6 hpl st0 va R t0 stackBytes out c
      hext6 hext1 hext2 hstk hpanic hshim halloc hrealloc)

end WriterHelpers

end VerifiedLibraries.RustStd
