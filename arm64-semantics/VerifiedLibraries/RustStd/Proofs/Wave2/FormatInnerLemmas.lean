/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Spec
public import VerifiedLibraries.RustStd.Spec.AllocFormatInner
public import VerifiedLibraries.RustStd.Proofs.Wave2.FormatInnerSym
public import VerifiedLibraries.RustStd.Proofs.ExecSeg
public import VerifiedLibraries.RustStd.Proofs.VecBridge

/-!
# Helper Lemmas for `alloc::fmt::format::format_inner`

Vtable placement projection (`allocStringWriteAddrs`) and `InElf` vtable cell discharge, `SepWPp`
bind/call and pure-segment lifters refreshing `allocMultiLib.CodeLoaded`, and `decodeFmtTemplate`
bounds and placeholder-skip arithmetic.
-/

@[expose] public section

set_option autoImplicit false

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup

/-! ## `<String as fmt::Write>` vtable placement and `InElf` discharge -/

/-- Concrete `StringWriteAddrs` for a placement `mpl` of `allocMultiLib` (`vtable` at
    `mpl.ρ stringWriteVtableSym`, `writeStr` at block `7`, `writeChar` at block `6`, and
    `writeFmt` at block `8`). -/
def allocStringWriteAddrs (mpl : Obj.MultiPlacement) : StringWriteAddrs where
  vtable := mpl.ρ stringWriteVtableSym
  writeStr := mpl.base 7
  writeChar := mpl.base 6
  writeFmt := mpl.base 8

@[simp] theorem allocStringWriteAddrs_vtable (mpl : Obj.MultiPlacement) :
    (allocStringWriteAddrs mpl).vtable = mpl.ρ stringWriteVtableSym := rfl

@[simp] theorem allocStringWriteAddrs_writeStr (mpl : Obj.MultiPlacement) :
    (allocStringWriteAddrs mpl).writeStr = mpl.base 7 := rfl

@[simp] theorem allocStringWriteAddrs_writeChar (mpl : Obj.MultiPlacement) :
    (allocStringWriteAddrs mpl).writeChar = mpl.base 6 := rfl

@[simp] theorem allocStringWriteAddrs_writeFmt (mpl : Obj.MultiPlacement) :
    (allocStringWriteAddrs mpl).writeFmt = mpl.base 8 := rfl

theorem allocStringWriteAddrs_vtable_eq_resolve (mpl : Obj.MultiPlacement) :
    (allocStringWriteAddrs mpl).vtable = allocMultiLib.resolve mpl stringWriteVtableSym := by
  simp [allocStringWriteAddrs, Obj.MultiPlacedLib.resolve, stringWriteVtableSym,
    lookupBlockSym_vtable34_none]

theorem lookupBlockSym_writeStr :
    Obj.lookupBlockSym fmtInnerWriteStrBlockSym allocMultiLib.blocks = some (7, 0) := by
  decide

theorem lookupBlockSym_writeChar :
    Obj.lookupBlockSym fmtInnerWriteCharBlockSym allocMultiLib.blocks = some (6, 0) := by
  decide

theorem lookupBlockSym_writeFmt :
    Obj.lookupBlockSym fmtInnerWriteFmtBlockSym allocMultiLib.blocks = some (8, 0) := by
  decide

theorem allocStringWriteAddrs_writeStr_eq_fnAddr (mpl : Obj.MultiPlacement) :
    (allocStringWriteAddrs mpl).writeStr = allocMultiLib.fnAddr mpl fmtInnerWriteStrBlockSym := by
  simp [allocStringWriteAddrs, Obj.MultiPlacedLib.fnAddr, lookupBlockSym_writeStr]

theorem allocStringWriteAddrs_writeChar_eq_fnAddr (mpl : Obj.MultiPlacement) :
    (allocStringWriteAddrs mpl).writeChar = allocMultiLib.fnAddr mpl fmtInnerWriteCharBlockSym := by
  simp [allocStringWriteAddrs, Obj.MultiPlacedLib.fnAddr, lookupBlockSym_writeChar]

theorem allocStringWriteAddrs_writeFmt_eq_fnAddr (mpl : Obj.MultiPlacement) :
    (allocStringWriteAddrs mpl).writeFmt = allocMultiLib.fnAddr mpl fmtInnerWriteFmtBlockSym := by
  simp [allocStringWriteAddrs, Obj.MultiPlacedLib.fnAddr, lookupBlockSym_writeFmt]

private theorem bytesLE8_eq_unpack64 (v : BitVec 64) :
    Obj.bytesLE 8 v = unpack64 v := rfl

/-- `allocData[2]` (`"rust_alloc:.data.rel.ro..Lanon.34"`) has 48 patched bytes whose trailing
    24 bytes (`+0x18`, `+0x20`, `+0x28`) are the little-endian 64-bit addresses `mpl.base 7`,
    `mpl.base 6`, `mpl.base 8`. -/
theorem allocVtableData2_patchedData_split (mpl : Obj.MultiPlacement) :
    let d2 := allocMultiLib.data[2]
    let bs := allocMultiLib.patchedData mpl d2
    bs = bs.take 24 ++ unpack64 (mpl.base 7) ++ unpack64 (mpl.base 6) ++ unpack64 (mpl.base 8) ∧
      (bs.take 24).length = 24 := by
  have hd : allocMultiLib.data[2] =
      { sym := stringWriteVtableSym
        align := 8
        readOnly := false
        bytes := allocPlacedData2
        zeroTail := 0
        relocs :=
          [(allocMultiLib.data[2]).relocs[0],
           { off := 24, kind := .abs64, sym := fmtInnerWriteStrBlockSym, addend := 0 },
           { off := 32, kind := .abs64, sym := fmtInnerWriteCharBlockSym, addend := 0 },
           { off := 40, kind := .abs64, sym := fmtInnerWriteFmtBlockSym, addend := 0 }] } := by
    decide
  have hk0 : (allocMultiLib.data[2]).relocs[0].kind = .abs64 ∧
      (allocMultiLib.data[2]).relocs[0].off = 0 := by decide
  have hres7 : allocMultiLib.resolve mpl fmtInnerWriteStrBlockSym = mpl.base 7 := by
    simp [Obj.MultiPlacedLib.resolve, lookupBlockSym_writeStr]
  have hres6 : allocMultiLib.resolve mpl fmtInnerWriteCharBlockSym = mpl.base 6 := by
    simp [Obj.MultiPlacedLib.resolve, lookupBlockSym_writeChar]
  have hres8 : allocMultiLib.resolve mpl fmtInnerWriteFmtBlockSym = mpl.base 8 := by
    simp [Obj.MultiPlacedLib.resolve, lookupBlockSym_writeFmt]
  dsimp only
  rw [hd]
  unfold MultiPlacedLib.patchedData
  dsimp only [allocPlacedData2, List.foldl, List.replicate, List.append_nil,
    MultiPlacedLib.patchDataReloc]
  rw [hk0.1, hk0.2]
  dsimp only [Obj.addSignedAddr]
  simp only [bytesLE8_eq_unpack64, hres7, hres6, hres8]
  dsimp only [unpack64, List.take, List.drop, List.append, List.length]
  exact ⟨rfl, rfl⟩

/-- Frame-preserving freeze from writable `allocData[2]` bytes to `stringWriteVtableAt` (retaining
    the 24-byte header `[0, 0x18)` read-only alongside `stringWriteVtableAt`). -/
theorem satisfies_stringWriteVtableAt_of_vtableBytes {m : Memory} (mpl : Obj.MultiPlacement)
    {R : SepProp}
    (hm : m ⊨ ((mpl.ρ stringWriteVtableSym) ↦ₛ
      allocMultiLib.patchedData mpl (allocMultiLib.data[2])) ∗ R) :
    m ⊨ stringWriteVtableAt (allocStringWriteAddrs mpl) ∗
      (((mpl.ρ stringWriteVtableSym) ↦ᵣ
        (allocMultiLib.patchedData mpl (allocMultiLib.data[2])).take 24) ∗ R) := by
  have hm_ro : m ⊨ ((mpl.ρ stringWriteVtableSym) ↦ᵣ
      allocMultiLib.patchedData mpl (allocMultiLib.data[2])) ∗ R :=
    Satisfies.pointsToBytes_to_ro hm
  obtain ⟨hsplit, hlen24⟩ := allocVtableData2_patchedData_split mpl
  rw [hsplit] at hm_ro
  simp only [List.append_assoc, pointsToBytesRO_append, hlen24] at hm_ro
  have hlen_u7 : (unpack64 (mpl.base 7)).length = 8 := by simp [unpack64]
  have hlen_u6 : (unpack64 (mpl.base 6)).length = 8 := by simp [unpack64]
  rw [hlen_u7, hlen_u6] at hm_ro
  simp only [← pointsTo64RO_eq_pointsToBytesRO] at hm_ro
  have ha18 : mpl.ρ stringWriteVtableSym + BitVec.ofNat 64 24 =
      (allocStringWriteAddrs mpl).vtable + 0x18#64 := rfl
  have ha20 : ((allocStringWriteAddrs mpl).vtable + 0x18#64) + BitVec.ofNat 64 8 =
      (allocStringWriteAddrs mpl).vtable + 0x20#64 := by
    simp only [allocStringWriteAddrs_vtable]; bv_arith
  have ha28 : ((allocStringWriteAddrs mpl).vtable + 0x20#64) + BitVec.ofNat 64 8 =
      (allocStringWriteAddrs mpl).vtable + 0x28#64 := by
    simp only [allocStringWriteAddrs_vtable]; bv_arith
  rw [ha18] at hm_ro
  rw [ha20] at hm_ro
  rw [ha28] at hm_ro
  unfold stringWriteVtableAt
  simp only [allocStringWriteAddrs_writeStr, allocStringWriteAddrs_writeChar,
    allocStringWriteAddrs_writeFmt]
  revert hm_ro; intro hm_ro; sep_frame

/-- Concrete `InElf` + `loadState` vtable cell-discharge lemma: any loaded ELF containing
    `allocMultiLib` at a `DataDisjoint` placement `mpl` satisfies
    `stringWriteVtableAt (allocStringWriteAddrs mpl)` (together with the rest of `allocMultiLib`'s
    initial data). -/
theorem stringWriteVtableAt_of_inElf {mpl : Obj.MultiPlacement}
    {img : ElfImage} {inputs : ProcessInputs} {s : State}
    (hpl : allocMultiLib.Placeable mpl)
    (hin : allocMultiLib.InElf img mpl)
    (hload : img.loadState inputs = .ok s)
    (hdisj : allocMultiLib.DataDisjoint mpl) :
    ∃ Rest : SepProp,
      s.mem ⊨ stringWriteVtableAt (allocStringWriteAddrs mpl) ∗ Rest := by
  have hinit := allocMultiLib.satisfies_dataInit_of_inElf hpl hin hload (by decide) hdisj
  let f : SymDataInfo → SepProp := fun d =>
    if d.readOnly then pointsToBytesRO (mpl.ρ d.sym) (allocMultiLib.patchedData mpl d)
    else pointsToBytes (mpl.ρ d.sym) (allocMultiLib.patchedData mpl d)
  have hd2_mem : allocMultiLib.data[2] ∈ allocMultiLib.data := List.getElem_mem (by decide)
  obtain ⟨Rest0, hfocus⟩ := Obj.sepAll_focus (List.mem_map_of_mem (f := f) hd2_mem)
  change s.mem ⊨ Obj.sepAll (allocMultiLib.data.map f) at hinit
  rw [hfocus] at hinit
  have hf_d2 : f (allocMultiLib.data[2]) =
      ((mpl.ρ stringWriteVtableSym) ↦ₛ allocMultiLib.patchedData mpl (allocMultiLib.data[2])) := rfl
  rw [hf_d2] at hinit
  exact ⟨_, satisfies_stringWriteVtableAt_of_vtableBytes mpl hinit⟩

/-! ## `SepWPp` bind and call refreshing `allocMultiLib.CodeLoaded` -/

/-- Sequence a `SepWPp` call/segment up to `mid` with a continuation at `mid`, refreshing
    `allocMultiLib.CodeLoaded mpl` via `Steps.keepsFrozen`. -/
theorem sepWPp_bind_alloc_codeLoaded {mpl : MultiPlacement} {P : Program}
    {mid ret : BitVec 64} {s : State} {Pre : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : allocMultiLib.CodeLoaded mpl s.mem)
    (h : SepWPp P mid s Pre
      (fun sm Pm => allocMultiLib.CodeLoaded mpl sm.mem → SepWPp P ret sm Pm Q Qp oom) Qp oom) :
    SepWPp P ret s Pre Q Qp oom := by
  intro R hm hL_P
  obtain ⟨sm, hsteps1, hout1⟩ := h R hm hL_P
  rcases hout1 with ⟨_, _, Pm, hmm, hcont⟩ | hpan | hoom_m
  · have hcl_m : allocMultiLib.CodeLoaded mpl sm.mem := hcl.of_keepsFrozen hsteps1.keepsFrozen
    obtain ⟨sf, hsteps2, hout2⟩ := hcont hcl_m R hmm (hsteps1.codeLoaded hL_P)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact ⟨sm, hsteps1, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hsteps1, Or.inr (Or.inr hoom_m)⟩

/-- Call a `subroutine_ok` callee in `SepWPp` (handling normal return, panic, and OOM) while
    refreshing `allocMultiLib.CodeLoaded mpl` on normal return. -/
theorem sepWPp_call_alloc_codeLoaded {mpl : MultiPlacement} {P : Program}
    {α : Type} {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α}
    {s : State} {Pre F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : allocMultiLib.CodeLoaded mpl s.mem)
    (hcall : subroutine_ok P entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      allocMultiLib.CodeLoaded mpl sf.mem →
      SepWPp P ret sf (spec.post x s sf ∗ F) Q Qp oom)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R')) :
    SepWPp P ret s Pre Q Qp oom := by
  refine sepWPp_bind_alloc_codeLoaded (mid := ret_pc) hcl ?_
  exact SepWPp.call (x := x) (F := F) hcall hpc hrun hsp hlr hpre hexit hpanic
    (fun sf hpc_f hrun_f hsp_f hcs_f =>
      SepWPp.done hpc_f hrun_f (fun hcl_f => hnext sf hpc_f hrun_f hsp_f hcs_f hcl_f)) hoom

/-! ## Template non-wrap and `decodeFmtTemplate` bounds -/

/-- Any read-only byte slice `p ↦ᵣ tpl` separated from a writable byte `a ↦₈ w` has
    `tpl.length < 2 ^ 64` (since `.ro _` and `.rw _` cannot share address `a`). -/
theorem pointsToBytesRO_length_lt_of_pointsTo8 {m : Memory} {p a : BitVec 64}
    {tpl : List (BitVec 8)} {w : BitVec 8} {R : SepProp}
    (hm : m ⊨ (p ↦ᵣ tpl) ∗ (a ↦₈ w) ∗ R) :
    tpl.length < 2 ^ 64 := by
  apply Classical.byContradiction
  intro hge
  have hge' : 2 ^ 64 ≤ tpl.length := Nat.le_of_not_lt hge
  let k : Nat := (a - p).toNat
  have hk_lt : k < 2 ^ 64 := (a - p).isLt
  have hk_len : k < tpl.length := Nat.lt_of_lt_of_le hk_lt hge'
  have hsplit_list : tpl = tpl.take k ++ tpl[k] :: tpl.drop (k + 1) :=
    (List.take_append_drop k tpl).symm.trans
      (congrArg (tpl.take k ++ ·) (List.drop_eq_getElem_cons hk_len))
  have hro_eq : (p ↦ᵣ tpl) = (p ↦ᵣ (tpl.take k ++ tpl[k] :: tpl.drop (k + 1))) :=
    congrArg (p ↦ᵣ ·) hsplit_list
  have htake_len : (tpl.take k).length = k := List.length_take_of_le (Nat.le_of_lt hk_len)
  have haddr : p + BitVec.ofNat 64 k = a := by
    dsimp only [k]
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    bv_omega
  rw [hro_eq, pointsToBytesRO_append, htake_len, haddr, pointsToBytesRO_cons] at hm
  have hm_bad : m ⊨ (a ↦₈ᵣ tpl[k]) ∗ ((a ↦₈ w) ∗
      ((p ↦ᵣ tpl.take k) ∗ ((a + 1#64) ↦ᵣ tpl.drop (k + 1)) ∗ R)) := by
    revert hm; intro hm; sep_frame
  exact not_satisfies_ownsRO_ownsRW
    (ownsRO_pointsTo8RO a tpl[k])
    (ownsRW_sepConj_left (ownsCell_pointsTo8 a w).ownsRW)
    hm_bad

/-- Any read-only byte slice `p ↦ᵣ tpl` separated from a writable `memRegion ret 24` has
    `tpl.length < 2 ^ 64`. -/
theorem pointsToBytesRO_length_lt_of_memRegion24 {m : Memory} {p ret : BitVec 64}
    {tpl : List (BitVec 8)} {R : SepProp}
    (hm : m ⊨ (p ↦ᵣ tpl) ∗ memRegion ret 24 ∗ R) :
    tpl.length < 2 ^ 64 := by
  rw [memRegion24_eq_vecHeader ret] at hm
  dsimp only [vecHeader] at hm
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm
  rcases hm with ⟨c, ptr, len, hm⟩
  rw [pointsTo64_eq_pointsToBytes ret c] at hm
  have hu : unpack64 c = (c.extractLsb' 0 8) :: (unpack64 c).drop 1 := rfl
  rw [hu, pointsToBytes_cons] at hm
  have hm' : m ⊨ (p ↦ᵣ tpl) ∗ (ret ↦₈ c.extractLsb' 0 8) ∗
      (((ret + 1#64) ↦ₛ (unpack64 c).drop 1) ∗ ((ret + 8#64) ↦₆₄ ptr) ∗
       ((ret + 16#64) ↦₆₄ len) ∗ R) := by
    revert hm; intro hm; sep_frame
  exact pointsToBytesRO_length_lt_of_pointsTo8 hm'

/-- If `decodeFmtTemplate` succeeds on `bs`, then `bs ≠ []` and the total literal length of the
    decoded calls is strictly less than `bs.length` (the trailing `0x00` byte is not a literal). -/
theorem decodeFmtTemplate_nonempty_and_litLen_lt {tplPtr : BitVec 64}
    {args : List (BitVec 64 × BitVec 64)} :
    ∀ {fuel pos ai : Nat} {bs : List (BitVec 8)} {cs : List FmtCall},
      decodeFmtTemplate tplPtr args fuel pos ai bs = some cs →
      bs ≠ [] ∧ fmtLiteralLen cs < bs.length
  | 0, _, _, _, _, h => by simp [decodeFmtTemplate] at h
  | _ + 1, _, _, [], _, h => by simp [decodeFmtTemplate] at h
  | fuel + 1, pos, ai, n :: rest, cs, h => by
    refine ⟨List.cons_ne_nil _ _, ?_⟩
    simp only [decodeFmtTemplate] at h
    by_cases hn0 : n = 0#8
    · simp only [hn0, ↓reduceIte] at h
      by_cases hr0 : rest = []
      · simp only [hr0, ↓reduceIte, Option.some.injEq] at h
        subst h; simp [fmtLiteralLen]
      · simp [hr0] at h
    · simp only [hn0, ↓reduceIte] at h
      by_cases hn80 : n.toNat < 0x80
      · simp only [hn80, ↓reduceIte] at h
        by_cases hrlen : rest.length < n.toNat
        · simp [hrlen] at h
        · simp only [hrlen, ↓reduceIte, Option.map_eq_some_iff] at h
          rcases h with ⟨cs', hrec, rfl⟩
          have ⟨_, hlt'⟩ := decodeFmtTemplate_nonempty_and_litLen_lt hrec
          simp only [List.length_drop] at hlt'
          have htake : (rest.take n.toNat).length = n.toNat :=
            List.length_take_of_le (Nat.le_of_not_lt hrlen)
          simp only [fmtLiteralLen, htake, List.length_cons]
          omega
      · simp only [hn80, ↓reduceIte] at h
        by_cases heq80 : n = 0x80#8
        · simp only [heq80, ↓reduceIte] at h
          by_cases hr2 : rest.length < 2
          · simp [hr2] at h
          · simp only [hr2, ↓reduceIte] at h
            by_cases hrlen : (rest.drop 2).length < leBytesNat (rest.take 2)
            · simp only [hrlen, ↓reduceIte] at h; cases h
            · simp only [hrlen, ↓reduceIte, Option.map_eq_some_iff] at h
              rcases h with ⟨cs', hrec, rfl⟩
              have ⟨_, hlt'⟩ := decodeFmtTemplate_nonempty_and_litLen_lt hrec
              simp only [List.length_drop] at hlt' hrlen
              have htake : ((rest.drop 2).take (leBytesNat (rest.take 2))).length =
                  leBytesNat (rest.take 2) := by
                rw [List.length_take, List.length_drop]
                omega
              simp only [fmtLiteralLen, htake, List.length_cons]
              omega
        · simp only [heq80, ↓reduceIte] at h
          by_cases hnc0 : n.toNat < 0xc0
          · simp [hnc0] at h
          · simp only [hnc0, ↓reduceIte] at h
            cases hph : decodeFmtPlaceholder n rest args ai with
            | none => simp [hph] at h
            | some val =>
              rcases val with ⟨opts, idx, ai', k⟩
              simp only [hph] at h
              cases harg : args[idx]? with
              | none => simp [harg] at h
              | some vf =>
                rcases vf with ⟨value, fmtFn⟩
                simp only [harg, Option.map_eq_some_iff] at h
                rcases h with ⟨cs', hrec, rfl⟩
                have ⟨_, hlt'⟩ := decodeFmtTemplate_nonempty_and_litLen_lt hrec
                simp only [List.length_drop] at hlt'
                simp only [fmtLiteralLen, List.length_cons]
                omega

/-- Extracting the byte skip `k = lf + lw + lp + li` and `k ≤ rest.length` from a successful
    `decodeFmtPlaceholder n rest args ai = some (opts, idx, ai', k)`. -/
theorem decodeFmtPlaceholder_skip_eq {n : BitVec 8} {rest : List (BitVec 8)}
    {args : List (BitVec 64 × BitVec 64)} {ai : Nat}
    {opts : FmtOptions} {idx ai' k : Nat}
    (h : decodeFmtPlaceholder n rest args ai = some (opts, idx, ai', k)) :
    k = (if n.getLsbD 0 then 4 else 0) + (if n.getLsbD 1 then 2 else 0) +
        (if n.getLsbD 2 then 2 else 0) + (if n.getLsbD 3 then 2 else 0) ∧
      k ≤ rest.length := by
  unfold decodeFmtPlaceholder at h
  dsimp only at h
  by_cases hlt : rest.length <
      (if n.getLsbD 0 then 4 else 0) + (if n.getLsbD 1 then 2 else 0) +
      (if n.getLsbD 2 then 2 else 0) + (if n.getLsbD 3 then 2 else 0)
  · simp only [hlt, ↓reduceIte] at h; cases h
  · simp only [hlt, ↓reduceIte] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨_, _, _, rfl⟩
      exact ⟨rfl, Nat.le_of_not_lt hlt⟩
    · contradiction

set_option maxRecDepth 200000 in
/-- Exact 64-bit pointer increment computed by `format_inner+0x07c..+0x0ac` (`rbit`/`lsr`/`and`)
    matches `BitVec.ofNat 64 (lf + lw + lp + li)` for every byte `n : BitVec 8`. -/
theorem placeholder_ptr_step_bv (n : BitVec 8) (base : BitVec 64) :
    let w10 : BitVec 32 := n.zeroExtend 32
    let w13 : BitVec 64 := ((w10 >>> 1) &&& 2#32).zeroExtend 64
    let w10' : BitVec 64 := ((w10 >>> 2) &&& 2#32).zeroExtend 64
    let w12 : BitVec 64 := (((w10 &&& 3#32).reverse) >>> 29).zeroExtend 64
    base + w13 + w10' + w12 =
      base + BitVec.ofNat 64
        ((if n.getLsbD 0 then 4 else 0) + (if n.getLsbD 1 then 2 else 0) +
         (if n.getLsbD 2 then 2 else 0) + (if n.getLsbD 3 then 2 else 0)) := by
  have hconst :
      (((n.zeroExtend 32 >>> 1) &&& 2#32).zeroExtend 64 : BitVec 64) +
      (((n.zeroExtend 32 >>> 2) &&& 2#32).zeroExtend 64 : BitVec 64) +
      ((((n.zeroExtend 32 &&& 3#32).reverse) >>> 29).zeroExtend 64 : BitVec 64) =
      BitVec.ofNat 64
        ((if n.getLsbD 0 then 4 else 0) + (if n.getLsbD 1 then 2 else 0) +
         (if n.getLsbD 2 then 2 else 0) + (if n.getLsbD 3 then 2 else 0)) := by
    revert n; decide
  dsimp only
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.add_assoc (((n.zeroExtend 32 >>> 1) &&& 2#32).zeroExtend 64),
    hconst]

/-! ## Block-scoped pure-segment lifter and `oracle`/`symtab` preservation -/

theorem allocBlockNoSvc0_03 : checkBlockNoSvc0 (allocMultiLib.blockLib 3).text = true := by
  decide

private def projOra (s : State) : Oracle := s.oracle
private theorem projOra_adv (s : State) : projOra s.advancePC = projOra s := by cases s; rfl
private theorem projOra_pc (s : State) (p : BitVec 64) : projOra (s.setPC p) = projOra s := by cases s; rfl
private theorem projOra_w64 (s : State) (r : Reg) (v : BitVec 64) : projOra (s.writeReg64 r v) = projOra s := by
  cases s; cases r <;> rfl
private theorem projOra_w32 (s : State) (r : Reg) (v : BitVec 32) : projOra (s.writeReg32 r v) = projOra s :=
  projOra_w64 s r _
private theorem projOra_w (s : State) (w : Width) (r : Reg) (v : BitVec 64) : projOra (s.writeReg w r v) = projOra s :=
  projOra_w64 s r _
private theorem projOra_v128 (s : State) (r : BitVec 5) (v : BitVec 128) : projOra (s.writeVReg128 r v) = projOra s := by
  cases s; rfl
private theorem projOra_v64 (s : State) (r : BitVec 5) (v : BitVec 64) : projOra (s.writeVReg64 r v) = projOra s :=
  projOra_v128 s r _
private theorem projOra_v32 (s : State) (r : BitVec 5) (v : BitVec 32) : projOra (s.writeVReg32 r v) = projOra s :=
  projOra_v128 s r _
private theorem projOra_ps (s : State) (p : PState) : projOra (s.setPState p) = projOra s := by cases s; rfl
private theorem projOra_fp (s : State) (f : BitVec 32) : projOra (s.setFpsr f) = projOra s := by cases s; rfl
private theorem projOra_ofp (s : State) (f : BitVec 32) : projOra (s.orFpsr f) = projOra s := by cases s; rfl
private theorem projOra_st (s : State) (st : ExecStatus) : projOra (s.setStatus st) = projOra s := by cases s; rfl
private theorem projOra_wst (s : State) (st : ExecStatus) : projOra { s with status := st } = projOra s := by cases s; rfl
private theorem projOra_mem (s : State) (m : Memory) : projOra (s.setMem m) = projOra s := by cases s; rfl
private theorem projOra_tp (s : State) (v : BitVec 64) : projOra (setTpidrEl0 s v) = projOra s := by cases s; rfl
private theorem projOra_ex (s : State) : projOra s.stepExclOracle = projOra s := by cases s; rfl
private theorem projOra_as (s : State) (rd : BitVec 5) (r : Except String (BitVec 128)) :
    projOra (applySimdResult s rd r) = projOra s := by cases s; cases r <;> rfl
private theorem projOra_ass (s : State) (rd : BitVec 5) (r : Except String (BitVec 128)) (sat : Option (BitVec 32)) :
    projOra (applySimdSatResult s rd r sat) = projOra s := by cases s; cases r <;> cases sat <;> rfl
private theorem projOra_slr (sz : SimdMemSize) (m : Memory) :
    ∀ (n : Nat) (vt : BitVec 5) (ea : BitVec 64) (s : State), projOra (simdLoadRegs sz m n vt ea s) = projOra s
  | 0, _, _, _ => rfl
  | n + 1, _, _, s => (projOra_slr sz m n _ _ _).trans (projOra_v128 s _ _)

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 400000 in
private theorem execInst_oracle_of_not_isSvc0 {inst : Instr} (h : inst.isSvc0 = false) (s : State) :
    (execInst inst s).oracle = s.oracle := by
  change projOra (execInst inst s) = projOra s
  cases inst
  case system isHalt imm =>
    cases isHalt
    · by_cases himm : imm == 0#16
      · have heq : imm = 0#16 := of_decide_eq_true himm; subst heq; simp [Instr.isSvc0] at h
      · dsimp only [execInst, execInstWithSvc]; simp [himm, projOra_st]
    · dsimp only [execInst, execInstWithSvc]; by_cases himm : imm == 1#16 <;> simp [himm, projOra_st]
  case simdThreeSame q u size rm opcode rn rd =>
    dsimp only [execInst, execInstWithSvc]
    by_cases hop : opcode == 0b00011#5
    · simp only [hop, ↓reduceIte]
      rcases size with ⟨_ | _ | _ | _ | _, _⟩ <;> try omega
      all_goals (cases u <;> first | exact (projOra_adv _).trans (projOra_v128 _ _ _) | exact projOra_ass _ _ _ _)
    · simp only [hop, Bool.false_eq_true, ↓reduceIte, projOra_adv, projOra_v128, projOra_st, projOra_wst,
        projOra_as, projOra_ass, apply_ite projOra, ite_self]
  case ldpSimd _ _ _ addr | stpSimd _ _ _ addr | ldrSimd _ _ addr | strSimd _ _ addr =>
    dsimp only [execInst, execInstWithSvc]
    rcases evalAddrMode s addr with ⟨_, _ | ⟨_, _⟩⟩ <;>
      simp [projOra_adv, projOra_mem, projOra_v128, projOra_w64, projOra_st, apply_ite projOra]
  case ldr | ldrLit | str | ldp | stp | ldnp | stnp | addSubImm | logicalImm | moveWide | bitfield
     | logicalShift | addSubShift | addSubExt | addSubCarry | condCompareReg | condCompareImm
     | condSelect | dataProc1 | dataProc2 | dataProc3 =>
    cases s; dsimp only [execInst, execInstWithSvc, execLdr, execLdrLit, execStr, execLdp, execStp,
      execAddSubImm, execLogicalImm, execMoveWide, execBitfield, execLogicalShift, execAddSubShift,
      execAddSubExt, execAddSubCarry, execCondCompare, execCondSelect, execDataProc1, execDataProc2,
      execDataProc3]; (repeat' split) <;> rfl
  all_goals
    dsimp only [execInst, execInstWithSvc]
    simp only [projOra_adv, projOra_pc, projOra_w64, projOra_w32, projOra_w, projOra_v128, projOra_v64,
      projOra_v32, projOra_ps, projOra_fp, projOra_ofp, projOra_st, projOra_wst, projOra_mem, projOra_tp,
      projOra_ex, projOra_as, projOra_ass, projOra_slr, apply_ite projOra, ite_self]
    try (cases s; (repeat' split) <;> rfl)

private theorem execInst_oracle_symtab {inst : Instr} (h : inst.isSvc0 = false) (s : State) :
    (execInst inst s).oracle = s.oracle ∧ (execInst inst s).symtab = s.symtab := by
  refine ⟨execInst_oracle_of_not_isSvc0 h s, ?_⟩
  have hev := Arm64.evalInst_eq_execInst_of_not_isSvc0 (prog := {}) h (s := s)
  rw [← hev]
  exact evalInst_symtab {} inst s

private theorem strip_codeLoaded_fmt {prog : Program} {m : Memory} (hL : prog.CodeLoaded m) :
    prog.CodeLoaded (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hno := hL.no_wrap
  have hsub : prog.base + BitVec.ofNat 64 i - prog.base = BitVec.ofNat 64 i := by bv_omega
  have hkeep : ProofLib.progKeep prog (prog.base + BitVec.ofNat 64 i) = true := by
    unfold ProofLib.progKeep
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_true hi
  rw [ProofLib.strip_read8, ProofLib.strip_perm_of_keep hkeep, ProofLib.strip_isLazyFree]
  exact ⟨hL.byte_eq i hi, hL.perm_eq i hi, hL.isLazyFree_eq i hi⟩

private theorem strip_execOnlyIn_fmt (prog : Program) (m : Memory) :
    prog.ExecOnlyIn (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) :=
  fun _ hpx => of_decide_eq_true (ProofLib.strip_perm_x_imp hpx).2

private theorem steps_start_running_fmt {Q : Program} {s sf : State}
    (h : Steps Q s sf) (hr : sf.status = .Running) : s.status = .Running := by
  cases h with
  | refl => exact hr
  | step h1 _ => cases h1 <;> assumption

/-- What a pure non-syscall instruction segment preserves on the real state `s ↝ sm`:
    `NonSyscallPreserved s sm` plus `sm.oracle = s.oracle ∧ sm.symtab = s.symtab`. -/
def PureSegPreserved (s sm : State) : Prop :=
  ProofLib.NonSyscallPreserved s sm ∧ sm.oracle = s.oracle ∧ sm.symtab = s.symtab

theorem PureSegPreserved.refl (s : State) : PureSegPreserved s s :=
  ⟨ProofLib.NonSyscallPreserved.refl s, rfl, rfl⟩

theorem PureSegPreserved.trans {s0 s1 s2 : State}
    (h01 : PureSegPreserved s0 s1) (h12 : PureSegPreserved s1 s2) :
    PureSegPreserved s0 s2 :=
  ⟨ProofLib.NonSyscallPreserved.trans h01.1 h12.1, h12.2.1.trans h01.2.1, h12.2.2.trans h01.2.2⟩

private theorem steps_rebase_lift_fmt_block {P R_j : Program}
    (hext_blk : ∀ off : Nat, off < R_j.code.length →
      P.externAt? (R_j.base + BitVec.ofNat 64 off) = none)
    (hext_R : ∀ pc, R_j.externAt? pc = none)
    (hall : R_j.allInstrs (fun i => !i.isSvc0) = true)
    {s1' sf' : State} (hsteps : Steps R_j s1' sf') (hrun_f : sf'.status = .Running) :
    ∀ (s1 : State), s1' = ProofLib.stripS (ProofLib.progKeep R_j) s1 → R_j.CodeLoaded s1.mem →
      ∃ sf : State, sf' = ProofLib.stripS (ProofLib.progKeep R_j) sf ∧
        Steps P s1 sf ∧ PureSegPreserved s1 sf := by
  induction hsteps with
  | refl =>
    intro s1 hs1 _
    exact ⟨s1, hs1, .refl s1, PureSegPreserved.refl s1⟩
  | @step sa' sb' sc' h1 hrest ih =>
    intro s1 hsa hL1
    have hrb' : sb'.status = .Running := steps_start_running_fmt hrest hrun_f
    subst hsa
    cases h1 with
    | halt_unmapped _ _ _ => cases s1; cases hrb'
    | extern _ he _ _ => rw [hext_R] at he; cases he
    | extern_fault _ he _ => rw [hext_R] at he; cases he
    | @exec inst hr1' hfe' =>
      have hr1 : s1.status = .Running := by cases s1; exact hr1'
      have hL1' : R_j.CodeLoaded (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem :=
        strip_codeLoaded_fmt hL1
      have hexec' : R_j.ExecOnlyIn (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem :=
        strip_execOnlyIn_fmt R_j s1.mem
      have hnsvc0 : inst.isSvc0 = false := by
        simpa using Program.fetchMem_of_allInstrs hall hL1' hexec' _ inst hfe'
      have hfe_P : P.fetchMem s1.mem s1.pc = some inst := by
        have hpc_eq : (ProofLib.stripS (ProofLib.progKeep R_j) s1).pc = s1.pc := by cases s1; rfl
        have hmem_eq : (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem =
            ProofLib.stripExecOutside (ProofLib.progKeep R_j) s1.mem := by cases s1; rfl
        rw [hpc_eq, hmem_eq] at hfe'
        unfold Program.fetchMem at hfe' ⊢
        rw [hext_R] at hfe'
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfe'
        by_cases hal_pc : s1.pc.toNat % 4 = 0
        · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfe'
          split at hfe'
          · contradiction
          · rename_i hce'
            simp only [Bool.not_eq_true', Bool.not_eq_false] at hce'
            have hkeep0 : ProofLib.progKeep R_j s1.pc = true := by
              have hce0 := hce'
              unfold Memory.canExec at hce0
              rw [Memory.allPerm_iff] at hce0
              have hx0 := hce0 0 (by omega)
              simpa using (ProofLib.strip_perm_x_imp hx0).2
            have hoff_lt : (s1.pc - R_j.base).toNat < R_j.code.length :=
              of_decide_eq_true hkeep0
            have hpc_off : R_j.base + BitVec.ofNat 64 (s1.pc - R_j.base).toNat = s1.pc := by
              simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
              bv_lin
            have hext_P_pc : P.externAt? s1.pc = none :=
              hpc_off ▸ hext_blk (s1.pc - R_j.base).toNat hoff_lt
            rw [hext_P_pc]
            simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
              hal_pc, ne_eq, not_true_eq_false]
            have hce : s1.mem.canExec s1.pc 4 = true := by
              unfold Memory.canExec at hce' ⊢
              rw [Memory.allPerm_iff] at hce' ⊢
              intro k hk
              have hxk := hce' k hk
              rwa [ProofLib.strip_perm_of_keep (ProofLib.strip_perm_x_imp hxk).2] at hxk
            have hr32 :
                (ProofLib.stripExecOutside (ProofLib.progKeep R_j) s1.mem).read32 s1.pc =
                  s1.mem.read32 s1.pc := by
              simp [Memory.read32, ProofLib.strip_read8]
            rw [hr32] at hfe'
            simp only [hce, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            exact hfe'
        · simp only [hal_pc, ne_eq, not_false_eq_true, ↓reduceIte] at hfe'
          contradiction
      have hev_R : R_j.evalInst inst (ProofLib.stripS (ProofLib.progKeep R_j) s1) =
          ProofLib.stripS (ProofLib.progKeep R_j) (execInst inst s1) := by
        rw [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0, ProofLib.execInst_stripS hnsvc0]
      have hstep_P : Step P s1 (execInst inst s1) := by
        have := Step.exec (prog := P) hr1 hfe_P
        rwa [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0] at this
      obtain ⟨sf, hsf_eq, hsteps_P, hpseg_rest⟩ :=
        ih hrun_f (execInst inst s1) hev_R (hstep_P.codeLoaded hL1)
      have hstep_pure : PureSegPreserved s1 (execInst inst s1) :=
        ⟨ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1,
         execInst_oracle_symtab hnsvc0 s1⟩
      exact ⟨sf, hsf_eq, .step hstep_P hsteps_P, PureSegPreserved.trans hstep_pure hpseg_rest⟩

/-- Run a pure segment of `allocMultiLib` block `j` in `SepWPp` with block-local hook freedom only,
    refreshing `CodeLoaded` and supplying `PureSegPreserved s sm` (including `oracle` and `symtab`). -/
theorem sepWPp_seg_alloc_block_pure {mpl : MultiPlacement} {P : Program}
    (j : Nat) (hj : j < allocMultiLib.blocks.length)
    (hext_blk : FmtAllocBlockNoExtern mpl P j)
    (hchk : checkBlockNoSvc0 (allocMultiLib.blockLib j).text = true)
    {mid ret : BitVec 64} {s : State} {Pre : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : allocMultiLib.CodeLoaded mpl s.mem)
    (hseg : ∀ s' : State, SameCpuState s' s →
      SepWP ((allocMultiLib.blockProgram mpl j).rebase (mpl.base j) (fun _ => none)) mid s' Pre
        (fun sm' Pm =>
          ∀ sm : State, SameCpuState sm sm' → allocMultiLib.CodeLoaded mpl sm.mem →
            PureSegPreserved s sm →
            SepWPp P ret sm Pm Q Qp oom)) :
    SepWPp P ret s Pre Q Qp oom := by
  let R_j := (allocMultiLib.blockProgram mpl j).rebase (mpl.base j) (fun _ => none)
  let keep := ProofLib.progKeep R_j
  have hL_R : R_j.CodeLoaded s.mem := (hcl j hj).of_base_code rfl rfl
  have hext_R : ∀ pc, R_j.externAt? pc = none := by intro pc; simp [R_j]
  have hext_R_blk : ∀ off : Nat, off < R_j.code.length →
      P.externAt? (R_j.base + BitVec.ofNat 64 off) = none := by
    intro off hoff
    simp only [R_j, Program.rebase, MultiPlacedLib.blockProgram, PlacedLib.program,
      Obj.CodeBlock.length_patched] at hoff ⊢
    exact hext_blk off (Nat.lt_of_lt_of_le hoff (Nat.mul_div_le _ 4))
  have hall : R_j.allInstrs (fun i => !i.isSvc0) = true :=
    blockProgram_rebase_allInstrs_not_isSvc0 allocMultiLib mpl j hchk
  intro R hm hL_P
  obtain ⟨R_view, hm_strip, hunstrip⟩ := ProofLib.strip_frame keep hm
  have hcpu_in : SameCpuState (ProofLib.stripS keep s) s :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨sm', hsteps', hout'⟩ :=
    SepWP.to_reaches_pc (hseg (ProofLib.stripS keep s) hcpu_in) hm_strip
      (strip_codeLoaded_fmt hL_R)
  rcases hout' with ⟨_, hrun_m', Pm, hmm', hcont⟩ | ⟨_, hoom⟩
  · obtain ⟨sm, hsm_eq, hsteps_P, hpseg⟩ :=
      steps_rebase_lift_fmt_block hext_R_blk hext_R hall hsteps' hrun_m' s rfl hL_R
    have hcl_m : allocMultiLib.CodeLoaded mpl sm.mem :=
      fun k hk => hsteps_P.codeLoaded (hcl k hk)
    have hperm_eq : ∀ a, sm.mem.perm a = s.mem.perm a := fun a => congrFun hpseg.1.2.1 a
    have hmm'_mem : ProofLib.stripExecOutside keep sm.mem ⊨ Pm ∗ R_view := by
      have hm_eq : sm'.mem = ProofLib.stripExecOutside keep sm.mem := by rw [hsm_eq]; rfl
      rwa [← hm_eq]
    have hmm : sm.mem ⊨ Pm ∗ R := hunstrip hperm_eq hmm'_mem
    have hwp_cont := hcont sm (SameCpuState.of_stripS_left hsm_eq) hcl_m hpseg
    obtain ⟨sf, hsteps2, hout2⟩ := hwp_cont R hmm (hsteps_P.codeLoaded hL_P)
    exact ⟨sf, hsteps_P.trans hsteps2, hout2⟩
  · rcases (satisfies_pure_sepConj _ _ _).mp hoom with ⟨hf, _⟩
    exact False.elim hf

end VerifiedLibraries.RustStd
