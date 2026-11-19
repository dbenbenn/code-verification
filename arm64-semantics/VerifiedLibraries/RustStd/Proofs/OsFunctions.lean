/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Spec
public import VerifiedLibraries.RustStd.Generated.RustCoreOsFnPlacedObj
public import VerifiedLibraries.RustStd.Generated.RustStdIoPlacedObj
public import VerifiedLibraries.RustStd.Proofs.ExecSeg
public import VerifiedLibraries.RustStd.Proofs.CoreIo
public import ProofLib.GenPlacedFetches
public import ProofLib
public meta import ProofLib.ProgramReflection

/-!
# Placement-Generic `OS_FUNCTIONS` and `is_interrupted` Contracts

Proves placement-generic GOT relocation stepping and fetch lemmas (`GotToNopAdr`, `GotToAdrpAdd`,
and unrelaxed GOT load) and establishes contracts for `std::sys::io::error::unix::is_interrupted`,
`core::io::error::os_functions::get_os_functions`, and
`core::io::error::os_functions::set_functions::set_functions_inner`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.literalFetch false

namespace VerifiedLibraries.RustStd.Io

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
  ProofLib.GenPlacedFetches ProofLib.StdStartup VerifiedLibraries.RustStd

/-! ## GOT Relocation Stepping and Fetch Lemmas -/

section GotHelpers

private theorem ldrToAddWord_mask (w : BitVec 32) :
    ldrToAddWord w &&& 0xffc00000#32 = 0x91000000#32 := by
  unfold ldrToAddWord; bv_bits

private theorem ldrToAddWord_rd (w : BitVec 32) :
    (ldrToAddWord w).extractLsb' 0 5 = w.extractLsb' 0 5 := by
  unfold ldrToAddWord; bv_bits

private theorem ldrToAddWord_rn (w : BitVec 32) :
    (ldrToAddWord w).extractLsb' 5 5 = w.extractLsb' 5 5 := by
  unfold ldrToAddWord; bv_bits

private theorem patchedWord_of_got_unpaired {blk : CodeBlock} {pl : Placement} {off : Nat}
    {r : RelocEntry}
    (hr : blk.relocAt? off = some r)
    (hk : r.kind = .adrGotPage ∨ r.kind = .ld64GotLo12Nc)
    (hgp0 : blk.gotPairAt off = false)
    (hgpm4 : (off < 4 || !blk.gotPairAt (off - 4)) = true) :
    blk.patchedWord pl off =
      patchRelocWord r.kind (blk.wordAt off) (pl.base + BitVec.ofNat 64 off) (blk.target pl r) := by
  have hk_nadrp : r.kind ≠ .adrpHi21 := by rcases hk with h | h <;> rw [h] <;> decide
  have hk_nadd : r.kind ≠ .addLo12 := by rcases hk with h | h <;> rw [h] <;> decide
  have hb : blk.b2bNext? r = none := by
    rcases hk with h | h <;> simp [CodeBlock.b2bNext?, h]
  have hrel0 : blk.relaxedAt pl off = false :=
    CodeBlock.relaxedAt_of_relaxableAt_false (CodeBlock.relaxableAt_false_of_kind hr hk_nadrp)
  have hrelm4 : (4 ≤ off && blk.relaxedAt pl (off - 4)) = false := by
    by_cases h4 : 4 ≤ off
    · have hprev : blk.relaxableAt (off - 4) = false :=
        CodeBlock.relaxableAt_false_of_next_kind (r := r)
          (by rw [show off - 4 + 4 = off by omega]; exact hr) hk_nadd
      simp [h4, CodeBlock.relaxedAt_of_relaxableAt_false hprev]
    · simp [h4]
  have htls : blk.tlsieRelaxableAt off = false := by
    unfold CodeBlock.tlsieRelaxableAt; rw [hr]
    rcases hk with h | h <;> simp [h]
  have hgprev : (4 ≤ off && blk.gotPairAt (off - 4)) = false := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hgpm4
    rcases hgpm4 with hlt | hgp
    · simp [show ¬ 4 ≤ off by omega]
    · simp [hgp]
  have hgprev_rx : (r.kind.isGotOrTlsIe && 4 ≤ off &&
      (blk.gotPairAt (off - 4) && pl.relax (off - 4))) = false := by
    by_cases h4 : 4 ≤ off
    · simp only [h4, decide_true, Bool.true_and] at hgprev
      simp [hgprev]
    · simp [h4]
  have hnb : (r.kind == .call26 || r.kind == .jump26) = false := by
    rcases hk with h | h <;> simp [h]
  unfold CodeBlock.patchedWord
  rw [hr]
  simp only [hrel0, hrelm4, hgprev_rx, hgp0, htls, hgprev, Bool.false_or, Bool.and_false,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte, CodeBlock.relocTarget_of_b2bNext_none hb,
    CodeBlock.undefWeakBranch_of_not_branch hnb]

/-- Step a non-adjacent `R_AARCH64_ADR_GOT_PAGE` (`ADRP Xd, :got:sym`, `gotPairAt off = false`)
    for any `Placeable` placement `pl` (regardless of `pl.relax`). -/
theorem sepWP_rebase_adrGotPage_unpaired {lib : PlacedLib} {pl : Placement} {off off4 : Nat}
    {X O X' O' : String → Option (State → State)} {svc : State → State} {b : BitVec 64}
    {r : RelocEntry} {rd : BitVec 5} {T tgt : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hP : lib.Placeable pl) (hb : b = pl.base)
    (hr : lib.text.relocAt? off = some r) (hk : r.kind = .adrGotPage)
    (hgp0 : lib.text.gotPairAt off = false)
    (hgpm4 : (off < 4 || !lib.text.gotPairAt (off - 4)) = true)
    {w : BitVec 32} (hwd : lib.text.wordAt off = w)
    (hw : w &&& 0x9f000000#32 = 0x90000000#32)
    (hrd : w.extractLsb' 0 5 = rd) (hrd31 : rd ≠ 31#5)
    (hT : lib.text.target pl r = T) (h4 : off + 4 = off4)
    (hh0 : ((lib.program pl X O svc).rebase b X' O').hookAtOff? off = none)
    (hpc : s.pc = b + BitVec.ofNat 64 off) (hrun : s.status = .Running)
    (hnext : SepWP ((lib.program pl X O svc).rebase b X' O') tgt
      ((s.writeReg64 (.gpr rd) (pageOf T)).setPC (b + BitVec.ofNat 64 off4)) P post oom) :
    SepWP ((lib.program pl X O svc).rebase b X' O') tgt s P post oom := by
  subst hb hT h4 hwd
  have hroff := CodeBlock.relocAt?_off hr
  obtain ⟨hal, hlen, hrange⟩ := hP.text.relocs_ok r (CodeBlock.relocAt?_mem hr)
  rw [hroff] at hal hlen hrange
  have hnw := hP.text.no_wrap
  have hb2b : lib.text.b2bNext? r = none := by simp [CodeBlock.b2bNext?, hk]
  rw [CodeBlock.relocTarget_of_b2bNext_none hb2b, hk] at hrange
  simp only [CodeBlock.relocInRange, hgp0, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hrange
  have hw0 := patchedWord_of_got_unpaired (pl := pl) hr (.inl hk) hgp0 hgpm4
  rw [hk] at hw0
  let prog := (lib.program pl X O svc).rebase pl.base X' O'
  have hf0 : prog.fetch (pl.base + BitVec.ofNat 64 off) = decode (lib.text.patchedWord pl off) :=
    Program.fetch_of_readWordOff (by omega) hh0 (CodeBlock.readWordOff_patched (by simp [prog]) hal hlen)
  rw [hw0] at hf0
  simp only [patchRelocWord] at hf0
  rw [decode_adrpWord hw hrange, hrd, fromZRBits_of_ne hrd31] at hf0
  have hstep4 : pl.base + BitVec.ofNat 64 (off + 4) = pl.base + BitVec.ofNat 64 off + 4#64 := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]
  rw [hstep4] at hnext
  refine SepWP.step_pure (s' := ((s.setPC (pl.base + BitVec.ofNat 64 off)).writeReg64 (.gpr rd)
      (pageOf (lib.text.target pl r))).advancePC) hpc hrun hf0 ?_ rfl ?_
  · simp only [Program.evalInst, execInstWithSvc, ite_true, State.pc_setPC]
    rw [adrp_pageOf_cancel]
  · rw [write_advance_state]; exact hnext

/-- Fetch a non-adjacent `R_AARCH64_LD64_GOT_LO12_NC` (`LDR Xt, [Xn, :got_lo12:sym]`,
    `gotPairAt (off - 4) = false`) for any `Placeable` placement `pl` (regardless of `pl.relax`). -/
theorem fetch_rebase_ld64GotLo12_unpaired {lib : PlacedLib} {pl : Placement} {off : Nat}
    {X O X' O' : String → Option (State → State)} {svc : State → State} {b : BitVec 64}
    {r : RelocEntry} {T : BitVec 64} {inst : Instr}
    (hP : lib.Placeable pl)
    (hr : lib.text.relocAt? off = some r) (hk : r.kind = .ld64GotLo12Nc)
    (hgp0 : lib.text.gotPairAt off = false)
    (hgpm4 : (off < 4 || !lib.text.gotPairAt (off - 4)) = true)
    (hh : ((lib.program pl X O svc).rebase b X' O').hookAtOff? off = none)
    {w : BitVec 32} (hwd : lib.text.wordAt off = w)
    (hscale : (w.extractLsb' 30 2).toNat = 3)
    (hw1 : w &&& 0x3f000000#32 = 0x39000000#32)
    (hw2 : (w &&& 0xffc00000#32 == 0xf9800000#32) = false)
    (hT : lib.text.target pl r = T)
    (hinst : mkLoadStoreInst 3 (w.extractLsb' 22 2).toNat (Reg.fromZRBits (w.extractLsb' 0 5))
      (.Offset (Reg.fromSPBits (w.extractLsb' 5 5)) (lo12Of T)) = some inst) :
    ((lib.program pl X O svc).rebase b X' O').fetch (b + BitVec.ofNat 64 off) = some inst := by
  subst hT hwd
  have hroff := CodeBlock.relocAt?_off hr
  obtain ⟨hal4, hlen, hrange⟩ := hP.text.relocs_ok r (CodeBlock.relocAt?_mem hr)
  rw [hroff] at hal4 hlen hrange
  have hnw := hP.text.no_wrap
  have hb2b : lib.text.b2bNext? r = none := by simp [CodeBlock.b2bNext?, hk]
  rw [CodeBlock.relocTarget_of_b2bNext_none hb2b, hk] at hrange
  have hgprev : (4 ≤ off && lib.text.gotPairAt (off - 4)) = false := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hgpm4
    rcases hgpm4 with hlt | hgp
    · simp [show ¬ 4 ≤ off by omega]
    · simp [hgp]
  have hal : Lo12Aligned 3 (lib.text.target pl r) := by
    unfold CodeBlock.relocInRange at hrange
    by_cases h4 : 4 ≤ off
    · simp only [h4, decide_true, Bool.true_and] at hgprev
      simpa [h4, hgprev] using hrange
    · simpa [h4] using hrange
  let prog := (lib.program pl X O svc).rebase b X' O'
  have hf : prog.fetch (b + BitVec.ofNat 64 off) = decode (lib.text.patchedWord pl off) := by
    have hb_prog : prog.base = b := rfl
    rw [← hb_prog]
    exact Program.fetch_of_readWordOff (by omega) hh (CodeBlock.readWordOff_patched (by simp [prog]) hal4 hlen)
  rw [hf, patchedWord_of_got_unpaired (pl := pl) hr (.inr hk) hgp0 hgpm4, hk]
  simp only [patchRelocWord]
  rw [decode_ldstGprLo12Word hscale hw1 hw2 hal, hinst]

theorem gotPairAt_spec {blk : CodeBlock} {off : Nat} {r1 : RelocEntry}
    (h : blk.gotPairAt off = true) (hr1 : blk.relocAt? off = some r1) :
    ∃ r2, blk.relocAt? (off + 4) = some r2 ∧
      r1.kind = .adrGotPage ∧ r2.kind = .ld64GotLo12Nc ∧
      r1.sym = r2.sym ∧ r1.addend = 0 ∧ r2.addend = 0 ∧
      blk.wordAt off &&& 0x9f000000#32 = 0x90000000#32 ∧
      blk.wordAt (off + 4) &&& 0xffc00000#32 = 0xf9400000#32 ∧
      (blk.wordAt off &&& 0x1f#32) = (blk.wordAt (off + 4) &&& 0x1f#32) ∧
      ((blk.wordAt (off + 4) >>> 5) &&& 0x1f#32) = (blk.wordAt off &&& 0x1f#32) ∧
      (blk.wordAt off &&& 0x1f#32) ≠ 0x1f#32 := by
  unfold CodeBlock.gotPairAt at h
  rw [hr1] at h
  cases hr2 : blk.relocAt? (off + 4) with
  | none => rw [hr2] at h; simp at h
  | some r2 =>
    rw [hr2] at h
    simp only [isAdrpWord, isLdr64UnsignedWord, Bool.and_eq_true, beq_iff_eq, bne_iff_ne,
      and_assoc] at h
    rcases h with ⟨hk1, hk2, hs, ha1, ha2, hw0, hw1, hm1, hm2, hne31⟩
    exact ⟨r2, rfl, hk1, hk2, hs, ha1, ha2, hw0, hw1, hm1, hm2, hne31⟩

/-- Step a relaxed adjacent GOT pair (`gotPairAt off = true` with `pl.relax off || pl.relax (off + 4)`),
    covering both `GotToNopAdr` (`pl.relax off = true`) and `GotToAdrpAdd`
    (`pl.relax off = false ∧ pl.relax (off + 4) = true`). -/
theorem sepWP_rebase_gotPair_relaxed {lib : PlacedLib} {pl : Placement} {off off8 : Nat}
    {X O X' O' : String → Option (State → State)} {svc : State → State}
    {r1 : RelocEntry} {rd : BitVec 5} {tgt : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hP : lib.Placeable pl)
    (hgp : lib.text.gotPairAt off = true)
    (hgpm4 : (off < 4 || !lib.text.gotPairAt (off - 4)) = true)
    (hr1 : lib.text.relocAt? off = some r1)
    (hrx : (pl.relax off || pl.relax (off + 4)) = true)
    (hrd : (lib.text.wordAt off).extractLsb' 0 5 = rd) (hrd31 : rd ≠ 31#5)
    (h8_eq : off + 8 = off8)
    (hh0 : ((lib.program pl X O svc).rebase pl.base X' O').hookAtOff? off = none)
    (hh4 : ((lib.program pl X O svc).rebase pl.base X' O').hookAtOff? (off + 4) = none)
    (hpc : s.pc = pl.base + BitVec.ofNat 64 off) (hrun : s.status = .Running)
    (hnext : SepWP ((lib.program pl X O svc).rebase pl.base X' O') tgt
      ((s.writeReg64 (.gpr rd) (lib.text.target pl r1)).setPC (pl.base + BitVec.ofNat 64 off8))
      P post oom) :
    SepWP ((lib.program pl X O svc).rebase pl.base X' O') tgt s P post oom := by
  subst h8_eq
  have h8 : pl.base + BitVec.ofNat 64 (off + 8) = s.pc + 8#64 := by
    rw [hpc, BitVec.ofNat_add, BitVec.add_assoc]
  rw [h8] at hnext
  obtain ⟨r2, hr2, hk1, hk2, hsym, ha1, ha2, hw0, hw1, hm1, hm2, _⟩ := gotPairAt_spec hgp hr1
  have hT2 : lib.text.target pl r2 = lib.text.target pl r1 := by
    simp only [CodeBlock.target, hsym, ha1, ha2]
  have hroff := CodeBlock.relocAt?_off hr1
  have hr2off := CodeBlock.relocAt?_off hr2
  obtain ⟨hal, hlen, hrange1⟩ := hP.text.relocs_ok r1 (CodeBlock.relocAt?_mem hr1)
  obtain ⟨hal2, hlen2, hrange2⟩ := hP.text.relocs_ok r2 (CodeBlock.relocAt?_mem hr2)
  rw [hroff] at hal hlen hrange1
  rw [hr2off] at hal2 hlen2 hrange2
  have hnw := hP.text.no_wrap
  obtain ⟨hrd1, hrn1⟩ := rd_fields_of_pair hrd hm1 hm2
  let prog := (lib.program pl X O svc).rebase pl.base X' O'
  have hf0 : prog.fetch (pl.base + BitVec.ofNat 64 off) = decode (lib.text.patchedWord pl off) :=
    Program.fetch_of_readWordOff (by omega) hh0 (CodeBlock.readWordOff_patched (by simp [prog]) hal hlen)
  have hf4 : prog.fetch (pl.base + BitVec.ofNat 64 (off + 4)) = decode (lib.text.patchedWord pl (off + 4)) :=
    Program.fetch_of_readWordOff (by omega) hh4 (CodeBlock.readWordOff_patched (by simp [prog]) hal2 hlen2)
  have hplace4 : pl.base + BitVec.ofNat 64 (off + 4) = s.pc + 4#64 := by
    rw [hpc, BitVec.ofNat_add, BitVec.add_assoc]
  rw [hplace4] at hf4
  have hrel0 : lib.text.relaxedAt pl off = false :=
    CodeBlock.relaxedAt_of_relaxableAt_false
      (CodeBlock.relaxableAt_false_of_kind hr1 (by rw [hk1]; decide))
  have hrel4 : lib.text.relaxedAt pl (off + 4) = false :=
    CodeBlock.relaxedAt_of_relaxableAt_false
      (CodeBlock.relaxableAt_false_of_kind hr2 (by rw [hk2]; decide))
  have hrelm4 : (4 ≤ off && lib.text.relaxedAt pl (off - 4)) = false := by
    by_cases h4 : 4 ≤ off
    · have hp : lib.text.relaxableAt (off - 4) = false :=
        CodeBlock.relaxableAt_false_of_next_kind (r := r1)
          (by rw [show off - 4 + 4 = off by omega]; exact hr1) (by rw [hk1]; decide)
      simp [h4, CodeBlock.relaxedAt_of_relaxableAt_false hp]
    · simp [h4]
  have hn4_or_ngp : ¬ 4 ≤ off ∨ lib.text.gotPairAt (off - 4) = false := by
    simpa [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', Nat.not_le] using hgpm4
  have hb1 : lib.text.b2bNext? r1 = none := by simp [CodeBlock.b2bNext?, hk1]
  have hb2 : lib.text.b2bNext? r2 = none := by simp [CodeBlock.b2bNext?, hk2]
  have hreg : Reg.fromZRBits rd = .gpr rd := fromZRBits_of_ne hrd31
  cases hrx0 : pl.relax off with
  | true =>
    have hw0_eq : lib.text.patchedWord pl off = nopWord := by
      unfold CodeBlock.patchedWord; rw [hr1]
      rcases hn4_or_ngp with hn4 | hngp <;>
        simp [RelocKind.isGotOrTlsIe, CodeBlock.patchGotOrTlsIeRelaxed, *]
    have hw1_eq : lib.text.patchedWord pl (off + 4) =
        adrWord (adrTemplate (lib.text.wordAt (off + 4)))
          (pl.base + BitVec.ofNat 64 (off + 4)) (lib.text.target pl r2) := by
      unfold CodeBlock.patchedWord; rw [hr2]
      have hsub : off + 4 - 4 = off := by omega
      simp [hrel4, hsub, hrel0, hk2, RelocKind.isGotOrTlsIe, hgp, hrx0,
        show 4 ≤ off + 4 by omega]
    rw [CodeBlock.relocTarget_of_b2bNext_none hb2, hk2, hT2] at hrange2
    have hadr : AdrInRange (s.pc + 4#64) (lib.text.target pl r1) := by
      unfold CodeBlock.relocInRange at hrange2
      have hsub : off + 4 - 4 = off := by omega
      rw [← hplace4]; simpa [show 4 ≤ off + 4 by omega, hsub, hgp, hrx0] using hrange2
    have hnop : decode nopWord = some .nop := rfl
    rw [hw0_eq, hnop] at hf0
    rw [hw1_eq, hT2, hplace4, decode_adrWord (adrTemplate_mask _) hadr, adrTemplate_rd, hrd1, hreg] at hf4
    refine SepWP.step_pure (s' := (s.setPC (pl.base + BitVec.ofNat 64 off)).advancePC)
      hpc hrun hf0 rfl rfl ?_
    refine SepWP.step_pure (s' := ((((s.setPC (pl.base + BitVec.ofNat 64 off)).advancePC).setPC
        (s.pc + 4#64)).writeReg64 (.gpr rd) (lib.text.target pl r1)).advancePC) ?_ ?_ hf4 ?_ rfl ?_
    · simp [State.advancePC, State.setPC, hpc]
    · simpa [State.advancePC, State.setPC] using hrun
    · simp only [Program.evalInst, execInstWithSvc, Bool.false_eq_true, ↓reduceIte, State.pc_setPC]
      congr 2; bv_lin
    · rw [hpc, nop_pair_state, ← hpc]; exact hnext
  | false =>
    rw [hrx0, Bool.false_or] at hrx
    have hw0_eq : lib.text.patchedWord pl off =
        adrpWord (lib.text.wordAt off) (pl.base + BitVec.ofNat 64 off) (lib.text.target pl r1) := by
      unfold CodeBlock.patchedWord; rw [hr1]
      rcases hn4_or_ngp with hn4 | hngp <;>
        simp [CodeBlock.relocTarget_of_b2bNext_none hb1, RelocKind.isGotOrTlsIe, patchRelocWord,
          CodeBlock.undefWeakBranch, *]
    have hw1_eq : lib.text.patchedWord pl (off + 4) =
        lo12Word 0 (ldrToAddWord (lib.text.wordAt (off + 4))) (lib.text.target pl r2) := by
      unfold CodeBlock.patchedWord; rw [hr2]
      have hsub : off + 4 - 4 = off := by omega
      simp [hrel4, hsub, hrel0, hk2, RelocKind.isGotOrTlsIe, hgp, hrx0, hrx,
        show 4 ≤ off + 4 by omega, CodeBlock.patchGotOrTlsIeRelaxed]
    rw [CodeBlock.relocTarget_of_b2bNext_none hb1, hk1] at hrange1
    simp only [CodeBlock.relocInRange, hrx0, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hrange1
    rw [hw0_eq, decode_adrpWord hw0 hrange1, hrd, hreg] at hf0
    rw [hw1_eq, hT2, decode_addLo12Word (ldrToAddWord_mask _), ldrToAddWord_rd, ldrToAddWord_rn,
      hrd1, hrn1, fromSPBits_of_ne hrd31] at hf4
    refine SepWP.step_pure (s' := ((s.setPC (pl.base + BitVec.ofNat 64 off)).writeReg64 (.gpr rd)
        (pageOf (lib.text.target pl r1))).advancePC) hpc hrun hf0 ?_ rfl ?_
    · simp only [Program.evalInst, execInstWithSvc, ite_true, State.pc_setPC]
      rw [adrp_pageOf_cancel]
    refine SepWP.step_pure (s' := (((((s.setPC (pl.base + BitVec.ofNat 64 off)).writeReg64 (.gpr rd)
        (pageOf (lib.text.target pl r1))).advancePC).setPC (s.pc + 4#64)).writeReg64 (.gpr rd)
        (lib.text.target pl r1)).advancePC) ?_ ?_ hf4 ?_ rfl ?_
    · simp [State.writeReg64, State.advancePC, State.setPC, hpc]
    · simpa [State.writeReg64, State.advancePC, State.setPC] using hrun
    · simp only [Program.evalInst, execInstWithSvc, execAddSubImm, Bool.false_eq_true,
        ↓reduceIte, zeroExtend_truncate_lo12Of, evalAddSub_w64_add, State.readReg,
        State.writeReg, readReg64_pair _ hrd31, pageOf_add_lo12Of]
    · rw [hpc, pair_state, ← hpc]; exact hnext

/-- Step the unrelaxed `ADRP` of an adjacent GOT pair (`pl.relax off = false`). -/
theorem sepWP_rebase_gotPair_adrp_unrelaxed {lib : PlacedLib} {pl : Placement} {off off4 : Nat}
    {X O X' O' : String → Option (State → State)} {svc : State → State}
    {r1 : RelocEntry} {rd : BitVec 5} {tgt : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hP : lib.Placeable pl)
    (hgpm4 : (off < 4 || !lib.text.gotPairAt (off - 4)) = true)
    (hr1 : lib.text.relocAt? off = some r1) (hk1 : r1.kind = .adrGotPage)
    (hrx0 : pl.relax off = false)
    (hw0 : lib.text.wordAt off &&& 0x9f000000#32 = 0x90000000#32)
    (hrd : (lib.text.wordAt off).extractLsb' 0 5 = rd) (hrd31 : rd ≠ 31#5)
    (h4_eq : off + 4 = off4)
    (hh0 : ((lib.program pl X O svc).rebase pl.base X' O').hookAtOff? off = none)
    (hpc : s.pc = pl.base + BitVec.ofNat 64 off) (hrun : s.status = .Running)
    (hnext : SepWP ((lib.program pl X O svc).rebase pl.base X' O') tgt
      ((s.writeReg64 (.gpr rd) (pageOf (lib.text.target pl r1))).setPC
        (pl.base + BitVec.ofNat 64 off4)) P post oom) :
    SepWP ((lib.program pl X O svc).rebase pl.base X' O') tgt s P post oom := by
  subst h4_eq
  have hroff := CodeBlock.relocAt?_off hr1
  obtain ⟨hal, hlen, hrange1⟩ := hP.text.relocs_ok r1 (CodeBlock.relocAt?_mem hr1)
  rw [hroff] at hal hlen hrange1
  have hnw := hP.text.no_wrap
  have hb1 : lib.text.b2bNext? r1 = none := by simp [CodeBlock.b2bNext?, hk1]
  rw [CodeBlock.relocTarget_of_b2bNext_none hb1, hk1] at hrange1
  simp only [CodeBlock.relocInRange, hrx0, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hrange1
  have hrel0 : lib.text.relaxedAt pl off = false :=
    CodeBlock.relaxedAt_of_relaxableAt_false
      (CodeBlock.relaxableAt_false_of_kind hr1 (by rw [hk1]; decide))
  have hrelm4 : (4 ≤ off && lib.text.relaxedAt pl (off - 4)) = false := by
    by_cases h4 : 4 ≤ off
    · have hp : lib.text.relaxableAt (off - 4) = false :=
        CodeBlock.relaxableAt_false_of_next_kind (r := r1)
          (by rw [show off - 4 + 4 = off by omega]; exact hr1) (by rw [hk1]; decide)
      simp [h4, CodeBlock.relaxedAt_of_relaxableAt_false hp]
    · simp [h4]
  have hn4_or_ngp : ¬ 4 ≤ off ∨ lib.text.gotPairAt (off - 4) = false := by
    simpa [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', Nat.not_le] using hgpm4
  have hw0_eq : lib.text.patchedWord pl off =
      adrpWord (lib.text.wordAt off) (pl.base + BitVec.ofNat 64 off) (lib.text.target pl r1) := by
    unfold CodeBlock.patchedWord; rw [hr1]
    rcases hn4_or_ngp with hn4 | hngp <;>
      simp [CodeBlock.relocTarget_of_b2bNext_none hb1, RelocKind.isGotOrTlsIe, patchRelocWord,
          CodeBlock.undefWeakBranch, *]
  let prog := (lib.program pl X O svc).rebase pl.base X' O'
  have hf0 : prog.fetch (pl.base + BitVec.ofNat 64 off) = decode (lib.text.patchedWord pl off) :=
    Program.fetch_of_readWordOff (by omega) hh0 (CodeBlock.readWordOff_patched (by simp [prog]) hal hlen)
  rw [hw0_eq, decode_adrpWord hw0 hrange1, hrd, fromZRBits_of_ne hrd31] at hf0
  have h4 : pl.base + BitVec.ofNat 64 (off + 4) = pl.base + BitVec.ofNat 64 off + 4#64 := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]
  rw [h4] at hnext
  refine SepWP.step_pure (s' := ((s.setPC (pl.base + BitVec.ofNat 64 off)).writeReg64 (.gpr rd)
      (pageOf (lib.text.target pl r1))).advancePC) hpc hrun hf0 ?_ rfl ?_
  · simp only [Program.evalInst, execInstWithSvc, ite_true, State.pc_setPC]
    rw [adrp_pageOf_cancel]
  · rw [write_advance_state]; exact hnext

/-- Fetch the unrelaxed `LDR` (`off + 4`) of an adjacent GOT pair
    (`pl.relax off = false ∧ pl.relax (off + 4) = false`). -/
theorem fetch_rebase_gotPair_ldr_unrelaxed {lib : PlacedLib} {pl : Placement} {off : Nat}
    {X O X' O' : String → Option (State → State)} {svc : State → State}
    {r1 r2 : RelocEntry} {inst : Instr}
    (hP : lib.Placeable pl)
    (hr1 : lib.text.relocAt? off = some r1) (hk1 : r1.kind = .adrGotPage)
    (hr2 : lib.text.relocAt? (off + 4) = some r2) (hk2 : r2.kind = .ld64GotLo12Nc)
    (hrx0 : pl.relax off = false) (hrx4 : pl.relax (off + 4) = false)
    (hh4 : ((lib.program pl X O svc).rebase pl.base X' O').hookAtOff? (off + 4) = none)
    {w1 : BitVec 32} (hwd1 : lib.text.wordAt (off + 4) = w1)
    (hscale : (w1.extractLsb' 30 2).toNat = 3)
    (hw1 : w1 &&& 0x3f000000#32 = 0x39000000#32)
    (hw2 : (w1 &&& 0xffc00000#32 == 0xf9800000#32) = false)
    (hinst : mkLoadStoreInst 3 (w1.extractLsb' 22 2).toNat (Reg.fromZRBits (w1.extractLsb' 0 5))
      (.Offset (Reg.fromSPBits (w1.extractLsb' 5 5)) (lo12Of (lib.text.target pl r2))) = some inst) :
    ((lib.program pl X O svc).rebase pl.base X' O').fetch
      (pl.base + BitVec.ofNat 64 (off + 4)) = some inst := by
  subst hwd1
  have hr2off := CodeBlock.relocAt?_off hr2
  obtain ⟨hal2, hlen2, hrange2⟩ := hP.text.relocs_ok r2 (CodeBlock.relocAt?_mem hr2)
  rw [hr2off] at hal2 hlen2 hrange2
  have hnw := hP.text.no_wrap
  have hb2 : lib.text.b2bNext? r2 = none := by simp [CodeBlock.b2bNext?, hk2]
  rw [CodeBlock.relocTarget_of_b2bNext_none hb2, hk2] at hrange2
  have hsub : off + 4 - 4 = off := by omega
  have hal : Lo12Aligned 3 (lib.text.target pl r2) := by
    unfold CodeBlock.relocInRange at hrange2
    simpa [show 4 ≤ off + 4 by omega, hsub, hrx0, hrx4] using hrange2
  have hrel0 : lib.text.relaxedAt pl off = false :=
    CodeBlock.relaxedAt_of_relaxableAt_false
      (CodeBlock.relaxableAt_false_of_kind hr1 (by rw [hk1]; decide))
  have hrel4 : lib.text.relaxedAt pl (off + 4) = false :=
    CodeBlock.relaxedAt_of_relaxableAt_false
      (CodeBlock.relaxableAt_false_of_kind hr2 (by rw [hk2]; decide))
  have hw1_eq : lib.text.patchedWord pl (off + 4) =
      lo12Word 3 (lib.text.wordAt (off + 4)) (lib.text.target pl r2) := by
    unfold CodeBlock.patchedWord; rw [hr2]
    simp [hrel4, hsub, hrel0, hrx0, hrx4, show 4 ≤ off + 4 by omega,
      CodeBlock.relocTarget_of_b2bNext_none hb2, hk2, patchRelocWord, CodeBlock.undefWeakBranch]
  let prog := (lib.program pl X O svc).rebase pl.base X' O'
  have hf4 : prog.fetch (pl.base + BitVec.ofNat 64 (off + 4)) =
      decode (lib.text.patchedWord pl (off + 4)) :=
    Program.fetch_of_readWordOff (by omega) hh4
      (CodeBlock.readWordOff_patched (by simp [prog]) hal2 hlen2)
  rw [hf4, hw1_eq, decode_ldstGprLo12Word hscale hw1 hw2 hal, hinst]

end GotHelpers

/-! ## Symbol Names and Placement Classes -/

abbrev coreOsFunctionsSym : String :=
  "core::io::error::os_functions::OS_FUNCTIONS"

abbrev coreGetOsFunctionsSym : String :=
  "core::io::error::os_functions::get_os_functions"

abbrev coreSetFunctionsInnerSym : String :=
  "core::io::error::os_functions::set_functions::set_functions_inner"

abbrev stdOsFunctionsGotSym : String :=
  "_RNvNtNtNtCs2kXltWtc1W_4core2io5error12os_functions12OS_FUNCTIONS"

abbrev stdGetOsFunctionsExternSym : String :=
  "_RNvNtNtNtCs2kXltWtc1W_4core2io5error12os_functions16get_os_functions"

abbrev stdSetFunctionsInnerExternSym : String :=
  "_RNvNvNtNtNtCs2kXltWtc1W_4core2io5error12os_functions13set_functions19set_functions_inner"

abbrev stdIsInterruptedSym : String :=
  "std::sys::io::error::unix::is_interrupted [rust_std_io]"

abbrev stdErrorFunctionsSym : String :=
  "rust_std_io:.data.rel.ro..Lanon.71"

abbrev stdNulErrSimpleMsgSym : String :=
  "rust_std_io:.data.rel.ro..Lanon.74"

class RustCoreOsFnPlacement where
  mpl : MultiPlacement
  placeable : rustCoreOsFnMultiLib.Placeable mpl

abbrev coreOsFnMpl [RustCoreOsFnPlacement] : MultiPlacement := RustCoreOsFnPlacement.mpl

class RustStdIoPlacement where
  mpl : MultiPlacement
  placeable : rustStdIoMultiLib.Placeable mpl

abbrev stdIoMpl [RustStdIoPlacement] : MultiPlacement := RustStdIoPlacement.mpl

theorem coreOsFnAddr_eq_base [RustCoreOsFnPlacement] (j : Nat) (sym : String)
    (hj : j < rustCoreOsFnMultiLib.blocks.length)
    (hl : lookup sym rustCoreOsFnMultiLib.blocks[j].symbols = some 0) :
    rustCoreOsFnMultiLib.fnAddr coreOsFnMpl sym = coreOsFnMpl.base j :=
  fnAddr_eq_base RustCoreOsFnPlacement.placeable j sym hj hl

theorem stdIoFnAddr_eq_base [RustStdIoPlacement] (j : Nat) (sym : String)
    (hj : j < rustStdIoMultiLib.blocks.length)
    (hl : lookup sym rustStdIoMultiLib.blocks[j].symbols = some 0) :
    rustStdIoMultiLib.fnAddr stdIoMpl sym = stdIoMpl.base j :=
  fnAddr_eq_base RustStdIoPlacement.placeable j sym hj hl

/-! ## Per-Block Projections and Fetch Lemmas -/

def coreOsFnLib00 : PlacedLib := rustCoreOsFnMultiLib.blockLib 0
def coreOsFnPl00 [RustCoreOsFnPlacement] : Placement :=
  rustCoreOsFnMultiLib.blockPlacement coreOsFnMpl 0
theorem coreOsFnPlaceable00 [RustCoreOsFnPlacement] : coreOsFnLib00.Placeable coreOsFnPl00 :=
  rustCoreOsFnMultiLib.placeable_blockLib (by decide) RustCoreOsFnPlacement.placeable
def coreOsFnPC00 [RustCoreOsFnPlacement] : Program := coreOsFnLib00.program coreOsFnPl00

def coreOsFnProg00 : Program :=
  { code := coreOsFnLib00.text.code, symbols := coreOsFnLib00.text.symbols }
def coreOsFnTree00 : WordTree := word_tree_of% coreOsFnProg00
theorem coreOsFn00_code_eq : coreOsFnLib00.text.code = coreOsFnTree00.toBytes := by rfl_kernel
theorem coreOsFn00_tree_size : coreOsFnTree00.checkSize? = some 4 := by rfl_kernel

gen_placed_fetches coreOsFnPC00 coreOsFnLib00 coreOsFnTree00 coreOsFn00_code_eq coreOsFn00_tree_size
  via_placement coreOsFnPl00 coreOsFnPlaceable00 [0x8 → 0xc]

def coreOsFnLib01 : PlacedLib := rustCoreOsFnMultiLib.blockLib 1
def coreOsFnPl01 [RustCoreOsFnPlacement] : Placement :=
  rustCoreOsFnMultiLib.blockPlacement coreOsFnMpl 1
theorem coreOsFnPlaceable01 [RustCoreOsFnPlacement] : coreOsFnLib01.Placeable coreOsFnPl01 :=
  rustCoreOsFnMultiLib.placeable_blockLib (by decide) RustCoreOsFnPlacement.placeable
def coreOsFnPC01 [RustCoreOsFnPlacement] : Program := coreOsFnLib01.program coreOsFnPl01

def coreOsFnProg01 : Program :=
  { code := coreOsFnLib01.text.code, symbols := coreOsFnLib01.text.symbols }
def coreOsFnTree01 : WordTree := word_tree_of% coreOsFnProg01
theorem coreOsFn01_code_eq : coreOsFnLib01.text.code = coreOsFnTree01.toBytes := by rfl_kernel
theorem coreOsFn01_tree_size : coreOsFnTree01.checkSize? = some 4 := by rfl_kernel

gen_placed_fetches coreOsFnPC01 coreOsFnLib01 coreOsFnTree01 coreOsFn01_code_eq coreOsFn01_tree_size
  via_placement coreOsFnPl01 coreOsFnPlaceable01 [0x8 → 0xc]

def stdIoLib28 : PlacedLib := rustStdIoMultiLib.blockLib 28
def stdIoPl28 [RustStdIoPlacement] : Placement :=
  rustStdIoMultiLib.blockPlacement stdIoMpl 28
theorem stdIoPlaceable28 [RustStdIoPlacement] : stdIoLib28.Placeable stdIoPl28 :=
  rustStdIoMultiLib.placeable_blockLib (by decide) RustStdIoPlacement.placeable
def stdIoPC28 [RustStdIoPlacement] : Program := stdIoLib28.program stdIoPl28

def stdIoProg28 : Program :=
  { code := stdIoLib28.text.code, symbols := stdIoLib28.text.symbols }
def stdIoTree28 : WordTree := word_tree_of% stdIoProg28
theorem stdIo28_code_eq : stdIoLib28.text.code = stdIoTree28.toBytes := by rfl_kernel
theorem stdIo28_tree_size : stdIoTree28.checkSize? = some 3 := by rfl_kernel

gen_placed_fetches stdIoPC28 stdIoLib28 stdIoTree28 stdIo28_code_eq stdIo28_tree_size
  via_placement stdIoPl28 stdIoPlaceable28 [0x0 → 0x8]

theorem coreBlockNoSvc0_00 : checkBlockNoSvc0 (rustCoreOsFnMultiLib.blockLib 0).text = true := by
  decide
theorem coreBlockNoSvc0_01 : checkBlockNoSvc0 (rustCoreOsFnMultiLib.blockLib 1).text = true := by
  decide
theorem stdIoBlockNoSvc0_28 : checkBlockNoSvc0 (rustStdIoMultiLib.blockLib 28).text = true := by
  decide

/-! ## `OS_FUNCTIONS` GOT-Relaxation Invariant -/

/-- GOT-access assertion for block `j` (`0` = `get_os_functions`, `1` = `set_functions_inner`)
    of `rustCoreOsFnMultiLib`: pure equality `mplCore.ρ coreOsFunctionsSym = osFnCell` when
    relaxed (`GotToNopAdr` or `GotToAdrpAdd`), or a read-only GOT slot `mplCore.ρ coreOsFunctionsSym
    ↦₆₄ᵣ osFnCell` when unrelaxed. -/
def CoreOsFnGotAt (mplCore : MultiPlacement) (j : Nat) (osFnCell : BitVec 64) : SepProp :=
  if mplCore.relax j 0 || mplCore.relax j 4 then
    ⌜mplCore.ρ coreOsFunctionsSym = osFnCell⌝
  else
    (mplCore.ρ coreOsFunctionsSym ↦₆₄ᵣ osFnCell)

/-- Combined `OS_FUNCTIONS` and `FUNCTIONS` state across `rustStdIoMultiLib` and
    `rustCoreOsFnMultiLib` at runtime cell `osFnCell` holding current table pointer `osFnVal`. -/
def rustOsFnReady [RustStdIoPlacement] [RustCoreOsFnPlacement]
    (osFnCell osFnVal : BitVec 64) : SepProp :=
  ⌜stdIoMpl.ρ stdGetOsFunctionsExternSym =
      rustCoreOsFnMultiLib.fnAddr coreOsFnMpl coreGetOsFunctionsSym ∧
    stdIoMpl.ρ stdSetFunctionsInnerExternSym =
      rustCoreOsFnMultiLib.fnAddr coreOsFnMpl coreSetFunctionsInnerSym⌝ ∗
  (osFnCell ↦₆₄ osFnVal) ∗
  (stdIoMpl.ρ stdOsFunctionsGotSym ↦₆₄ᵣ osFnCell) ∗
  ((stdIoMpl.ρ stdErrorFunctionsSym + 16#64) ↦₆₄ᵣ
    rustStdIoMultiLib.fnAddr stdIoMpl stdIsInterruptedSym) ∗
  CoreOsFnGotAt coreOsFnMpl 0 osFnCell ∗
  CoreOsFnGotAt coreOsFnMpl 1 osFnCell

/-! ## Subroutine Contracts -/

section Proofs
arm64_proof_prelude

/-- Program-generic contract for `std::sys::io::error::unix::is_interrupted` under
    `CodeLoadedWhere keep`. -/
theorem rustIsInterrupted_okWhere [RustStdIoPlacement] {keep : Nat → Bool}
    (hk28 : keep 28 = true := by decide) {P : Program}
    (hext : ∀ pc, P.externAt? pc = none := by intro; simp)
    (hsvc : P.svc = Syscall.standard := by rfl) :
    subroutine_ok P (rustStdIoMultiLib.fnAddr stdIoMpl stdIsInterruptedSym)
      (rustStdIoMultiLib.withCodeLoadedWhere keep stdIoMpl rustIsInterruptedSpec) := by
  rw [stdIoFnAddr_eq_base 28 stdIsInterruptedSym (by decide) (by decide)]
  apply subroutine_ok_of_sepWP_init; intro err R s0 hpc hrun hpre _hsp
  dsimp only [MultiPlacedLib.withCodeLoadedWhere, rustIsInterruptedSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨hx0, hpre⟩
  rw [satisfies_pure_sepConj] at hpre; rcases hpre with ⟨hcl, hR⟩
  refine ⟨emp, by simpa [emp_sepConj] using hR, ?_⟩
  apply sepWP_prog_to_rebaseWhere hext hsvc 28 ⟨by decide, hk28⟩ hcl
  change SepWP (stdIoPC28.rebase stdIoPl28.base (fun _ => none)) _ _ _ _
  have hpc' : s0.pc = stdIoPl28.base := hpc; clear hpc; rename_i hpc; wp_steps
  refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) ?_
  refine ⟨?_, by simp [wp_norm, arm64_norm], by simp [CalleeSavedPreserved, calleeSavedVRegs, wp_norm, arm64_norm]⟩
  intro _; rw [satisfies_pure_sepConj]; refine ⟨⟨?_, ?_, rfl, ?_⟩, hR⟩
  · subst hx0; simp only [State.readReg32] at *
    by_cases h4 : (BitVec.truncate 32 (s0.readReg64 (.gpr 0#5)) == 4#32) = true
    · have hne : (BitVec.truncate 32 (s0.readReg64 (.gpr 0#5)) != 4#32) = false := by simp [bne, h4]
      simp [wp_norm, arm64_norm, h4, hne]
    · simp only [Bool.not_eq_true] at h4
      have hne : (BitVec.truncate 32 (s0.readReg64 (.gpr 0#5)) != 4#32) = true := by simp [bne, h4]
      simp [wp_norm, arm64_norm, h4, hne]
  · subst hx0; simp only [State.readReg32] at *
    by_cases h4 : (BitVec.truncate 32 (s0.readReg64 (.gpr 0#5)) == 4#32) = true
    · have hne : (BitVec.truncate 32 (s0.readReg64 (.gpr 0#5)) != 4#32) = false := by simp [bne, h4]
      simp [wp_norm, arm64_norm, h4, hne]
    · simp only [Bool.not_eq_true] at h4
      have hne : (BitVec.truncate 32 (s0.readReg64 (.gpr 0#5)) != 4#32) = true := by simp [bne, h4]
      simp [wp_norm, arm64_norm, h4, hne]
  · cases s0; exact ProcessFieldsPreserved.refl _

theorem rustIsInterrupted_block_okWhere [RustStdIoPlacement] {keep : Nat → Bool}
    (hk28 : keep 28 = true := by decide) :
    subroutine_ok (rustStdIoMultiLib.blockProgram stdIoMpl 28)
      (rustStdIoMultiLib.fnAddr stdIoMpl stdIsInterruptedSym)
      (rustStdIoMultiLib.withCodeLoadedWhere keep stdIoMpl rustIsInterruptedSpec) :=
  rustIsInterrupted_okWhere hk28 (by intro; simp) rfl

theorem rustIsInterrupted_block_ok [RustStdIoPlacement] :
    subroutine_ok (rustStdIoMultiLib.blockProgram stdIoMpl 28)
      (rustStdIoMultiLib.fnAddr stdIoMpl stdIsInterruptedSym)
      (rustStdIoMultiLib.withCodeLoaded stdIoMpl rustIsInterruptedSpec) :=
  rustStdIoMultiLib.subroutine_ok_withCodeLoaded_of_where
    (rustIsInterrupted_block_okWhere (keep := fun _ => true) rfl)

/-- Program-generic contract for `std::sys::io::error::unix::is_interrupted`. -/
theorem rustIsInterrupted_ok [RustStdIoPlacement] {P : Program}
    (hext : ∀ pc, P.externAt? pc = none := by intro; simp)
    (hsvc : P.svc = Syscall.standard := by rfl) :
    subroutine_ok P (rustStdIoMultiLib.fnAddr stdIoMpl stdIsInterruptedSym)
      (rustStdIoMultiLib.withCodeLoaded stdIoMpl rustIsInterruptedSpec) :=
  rustStdIoMultiLib.subroutine_ok_withCodeLoaded_of_where
    (rustIsInterrupted_okWhere (keep := fun _ => true) rfl hext hsvc)

/-- Contract for `core::io::error::os_functions::get_os_functions() -> &'static OsFunctions`
    across all GOT relaxation modes. -/
def rustGetOsFunctionsSpec [RustCoreOsFnPlacement] : Spec (BitVec 64 × BitVec 64) where
  pre := fun (osFnCell, osFnVal) _s0 =>
    (osFnCell ↦₆₄ osFnVal) ∗ CoreOsFnGotAt coreOsFnMpl 0 osFnCell
  post := fun (osFnCell, osFnVal) s0 sf =>
    ⌜sf.readReg64 .x0 = osFnVal ∧ sf.mem = s0.mem ∧ StdStatePreserved s0 sf⌝ ∗
    ((osFnCell ↦₆₄ osFnVal) ∗ CoreOsFnGotAt coreOsFnMpl 0 osFnCell)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

theorem rustGetOsFunctions_block_ok [RustCoreOsFnPlacement] :
    subroutine_ok (rustCoreOsFnMultiLib.blockProgram coreOsFnMpl 0)
      (rustCoreOsFnMultiLib.fnAddr coreOsFnMpl coreGetOsFunctionsSym)
      (rustCoreOsFnMultiLib.withCodeLoaded coreOsFnMpl rustGetOsFunctionsSpec) := by
  rw [coreOsFnAddr_eq_base 0 coreGetOsFunctionsSym (by decide) (by decide)]
  apply subroutine_ok_of_sepWP_init; rintro ⟨osFnCell, osFnVal⟩ R s0 hpc hrun hpre _hsp
  dsimp only [MultiPlacedLib.withCodeLoaded, rustGetOsFunctionsSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜rustCoreOsFnMultiLib.CodeLoaded coreOsFnMpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl, hpre⟩
  refine ⟨_, hpre, ?_⟩
  apply sepWP_block_to_rebase 0 (by decide) hcl
  change SepWP (coreOsFnPC00.rebase coreOsFnPl00.base (fun _ => none)) _ _ _ _
  have hpc0 : s0.pc = coreOsFnPl00.base + BitVec.ofNat 64 0 := by
    rw [hpc]; simp [coreOsFnPl00, MultiPlacedLib.blockPlacement]
  have htarget : coreOsFnLib00.text.target coreOsFnPl00
      ⟨0, .adrGotPage, coreOsFunctionsSym, 0, false⟩ = coreOsFnMpl.ρ coreOsFunctionsSym := rfl
  unfold CoreOsFnGotAt
  by_cases hrx : (coreOsFnMpl.relax 0 0 || coreOsFnMpl.relax 0 4) = true
  · wp_conv_pre => simp only [hrx, ↓reduceIte, sepConj_comm (osFnCell ↦₆₄ osFnVal)]
    apply SepWP.pure_elim; intro hT_eq
    apply sepWP_rebase_gotPair_relaxed (lib := coreOsFnLib00) (pl := coreOsFnPl00) (off := 0)
      (off8 := 8) (r1 := ⟨0, .adrGotPage, coreOsFunctionsSym, 0, false⟩) (rd := 8#5)
      coreOsFnPlaceable00 (by decide) (by decide) rfl hrx rfl (by decide) rfl
      (hookAtOff?_rebase_of_placeable coreOsFn00_code_eq coreOsFn00_tree_size coreOsFnPlaceable00 (by omega))
      (hookAtOff?_rebase_of_placeable coreOsFn00_code_eq coreOsFn00_tree_size coreOsFnPlaceable00 (by omega))
      hpc0 hrun
    change SepWP (coreOsFnPC00.rebase coreOsFnPl00.base (fun _ => none)) _ _ _ _
    rw [htarget, hT_eq]
    wp_sym_steps
    refine SepWP.done (by rfl) (by simpa [arm64_norm] using hrun) ?_
    refine ⟨?_, by simp [arm64_norm], by simp [CalleeSavedPreserved, calleeSavedVRegs, arm64_norm]⟩
    intro hm
    refine Satisfies.mono ?_ hm
    simp only [hrx, ↓reduceIte, sepConj_pure_true]
    rw [pure_sepConj_of_true ⟨by simp [arm64_norm], rfl,
      by simp [StdStatePreserved, State.writeReg64, State.setPC]⟩]
    sep_entail
  · simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hrx
    rcases hrx with ⟨hrx0, hrx4⟩
    have hrx_if : (coreOsFnMpl.relax 0 0 || coreOsFnMpl.relax 0 4) = false := by simp [hrx0, hrx4]
    wp_conv_pre => simp only [hrx_if, Bool.false_eq_true, ↓reduceIte]
    apply sepWP_rebase_gotPair_adrp_unrelaxed (lib := coreOsFnLib00) (pl := coreOsFnPl00) (off := 0)
      (off4 := 4) (r1 := ⟨0, .adrGotPage, coreOsFunctionsSym, 0, false⟩) (rd := 8#5)
      coreOsFnPlaceable00 (by decide) rfl rfl hrx0 (by decide) rfl (by decide) rfl
      (hookAtOff?_rebase_of_placeable coreOsFn00_code_eq coreOsFn00_tree_size coreOsFnPlaceable00 (by omega))
      hpc0 hrun
    change SepWP (coreOsFnPC00.rebase coreOsFnPl00.base (fun _ => none)) _ _ _ _
    have hfe4 : (coreOsFnPC00.rebase coreOsFnPl00.base (fun _ => none)).fetch
        (coreOsFnPl00.base + BitVec.ofNat 64 4) =
        some (.ldr .W64 .X64 false (.gpr 8#5)
          (.Offset (.gpr 8#5) (lo12Of (coreOsFnMpl.ρ coreOsFunctionsSym)))) :=
      fetch_rebase_gotPair_ldr_unrelaxed (lib := coreOsFnLib00) (pl := coreOsFnPl00) (off := 0)
        (r1 := ⟨0, .adrGotPage, coreOsFunctionsSym, 0, false⟩)
        (r2 := ⟨4, .ld64GotLo12Nc, coreOsFunctionsSym, 0, false⟩)
        coreOsFnPlaceable00 rfl rfl rfl rfl hrx0 hrx4
        (hookAtOff?_rebase_of_placeable coreOsFn00_code_eq coreOsFn00_tree_size coreOsFnPlaceable00 (by omega))
        (wordAt_of_getQuad? coreOsFn00_code_eq coreOsFn00_tree_size (j := 1) rfl)
        rfl (by decide) (by decide) rfl
    rw [htarget]
    wp_step
    wp_sym_steps
    refine SepWP.done (by rfl) (by simpa [arm64_norm] using hrun) ?_
    refine ⟨?_, by simp [arm64_norm], by simp [CalleeSavedPreserved, calleeSavedVRegs, arm64_norm]⟩
    intro hm
    refine Satisfies.mono ?_ hm
    simp only [hrx_if, Bool.false_eq_true, ↓reduceIte]
    rw [pure_sepConj_of_true ⟨by simp [arm64_norm], rfl,
      by simp [StdStatePreserved, State.writeReg64, State.setPC]⟩]
    sep_entail

/-- Program-generic contract for `core::io::error::os_functions::get_os_functions`. -/
theorem rustGetOsFunctions_ok [RustCoreOsFnPlacement] {P : Program}
    (hext : ∀ pc, P.externAt? pc = none := by intro; simp)
    (hsvc : P.svc = Syscall.standard := by rfl) :
    subroutine_ok P (rustCoreOsFnMultiLib.fnAddr coreOsFnMpl coreGetOsFunctionsSym)
      (rustCoreOsFnMultiLib.withCodeLoaded coreOsFnMpl rustGetOsFunctionsSpec) :=
  rustCoreOsFnMultiLib.subroutine_ok_of_block (j := 0) (by decide) rustGetOsFunctions_block_ok hext hsvc

theorem stdStatePreserved_of_seg {s s' sm' sm : State}
    (h_in : SameCpuState s' s) (h_out : SameCpuState sm sm')
    (hnsp : ProofLib.NonSyscallPreserved s sm)
    (htp : sm'.tpidrEl0 = s'.tpidrEl0) (hsig : sm'.sigActions = s'.sigActions) :
    StdStatePreserved s sm :=
  have hp := syscallPreserved_of_seg h_in h_out hnsp htp hsig
  ⟨hnsp.2.2.2.2.2.2, hnsp.1, hp.1, hp.2.1, hnsp.2.2.1, hnsp.2.2.2.1, hnsp.2.2.2.2.1,
    fun a => congrFun hnsp.2.1 a⟩

/-- Contract for `core::io::error::os_functions::set_functions::set_functions_inner(f)`
    across all three GOT relaxation modes. -/
def rustSetFunctionsInnerSpec [RustCoreOsFnPlacement] :
    Spec (BitVec 64 × BitVec 64 × BitVec 64) where
  pre := fun (osFnCell, oldVal, newVal) s0 =>
    ⌜s0.readReg64 .x0 = newVal⌝ ∗
    ((osFnCell ↦₆₄ oldVal) ∗ CoreOsFnGotAt coreOsFnMpl 1 osFnCell)
  post := fun (osFnCell, _, newVal) s0 sf =>
    ⌜StdStatePreserved s0 sf⌝ ∗
    ((osFnCell ↦₆₄ newVal) ∗ CoreOsFnGotAt coreOsFnMpl 1 osFnCell)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Program-generic contract for `core::io::error::os_functions::set_functions::set_functions_inner`
    across all three GOT relaxation modes. -/
theorem rustSetFunctionsInner_ok [RustCoreOsFnPlacement] {P : Program}
    (hext : ∀ pc, P.externAt? pc = none := by intro; simp) :
    subroutine_ok P (rustCoreOsFnMultiLib.fnAddr coreOsFnMpl coreSetFunctionsInnerSym)
      (rustCoreOsFnMultiLib.withCodeLoaded coreOsFnMpl rustSetFunctionsInnerSpec) := by
  rw [coreOsFnAddr_eq_base 1 coreSetFunctionsInnerSym (by decide) (by decide)]
  apply subroutine_ok_of_sepWP_init; rintro ⟨osFnCell, oldVal, newVal⟩ R s0 hpc hrun hpre _hsp
  dsimp only [MultiPlacedLib.withCodeLoaded, rustSetFunctionsInnerSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜rustCoreOsFnMultiLib.CodeLoaded coreOsFnMpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hx0, hpre⟩
  refine ⟨_, hpre, ?_⟩
  apply sepWP_seg_rebase_pure hext 1 (by decide) coreBlockNoSvc0_01 hcl (mid := s0.readReg64 .lr)
  intro s0' hcpu0
  change SepWP (coreOsFnPC01.rebase coreOsFnPl01.base (fun _ => none)) _ _ _ _
  have hpc0 : s0'.pc = coreOsFnPl01.base + BitVec.ofNat 64 0 := by
    rw [hcpu0.pc_eq, hpc]; simp [coreOsFnPl01, MultiPlacedLib.blockPlacement]
  have hrun0 : s0'.status = .Running := hcpu0.status_eq.trans hrun
  have hx0' : s0'.readReg64 .x0 = newVal := (hcpu0.readReg64 .x0).trans hx0
  have hlr0' : s0'.readReg64 (.gpr 30#5) = s0.readReg64 .lr := hcpu0.readReg64 .lr
  have htarget : coreOsFnLib01.text.target coreOsFnPl01
      ⟨0, .adrGotPage, coreOsFunctionsSym, 0, false⟩ = coreOsFnMpl.ρ coreOsFunctionsSym := rfl
  unfold CoreOsFnGotAt
  by_cases hrx : (coreOsFnMpl.relax 1 0 || coreOsFnMpl.relax 1 4) = true
  · wp_conv_pre => simp only [hrx, ↓reduceIte, sepConj_comm (osFnCell ↦₆₄ oldVal)]
    apply SepWP.pure_elim; intro hT_eq
    apply sepWP_rebase_gotPair_relaxed (lib := coreOsFnLib01) (pl := coreOsFnPl01) (off := 0)
      (off8 := 8) (r1 := ⟨0, .adrGotPage, coreOsFunctionsSym, 0, false⟩) (rd := 8#5)
      coreOsFnPlaceable01 (by decide) (by decide) rfl hrx rfl (by decide) rfl
      (hookAtOff?_rebase_of_placeable coreOsFn01_code_eq coreOsFn01_tree_size coreOsFnPlaceable01 (by omega))
      (hookAtOff?_rebase_of_placeable coreOsFn01_code_eq coreOsFn01_tree_size coreOsFnPlaceable01 (by omega))
      hpc0 hrun0
    change SepWP (coreOsFnPC01.rebase coreOsFnPl01.base (fun _ => none)) _ _ _ _
    rw [htarget, hT_eq]
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun0)
      fun sf hcpu_f _hcl_f hnsp => ?_
    have hstd := stdStatePreserved_of_seg hcpu0 hcpu_f hnsp (by simp [arm64_norm]) (by simp [arm64_norm])
    have hcs : CalleeSavedPreserved s0 sf := by
      rw [CalleeSavedPreserved.iff_regs]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hcpu_f.readReg64 (.gpr 19#5)]; simp [arm64_norm, hcpu0.readReg64 (.gpr 19#5)]
      · rw [hcpu_f.readReg64 (.gpr 20#5)]; simp [arm64_norm, hcpu0.readReg64 (.gpr 20#5)]
      · rw [hcpu_f.readReg64 (.gpr 21#5)]; simp [arm64_norm, hcpu0.readReg64 (.gpr 21#5)]
      · rw [hcpu_f.readReg64 (.gpr 22#5)]; simp [arm64_norm, hcpu0.readReg64 (.gpr 22#5)]
      · rw [hcpu_f.readReg64 (.gpr 23#5)]; simp [arm64_norm, hcpu0.readReg64 (.gpr 23#5)]
      · rw [hcpu_f.readReg64 (.gpr 24#5)]; simp [arm64_norm, hcpu0.readReg64 (.gpr 24#5)]
      · rw [hcpu_f.readReg64 (.gpr 25#5)]; simp [arm64_norm, hcpu0.readReg64 (.gpr 25#5)]
      · rw [hcpu_f.readReg64 (.gpr 26#5)]; simp [arm64_norm, hcpu0.readReg64 (.gpr 26#5)]
      · rw [hcpu_f.readReg64 (.gpr 27#5)]; simp [arm64_norm, hcpu0.readReg64 (.gpr 27#5)]
      · rw [hcpu_f.readReg64 (.gpr 28#5)]; simp [arm64_norm, hcpu0.readReg64 (.gpr 28#5)]
      · rw [hcpu_f.readReg64 Reg.fp]; simp [arm64_norm, hcpu0.readReg64 Reg.fp]
      · rw [hcpu_f.calleeSavedVRegs]; simp [arm64_norm, hcpu0.calleeSavedVRegs]
    refine SepWP.done (by rw [hcpu_f.pc_eq]; simp [arm64_norm])
      (by rw [hcpu_f.status_eq]; simpa [arm64_norm] using hrun0) ?_
    refine ⟨?_, by rw [hcpu_f.sp_eq]; simp [arm64_norm, hcpu0.sp_eq], hcs⟩
    intro hm
    refine Satisfies.mono ?_ hm
    simp only [hrx, ↓reduceIte, sepConj_pure_true, ← hx0']
    rw [pure_sepConj_of_true hstd]; sep_entail
  · simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hrx
    rcases hrx with ⟨hrx0, hrx4⟩
    have hrx_if : (coreOsFnMpl.relax 1 0 || coreOsFnMpl.relax 1 4) = false := by simp [hrx0, hrx4]
    wp_conv_pre => simp only [hrx_if, Bool.false_eq_true, ↓reduceIte]
    apply sepWP_rebase_gotPair_adrp_unrelaxed (lib := coreOsFnLib01) (pl := coreOsFnPl01) (off := 0)
      (off4 := 4) (r1 := ⟨0, .adrGotPage, coreOsFunctionsSym, 0, false⟩) (rd := 8#5)
      coreOsFnPlaceable01 (by decide) rfl rfl hrx0 (by decide) rfl (by decide) rfl
      (hookAtOff?_rebase_of_placeable coreOsFn01_code_eq coreOsFn01_tree_size coreOsFnPlaceable01 (by omega))
      hpc0 hrun0
    change SepWP (coreOsFnPC01.rebase coreOsFnPl01.base (fun _ => none)) _ _ _ _
    have hfe4 : (coreOsFnPC01.rebase coreOsFnPl01.base (fun _ => none)).fetch
        (coreOsFnPl01.base + BitVec.ofNat 64 4) =
        some (.ldr .W64 .X64 false (.gpr 8#5)
          (.Offset (.gpr 8#5) (lo12Of (coreOsFnMpl.ρ coreOsFunctionsSym)))) :=
      fetch_rebase_gotPair_ldr_unrelaxed (lib := coreOsFnLib01) (pl := coreOsFnPl01) (off := 0)
        (r1 := ⟨0, .adrGotPage, coreOsFunctionsSym, 0, false⟩)
        (r2 := ⟨4, .ld64GotLo12Nc, coreOsFunctionsSym, 0, false⟩)
        coreOsFnPlaceable01 rfl rfl rfl rfl hrx0 hrx4
        (hookAtOff?_rebase_of_placeable coreOsFn01_code_eq coreOsFn01_tree_size coreOsFnPlaceable01 (by omega))
        (wordAt_of_getQuad? coreOsFn01_code_eq coreOsFn01_tree_size (j := 1) rfl)
        rfl (by decide) (by decide) rfl
    rw [htarget]
    wp_step
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun0)
      fun sf hcpu_f _hcl_f hnsp => ?_
    have hstd := stdStatePreserved_of_seg hcpu0 hcpu_f hnsp (by simp [arm64_norm]) (by simp [arm64_norm])
    have hcs : CalleeSavedPreserved s0 sf := by
      rw [CalleeSavedPreserved.iff_regs]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hcpu_f.readReg64 (.gpr 19#5)]; simp [arm64_norm, hcpu0.readReg64 (.gpr 19#5)]
      · rw [hcpu_f.readReg64 (.gpr 20#5)]; simp [arm64_norm, hcpu0.readReg64 (.gpr 20#5)]
      · rw [hcpu_f.readReg64 (.gpr 21#5)]; simp [arm64_norm, hcpu0.readReg64 (.gpr 21#5)]
      · rw [hcpu_f.readReg64 (.gpr 22#5)]; simp [arm64_norm, hcpu0.readReg64 (.gpr 22#5)]
      · rw [hcpu_f.readReg64 (.gpr 23#5)]; simp [arm64_norm, hcpu0.readReg64 (.gpr 23#5)]
      · rw [hcpu_f.readReg64 (.gpr 24#5)]; simp [arm64_norm, hcpu0.readReg64 (.gpr 24#5)]
      · rw [hcpu_f.readReg64 (.gpr 25#5)]; simp [arm64_norm, hcpu0.readReg64 (.gpr 25#5)]
      · rw [hcpu_f.readReg64 (.gpr 26#5)]; simp [arm64_norm, hcpu0.readReg64 (.gpr 26#5)]
      · rw [hcpu_f.readReg64 (.gpr 27#5)]; simp [arm64_norm, hcpu0.readReg64 (.gpr 27#5)]
      · rw [hcpu_f.readReg64 (.gpr 28#5)]; simp [arm64_norm, hcpu0.readReg64 (.gpr 28#5)]
      · rw [hcpu_f.readReg64 Reg.fp]; simp [arm64_norm, hcpu0.readReg64 Reg.fp]
      · rw [hcpu_f.calleeSavedVRegs]; simp [arm64_norm, hcpu0.calleeSavedVRegs]
    refine SepWP.done (by rw [hcpu_f.pc_eq]; simp [arm64_norm])
      (by rw [hcpu_f.status_eq]; simpa [arm64_norm] using hrun0) ?_
    refine ⟨?_, by rw [hcpu_f.sp_eq]; simp [arm64_norm, hcpu0.sp_eq], hcs⟩
    intro hm
    refine Satisfies.mono ?_ hm
    simp only [hrx_if, Bool.false_eq_true, ↓reduceIte, ← hx0']
    rw [pure_sepConj_of_true hstd]; sep_entail

end Proofs

end VerifiedLibraries.RustStd.Io
