/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymFast -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySym

/-!
# `encapsulate1_serialized` (`B03`) — Symbolic NEON Certificates for `Seg3` (`Seg3Sym`)

Adapts `Mlkem1024.Decaps.PolySym*` to `B03` (`blkTree03` / `blkPC03`), adding read-only `src0`
support at `[sp + 4272, sp + 4784)` and certifying:
1. `Seg3` upper `Fwd2` NTT (`+0x3760 .. +0x4398`, `w = 3544 .. 4326`) → `lowerNttBinomial5_16`.
2. `Seg3` Barrett reduction (`+0x4484 .. +0x4720`, `w = 4385 .. 4552`) → `neonBarrettReduce16`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Sym

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open ProofLib.ProgramReflection (WordTree)
open ProofLib.GenPlacedFetches (fetch_rebase_of_noReloc hookAtOff?_rebase_of_placeable)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemPlacement)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem SepLoad128 Vec32 step_ldrQ128)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (
  SExpr SymCfg SymEnv SymGpr SymSpill40 SymState evalSExpr stepSymInst)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge (
  SymSpatial SymStateMatches matches_setPC matches_writeVReg sp_range_off)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySym (
  sepWP_of_stepSymInst)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymFast (
  stepSymInstFast stepSymInstFast_eq symGprBeq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure (
  polyAstEq polyNoSpillVreg symBarrett symLowerNttBinomial5)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (
  blk03_code_eq blk03_tree_size blkLib03 blkPC03 blkPl03 blkPlaceable03 blkTree03)

/-! ## 1. Relocation-Free Fetch on Clean `[wLo, wHi)` Slices of `B03` -/

@[expose] def fetchWordTree03 (j : Nat) : Option Instr :=
  match blkTree03.getQuad? j with
  | some (b0, b1, b2, b3) => decode (b3 ++ b2 ++ b1 ++ b0)
  | none => none

@[expose] def blk03NoRelocInRange (wLo wHi : Nat) : Bool :=
  blkLib03.text.relocs.all (fun r => decide (r.off < 4 * wLo ∨ 4 * wHi ≤ r.off))

theorem blk03_relocAt?_range {wLo wHi off : Nat}
    (hnr : blk03NoRelocInRange wLo wHi = true)
    (hlo : 4 * wLo ≤ off) (hhi : off < 4 * wHi) :
    (blkLib03.text.relocAt? off).isNone = true := by
  cases hr : blkLib03.text.relocAt? off with
  | none => rfl
  | some r =>
    have hmem := CodeBlock.relocAt?_mem hr
    have hoff := CodeBlock.relocAt?_off hr
    have hall := (List.all_eq_true.mp hnr) r hmem
    simp only [decide_eq_true_eq] at hall
    omega

theorem fetch_blk03_range [MlKemPlacement] {b : BitVec 64} {wLo wHi j : Nat} {inst : Instr}
    (hnr : blk03NoRelocInRange wLo wHi = true) (hmax : wHi ≤ 7114)
    (hlo : wLo ≤ j) (hhi : j < wHi) (hfw : fetchWordTree03 j = some inst) :
    (blkPC03.rebase b (fun _ => none)).fetch (b + BitVec.ofNat 64 (4 * j)) = some inst := by
  have hdec : blkTree03.fetchDecodeAt (4 * j) = some inst := by
    unfold WordTree.fetchDecodeAt
    have hdiv : 4 * j / 4 = j := by omega
    rw [hdiv]
    unfold fetchWordTree03 at hfw
    cases hq : blkTree03.getQuad? j with
    | none => simp [hq] at hfw
    | some q =>
      rcases q with ⟨b0, b1, b2, b3⟩
      simp [hq] at hfw ⊢
      exact hfw
  have hnh := hookAtOff?_rebase_of_placeable (pl := blkPl03) (b := b)
    (X := fun _ => none) blk03_code_eq blk03_tree_size blkPlaceable03 (off := 4 * j) (by omega)
  exact fetch_rebase_of_noReloc blk03_code_eq blk03_tree_size
    (by omega) (by omega) (by omega) hdec
    (blk03_relocAt?_range hnr (by omega) (by omega)) hnh

/-! ## 2. `B03` Symbolic Stepper with Optional `[sp + 4272, sp + 4784)` `src0` -/

@[expose] def Src4272OptMem (src4272 : Bool) (sp : BitVec 64) (src0 : Vec32) : SepProp :=
  if src4272 then Poly32Mem (sp + 4272#64) src0 else emp

@[expose] def SymSpatial03 (src4272 : Bool) (cfg : SymCfg) (sp : BitVec 64)
    (env : SymEnv) (st : SymState) (F : SepProp) : SepProp :=
  SymSpatial cfg sp env st (Src4272OptMem src4272 sp env.src0 ∗ F)

@[expose] def stepSymInst03Fast (src4272 : Bool) (cfg : SymCfg) (inst : Instr)
    (st : SymState) : Option SymState :=
  match inst with
  | .ldrSimd .Q128 vt (.Offset .sp off) =>
      let o := off.toNat
      if src4272 && Nat.ble 4272 o && Nat.blt o 4784 && (o - 4272) % 16 == 0 then
        some { st with vregs := st.vregs.set vt.toNat (.src ((o - 4272) / 16)) }
      else stepSymInstFast cfg inst st
  | _ => stepSymInstFast cfg inst st

@[expose] def runSymRange03Fast (src4272 : Bool) (cfg : SymCfg) :
    Nat → Nat → SymState → Option SymState
  | _, 0, st => some st
  | w, n + 1, st =>
      match fetchWordTree03 w with
      | some inst =>
          match stepSymInst03Fast src4272 cfg inst st with
          | some st' => runSymRange03Fast src4272 cfg (w + 1) n st'
          | none => none
      | none => none

theorem sepWP_of_stepSymInst03 {prog : Program} {tgt pc : BitVec 64}
    {src4272 : Bool} {cfg : SymCfg} {s : State} {sp : BitVec 64} {env : SymEnv}
    {st st' : SymState} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {inst : Instr}
    (hm : SymStateMatches sp env st s) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some inst)
    (hstep : stepSymInst03Fast src4272 cfg inst st = some st')
    (hnext : ∀ s' : State, s'.pc = pc + 4#64 → s'.status = .Running →
      SymStateMatches sp env st' s' →
      SepWP prog tgt s' (SymSpatial03 src4272 cfg sp env st' F) post oom) :
    SepWP prog tgt s (SymSpatial03 src4272 cfg sp env st F) post oom := by
  by_cases hldr : ∃ vt off, inst = .ldrSimd .Q128 vt (.Offset .sp off) ∧
      (src4272 && Nat.ble 4272 off.toNat && Nat.blt off.toNat 4784 &&
        (off.toNat - 4272) % 16 == 0) = true
  · rcases hldr with ⟨vt, off, rfl, hc⟩
    simp only [stepSymInst03Fast, hc, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, beq_iff_eq] at hc
    have hsrc : src4272 = true := hc.1.1.1; subst hsrc
    obtain ⟨hk, ha⟩ := sp_range_off (sp := sp) (base := 4272) (len := 32) hc.1.1.2 (by omega) hc.2
    have hsp_chk : checkAddrSPAligned s (.Offset .sp off) = true := hm.hsp_al
    have haddr : evalAddrMode s (.Offset .sp off) = (sp + off, none) := by
      simp [evalAddrMode, State.readReg64, hm.hsp]
    have hld : SepLoad128 (sp + off) (Src4272OptMem true sp env.src0)
        (evalSExpr env (.src ((off.toNat - 4272) / 16))) := by
      simpa [Src4272OptMem, evalSExpr] using
        SepLoad128.vec32 hk ha (rfl : env.src0.get ((off.toNat - 4272) / 16) = _)
    exact step_ldrQ128 hpc hrun hfetch hsp_chk haddr
      (SepLoad128.right (SepLoad128.right (SepLoad128.right (SepLoad128.left hld)))) rfl
      (hnext _ rfl hrun (matches_setPC (matches_writeVReg hm vt _) _))
  · have hdeleg : stepSymInst cfg inst st = some st' := by
      rw [← stepSymInstFast_eq]
      unfold stepSymInst03Fast at hstep
      split at hstep
      · rename_i vt off
        have hf : (src4272 && Nat.ble 4272 off.toNat && Nat.blt off.toNat 4784 &&
            (off.toNat - 4272) % 16 == 0) = false :=
          Bool.eq_false_iff.mpr fun h => hldr ⟨vt, off, rfl, h⟩
        simpa [hf] using hstep
      · exact hstep
    exact sepWP_of_stepSymInst hm hpc hrun hfetch hdeleg hnext

theorem sepWP_of_runSymRange03 [MlKemPlacement] {b : BitVec 64}
    {src4272 : Bool} {cfg : SymCfg} {sp : BitVec 64} {env : SymEnv}
    {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {wLo wHi : Nat} (count w : Nat) {st stEnd : SymState} {s : State}
    (hnr : blk03NoRelocInRange wLo wHi = true) (hmax : wHi ≤ 7114)
    (hlo : wLo ≤ w) (hhi : w + count ≤ wHi)
    (hrun_sym : runSymRange03Fast src4272 cfg w count st = some stEnd)
    (hm : SymStateMatches sp env st s)
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * w)) (hrun : s.status = .Running)
    (hpost : ∀ sf : State, sf.pc = b + BitVec.ofNat 64 (4 * (w + count)) →
      sf.status = .Running → SymStateMatches sp env stEnd sf →
      post sf (SymSpatial03 src4272 cfg sp env stEnd F)) :
    SepWP (blkPC03.rebase b (fun _ => none))
      (b + BitVec.ofNat 64 (4 * (w + count))) s (SymSpatial03 src4272 cfg sp env st F) post oom := by
  induction count generalizing w st s with
  | zero =>
    simp only [runSymRange03Fast, Option.some.injEq] at hrun_sym; subst hrun_sym
    have hpc0 : s.pc = b + BitVec.ofNat 64 (4 * (w + 0)) := by simpa using hpc
    exact SepWP.done hpc0 hrun (hpost s hpc0 hrun hm)
  | succ n ih =>
    unfold runSymRange03Fast at hrun_sym
    cases hfw : fetchWordTree03 w with
    | none => simp [hfw] at hrun_sym
    | some inst =>
      simp only [hfw] at hrun_sym
      cases hst : stepSymInst03Fast src4272 cfg inst st with
      | none => simp [hst] at hrun_sym
      | some st1 =>
        simp only [hst] at hrun_sym
        have hfetch := fetch_blk03_range (b := b) hnr hmax hlo (by omega) hfw
        refine sepWP_of_stepSymInst03 hm hpc hrun hfetch hst ?_
        intro s' hpc' hrun' hm'
        have hpc_eq : b + BitVec.ofNat 64 (4 * w) + 4#64 = b + BitVec.ofNat 64 (4 * (w + 1)) := by
          rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
          simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
        rw [hpc_eq] at hpc'
        have hend_eq : 4 * (w + (n + 1)) = 4 * (w + 1 + n) := by omega
        rw [hend_eq]
        exact ih (w + 1) (by omega) (by omega) hrun_sym hm' hpc' hrun'
          (fun sf h1 h2 h3 => hpost sf (by rwa [hend_eq]) h2 h3)

/-! ## 3. `Seg3` Upper `Fwd2` NTT (`+0x3760 .. +0x4398`, `w = 3544 .. 4326`) -/

@[expose] def cfgSeg3Ntt : SymCfg := ⟨1552, 40, .gpr 5#5, false⟩

@[expose] def seg3SpillConsts : SymSpill40 :=
  ⟨.const 0xd43e#16, .const 0xfa3e#16, .const 0x054e#16, .const 0xfb4e#16,
   .const 0x29c2#16, .const 0x03c2#16, .const 0xc2b6#16, .const 0xf129#16,
   .const 0x0629#16, .const 0x6c6e#16, .const 0x026e#16, .const 0xae55#16,
   .const 0xbeca#16, .const 0x6e1f#16, .const 0x011f#16, .const 0xcf8e#16,
   .const 0x058e#16, .const 0x34d5#16, .const 0x05d5#16, .const 0x0313#16,
   .const 0xfa13#16, .const 0x3999#16, .const 0xfe99#16, .const 0xf9c0#16,
   .spill0 24, .spill0 25, .spill0 26, .spill0 27,
   .spill0 28, .spill0 29, .spill0 30, .spill0 31,
   .spill0 32, .spill0 33, .spill0 34, .spill0 35,
   .spill0 36, .spill0 37, .spill0 38, .spill0 39⟩

@[expose] def symSeg3NttInit : SymState :=
  { vregs := ⟨.src 16, .vreg0 1, .src 18, .const 0x0d01#16,
     .vreg0 4, .vreg0 5, .vreg0 6, .vreg0 7,
     .vreg0 8, .vreg0 9, .vreg0 10, .vreg0 11,
     .vreg0 12, .vreg0 13, .vreg0 14, .vreg0 15,
     .vreg0 16, .vreg0 17, .vreg0 18, .vreg0 19,
     .vreg0 20, .vreg0 21, .vreg0 22, .vreg0 23,
     .vreg0 24, .vreg0 25, .vreg0 26, .vreg0 27,
     .vreg0 28, .vreg0 29, .vreg0 30, .vreg0 31⟩
    spill := seg3SpillConsts
    poly  := ⟨.poly 0, .poly 1, .poly 2, .poly 3, .poly 4, .poly 5, .poly 6, .poly 7,
     .poly 8, .poly 9, .poly 10, .poly 11, .poly 12, .poly 13, .poly 14, .poly 15,
     .poly 16, .poly 17, .poly 18, .poly 19, .poly 20, .poly 21, .poly 22, .poly 23,
     .poly 24, .poly 25, .poly 26, .poly 27, .poly 28, .poly 29, .poly 30, .poly 31⟩
    gprs  := ⟨.gpr0 0#5 0#64, .const64 0xf301#64, .gpr0 2#5 0#64, .const64 0x4ebf#64,
     .gpr0 4#5 0#64, .gpr0 5#5 0#64, .gpr0 6#5 0#64, .gpr0 7#5 0#64,
     .gpr0 8#5 0#64, .gpr0 9#5 0#64, .gpr0 10#5 0#64, .gpr0 11#5 0#64,
     .const64 0xf9fa#64, .const64 0x47fa#64, .const64 0x019b#64, .const64 0x229b#64,
     .const64 0x6833#64, .const64 0xf9dd#64, .const64 0xc0dd#64, .gpr0 19#5 0#64,
     .gpr0 20#5 0#64, .gpr0 21#5 0#64, .gpr0 22#5 0#64, .gpr0 23#5 0#64,
     .gpr0 24#5 0#64, .gpr0 25#5 0#64, .gpr0 26#5 0#64, .gpr0 27#5 0#64,
     .gpr0 28#5 0#64, .gpr0 29#5 0#64, .gpr0 30#5 0#64⟩ }

@[expose] def symSeg3NttEnd : SymState :=
  (runSymRange03Fast true cfgSeg3Ntt 3544 782 symSeg3NttInit).getD symSeg3NttInit

private theorem eq_some_getD03 {α : Type} {o : Option α} (d : α) (h : o.isSome = true) :
    o = some (o.getD d) := by
  cases o with
  | none => contradiction
  | some v => rfl

set_option maxRecDepth 200000 in
theorem run_seg3_ntt :
    runSymRange03Fast true cfgSeg3Ntt 3544 782 symSeg3NttInit = some symSeg3NttEnd :=
  eq_some_getD03 symSeg3NttInit (by decide +kernel)

set_option maxRecDepth 200000 in
theorem seg3_ntt_noSpillVreg : polyNoSpillVreg true symSeg3NttEnd.poly = true := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem seg3_ntt_ast_eq : polyAstEq true symSeg3NttEnd.poly symLowerNttBinomial5 = true := by
  decide +kernel

theorem noReloc_seg3_ntt : blk03NoRelocInRange 3544 4326 = true := by decide +kernel

private theorem eq_of_symGprBeq {a b : SymGpr} (h : symGprBeq a b = true) : a = b := by
  cases a <;> cases b <;> simp [symGprBeq] at h ⊢ <;> exact h

private def sExprConstBeq : SExpr → SExpr → Bool
  | .const a, .const b => a == b
  | _, _ => false

private theorem eq_of_sExprConstBeq {a b : SExpr} (h : sExprConstBeq a b = true) : a = b := by
  unfold sExprConstBeq at h
  split at h
  · exact (of_decide_eq_true h) ▸ rfl
  · cases h

set_option maxRecDepth 200000 in
theorem symSeg3NttEnd_vreg3 : symSeg3NttEnd.vregs.get 3 = .const 0x0d01#16 :=
  eq_of_sExprConstBeq (by decide +kernel)

set_option maxRecDepth 200000 in
private theorem symSeg3NttEnd_spill24_bool :
    ((List.range 24).all fun i =>
      sExprConstBeq (symSeg3NttEnd.spill.get i) (seg3SpillConsts.get i)) = true := by
  decide +kernel

theorem symSeg3NttEnd_spill_const (i : Nat) (hi : i < 24) :
    symSeg3NttEnd.spill.get i = seg3SpillConsts.get i :=
  eq_of_sExprConstBeq ((List.all_eq_true.mp symSeg3NttEnd_spill24_bool) i (List.mem_range.mpr hi))

set_option maxRecDepth 200000 in
private theorem symSeg3NttEnd_gprs_bool :
    (symGprBeq (symSeg3NttEnd.gprs.get 0) (.gpr0 0#5 0#64) &&
     symGprBeq (symSeg3NttEnd.gprs.get 1) (.const64 0xf301#64) &&
     symGprBeq (symSeg3NttEnd.gprs.get 2) (.gpr0 2#5 0#64) &&
     symGprBeq (symSeg3NttEnd.gprs.get 3) (.const64 0x4ebf#64) &&
     symGprBeq (symSeg3NttEnd.gprs.get 4) (.gpr0 4#5 0#64) &&
     symGprBeq (symSeg3NttEnd.gprs.get 5) (.gpr0 5#5 0#64) &&
     symGprBeq (symSeg3NttEnd.gprs.get 6) (.gpr0 9#5 0#64) &&
     symGprBeq (symSeg3NttEnd.gprs.get 7) (.gpr0 7#5 0#64) &&
     symGprBeq (symSeg3NttEnd.gprs.get 8) (.gpr0 0#5 0#64) &&
     symGprBeq (symSeg3NttEnd.gprs.get 9) (.gpr0 9#5 0#64) &&
     symGprBeq (symSeg3NttEnd.gprs.get 10) (.gpr0 10#5 0#64) &&
     symGprBeq (symSeg3NttEnd.gprs.get 12) (.const64 0xf9fa#64) &&
     symGprBeq (symSeg3NttEnd.gprs.get 13) (.const64 0x47fa#64) &&
     symGprBeq (symSeg3NttEnd.gprs.get 14) (.const64 0x019b#64) &&
     symGprBeq (symSeg3NttEnd.gprs.get 15) (.const64 0x229b#64) &&
     symGprBeq (symSeg3NttEnd.gprs.get 16) (.const64 0x6833#64) &&
     symGprBeq (symSeg3NttEnd.gprs.get 17) (.const64 0xf9dd#64) &&
     symGprBeq (symSeg3NttEnd.gprs.get 18) (.const64 0xc0dd#64) &&
     symGprBeq (symSeg3NttEnd.gprs.get 19) (.gpr0 19#5 0#64) &&
     symGprBeq (symSeg3NttEnd.gprs.get 20) (.gpr0 20#5 0#64) &&
     symGprBeq (symSeg3NttEnd.gprs.get 21) (.gpr0 21#5 0#64) &&
     symGprBeq (symSeg3NttEnd.gprs.get 22) (.const64 16#64) &&
     symGprBeq (symSeg3NttEnd.gprs.get 29) (.gpr0 29#5 0#64) &&
     symGprBeq (symSeg3NttEnd.gprs.get 30) (.gpr0 30#5 0#64)) = true := by
  decide +kernel

theorem symSeg3NttEnd_gprs :
    symSeg3NttEnd.gprs.get 0 = .gpr0 0#5 0#64 ∧
    symSeg3NttEnd.gprs.get 1 = .const64 0xf301#64 ∧
    symSeg3NttEnd.gprs.get 2 = .gpr0 2#5 0#64 ∧
    symSeg3NttEnd.gprs.get 3 = .const64 0x4ebf#64 ∧
    symSeg3NttEnd.gprs.get 4 = .gpr0 4#5 0#64 ∧
    symSeg3NttEnd.gprs.get 5 = .gpr0 5#5 0#64 ∧
    symSeg3NttEnd.gprs.get 6 = .gpr0 9#5 0#64 ∧
    symSeg3NttEnd.gprs.get 7 = .gpr0 7#5 0#64 ∧
    symSeg3NttEnd.gprs.get 8 = .gpr0 0#5 0#64 ∧
    symSeg3NttEnd.gprs.get 9 = .gpr0 9#5 0#64 ∧
    symSeg3NttEnd.gprs.get 10 = .gpr0 10#5 0#64 ∧
    symSeg3NttEnd.gprs.get 12 = .const64 0xf9fa#64 ∧
    symSeg3NttEnd.gprs.get 13 = .const64 0x47fa#64 ∧
    symSeg3NttEnd.gprs.get 14 = .const64 0x019b#64 ∧
    symSeg3NttEnd.gprs.get 15 = .const64 0x229b#64 ∧
    symSeg3NttEnd.gprs.get 16 = .const64 0x6833#64 ∧
    symSeg3NttEnd.gprs.get 17 = .const64 0xf9dd#64 ∧
    symSeg3NttEnd.gprs.get 18 = .const64 0xc0dd#64 ∧
    symSeg3NttEnd.gprs.get 19 = .gpr0 19#5 0#64 ∧
    symSeg3NttEnd.gprs.get 20 = .gpr0 20#5 0#64 ∧
    symSeg3NttEnd.gprs.get 21 = .gpr0 21#5 0#64 ∧
    symSeg3NttEnd.gprs.get 22 = .const64 16#64 ∧
    symSeg3NttEnd.gprs.get 29 = .gpr0 29#5 0#64 ∧
    symSeg3NttEnd.gprs.get 30 = .gpr0 30#5 0#64 := by
  have h := symSeg3NttEnd_gprs_bool
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩,
    h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩, h29⟩, h30⟩
  exact ⟨eq_of_symGprBeq h0, eq_of_symGprBeq h1, eq_of_symGprBeq h2, eq_of_symGprBeq h3,
    eq_of_symGprBeq h4, eq_of_symGprBeq h5, eq_of_symGprBeq h6, eq_of_symGprBeq h7,
    eq_of_symGprBeq h8, eq_of_symGprBeq h9, eq_of_symGprBeq h10, eq_of_symGprBeq h12,
    eq_of_symGprBeq h13, eq_of_symGprBeq h14, eq_of_symGprBeq h15, eq_of_symGprBeq h16,
    eq_of_symGprBeq h17, eq_of_symGprBeq h18, eq_of_symGprBeq h19, eq_of_symGprBeq h20,
    eq_of_symGprBeq h21, eq_of_symGprBeq h22, eq_of_symGprBeq h29, eq_of_symGprBeq h30⟩

/-! ## 4. `Seg3` Barrett Reduction (`+0x4484 .. +0x4720`, `w = 4385 .. 4552`) -/

@[expose] def cfgSeg3Bar : SymCfg := ⟨0, 0, .gpr 5#5, false⟩

@[expose] def symSeg3BarInit : SymState :=
  { vregs := ⟨.vreg0 0, .vreg0 1, .vreg0 2, .const 0x0d01#16,
     .vreg0 4, .vreg0 5, .vreg0 6, .vreg0 7,
     .vreg0 8, .vreg0 9, .vreg0 10, .vreg0 11,
     .vreg0 12, .vreg0 13, .vreg0 14, .vreg0 15,
     .vreg0 16, .vreg0 17, .vreg0 18, .vreg0 19,
     .vreg0 20, .vreg0 21, .vreg0 22, .vreg0 23,
     .vreg0 24, .vreg0 25, .vreg0 26, .vreg0 27,
     .vreg0 28, .vreg0 29, .vreg0 30, .vreg0 31⟩
    spill := seg3SpillConsts
    poly  := ⟨.poly 0, .poly 1, .poly 2, .poly 3, .poly 4, .poly 5, .poly 6, .poly 7,
     .poly 8, .poly 9, .poly 10, .poly 11, .poly 12, .poly 13, .poly 14, .poly 15,
     .poly 16, .poly 17, .poly 18, .poly 19, .poly 20, .poly 21, .poly 22, .poly 23,
     .poly 24, .poly 25, .poly 26, .poly 27, .poly 28, .poly 29, .poly 30, .poly 31⟩
    gprs  := ⟨.gpr0 0#5 0#64, .const64 0xf301#64, .gpr0 2#5 0#64, .const64 0x4ebf#64,
     .gpr0 4#5 0#64, .gpr0 5#5 0#64, .gpr0 6#5 0#64, .gpr0 7#5 0#64,
     .gpr0 8#5 0#64, .gpr0 9#5 0#64, .gpr0 10#5 0#64, .gpr0 11#5 0#64,
     .const64 0xf9fa#64, .const64 0x47fa#64, .const64 0x019b#64, .const64 0x229b#64,
     .const64 0x6833#64, .const64 0xf9dd#64, .const64 0xc0dd#64, .gpr0 19#5 0#64,
     .gpr0 20#5 0#64, .gpr0 21#5 0#64, .gpr0 22#5 0#64, .gpr0 23#5 0#64,
     .gpr0 24#5 0#64, .gpr0 25#5 0#64, .gpr0 26#5 0#64, .gpr0 27#5 0#64,
     .gpr0 28#5 0#64, .gpr0 29#5 0#64, .gpr0 30#5 0#64⟩ }

@[expose] def symSeg3BarMid : SymState :=
  (runSymRange03Fast false cfgSeg3Bar 4385 11 symSeg3BarInit).getD symSeg3BarInit

@[expose] def symSeg3BarEnd : SymState :=
  (runSymRange03Fast false cfgSeg3Bar 4397 155 symSeg3BarMid).getD symSeg3BarMid

theorem noReloc_seg3_bar_a : blk03NoRelocInRange 4385 4396 = true := by decide +kernel
theorem noReloc_seg3_bar_b : blk03NoRelocInRange 4397 4552 = true := by decide +kernel

theorem run_seg3_bar_a :
    runSymRange03Fast false cfgSeg3Bar 4385 11 symSeg3BarInit = some symSeg3BarMid :=
  eq_some_getD03 symSeg3BarInit (by decide +kernel)

set_option maxRecDepth 100000 in
theorem run_seg3_bar_b :
    runSymRange03Fast false cfgSeg3Bar 4397 155 symSeg3BarMid = some symSeg3BarEnd :=
  eq_some_getD03 symSeg3BarMid (by decide +kernel)

set_option maxRecDepth 100000 in
theorem seg3_bar_noSpillVreg : polyNoSpillVreg false symSeg3BarEnd.poly = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem seg3_bar_ast_eq : polyAstEq false symSeg3BarEnd.poly symBarrett = true := by
  decide +kernel

theorem symSeg3BarMid_gpr4 : symSeg3BarMid.gprs.get 4 = .gpr0 4#5 0#64 := by rfl_kernel

set_option maxRecDepth 100000 in
theorem symSeg3BarEnd_vreg3 : symSeg3BarEnd.vregs.get 3 = .const 0x0d01#16 := by rfl_kernel

set_option maxRecDepth 100000 in
private theorem symSeg3BarEnd_gprs_bool :
    (symGprBeq (symSeg3BarEnd.gprs.get 0) (.gpr0 0#5 0#64) &&
     symGprBeq (symSeg3BarEnd.gprs.get 1) (.const64 0xf301#64) &&
     symGprBeq (symSeg3BarEnd.gprs.get 2) (.gpr0 2#5 0#64) &&
     symGprBeq (symSeg3BarEnd.gprs.get 3) (.const64 0x4ebf#64) &&
     symGprBeq (symSeg3BarEnd.gprs.get 4) (.gpr0 4#5 0#64) &&
     symGprBeq (symSeg3BarEnd.gprs.get 5) (.gpr0 5#5 0#64) &&
     symGprBeq (symSeg3BarEnd.gprs.get 7) (.gpr0 7#5 128#64) &&
     symGprBeq (symSeg3BarEnd.gprs.get 9) (.gpr0 9#5 512#64) &&
     symGprBeq (symSeg3BarEnd.gprs.get 10) (.gpr0 10#5 512#64) &&
     symGprBeq (symSeg3BarEnd.gprs.get 12) (.const64 0xf9fa#64) &&
     symGprBeq (symSeg3BarEnd.gprs.get 13) (.const64 0x47fa#64) &&
     symGprBeq (symSeg3BarEnd.gprs.get 14) (.const64 0x019b#64) &&
     symGprBeq (symSeg3BarEnd.gprs.get 15) (.const64 0x229b#64) &&
     symGprBeq (symSeg3BarEnd.gprs.get 16) (.const64 0x6833#64) &&
     symGprBeq (symSeg3BarEnd.gprs.get 17) (.const64 0xf9dd#64) &&
     symGprBeq (symSeg3BarEnd.gprs.get 18) (.const64 0xc0dd#64) &&
     symGprBeq (symSeg3BarEnd.gprs.get 19) (.gpr0 19#5 0#64) &&
     symGprBeq (symSeg3BarEnd.gprs.get 20) (.gpr0 20#5 0#64) &&
     symGprBeq (symSeg3BarEnd.gprs.get 21) (.gpr0 21#5 0#64) &&
     symGprBeq (symSeg3BarEnd.gprs.get 29) (.gpr0 29#5 0#64) &&
     symGprBeq (symSeg3BarEnd.gprs.get 30) (.gpr0 30#5 0#64)) = true := by
  decide +kernel

theorem symSeg3BarEnd_gprs :
    symSeg3BarEnd.gprs.get 0 = .gpr0 0#5 0#64 ∧
    symSeg3BarEnd.gprs.get 1 = .const64 0xf301#64 ∧
    symSeg3BarEnd.gprs.get 2 = .gpr0 2#5 0#64 ∧
    symSeg3BarEnd.gprs.get 3 = .const64 0x4ebf#64 ∧
    symSeg3BarEnd.gprs.get 4 = .gpr0 4#5 0#64 ∧
    symSeg3BarEnd.gprs.get 5 = .gpr0 5#5 0#64 ∧
    symSeg3BarEnd.gprs.get 7 = .gpr0 7#5 128#64 ∧
    symSeg3BarEnd.gprs.get 9 = .gpr0 9#5 512#64 ∧
    symSeg3BarEnd.gprs.get 10 = .gpr0 10#5 512#64 ∧
    symSeg3BarEnd.gprs.get 12 = .const64 0xf9fa#64 ∧
    symSeg3BarEnd.gprs.get 13 = .const64 0x47fa#64 ∧
    symSeg3BarEnd.gprs.get 14 = .const64 0x019b#64 ∧
    symSeg3BarEnd.gprs.get 15 = .const64 0x229b#64 ∧
    symSeg3BarEnd.gprs.get 16 = .const64 0x6833#64 ∧
    symSeg3BarEnd.gprs.get 17 = .const64 0xf9dd#64 ∧
    symSeg3BarEnd.gprs.get 18 = .const64 0xc0dd#64 ∧
    symSeg3BarEnd.gprs.get 19 = .gpr0 19#5 0#64 ∧
    symSeg3BarEnd.gprs.get 20 = .gpr0 20#5 0#64 ∧
    symSeg3BarEnd.gprs.get 21 = .gpr0 21#5 0#64 ∧
    symSeg3BarEnd.gprs.get 29 = .gpr0 29#5 0#64 ∧
    symSeg3BarEnd.gprs.get 30 = .gpr0 30#5 0#64 := by
  have h := symSeg3BarEnd_gprs_bool
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h7⟩, h9⟩, h10⟩,
    h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h29⟩, h30⟩
  exact ⟨eq_of_symGprBeq h0, eq_of_symGprBeq h1, eq_of_symGprBeq h2, eq_of_symGprBeq h3,
    eq_of_symGprBeq h4, eq_of_symGprBeq h5, eq_of_symGprBeq h7, eq_of_symGprBeq h9,
    eq_of_symGprBeq h10, eq_of_symGprBeq h12, eq_of_symGprBeq h13, eq_of_symGprBeq h14,
    eq_of_symGprBeq h15, eq_of_symGprBeq h16, eq_of_symGprBeq h17, eq_of_symGprBeq h18,
    eq_of_symGprBeq h19, eq_of_symGprBeq h20, eq_of_symGprBeq h21, eq_of_symGprBeq h29,
    eq_of_symGprBeq h30⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Sym
