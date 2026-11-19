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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySym

/-!
# `generate_keypair_compressed` (`B05`): symbolic NEON certificates for `Seg3` (`sHat`)

Adapts `Mlkem1024.Decaps.PolySym*` to `B05` (`blkTree05` / `blkPC05`) with parameterized read-only
`src0` support (`srcBase : Option Nat`) and certifies `sHat` upper `Fwd2` NTT
(`+0x38f4 .. +0x453c`) and Barrett reduction (`+0x4628 .. +0x48c4`). The corresponding `eHat`
certificates live in `Seg3SymE`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3Sym

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
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (
  blk05_code_eq blk05_tree_size blkLib05 blkPC05 blkPl05 blkPlaceable05 blkTree05)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs (
  fetchWordTree05)

/-! ## 1. Relocation-Free Fetch on Clean `[wLo, wHi)` Slices of `B05` -/

@[expose] def blk05NoRelocInRange (wLo wHi : Nat) : Bool :=
  blkLib05.text.relocs.all (fun r => decide (r.off < 4 * wLo ∨ 4 * wHi ≤ r.off))

theorem blk05_relocAt?_range {wLo wHi off : Nat}
    (hnr : blk05NoRelocInRange wLo wHi = true)
    (hlo : 4 * wLo ≤ off) (hhi : off < 4 * wHi) :
    (blkLib05.text.relocAt? off).isNone = true := by
  cases hr : blkLib05.text.relocAt? off with
  | none => rfl
  | some r =>
    have hmem := CodeBlock.relocAt?_mem hr
    have hoff := CodeBlock.relocAt?_off hr
    have hall := (List.all_eq_true.mp hnr) r hmem
    simp only [decide_eq_true_eq] at hall
    omega

theorem fetch_blk05_range [MlKemPlacement] {b : BitVec 64} {wLo wHi j : Nat} {inst : Instr}
    (hnr : blk05NoRelocInRange wLo wHi = true) (hmax : wHi ≤ 7112)
    (hlo : wLo ≤ j) (hhi : j < wHi) (hfw : fetchWordTree05 j = some inst) :
    (blkPC05.rebase b (fun _ => none)).fetch (b + BitVec.ofNat 64 (4 * j)) = some inst := by
  have hdec : blkTree05.fetchDecodeAt (4 * j) = some inst := by
    unfold WordTree.fetchDecodeAt
    have hdiv : 4 * j / 4 = j := by omega
    rw [hdiv]
    unfold fetchWordTree05 at hfw
    cases hq : blkTree05.getQuad? j with
    | none => simp [hq] at hfw
    | some q =>
      rcases q with ⟨b0, b1, b2, b3⟩
      simp [hq] at hfw ⊢
      exact hfw
  have hnh := hookAtOff?_rebase_of_placeable (pl := blkPl05) (b := b)
    (X := fun _ => none) blk05_code_eq blk05_tree_size blkPlaceable05 (off := 4 * j) (by omega)
  exact fetch_rebase_of_noReloc blk05_code_eq blk05_tree_size
    (by omega) (by omega) (by omega) hdec
    (blk05_relocAt?_range hnr (by omega) (by omega)) hnh


/-! ## 2. `B05` Symbolic Stepper with Parameterized `srcBase : Option Nat` -/

@[expose] def SrcOptMem05 (srcBase : Option Nat) (sp : BitVec 64) (src0 : Vec32) : SepProp :=
  match srcBase with
  | some base => Poly32Mem (sp + BitVec.ofNat 64 base) src0
  | none => emp

@[expose] def SymSpatial05 (srcBase : Option Nat) (cfg : SymCfg) (sp : BitVec 64)
    (env : SymEnv) (st : SymState) (F : SepProp) : SepProp :=
  SymSpatial cfg sp env st (SrcOptMem05 srcBase sp env.src0 ∗ F)

@[expose] def stepSymInst05Fast (srcBase : Option Nat) (cfg : SymCfg) (inst : Instr)
    (st : SymState) : Option SymState :=
  match srcBase, inst with
  | some base, .ldrSimd .Q128 vt (.Offset .sp off) =>
      let o := off.toNat
      if Nat.ble base o && Nat.blt o (base + 512) && (o - base) % 16 == 0 then
        some { st with vregs := st.vregs.set vt.toNat (.src ((o - base) / 16)) }
      else stepSymInstFast cfg inst st
  | _, _ => stepSymInstFast cfg inst st

@[expose] def runSymRange05Fast (srcBase : Option Nat) (cfg : SymCfg) :
    Nat → Nat → SymState → Option SymState
  | _, 0, st => some st
  | w, n + 1, st =>
      match fetchWordTree05 w with
      | some inst =>
          match stepSymInst05Fast srcBase cfg inst st with
          | some st' => runSymRange05Fast srcBase cfg (w + 1) n st'
          | none => none
      | none => none

theorem sepWP_of_stepSymInst05 {prog : Program} {tgt pc : BitVec 64}
    {srcBase : Option Nat} {cfg : SymCfg} {s : State} {sp : BitVec 64} {env : SymEnv}
    {st st' : SymState} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {inst : Instr}
    (hm : SymStateMatches sp env st s) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some inst)
    (hstep : stepSymInst05Fast srcBase cfg inst st = some st')
    (hnext : ∀ s' : State, s'.pc = pc + 4#64 → s'.status = .Running →
      SymStateMatches sp env st' s' →
      SepWP prog tgt s' (SymSpatial05 srcBase cfg sp env st' F) post oom) :
    SepWP prog tgt s (SymSpatial05 srcBase cfg sp env st F) post oom := by
  by_cases hldr : ∃ base vt off, srcBase = some base ∧
      inst = .ldrSimd .Q128 vt (.Offset .sp off) ∧
      (Nat.ble base off.toNat && Nat.blt off.toNat (base + 512) &&
        (off.toNat - base) % 16 == 0) = true
  · rcases hldr with ⟨base, vt, off, rfl, rfl, hc⟩
    simp only [stepSymInst05Fast, hc, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, beq_iff_eq] at hc
    obtain ⟨hk, ha⟩ := sp_range_off (sp := sp) (base := base) (len := 32) hc.1.1 (by omega) hc.2
    have hsp_chk : checkAddrSPAligned s (.Offset .sp off) = true := hm.hsp_al
    have haddr : evalAddrMode s (.Offset .sp off) = (sp + off, none) := by
      simp [evalAddrMode, State.readReg64, hm.hsp]
    have hld : SepLoad128 (sp + off) (SrcOptMem05 (some base) sp env.src0)
        (evalSExpr env (.src ((off.toNat - base) / 16))) := by
      simpa [SrcOptMem05, evalSExpr] using
        SepLoad128.vec32 hk ha (rfl : env.src0.get ((off.toNat - base) / 16) = _)
    exact step_ldrQ128 hpc hrun hfetch hsp_chk haddr
      (SepLoad128.right (SepLoad128.right (SepLoad128.right (SepLoad128.left hld)))) rfl
      (hnext _ rfl hrun (matches_setPC (matches_writeVReg hm vt _) _))
  · have hdeleg : stepSymInst cfg inst st = some st' := by
      rw [← stepSymInstFast_eq]
      unfold stepSymInst05Fast at hstep
      split at hstep
      · rename_i base vt off
        have hf : (Nat.ble base off.toNat && Nat.blt off.toNat (base + 512) &&
            (off.toNat - base) % 16 == 0) = false :=
          Bool.eq_false_iff.mpr fun h => hldr ⟨base, vt, off, rfl, rfl, h⟩
        simpa [hf] using hstep
      · exact hstep
    exact sepWP_of_stepSymInst hm hpc hrun hfetch hdeleg hnext

theorem sepWP_of_runSymRange05 [MlKemPlacement] {b : BitVec 64}
    {srcBase : Option Nat} {cfg : SymCfg} {sp : BitVec 64} {env : SymEnv}
    {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {wLo wHi : Nat} (count w : Nat) {st stEnd : SymState} {s : State}
    (hnr : blk05NoRelocInRange wLo wHi = true) (hmax : wHi ≤ 7112)
    (hlo : wLo ≤ w) (hhi : w + count ≤ wHi)
    (hrun_sym : runSymRange05Fast srcBase cfg w count st = some stEnd)
    (hm : SymStateMatches sp env st s)
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * w)) (hrun : s.status = .Running)
    (hpost : ∀ sf : State, sf.pc = b + BitVec.ofNat 64 (4 * (w + count)) →
      sf.status = .Running → SymStateMatches sp env stEnd sf →
      post sf (SymSpatial05 srcBase cfg sp env stEnd F)) :
    SepWP (blkPC05.rebase b (fun _ => none))
      (b + BitVec.ofNat 64 (4 * (w + count))) s (SymSpatial05 srcBase cfg sp env st F) post oom := by
  induction count generalizing w st s with
  | zero =>
    simp only [runSymRange05Fast, Option.some.injEq] at hrun_sym; subst hrun_sym
    have hpc0 : s.pc = b + BitVec.ofNat 64 (4 * (w + 0)) := by simpa using hpc
    exact SepWP.done hpc0 hrun (hpost s hpc0 hrun hm)
  | succ n ih =>
    unfold runSymRange05Fast at hrun_sym
    cases hfw : fetchWordTree05 w with
    | none => simp [hfw] at hrun_sym
    | some inst =>
      simp only [hfw] at hrun_sym
      cases hst : stepSymInst05Fast srcBase cfg inst st with
      | none => simp [hst] at hrun_sym
      | some st1 =>
        simp only [hst] at hrun_sym
        have hfetch := fetch_blk05_range (b := b) hnr hmax hlo (by omega) hfw
        refine sepWP_of_stepSymInst05 hm hpc hrun hfetch hst ?_
        intro s' hpc' hrun' hm'
        have hpc_eq : b + BitVec.ofNat 64 (4 * w) + 4#64 = b + BitVec.ofNat 64 (4 * (w + 1)) := by
          rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
          simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
        rw [hpc_eq] at hpc'
        have hend_eq : 4 * (w + (n + 1)) = 4 * (w + 1 + n) := by omega
        rw [hend_eq]
        exact ih (w + 1) (by omega) (by omega) hrun_sym hm' hpc' hrun'
          (fun sf h1 h2 h3 => hpost sf (by rwa [hend_eq]) h2 h3)

theorem eq_some_getD05 {α : Type} {o : Option α} (d : α) (h : o.isSome = true) :
    o = some (o.getD d) := by
  cases o with
  | none => contradiction
  | some v => rfl

theorem eq_of_symGprBeq {a b : SymGpr} (h : symGprBeq a b = true) : a = b := by
  cases a <;> cases b <;> simp [symGprBeq] at h ⊢ <;> exact h

@[expose] def sExprConstBeq : SExpr → SExpr → Bool
  | .const a, .const b => a == b
  | _, _ => false

theorem eq_of_sExprConstBeq {a b : SExpr} (h : sExprConstBeq a b = true) : a = b := by
  unfold sExprConstBeq at h
  split at h
  · exact (of_decide_eq_true h) ▸ rfl
  · cases h

/-! ## 3. `sHat` Upper `Fwd2` NTT (`+0x38f4 .. +0x453c`, `w = 3645 .. 4431`) -/

@[expose] def cfgSHatNtt : SymCfg := ⟨1568, 40, .gpr 6#5, false⟩

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

@[expose] def symSHatNttInit : SymState :=
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
    gprs  := ⟨.const64 0xc0dd#64, .gpr0 1#5 0#64, .const64 0xf301#64, .gpr0 3#5 0#64,
     .const64 0x4ebf#64, .gpr0 5#5 0#64, .gpr0 31#5 0#64, .gpr0 7#5 0#64,
     .gpr0 8#5 0#64, .gpr0 9#5 0#64, .gpr0 10#5 0#64, .gpr0 11#5 0#64,
     .gpr0 12#5 0#64, .const64 0xf9fa#64, .const64 0x47fa#64, .const64 0x019b#64,
     .const64 0x229b#64, .const64 0x6833#64, .const64 0xf9dd#64, .gpr0 19#5 0#64,
     .gpr0 20#5 0#64, .gpr0 21#5 0#64, .gpr0 22#5 0#64, .gpr0 23#5 0#64,
     .gpr0 24#5 0#64, .gpr0 25#5 0#64, .gpr0 26#5 0#64, .gpr0 27#5 0#64,
     .gpr0 28#5 0#64, .gpr0 29#5 0#64, .gpr0 30#5 0#64⟩ }

@[expose] def symSHatNttA : SymState :=
  (runSymRange05Fast (some 17376) cfgSHatNtt 3645 68 symSHatNttInit).getD symSHatNttInit

@[expose] def symSHatNttA' : SymState :=
  { symSHatNttA with gprs := symSHatNttA.gprs.set 8 (.spAdd 8416#64) }

@[expose] def symSHatNttB : SymState :=
  (runSymRange05Fast (some 17376) cfgSHatNtt 3714 38 symSHatNttA').getD symSHatNttA'

@[expose] def symSHatNttB' : SymState :=
  { symSHatNttB with gprs := symSHatNttB.gprs.set 6 (.gpr0 6#5 0#64) }

@[expose] def symSHatNttEnd : SymState :=
  (runSymRange05Fast (some 17376) cfgSHatNtt 3753 678 symSHatNttB').getD symSHatNttB'

theorem noReloc_sHat_ntt_a : blk05NoRelocInRange 3645 3713 = true := by decide +kernel
theorem noReloc_sHat_ntt_b : blk05NoRelocInRange 3714 3752 = true := by decide +kernel
theorem noReloc_sHat_ntt_c : blk05NoRelocInRange 3753 4431 = true := by decide +kernel

set_option maxRecDepth 200000 in
theorem run_sHat_ntt_a :
    runSymRange05Fast (some 17376) cfgSHatNtt 3645 68 symSHatNttInit = some symSHatNttA :=
  eq_some_getD05 symSHatNttInit (by decide +kernel)

set_option maxRecDepth 200000 in
theorem run_sHat_ntt_b :
    runSymRange05Fast (some 17376) cfgSHatNtt 3714 38 symSHatNttA' = some symSHatNttB :=
  eq_some_getD05 symSHatNttA' (by decide +kernel)

theorem symSHatNttB_gpr8 : symSHatNttB.gprs.get 8 = .spAdd 8416#64 :=
  eq_of_symGprBeq (by decide +kernel)

theorem symSHatNttB_gpr6 : symSHatNttB.gprs.get 6 = .gpr0 31#5 0#64 :=
  eq_of_symGprBeq (by decide +kernel)

private def checkSHatNttEnd (st : SymState) : Bool :=
  polyNoSpillVreg true st.poly &&
  polyAstEq true st.poly symLowerNttBinomial5 &&
  sExprConstBeq (st.vregs.get 3) (.const 0x0d01#16) &&
  ((List.range 24).all fun i => sExprConstBeq (st.spill.get i) (seg3SpillConsts.get i)) &&
  (symGprBeq (st.gprs.get 0) (.const64 0xc0dd#64) &&
   symGprBeq (st.gprs.get 1) (.gpr0 1#5 0#64) &&
   symGprBeq (st.gprs.get 2) (.const64 0xf301#64) &&
   symGprBeq (st.gprs.get 3) (.gpr0 3#5 0#64) &&
   symGprBeq (st.gprs.get 4) (.const64 0x4ebf#64) &&
   symGprBeq (st.gprs.get 5) (.gpr0 5#5 0#64) &&
   symGprBeq (st.gprs.get 6) (.gpr0 6#5 0#64) &&
   symGprBeq (st.gprs.get 7) (.gpr0 11#5 0#64) &&
   symGprBeq (st.gprs.get 8) (.gpr0 1#5 0#64) &&
   symGprBeq (st.gprs.get 9) (.gpr0 9#5 0#64) &&
   symGprBeq (st.gprs.get 10) (.gpr0 10#5 0#64) &&
   symGprBeq (st.gprs.get 11) (.gpr0 11#5 0#64) &&
   symGprBeq (st.gprs.get 13) (.const64 0xf9fa#64) &&
   symGprBeq (st.gprs.get 14) (.const64 0x47fa#64) &&
   symGprBeq (st.gprs.get 15) (.const64 0x019b#64) &&
   symGprBeq (st.gprs.get 16) (.const64 0x229b#64) &&
   symGprBeq (st.gprs.get 17) (.const64 0x6833#64) &&
   symGprBeq (st.gprs.get 18) (.const64 0xf9dd#64) &&
   symGprBeq (st.gprs.get 19) (.gpr0 19#5 0#64) &&
   symGprBeq (st.gprs.get 20) (.gpr0 20#5 0#64) &&
   symGprBeq (st.gprs.get 21) (.gpr0 21#5 0#64) &&
   symGprBeq (st.gprs.get 22) (.const64 16#64) &&
   symGprBeq (st.gprs.get 29) (.gpr0 29#5 0#64) &&
   symGprBeq (st.gprs.get 30) (.gpr0 30#5 0#64))

set_option maxRecDepth 200000 in
private theorem sHat_ntt_cert_all :
    (match runSymRange05Fast (some 17376) cfgSHatNtt 3753 678 symSHatNttB' with
     | some st => checkSHatNttEnd st
     | none => false) = true := by
  decide +kernel

theorem run_sHat_ntt_c :
    runSymRange05Fast (some 17376) cfgSHatNtt 3753 678 symSHatNttB' = some symSHatNttEnd := by
  have h := sHat_ntt_cert_all
  unfold symSHatNttEnd
  cases hr : runSymRange05Fast (some 17376) cfgSHatNtt 3753 678 symSHatNttB' with
  | none => simp [hr] at h
  | some st => rfl

private theorem sHat_ntt_end_ok : checkSHatNttEnd symSHatNttEnd = true := by
  have h := sHat_ntt_cert_all
  rwa [run_sHat_ntt_c] at h

private theorem sHat_ntt_end_parts :
    polyNoSpillVreg true symSHatNttEnd.poly = true ∧
    polyAstEq true symSHatNttEnd.poly symLowerNttBinomial5 = true ∧
    sExprConstBeq (symSHatNttEnd.vregs.get 3) (.const 0x0d01#16) = true ∧
    ((List.range 24).all fun i =>
      sExprConstBeq (symSHatNttEnd.spill.get i) (seg3SpillConsts.get i)) = true := by
  have h := sHat_ntt_end_ok
  unfold checkSHatNttEnd at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2⟩

theorem sHat_ntt_noSpillVreg : polyNoSpillVreg true symSHatNttEnd.poly = true :=
  sHat_ntt_end_parts.1

theorem sHat_ntt_ast_eq : polyAstEq true symSHatNttEnd.poly symLowerNttBinomial5 = true :=
  sHat_ntt_end_parts.2.1

theorem symSHatNttEnd_vreg3 : symSHatNttEnd.vregs.get 3 = .const 0x0d01#16 :=
  eq_of_sExprConstBeq sHat_ntt_end_parts.2.2.1

theorem symSHatNttEnd_spill_const (i : Nat) (hi : i < 24) :
    symSHatNttEnd.spill.get i = seg3SpillConsts.get i :=
  eq_of_sExprConstBeq ((List.all_eq_true.mp sHat_ntt_end_parts.2.2.2) i (List.mem_range.mpr hi))

theorem symSHatNttEnd_gprs :
    symSHatNttEnd.gprs.get 0 = .const64 0xc0dd#64 ∧
    symSHatNttEnd.gprs.get 1 = .gpr0 1#5 0#64 ∧
    symSHatNttEnd.gprs.get 2 = .const64 0xf301#64 ∧
    symSHatNttEnd.gprs.get 3 = .gpr0 3#5 0#64 ∧
    symSHatNttEnd.gprs.get 4 = .const64 0x4ebf#64 ∧
    symSHatNttEnd.gprs.get 5 = .gpr0 5#5 0#64 ∧
    symSHatNttEnd.gprs.get 6 = .gpr0 6#5 0#64 ∧
    symSHatNttEnd.gprs.get 7 = .gpr0 11#5 0#64 ∧
    symSHatNttEnd.gprs.get 8 = .gpr0 1#5 0#64 ∧
    symSHatNttEnd.gprs.get 9 = .gpr0 9#5 0#64 ∧
    symSHatNttEnd.gprs.get 10 = .gpr0 10#5 0#64 ∧
    symSHatNttEnd.gprs.get 11 = .gpr0 11#5 0#64 ∧
    symSHatNttEnd.gprs.get 13 = .const64 0xf9fa#64 ∧
    symSHatNttEnd.gprs.get 14 = .const64 0x47fa#64 ∧
    symSHatNttEnd.gprs.get 15 = .const64 0x019b#64 ∧
    symSHatNttEnd.gprs.get 16 = .const64 0x229b#64 ∧
    symSHatNttEnd.gprs.get 17 = .const64 0x6833#64 ∧
    symSHatNttEnd.gprs.get 18 = .const64 0xf9dd#64 ∧
    symSHatNttEnd.gprs.get 19 = .gpr0 19#5 0#64 ∧
    symSHatNttEnd.gprs.get 20 = .gpr0 20#5 0#64 ∧
    symSHatNttEnd.gprs.get 21 = .gpr0 21#5 0#64 ∧
    symSHatNttEnd.gprs.get 22 = .const64 16#64 ∧
    symSHatNttEnd.gprs.get 29 = .gpr0 29#5 0#64 ∧
    symSHatNttEnd.gprs.get 30 = .gpr0 30#5 0#64 := by
  have h0 := sHat_ntt_end_ok
  unfold checkSHatNttEnd at h0
  simp only [Bool.and_eq_true] at h0
  have h := h0.2
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩,
    h11⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩, h29⟩, h30⟩
  exact ⟨eq_of_symGprBeq h0, eq_of_symGprBeq h1, eq_of_symGprBeq h2, eq_of_symGprBeq h3,
    eq_of_symGprBeq h4, eq_of_symGprBeq h5, eq_of_symGprBeq h6, eq_of_symGprBeq h7,
    eq_of_symGprBeq h8, eq_of_symGprBeq h9, eq_of_symGprBeq h10, eq_of_symGprBeq h11,
    eq_of_symGprBeq h13, eq_of_symGprBeq h14, eq_of_symGprBeq h15, eq_of_symGprBeq h16,
    eq_of_symGprBeq h17, eq_of_symGprBeq h18, eq_of_symGprBeq h19, eq_of_symGprBeq h20,
    eq_of_symGprBeq h21, eq_of_symGprBeq h22, eq_of_symGprBeq h29, eq_of_symGprBeq h30⟩

/-! ## 4. `sHat` Barrett Reduction (`+0x4628 .. +0x48c4`, `w = 4490 .. 4657`) -/

@[expose] def cfgSHatBar : SymCfg := ⟨0, 0, .gpr 6#5, false⟩

@[expose] def symSHatBarInit : SymState :=
  { symSHatNttInit with gprs := symSHatNttInit.gprs.set 6 (.gpr0 6#5 0#64) }

@[expose] def symSHatBarMid : SymState :=
  (runSymRange05Fast none cfgSHatBar 4490 11 symSHatBarInit).getD symSHatBarInit

@[expose] def symSHatBarEnd : SymState :=
  (runSymRange05Fast none cfgSHatBar 4502 155 symSHatBarMid).getD symSHatBarMid

theorem noReloc_sHat_bar_a : blk05NoRelocInRange 4490 4501 = true := by decide +kernel
theorem noReloc_sHat_bar_b : blk05NoRelocInRange 4502 4657 = true := by decide +kernel

theorem run_sHat_bar_a :
    runSymRange05Fast none cfgSHatBar 4490 11 symSHatBarInit = some symSHatBarMid :=
  eq_some_getD05 symSHatBarInit (by decide +kernel)

theorem symSHatBarMid_gpr5 : symSHatBarMid.gprs.get 5 = .gpr0 5#5 0#64 :=
  eq_of_symGprBeq (by decide +kernel)

private def checkSHatBarEnd (st : SymState) : Bool :=
  polyNoSpillVreg false st.poly &&
  polyAstEq false st.poly symBarrett &&
  sExprConstBeq (st.vregs.get 3) (.const 0x0d01#16) &&
  (symGprBeq (st.gprs.get 0) (.const64 0xc0dd#64) &&
   symGprBeq (st.gprs.get 1) (.gpr0 1#5 0#64) &&
   symGprBeq (st.gprs.get 2) (.const64 0xf301#64) &&
   symGprBeq (st.gprs.get 3) (.gpr0 3#5 0#64) &&
   symGprBeq (st.gprs.get 4) (.const64 0x4ebf#64) &&
   symGprBeq (st.gprs.get 5) (.gpr0 5#5 0#64) &&
   symGprBeq (st.gprs.get 6) (.gpr0 6#5 0#64) &&
   symGprBeq (st.gprs.get 9) (.gpr0 9#5 512#64) &&
   symGprBeq (st.gprs.get 10) (.gpr0 10#5 0#64) &&
   symGprBeq (st.gprs.get 11) (.gpr0 11#5 512#64) &&
   symGprBeq (st.gprs.get 13) (.const64 0xf9fa#64) &&
   symGprBeq (st.gprs.get 14) (.const64 0x47fa#64) &&
   symGprBeq (st.gprs.get 15) (.const64 0x019b#64) &&
   symGprBeq (st.gprs.get 16) (.const64 0x229b#64) &&
   symGprBeq (st.gprs.get 17) (.const64 0x6833#64) &&
   symGprBeq (st.gprs.get 18) (.const64 0xf9dd#64) &&
   symGprBeq (st.gprs.get 19) (.gpr0 19#5 0#64) &&
   symGprBeq (st.gprs.get 20) (.gpr0 20#5 0#64) &&
   symGprBeq (st.gprs.get 21) (.gpr0 21#5 128#64) &&
   symGprBeq (st.gprs.get 29) (.gpr0 29#5 0#64) &&
   symGprBeq (st.gprs.get 30) (.gpr0 30#5 0#64))

set_option maxRecDepth 100000 in
private theorem sHat_bar_cert_all :
    (match runSymRange05Fast none cfgSHatBar 4502 155 symSHatBarMid with
     | some st => checkSHatBarEnd st
     | none => false) = true := by
  decide +kernel

theorem run_sHat_bar_b :
    runSymRange05Fast none cfgSHatBar 4502 155 symSHatBarMid = some symSHatBarEnd := by
  have h := sHat_bar_cert_all
  unfold symSHatBarEnd
  cases hr : runSymRange05Fast none cfgSHatBar 4502 155 symSHatBarMid with
  | none => simp [hr] at h
  | some st => rfl

private theorem sHat_bar_end_ok : checkSHatBarEnd symSHatBarEnd = true := by
  have h := sHat_bar_cert_all
  rwa [run_sHat_bar_b] at h

private theorem sHat_bar_end_parts :
    polyNoSpillVreg false symSHatBarEnd.poly = true ∧
    polyAstEq false symSHatBarEnd.poly symBarrett = true ∧
    sExprConstBeq (symSHatBarEnd.vregs.get 3) (.const 0x0d01#16) = true := by
  have h := sHat_bar_end_ok
  unfold checkSHatBarEnd at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩

theorem sHat_bar_noSpillVreg : polyNoSpillVreg false symSHatBarEnd.poly = true :=
  sHat_bar_end_parts.1

theorem sHat_bar_ast_eq : polyAstEq false symSHatBarEnd.poly symBarrett = true :=
  sHat_bar_end_parts.2.1

theorem symSHatBarEnd_vreg3 : symSHatBarEnd.vregs.get 3 = .const 0x0d01#16 :=
  eq_of_sExprConstBeq sHat_bar_end_parts.2.2

theorem symSHatBarEnd_gprs :
    symSHatBarEnd.gprs.get 0 = .const64 0xc0dd#64 ∧
    symSHatBarEnd.gprs.get 1 = .gpr0 1#5 0#64 ∧
    symSHatBarEnd.gprs.get 2 = .const64 0xf301#64 ∧
    symSHatBarEnd.gprs.get 3 = .gpr0 3#5 0#64 ∧
    symSHatBarEnd.gprs.get 4 = .const64 0x4ebf#64 ∧
    symSHatBarEnd.gprs.get 5 = .gpr0 5#5 0#64 ∧
    symSHatBarEnd.gprs.get 6 = .gpr0 6#5 0#64 ∧
    symSHatBarEnd.gprs.get 9 = .gpr0 9#5 512#64 ∧
    symSHatBarEnd.gprs.get 10 = .gpr0 10#5 0#64 ∧
    symSHatBarEnd.gprs.get 11 = .gpr0 11#5 512#64 ∧
    symSHatBarEnd.gprs.get 13 = .const64 0xf9fa#64 ∧
    symSHatBarEnd.gprs.get 14 = .const64 0x47fa#64 ∧
    symSHatBarEnd.gprs.get 15 = .const64 0x019b#64 ∧
    symSHatBarEnd.gprs.get 16 = .const64 0x229b#64 ∧
    symSHatBarEnd.gprs.get 17 = .const64 0x6833#64 ∧
    symSHatBarEnd.gprs.get 18 = .const64 0xf9dd#64 ∧
    symSHatBarEnd.gprs.get 19 = .gpr0 19#5 0#64 ∧
    symSHatBarEnd.gprs.get 20 = .gpr0 20#5 0#64 ∧
    symSHatBarEnd.gprs.get 21 = .gpr0 21#5 128#64 ∧
    symSHatBarEnd.gprs.get 29 = .gpr0 29#5 0#64 ∧
    symSHatBarEnd.gprs.get 30 = .gpr0 30#5 0#64 := by
  have h0 := sHat_bar_end_ok
  unfold checkSHatBarEnd at h0
  simp only [Bool.and_eq_true] at h0
  have h := h0.2
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h9⟩, h10⟩,
    h11⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h29⟩, h30⟩
  exact ⟨eq_of_symGprBeq h0, eq_of_symGprBeq h1, eq_of_symGprBeq h2, eq_of_symGprBeq h3,
    eq_of_symGprBeq h4, eq_of_symGprBeq h5, eq_of_symGprBeq h6, eq_of_symGprBeq h9,
    eq_of_symGprBeq h10, eq_of_symGprBeq h11, eq_of_symGprBeq h13, eq_of_symGprBeq h14,
    eq_of_symGprBeq h15, eq_of_symGprBeq h16, eq_of_symGprBeq h17, eq_of_symGprBeq h18,
    eq_of_symGprBeq h19, eq_of_symGprBeq h20, eq_of_symGprBeq h21, eq_of_symGprBeq h29,
    eq_of_symGprBeq h30⟩






end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3Sym
