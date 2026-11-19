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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs

/-!
# `kyber_decapsulate` (`B06`): Relocation-Free Fetch and State Bridges

1. Generic relocation-free fetch lemma `fetch_blk06_range` parameterized by `blk06NoRelocInRange`.
2. Flat table indexing and evaluation lemmas (`SymVRegs`, `SymSpill40`, `SymVec32`, `SymGprs`).
3. Concrete state/spatial matching (`SymStateMatches`, `SymSpatial`) and step-preservation
   lemmas (`matches_writeVReg`, `matches_writeGpr`, `sp_range_off`, `gpr_poly_off`, etc.).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open ProofLib.ProgramReflection (WordTree)
open ProofLib.GenPlacedFetches (fetch_rebase_of_noReloc hookAtOff?_rebase_of_placeable)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemPlacement)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem
  Vec32
  vec32_ofFn_get
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blk06_code_eq
  blk06_tree_size
  blkLib06
  blkPC06
  blkPl06
  blkPlaceable06
  blkTree06
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (
  PolyLoc
  SExpr
  Spill40
  SpillSliceMem
  SymCfg
  SymEnv
  SymGpr
  SymGprs
  SymSpill40
  SymState
  SymVRegs
  SymVec32
  evalSExpr
  evalSymGpr
  fetchWordTree06
  spill40_ofFn_get
)

/-! ## 1. Relocation-Free Instruction Fetch on Any Clean `[wLo, wHi)` Slice of `B06` -/

@[expose] def blk06NoRelocInRange (wLo wHi : Nat) : Bool :=
  blkLib06.text.relocs.all (fun r => decide (r.off < 4 * wLo ∨ 4 * wHi ≤ r.off))

theorem blk06_relocAt?_range {wLo wHi off : Nat}
    (hnr : blk06NoRelocInRange wLo wHi = true)
    (hlo : 4 * wLo ≤ off) (hhi : off < 4 * wHi) :
    (blkLib06.text.relocAt? off).isNone = true := by
  cases hr : blkLib06.text.relocAt? off with
  | none => rfl
  | some r =>
    have hmem := CodeBlock.relocAt?_mem hr
    have hoff := CodeBlock.relocAt?_off hr
    have hall := (List.all_eq_true.mp hnr) r hmem
    simp only [decide_eq_true_eq] at hall
    omega

theorem fetch_blk06_range [MlKemPlacement] {b : BitVec 64} {wLo wHi j : Nat} {inst : Instr}
    (hnr : blk06NoRelocInRange wLo wHi = true) (hmax : wHi ≤ 13979)
    (hlo : wLo ≤ j) (hhi : j < wHi) (hfw : fetchWordTree06 j = some inst) :
    (blkPC06.rebase b (fun _ => none)).fetch (b + BitVec.ofNat 64 (4 * j)) = some inst := by
  have hdec : blkTree06.fetchDecodeAt (4 * j) = some inst := by
    unfold WordTree.fetchDecodeAt
    have hdiv : 4 * j / 4 = j := by omega
    rw [hdiv]
    unfold fetchWordTree06 at hfw
    cases hq : blkTree06.getQuad? j with
    | none => simp [hq] at hfw
    | some q =>
      rcases q with ⟨b0, b1, b2, b3⟩
      simp [hq] at hfw ⊢
      exact hfw
  have hnh := hookAtOff?_rebase_of_placeable (pl := blkPl06) (b := b)
    (X := fun _ => none) blk06_code_eq blk06_tree_size blkPlaceable06 (off := 4 * j) (by omega)
  exact fetch_rebase_of_noReloc blk06_code_eq blk06_tree_size
    (by omega) (by omega) (by omega) hdec
    (blk06_relocAt?_range hnr (by omega) (by omega)) hnh

/-! ## 2. Flat Table Indexing & Evaluation Lemmas -/

theorem symVRegs_ofFn_get (f : Nat → SExpr) (j : Nat) (hj : j < 32) :
    (SymVRegs.ofFn f).get j = f j := by
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
  | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
  | _ + 32 => omega

private theorem symVRegs_set_eq_ofFn (t : SymVRegs) (k : Nat) (hk : k < 32) (x : SExpr) :
    t.set k x = SymVRegs.ofFn (fun j => if j = k then x else t.get j) := by
  cases t
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
  | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
  | _ + 32 => omega

theorem symVRegs_set_get (t : SymVRegs) (k j : Nat) (hk : k < 32) (hj : j < 32) (x : SExpr) :
    (t.set k x).get j = if j = k then x else t.get j := by
  rw [symVRegs_set_eq_ofFn t k hk x, symVRegs_ofFn_get _ j hj]

theorem symSpill40_ofFn_get (f : Nat → SExpr) (j : Nat) (hj : j < 40) :
    (SymSpill40.ofFn f).get j = f j := by
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
  | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29
  | 30 | 31 | 32 | 33 | 34 | 35 | 36 | 37 | 38 | 39 => rfl
  | _ + 40 => omega

private theorem symSpill40_set_eq_ofFn (t : SymSpill40) (k : Nat) (hk : k < 40) (x : SExpr) :
    t.set k x = SymSpill40.ofFn (fun j => if j = k then x else t.get j) := by
  cases t
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
  | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29
  | 30 | 31 | 32 | 33 | 34 | 35 | 36 | 37 | 38 | 39 => rfl
  | _ + 40 => omega

theorem symSpill40_eval_get (env : SymEnv) (t : SymSpill40) (k : Nat) (hk : k < 40) :
    (t.eval env).get k = evalSExpr env (t.get k) :=
  spill40_ofFn_get _ k hk

theorem symSpill40_eval_set (env : SymEnv) (t : SymSpill40) (k : Nat) (x : SExpr) :
    (t.set k x).eval env = (t.eval env).set k (evalSExpr env x) := by
  cases t
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
  | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29
  | 30 | 31 | 32 | 33 | 34 | 35 | 36 | 37 | 38 | 39 => rfl
  | _ + 40 => rfl

theorem symVec32_ofFn_get (f : Nat → SExpr) (j : Nat) (hj : j < 32) :
    (SymVec32.ofFn f).get j = f j := by
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
  | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
  | _ + 32 => omega

theorem symVec32_eval_get (env : SymEnv) (t : SymVec32) (k : Nat) (hk : k < 32) :
    (t.eval env).get k = evalSExpr env (t.get k) :=
  vec32_ofFn_get _ k hk

theorem symVec32_eval_set (env : SymEnv) (t : SymVec32) (k : Nat) (x : SExpr) :
    (t.set k x).eval env = (t.eval env).set k (evalSExpr env x) := by
  cases t
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
  | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
  | _ + 32 => rfl

theorem symGprs_ofFn_get (f : Nat → SymGpr) (j : Nat) (hj : j < 31) :
    (SymGprs.ofFn f).get j = f j := by
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
  | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 => rfl
  | _ + 31 => omega

private theorem symGprs_set_eq_ofFn (t : SymGprs) (k : Nat) (hk : k < 31) (x : SymGpr) :
    t.set k x = SymGprs.ofFn (fun j => if j = k then x else t.get j) := by
  cases t
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
  | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 => rfl
  | _ + 31 => omega

theorem symGprs_set_get (t : SymGprs) (k j : Nat) (hk : k < 31) (hj : j < 31) (x : SymGpr) :
    (t.set k x).get j = if j = k then x else t.get j := by
  rw [symGprs_set_eq_ofFn t k hk x, symGprs_ofFn_get _ j hj]

/-! ## 3. Concrete State/Spatial Matching & Step-Preservation Helpers -/

@[expose] def SrcOptMem (hasSrc : Bool) (sp : BitVec 64) (src0 : Vec32) : SepProp :=
  if hasSrc then Poly32Mem (sp + 14432#64) src0 else emp

@[expose] def polyPtr (cfg : SymCfg) (sp : BitVec 64) (env : SymEnv) : BitVec 64 :=
  match cfg.polyLoc with
  | .spOff off => sp + BitVec.ofNat 64 off
  | .gpr r => env.gpr0 r

structure SymStateMatches (sp : BitVec 64) (env : SymEnv) (st : SymState) (s : State) : Prop where
  hsp     : s.sp = sp
  hsp_al  : s.spAligned = true
  hpstate : s.pstate = env.pstate0
  hvregs  : ∀ r : BitVec 5, s.readVReg128 r = evalSExpr env (st.vregs.get r.toNat)
  hgprs   : ∀ r : BitVec 5, r ≠ 31#5 →
    s.readReg64 (.gpr r) = evalSymGpr sp env.gpr0 (st.gprs.get r.toNat)

@[expose] def SymSpatial (cfg : SymCfg) (sp : BitVec 64) (env : SymEnv)
    (st : SymState) (F : SepProp) : SepProp :=
  SpillSliceMem cfg.spillLen (sp + BitVec.ofNat 64 cfg.spillOff) (st.spill.eval env) ∗
    Poly32Mem (polyPtr cfg sp env) (st.poly.eval env) ∗
    SrcOptMem cfg.hasSrc sp env.src0 ∗ F

theorem matches_writeVReg {sp : BitVec 64} {env : SymEnv} {st : SymState} {s : State}
    (hm : SymStateMatches sp env st s) (rd : BitVec 5) (e : SExpr) :
    SymStateMatches sp env { st with vregs := st.vregs.set rd.toNat e }
      (s.writeVReg128 rd (evalSExpr env e)) := by
  refine ⟨hm.hsp, hm.hsp_al, hm.hpstate, ?_, hm.hgprs⟩
  intro r
  rw [symVRegs_set_get st.vregs rd.toNat r.toNat rd.isLt r.isLt e]
  by_cases heq : r = rd
  · subst heq; simp [State.readVReg128, State.writeVReg128]
  · have hne : r.toNat ≠ rd.toNat := fun h => heq (BitVec.eq_of_toNat_eq h)
    simp only [hne, ↓reduceIte]
    simpa [State.readVReg128, State.writeVReg128, heq] using hm.hvregs r

private theorem bitvec5_lt31 {r : BitVec 5} (hr : r ≠ 31#5) : r.toNat < 31 := by
  have hlt := r.isLt
  have hne : r.toNat ≠ 31 := fun h => hr (BitVec.eq_of_toNat_eq (by simpa using h))
  omega

theorem matches_writeGpr {sp : BitVec 64} {env : SymEnv} {st : SymState} {s : State}
    (hm : SymStateMatches sp env st s) {rd : BitVec 5} (hrd : rd ≠ 31#5)
    (sg : SymGpr) {val : BitVec 64} (hval : val = evalSymGpr sp env.gpr0 sg) :
    SymStateMatches sp env { st with gprs := st.gprs.set rd.toNat sg }
      (s.writeReg64 (.gpr rd) val) := by
  refine ⟨hm.hsp, hm.hsp_al, hm.hpstate, hm.hvregs, ?_⟩
  intro r hr
  rw [symGprs_set_get st.gprs rd.toNat r.toNat (bitvec5_lt31 hrd) (bitvec5_lt31 hr) sg]
  by_cases heq : r = rd
  · subst heq
    have hb : (r == 31#5) = false := beq_false_of_ne hr
    simp [State.readReg64, State.writeReg64, hb, hval]
  · have hne : r.toNat ≠ rd.toNat := fun h => heq (BitVec.eq_of_toNat_eq h)
    have hb_r : (r == 31#5) = false := beq_false_of_ne hr
    have hb_rd : (rd == 31#5) = false := beq_false_of_ne hrd
    simp only [hne, ↓reduceIte]
    simpa [State.readReg64, State.writeReg64, hb_r, hb_rd, heq] using hm.hgprs r hr

theorem matches_getGpr {sp : BitVec 64} {env : SymEnv} {st : SymState} {s : State}
    (hm : SymStateMatches sp env st s) {r : BitVec 5} (hr : r ≠ 31#5) :
    s.readReg64 (.gpr r) = evalSymGpr sp env.gpr0 (st.gprs.get r.toNat) :=
  hm.hgprs r hr

theorem matches_getFromZRBits {sp : BitVec 64} {env : SymEnv} {st : SymState} {s : State}
    (hm : SymStateMatches sp env st s) {r : BitVec 5} (hr : r ≠ 31#5) :
    s.readReg64 (Reg.fromZRBits r) = evalSymGpr sp env.gpr0 (st.gprs.get r.toNat) := by
  have hb : (r == 31#5) = false := beq_false_of_ne hr
  simpa [Reg.fromZRBits, hb] using hm.hgprs r hr

theorem matches_orFpsr {sp : BitVec 64} {env : SymEnv} {st : SymState} {s : State}
    (hm : SymStateMatches sp env st s) (fl : BitVec 32) :
    SymStateMatches sp env st (s.orFpsr fl) :=
  ⟨hm.hsp, hm.hsp_al, hm.hpstate, hm.hvregs, hm.hgprs⟩

theorem matches_setPC {sp : BitVec 64} {env : SymEnv} {st : SymState} {s : State}
    (hm : SymStateMatches sp env st s) (pc' : BitVec 64) :
    SymStateMatches sp env st (s.setPC pc') :=
  ⟨hm.hsp, hm.hsp_al, hm.hpstate, hm.hvregs, hm.hgprs⟩

theorem matches_advancePC {sp : BitVec 64} {env : SymEnv} {st : SymState} {s : State}
    (hm : SymStateMatches sp env st s) :
    SymStateMatches sp env st s.advancePC :=
  ⟨hm.hsp, hm.hsp_al, hm.hpstate, hm.hvregs, hm.hgprs⟩

theorem matches_store {sp : BitVec 64} {env : SymEnv} {st : SymState} {s : State}
    (hm : SymStateMatches sp env st s) (sp' : SymSpill40) (p' : SymVec32)
    (pc' : BitVec 64) (m' : Memory) :
    SymStateMatches sp env { st with spill := sp', poly := p' }
      (((applyWriteback s none).setPC pc').setMem m') :=
  ⟨hm.hsp, hm.hsp_al, hm.hpstate, hm.hvregs, hm.hgprs⟩

theorem sp_range_off {sp : BitVec 64} {base len : Nat} {off : BitVec 64}
    (hlo : base ≤ off.toNat) (hhi : off.toNat < base + 16 * len)
    (hm : (off.toNat - base) % 16 = 0) :
    (off.toNat - base) / 16 < len ∧
      (sp + BitVec.ofNat 64 base) + BitVec.ofNat 64 (16 * ((off.toNat - base) / 16)) = sp + off := by
  refine ⟨by omega, ?_⟩
  have hlt : off.toNat < 2 ^ 64 := off.isLt
  have heq : BitVec.ofNat 64 base + BitVec.ofNat 64 (16 * ((off.toNat - base) / 16)) = off := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [BitVec.add_assoc, heq]

theorem gpr_poly_off {ptr off : BitVec 64} (ho : off.toNat < 512) (hm : off.toNat % 16 = 0) :
    off.toNat / 16 < 32 ∧ ptr + BitVec.ofNat 64 (16 * (off.toNat / 16)) = ptr + off := by
  refine ⟨by omega, ?_⟩
  have heq : BitVec.ofNat 64 (16 * (off.toNat / 16)) = off := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofNat]; omega
  rw [heq]

theorem gpr_poly_off16 {ptr off : BitVec 64} (ho : off.toNat + 16 < 512) (hm : off.toNat % 16 = 0) :
    off.toNat / 16 + 1 < 32 ∧ (ptr + off) + 16#64 = ptr + BitVec.ofNat 64 (16 * (off.toNat / 16 + 1)) := by
  refine ⟨by omega, ?_⟩
  have heq : off + 16#64 = BitVec.ofNat 64 (16 * (off.toNat / 16 + 1)) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [BitVec.add_assoc, heq]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge
