/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyEval -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem

/-!
# `decapsulate_compressed_key` (`B04`) — Fetch, State, & Spatial Routing Bridges (`SymPolyBridge`)
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyBridge

open Arm64 Arm64.Obj ProofLib SepProp
open scoped ProofLib.ProgramReflection
open ProofLib.ProgramReflection (WordTree)
open ProofLib.GenPlacedFetches (hookAtOff?_rebase_of_placeable fetch_rebase_of_noReloc)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemPlacement)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
  (SepLoad128 SepStore128)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
  (blkLib04 blkPl04 blkPC04 blkTree04 blkPlaceable04 blk04_code_eq blk04_tree_size)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyDefs
  (SExpr SymGpr SymPState SymSpill13 SymSpill6 SymSpill21 SymVec32
   SpillMode SymCfg SymState fetchWordTree04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyEval
  (SymEnv evalSExpr evalSymGpr evalSymPState symVRegs_set_get symGprs31_set_get
   symSpill13_eval_get symSpill13_eval_set symSpill6_eval_get symSpill6_eval_set
   symSpill21_eval_get symSpill21_eval_set symVec32_eval_get symVec32_eval_set
   polyAddr spillMemAt inPolyMemAt SymSpatial SymStateMatches)

/-! ## 1. Relocation-Free Instruction Fetch Across All 8 `B04` Straight-Line Blocks -/

/-- Word indices inside the 8 relocation-free straight-line NEON blocks of `B04`. -/
@[expose] def InSymWord04 (j : Nat) : Prop :=
  (461 ≤ j ∧ j < 1304) ∨ (1306 ≤ j ∧ j < 1333) ∨ (1393 ≤ j ∧ j < 1562) ∨
  (2048 ≤ j ∧ j < 3608) ∨ (7556 ≤ j ∧ j < 8338) ∨ (8397 ≤ j ∧ j < 8564) ∨
  (9333 ≤ j ∧ j < 10791) ∨ (11683 ≤ j ∧ j < 13243)

private theorem blk04_relocs_outside_sym :
    blkLib04.text.relocs.all (fun r => decide (
      !(1844 ≤ r.off && r.off < 5216) &&
      !(5224 ≤ r.off && r.off < 5332) &&
      !(5572 ≤ r.off && r.off < 6248) &&
      !(8192 ≤ r.off && r.off < 14432) &&
      !(30224 ≤ r.off && r.off < 33352) &&
      !(33588 ≤ r.off && r.off < 34256) &&
      !(37332 ≤ r.off && r.off < 43164) &&
      !(46732 ≤ r.off && r.off < 52972))) = true := by
  rfl_kernel

private theorem blk04_relocAt?_sym {j : Nat} (hj : InSymWord04 j) :
    (blkLib04.text.relocAt? (4 * j)).isNone = true := by
  cases hr : blkLib04.text.relocAt? (4 * j) with
  | none => rfl
  | some r =>
    have hmem := CodeBlock.relocAt?_mem hr
    have hoff := CodeBlock.relocAt?_off hr
    have hall := (List.all_eq_true.mp blk04_relocs_outside_sym) r hmem
    simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true',
      Bool.and_eq_false_iff, decide_eq_false_iff_not] at hall
    unfold InSymWord04 at hj
    omega

theorem fetch_blk04_sym [MlKemPlacement] {b : BitVec 64} {j : Nat} {inst : Instr}
    (hj : InSymWord04 j) (hfw : fetchWordTree04 j = some inst) :
    (blkPC04.rebase b (fun _ => none)).fetch (b + BitVec.ofNat 64 (4 * j)) = some inst := by
  have hj_lt : j < 13411 := by unfold InSymWord04 at hj; omega
  have hdec : blkTree04.fetchDecodeAt (4 * j) = some inst := by
    unfold WordTree.fetchDecodeAt
    rw [show 4 * j / 4 = j from by omega]
    unfold fetchWordTree04 at hfw
    cases hq : blkTree04.getQuad? j with
    | none => simp [hq] at hfw
    | some q =>
      rcases q with ⟨b0, b1, b2, b3⟩
      simp [hq] at hfw ⊢
      exact hfw
  have hnh := hookAtOff?_rebase_of_placeable (pl := blkPl04) (b := b)
    (X := fun _ => none) blk04_code_eq blk04_tree_size blkPlaceable04 (off := 4 * j) (by omega)
  exact fetch_rebase_of_noReloc blk04_code_eq blk04_tree_size
    (by omega) (by omega) (by omega) hdec (blk04_relocAt?_sym hj) hnh

/-! ## 2. `SymStateMatches` Preservation Helpers -/

theorem fromZRBits_lt31 {rn : BitVec 5} (hrn : rn.toNat < 31) :
    Reg.fromZRBits rn = .gpr rn := by
  have hne : rn ≠ 31#5 := by intro h; subst h; simp at hrn
  simp [Reg.fromZRBits, hne]

theorem matches_writeVReg {cfg : SymCfg} {sp polyPtr : BitVec 64} {env : SymEnv}
    {st : SymState} {s : State}
    (hm : SymStateMatches cfg sp polyPtr env st s) (rd : BitVec 5) (e : SExpr) :
    SymStateMatches cfg sp polyPtr env { st with vregs := st.vregs.set rd.toNat e }
      (s.writeVReg128 rd (evalSExpr env e)) := by
  refine ⟨hm.hsp, hm.hsp_al, hm.hpoly, ?_, hm.hgprs, hm.hpstate⟩
  intro r
  rw [symVRegs_set_get st.vregs rd.toNat e rd.isLt r.toNat r.isLt]
  by_cases h : r.toNat = rd.toNat
  · have hrd : r = rd := BitVec.eq_of_toNat_eq h
    subst hrd; simp
  · have hrd : r ≠ rd := fun heq => h (congrArg BitVec.toNat heq)
    simp [h, hrd, hm.hvregs r]

theorem matches_writeGpr {cfg : SymCfg} {sp polyPtr : BitVec 64} {env : SymEnv}
    {st : SymState} {s : State}
    (hm : SymStateMatches cfg sp polyPtr env st s) {rd : BitVec 5} {sg : SymGpr} {val : BitVec 64}
    (hrd : rd.toNat < 31) (hnp : cfg.polyReg? ≠ some rd)
    (hval : val = evalSymGpr sp env sg) :
    SymStateMatches cfg sp polyPtr env { st with gprs := st.gprs.set rd.toNat sg }
      (s.writeReg64 (.gpr rd) val) := by
  refine ⟨hm.hsp, hm.hsp_al, ?_, hm.hvregs, ?_, hm.hpstate⟩
  · intro r hr
    have hne : Reg.gpr r ≠ Reg.gpr rd := by
      intro heq; cases heq; exact hnp hr
    rw [State.readReg64_writeReg64_ne _ _ _ _ hne]
    exact hm.hpoly r hr
  · intro r hr
    rw [symGprs31_set_get st.gprs rd.toNat sg hrd r.toNat hr]
    by_cases h : r.toNat = rd.toNat
    · have heq : r = rd := BitVec.eq_of_toNat_eq h
      subst heq
      have hr31 : r ≠ 31#5 := by intro he; subst he; simp at hr
      simp [hr31, hval]
    · have hne : Reg.gpr r ≠ Reg.gpr rd := fun heq => by cases heq; exact h rfl
      rw [State.readReg64_writeReg64_ne _ _ _ _ hne]
      simp [h, hm.hgprs r hr]

theorem matches_setPState {cfg : SymCfg} {sp polyPtr : BitVec 64} {env : SymEnv}
    {st : SymState} {s : State}
    (hm : SymStateMatches cfg sp polyPtr env st s) {spst : SymPState} {pst : PState}
    (hpst : pst = evalSymPState sp env spst) :
    SymStateMatches cfg sp polyPtr env { st with pstate := spst } (s.setPState pst) :=
  ⟨hm.hsp, hm.hsp_al, hm.hpoly, hm.hvregs, hm.hgprs, hpst⟩

theorem matches_orFpsr {cfg : SymCfg} {sp polyPtr : BitVec 64} {env : SymEnv}
    {st : SymState} {s : State}
    (hm : SymStateMatches cfg sp polyPtr env st s) (fl : BitVec 32) :
    SymStateMatches cfg sp polyPtr env st (s.orFpsr fl) :=
  ⟨hm.hsp, hm.hsp_al, hm.hpoly, hm.hvregs, hm.hgprs, hm.hpstate⟩

theorem matches_setPC {cfg : SymCfg} {sp polyPtr : BitVec 64} {env : SymEnv}
    {st : SymState} {s : State}
    (hm : SymStateMatches cfg sp polyPtr env st s) (pc' : BitVec 64) :
    SymStateMatches cfg sp polyPtr env st (s.setPC pc') :=
  ⟨hm.hsp, hm.hsp_al, hm.hpoly, hm.hvregs, hm.hgprs, hm.hpstate⟩

theorem matches_advancePC {cfg : SymCfg} {sp polyPtr : BitVec 64} {env : SymEnv}
    {st : SymState} {s : State}
    (hm : SymStateMatches cfg sp polyPtr env st s) :
    SymStateMatches cfg sp polyPtr env st s.advancePC :=
  ⟨hm.hsp, hm.hsp_al, hm.hpoly, hm.hvregs, hm.hgprs, hm.hpstate⟩

theorem matches_store {cfg : SymCfg} {sp polyPtr : BitVec 64} {env : SymEnv}
    {st : SymState} {s : State}
    (hm : SymStateMatches cfg sp polyPtr env st s)
    (s13 : SymSpill13) (s6 : SymSpill6) (s21 : SymSpill21) (p' : SymVec32)
    (pc' : BitVec 64) (m' : Memory) :
    SymStateMatches cfg sp polyPtr env
      { st with spill13 := s13, spill6 := s6, spill21 := s21, poly := p' }
      (((applyWriteback s none).setPC pc').setMem m') :=
  ⟨hm.hsp, hm.hsp_al, hm.hpoly, hm.hvregs, hm.hgprs, hm.hpstate⟩

/-! ## 3. Offset Arithmetic & `SepLoad128` / `SepStore128` Routing into `SymSpatial` -/

theorem ptr_off_k {ptr off : BitVec 64} {n : Nat}
    (hhi : off.toNat < 16 * n) (hm : off.toNat % 16 = 0) :
    off.toNat / 16 < n ∧ ptr + BitVec.ofNat 64 (16 * (off.toNat / 16)) = ptr + off := by
  refine ⟨by omega, congrArg (ptr + ·) ?_⟩
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofNat]; omega

theorem ptr_off_k16 {ptr off : BitVec 64} {n : Nat}
    (hhi : off.toNat + 16 < 16 * n) (hm : off.toNat % 16 = 0) :
    off.toNat / 16 + 1 < n ∧
      (ptr + off) + 16#64 = ptr + BitVec.ofNat 64 (16 * (off.toNat / 16 + 1)) := by
  refine ⟨by omega, ?_⟩
  rw [BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem base_off_k {sp off : BitVec 64} (lo n : Nat)
    (hlo : lo ≤ off.toNat) (hhi : off.toNat < lo + 16 * n) (hm : (off.toNat - lo) % 16 = 0) :
    (off.toNat - lo) / 16 < n ∧
      (sp + BitVec.ofNat 64 lo) + BitVec.ofNat 64 (16 * ((off.toNat - lo) / 16)) = sp + off := by
  refine ⟨by omega, ?_⟩
  rw [BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem base_off_k16 {sp off : BitVec 64} (lo n : Nat)
    (hlo : lo ≤ off.toNat) (hhi : off.toNat + 16 < lo + 16 * n) (hm : (off.toNat - lo) % 16 = 0) :
    (off.toNat - lo) / 16 + 1 < n ∧
      (sp + off) + 16#64 =
        (sp + BitVec.ofNat 64 lo) + BitVec.ofNat 64 (16 * ((off.toNat - lo) / 16 + 1)) := by
  refine ⟨by omega, ?_⟩
  rw [BitVec.add_assoc, BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem load_polyReg {cfg : SymCfg} {sp polyPtr ea : BitVec 64} {env : SymEnv}
    {st : SymState} {F : SepProp} {r : BitVec 5} {k : Nat}
    (hpr : cfg.polyReg? = some r) (hk : k < 32)
    (ha : polyPtr + BitVec.ofNat 64 (16 * k) = ea) :
    SepLoad128 ea (SymSpatial cfg sp polyPtr env st F) (evalSExpr env (st.poly.get k)) := by
  unfold SymSpatial polyAddr; rw [hpr]
  exact SepLoad128.left (SepLoad128.vec32 hk ha (symVec32_eval_get env st.poly k hk))

theorem store_polyReg {cfg : SymCfg} {sp polyPtr ea : BitVec 64} {env : SymEnv}
    {st : SymState} {F : SepProp} {r : BitVec 5} {k : Nat} {e : SExpr}
    (hpr : cfg.polyReg? = some r) (hk : k < 32)
    (ha : polyPtr + BitVec.ofNat 64 (16 * k) = ea) :
    SepStore128 ea (evalSExpr env e) (SymSpatial cfg sp polyPtr env st F)
      (SymSpatial cfg sp polyPtr env { st with poly := st.poly.set k e } F) := by
  unfold SymSpatial polyAddr; rw [hpr]
  exact SepStore128.left (SepStore128.vec32 hk ha (symVec32_eval_set env st.poly k e).symm)

theorem load_polySp {cfg : SymCfg} {sp polyPtr ea : BitVec 64} {env : SymEnv}
    {st : SymState} {F : SepProp} {k : Nat}
    (hpr : cfg.polyReg? = none) (hk : k < 32)
    (ha : (sp + 20704#64) + BitVec.ofNat 64 (16 * k) = ea) :
    SepLoad128 ea (SymSpatial cfg sp polyPtr env st F) (evalSExpr env (st.poly.get k)) := by
  unfold SymSpatial polyAddr; rw [hpr]
  exact SepLoad128.left (SepLoad128.vec32 hk ha (symVec32_eval_get env st.poly k hk))

theorem store_polySp {cfg : SymCfg} {sp polyPtr ea : BitVec 64} {env : SymEnv}
    {st : SymState} {F : SepProp} {k : Nat} {e : SExpr}
    (hpr : cfg.polyReg? = none) (hk : k < 32)
    (ha : (sp + 20704#64) + BitVec.ofNat 64 (16 * k) = ea) :
    SepStore128 ea (evalSExpr env e) (SymSpatial cfg sp polyPtr env st F)
      (SymSpatial cfg sp polyPtr env { st with poly := st.poly.set k e } F) := by
  unfold SymSpatial polyAddr; rw [hpr]
  exact SepStore128.left (SepStore128.vec32 hk ha (symVec32_eval_set env st.poly k e).symm)

theorem load_spill13 {cfg : SymCfg} {sp polyPtr ea : BitVec 64} {env : SymEnv}
    {st : SymState} {F : SepProp} {k : Nat}
    (hm : cfg.spillMode = .s40) (hk : k < 13)
    (ha : (sp + 1616#64) + BitVec.ofNat 64 (16 * k) = ea) :
    SepLoad128 ea (SymSpatial cfg sp polyPtr env st F) (evalSExpr env (st.spill13.get k)) := by
  unfold SymSpatial spillMemAt; rw [hm]
  exact SepLoad128.right (SepLoad128.left (SepLoad128.left
    (SepLoad128.spill13 hk ha (symSpill13_eval_get env st.spill13 k hk))))

theorem store_spill13 {cfg : SymCfg} {sp polyPtr ea : BitVec 64} {env : SymEnv}
    {st : SymState} {F : SepProp} {k : Nat} {e : SExpr}
    (hm : cfg.spillMode = .s40) (hk : k < 13)
    (ha : (sp + 1616#64) + BitVec.ofNat 64 (16 * k) = ea) :
    SepStore128 ea (evalSExpr env e) (SymSpatial cfg sp polyPtr env st F)
      (SymSpatial cfg sp polyPtr env { st with spill13 := st.spill13.set k e } F) := by
  unfold SymSpatial spillMemAt; rw [hm]
  exact SepStore128.right (SepStore128.left (SepStore128.left
    (SepStore128.spill13 hk ha (symSpill13_eval_set env st.spill13 k e).symm)))

theorem load_spill6 {cfg : SymCfg} {sp polyPtr ea : BitVec 64} {env : SymEnv}
    {st : SymState} {F : SepProp} {k : Nat}
    (hm : cfg.spillMode = .s27 ∨ cfg.spillMode = .s40) (hk : k < 6)
    (ha : (sp + 1824#64) + BitVec.ofNat 64 (16 * k) = ea) :
    SepLoad128 ea (SymSpatial cfg sp polyPtr env st F) (evalSExpr env (st.spill6.get k)) := by
  unfold SymSpatial spillMemAt
  rcases hm with h | h <;> rw [h]
  · exact SepLoad128.right (SepLoad128.left (SepLoad128.left
      (SpillMem.SepLoad128.spill6 hk ha (symSpill6_eval_get env st.spill6 k hk))))
  · exact SepLoad128.right (SepLoad128.left (SepLoad128.right (SepLoad128.left
      (SpillMem.SepLoad128.spill6 hk ha (symSpill6_eval_get env st.spill6 k hk)))))

theorem store_spill6 {cfg : SymCfg} {sp polyPtr ea : BitVec 64} {env : SymEnv}
    {st : SymState} {F : SepProp} {k : Nat} {e : SExpr}
    (hm : cfg.spillMode = .s27 ∨ cfg.spillMode = .s40) (hk : k < 6)
    (ha : (sp + 1824#64) + BitVec.ofNat 64 (16 * k) = ea) :
    SepStore128 ea (evalSExpr env e) (SymSpatial cfg sp polyPtr env st F)
      (SymSpatial cfg sp polyPtr env { st with spill6 := st.spill6.set k e } F) := by
  unfold SymSpatial spillMemAt
  rcases hm with h | h <;> rw [h]
  · exact SepStore128.right (SepStore128.left (SepStore128.left
      (SpillMem.SepStore128.spill6 hk ha (symSpill6_eval_set env st.spill6 k e).symm)))
  · exact SepStore128.right (SepStore128.left (SepStore128.right (SepStore128.left
      (SpillMem.SepStore128.spill6 hk ha (symSpill6_eval_set env st.spill6 k e).symm))))

theorem load_spill21 {cfg : SymCfg} {sp polyPtr ea : BitVec 64} {env : SymEnv}
    {st : SymState} {F : SepProp} {k : Nat}
    (hm : cfg.spillMode ≠ .none) (hk : k < 21)
    (ha : (sp + 1920#64) + BitVec.ofNat 64 (16 * k) = ea) :
    SepLoad128 ea (SymSpatial cfg sp polyPtr env st F) (evalSExpr env (st.spill21.get k)) := by
  unfold SymSpatial spillMemAt
  cases h : cfg.spillMode
  · exact absurd h hm
  · exact SepLoad128.right (SepLoad128.left
      (SpillMem.SepLoad128.spill21 hk ha (symSpill21_eval_get env st.spill21 k hk)))
  · exact SepLoad128.right (SepLoad128.left (SepLoad128.right
      (SpillMem.SepLoad128.spill21 hk ha (symSpill21_eval_get env st.spill21 k hk))))
  · exact SepLoad128.right (SepLoad128.left (SepLoad128.right (SepLoad128.right
      (SpillMem.SepLoad128.spill21 hk ha (symSpill21_eval_get env st.spill21 k hk)))))

theorem store_spill21 {cfg : SymCfg} {sp polyPtr ea : BitVec 64} {env : SymEnv}
    {st : SymState} {F : SepProp} {k : Nat} {e : SExpr}
    (hm : cfg.spillMode ≠ .none) (hk : k < 21)
    (ha : (sp + 1920#64) + BitVec.ofNat 64 (16 * k) = ea) :
    SepStore128 ea (evalSExpr env e) (SymSpatial cfg sp polyPtr env st F)
      (SymSpatial cfg sp polyPtr env { st with spill21 := st.spill21.set k e } F) := by
  unfold SymSpatial spillMemAt
  cases h : cfg.spillMode
  · exact absurd h hm
  · exact SepStore128.right (SepStore128.left
      (SpillMem.SepStore128.spill21 hk ha (symSpill21_eval_set env st.spill21 k e).symm))
  · exact SepStore128.right (SepStore128.left (SepStore128.right
      (SpillMem.SepStore128.spill21 hk ha (symSpill21_eval_set env st.spill21 k e).symm)))
  · exact SepStore128.right (SepStore128.left (SepStore128.right (SepStore128.right
      (SpillMem.SepStore128.spill21 hk ha (symSpill21_eval_set env st.spill21 k e).symm))))

theorem load_inPoly {cfg : SymCfg} {sp polyPtr ea : BitVec 64} {env : SymEnv}
    {st : SymState} {F : SepProp} {k : Nat}
    (hip : cfg.hasInPoly = true) (hk : k < 32)
    (ha : (sp + 11856#64) + BitVec.ofNat 64 (16 * k) = ea) :
    SepLoad128 ea (SymSpatial cfg sp polyPtr env st F) (evalSExpr env (.inPoly k)) := by
  unfold SymSpatial inPolyMemAt; rw [hip]
  exact SepLoad128.right (SepLoad128.right (SepLoad128.left
    (SepLoad128.vec32 hk ha rfl)))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SymPolyBridge
