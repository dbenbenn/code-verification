/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4SymDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem

/-!
# `encapsulate2` (`B20`) — AdvSIMD & State Bridges for `Seg4Sym`
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4SymBridge

open Arm64 Arm64.Obj ProofLib SepProp
open scoped ProofLib.ProgramReflection
open ProofLib.ProgramReflection (WordTree)
open ProofLib.GenPlacedFetches (hookAtOff?_rebase_of_placeable fetch_rebase_of_noReloc)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
  (MlKemPlacement)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec
  (sqdmulh16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
  (lane16 dup8x16 ext_lane16 lane16_dup8x16 extractLsb64_lo_pack8x16 extractLsb64_hi_pack8x16
   simdLaneSInt_16_zeroExtend truncate16_intToSimdLane_16
   lane16_mapSimdLanes_true_16 lane16_zipSimdLanes_true_16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
  (simdAdd8h simdSub8h simdMul8h simdMla8h simdSqdmulh8h simdSshr8h
   lane16_not lane16_simdAdd8h lane16_simdSub8h lane16_simdMul8h
   lane16_simdMla8h lane16_simdSqdmulh8h lane16_simdSshr8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Arith
  (toInt_sshiftRight_16 sqdmulh16_toInt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
  (blkLib20 blkPC20 blkTree20 blkPlaceable20 blk20_code_eq blk20_tree_size)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
  (append_extractLsb64)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4SymDefs
  (SExpr SymGpr SymGprs SymState fetchWordTree20
   SymEnv evalSExpr symVRegs_set_get SymGprMatches SymStateMatches)

/-! ## 1. Relocation-Free Instruction Fetch on `[0x10a0 .. 0x28e8)` -/

private theorem blk20_relocs_outside_seg4 :
    blkLib20.text.relocs.all (fun r => decide (r.off < 0x10a0 ∨ 0x28e8 ≤ r.off)) = true := by
  rfl_kernel

private theorem blk20_relocAt?_seg4 {off : Nat} (hlo : 0x10a0 ≤ off) (hhi : off < 0x28e8) :
    (blkLib20.text.relocAt? off).isNone = true := by
  cases hr : blkLib20.text.relocAt? off with
  | none => rfl
  | some r =>
    have hmem := CodeBlock.relocAt?_mem hr
    have hoff := CodeBlock.relocAt?_off hr
    have hall := (List.all_eq_true.mp blk20_relocs_outside_seg4) r hmem
    simp only [decide_eq_true_eq] at hall
    omega

theorem fetch_blk20_seg4 [MlKemPlacement] {b : BitVec 64} {j : Nat} {inst : Instr}
    (hlo : 1064 ≤ j) (hhi : j < 2618) (hfw : fetchWordTree20 j = some inst) :
    (blkPC20.rebase b (fun _ => none)).fetch (b + BitVec.ofNat 64 (4 * j)) = some inst := by
  have hdec : blkTree20.fetchDecodeAt (4 * j) = some inst := by
    unfold WordTree.fetchDecodeAt
    have hdiv : 4 * j / 4 = j := by omega
    rw [hdiv]
    unfold fetchWordTree20 at hfw
    cases hq : blkTree20.getQuad? j with
    | none => simp [hq] at hfw
    | some q =>
      rcases q with ⟨b0, b1, b2, b3⟩
      simp [hq] at hfw ⊢
      exact hfw
  have hnh := hookAtOff?_rebase_of_placeable (pl := Base.blkPl20) (b := b)
    (X := fun _ => none) blk20_code_eq blk20_tree_size blkPlaceable20 (off := 4 * j) (by omega)
  exact fetch_rebase_of_noReloc blk20_code_eq blk20_tree_size
    (by omega) (by omega) (by omega) hdec
    (blk20_relocAt?_seg4 (by omega) (by omega)) hnh

/-! ## 2. Pure AdvSIMD Vector Algebra Bridges -/

theorem rep8_eq_dup8x16 (c : BitVec 16) :
    (c ++ c ++ c ++ c) ++ (c ++ c ++ c ++ c) = dup8x16 c := by
  have hlo := extractLsb64_lo_pack8x16 (fun _ => c)
  have hhi := extractLsb64_hi_pack8x16 (fun _ => c)
  have happ := append_extractLsb64 (dup8x16 c)
  unfold dup8x16 at happ
  rw [hhi, hlo] at happ
  exact happ

private theorem not_append_same {n m : Nat} (a : BitVec n) (b : BitVec m) :
    ~~~(a ++ b) = ~~~a ++ ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro k _
  simp [BitVec.getLsbD_append]

theorem not_rep8_eq_dup8x16 (c : BitVec 16) :
    ~~~(c ++ c ++ c ++ c) ++ ~~~(c ++ c ++ c ++ c) = dup8x16 (~~~c) := by
  rw [not_append_same, not_append_same, not_append_same, rep8_eq_dup8x16]

theorem simdDup_eval (v : BitVec 64) :
    mapSimdLanes true 16 0#128 (fun _ => (v.zeroExtend 128) &&& 65535#128) =
      dup8x16 (v.truncate 16) := by
  apply ext_lane16; intro i
  rw [lane16_mapSimdLanes_true_16, lane16_dup8x16]
  have hmask : ∀ k : Fin 16, (65535#16)[k.val] = true := by decide
  ext k hk
  have hm : (65535#16)[k] = true := hmask ⟨k, hk⟩
  simp [BitVec.truncate, BitVec.zeroExtend, show k < 64 from by omega, hm]

theorem simdSshr_eval (vn vd : BitVec 128) (sh : Nat) (hsh0 : 0 < sh) (hsh : sh < 16) :
    zipSimdLanes true 16 vn vd
      (fun lane _ => intToSimdLane 16 (aslRShr (simdLaneSInt 16 lane) sh false)) =
      simdSshr8h vn sh := by
  apply ext_lane16; intro i
  rw [lane16_zipSimdLanes_true_16, lane16_simdSshr8h, simdLaneSInt_16_zeroExtend,
      truncate16_intToSimdLane_16]
  have hne : (sh == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
  have hpow : (Int.ofNat (1 <<< sh)) = (2 ^ sh : Int) := by
    match sh with
    | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 => rfl
    | 0 | _ + 16 => omega
  simp only [aslRShr, hne, Bool.false_eq_true, ↓reduceIte, hpow,
    ← toInt_sshiftRight_16 (lane16 vn i) sh hsh, BitVec.ofInt_toInt]

theorem simdSqdmulh_eval (vn vm : BitVec 128) :
    zipSimdLanes true 16 vn vm
      (fun a b => aslSignedSat 16 (aslRShr (2 * simdLaneSInt 16 a * simdLaneSInt 16 b) 16 false)) =
      simdSqdmulh8h vn vm := by
  apply ext_lane16; intro i
  rw [lane16_zipSimdLanes_true_16, lane16_simdSqdmulh8h,
      simdLaneSInt_16_zeroExtend, simdLaneSInt_16_zeroExtend]
  set x := lane16 vn i
  set y := lane16 vm i
  by_cases h8000 : x = 0x8000#16 ∧ y = 0x8000#16
  · rcases h8000 with ⟨hx, hy⟩; rw [hx, hy]; decide
  · have hdiv : aslRShr (2 * x.toInt * y.toInt) 16 false = (sqdmulh16 x y).toInt := by
      rw [sqdmulh16_toInt h8000]
      change (2 * x.toInt * y.toInt) / (2 * 32768) = (x.toInt * y.toInt) / 32768
      rw [Int.mul_assoc]
      exact Int.mul_ediv_mul_of_pos _ _ (by decide : (0 : Int) < 2)
    rw [hdiv]
    set z := sqdmulh16 x y
    have hlo : -32768 ≤ z.toInt := BitVec.le_toInt z
    have hhi : z.toInt < 32768 := BitVec.toInt_lt
    have hg1 : ¬(z.toInt > (Int.ofNat (1 <<< (16 - 1)) - 1)) := by change ¬(z.toInt > 32767); omega
    have hg2 : ¬(z.toInt < -(Int.ofNat (1 <<< (16 - 1)))) := by change ¬(z.toInt < -32768); omega
    simp only [aslSignedSat, hg1, hg2, ↓reduceIte, truncate16_intToSimdLane_16, BitVec.ofInt_toInt]

theorem simdAdd_eval (vn vm : BitVec 128) :
    zipSimdLanes true 16 vn vm (fun a b => a + b) = simdAdd8h vn vm := by
  apply ext_lane16; intro i
  rw [lane16_zipSimdLanes_true_16, lane16_simdAdd8h]
  apply BitVec.eq_of_toNat_eq
  have ha := (lane16 vn i).isLt
  have hb := (lane16 vm i).isLt
  simp only [BitVec.truncate, BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_add]
  omega

theorem simdSub_eval (vn vm : BitVec 128) :
    zipSimdLanes true 16 vn vm (fun a b => a - b) = simdSub8h vn vm := by
  apply ext_lane16; intro i
  rw [lane16_zipSimdLanes_true_16, lane16_simdSub8h]
  apply BitVec.eq_of_toNat_eq
  have ha := (lane16 vn i).isLt
  have hb := (lane16 vm i).isLt
  simp only [BitVec.truncate, BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_sub]
  omega

theorem simdMul_eval (vn vm : BitVec 128) :
    zipSimdLanes true 16 vn vm (fun a b => a * b) = simdMul8h vn vm := by
  apply ext_lane16; intro i
  rw [lane16_zipSimdLanes_true_16, lane16_simdMul8h]
  apply BitVec.eq_of_toNat_eq
  have ha : (lane16 vn i).toNat < 2 ^ 128 := by have := (lane16 vn i).isLt; omega
  have hb : (lane16 vm i).toNat < 2 ^ 128 := by have := (lane16 vm i).isLt; omega
  simp only [BitVec.truncate, BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_mul,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  exact Nat.mod_mod_of_dvd _ (by decide : 2 ^ 16 ∣ 2 ^ 128)

theorem simdMla_eval (vd vn vm : BitVec 128) :
    zipSimdLanes true 16 vd (zipSimdLanes true 16 vn vm (fun a b => a * b)) (fun acc p => acc + p) =
      simdMla8h vd vn vm := by
  rw [simdMul_eval, simdAdd_eval]
  apply ext_lane16; intro i; simp

/-! ## 3. `SymStateMatches` Preservation & SP Offset Helpers -/

theorem matches_writeVReg {s0 s : State} {sp ret : BitVec 64} {env : SymEnv} {st : SymState}
    (hm : SymStateMatches s0 sp ret env st s) (rd : BitVec 5) (e : SExpr) :
    SymStateMatches s0 sp ret env { st with vregs := st.vregs.set rd.toNat e }
      (s.writeVReg128 rd (evalSExpr env e)) := by
  refine ⟨hm.hsp, hm.hsp_al, hm.hx19, hm.hunsp, ?_, hm.hx0, hm.hx1, hm.hx2, hm.hx8, hm.hx9, hm.hx20⟩
  intro r
  rw [symVRegs_set_get st.vregs rd.toNat r.toNat rd.isLt r.isLt e]
  by_cases heq : r = rd
  · subst heq; simp [State.readVReg128, State.writeVReg128]
  · have hne : r.toNat ≠ rd.toNat := fun h => heq (BitVec.eq_of_toNat_eq h)
    simp only [hne, ↓reduceIte]
    simpa [State.readVReg128, State.writeVReg128, heq] using hm.hvregs r

theorem matches_orFpsr {s0 s : State} {sp ret : BitVec 64} {env : SymEnv} {st : SymState}
    (hm : SymStateMatches s0 sp ret env st s) (fl : BitVec 32) :
    SymStateMatches s0 sp ret env st (s.orFpsr fl) :=
  ⟨hm.hsp, hm.hsp_al, hm.hx19, hm.hunsp, hm.hvregs, hm.hx0, hm.hx1, hm.hx2, hm.hx8, hm.hx9, hm.hx20⟩

theorem matches_setPC {s0 s : State} {sp ret : BitVec 64} {env : SymEnv} {st : SymState}
    (hm : SymStateMatches s0 sp ret env st s) (pc' : BitVec 64) :
    SymStateMatches s0 sp ret env st (s.setPC pc') :=
  ⟨hm.hsp, hm.hsp_al, hm.hx19, hm.hunsp, hm.hvregs, hm.hx0, hm.hx1, hm.hx2, hm.hx8, hm.hx9, hm.hx20⟩

theorem matches_advancePC {s0 s : State} {sp ret : BitVec 64} {env : SymEnv} {st : SymState}
    (hm : SymStateMatches s0 sp ret env st s) :
    SymStateMatches s0 sp ret env st s.advancePC :=
  ⟨hm.hsp, hm.hsp_al, hm.hx19, hm.hunsp, hm.hvregs, hm.hx0, hm.hx1, hm.hx2, hm.hx8, hm.hx9, hm.hx20⟩

theorem matches_setMem {s0 s : State} {sp ret : BitVec 64} {env : SymEnv} {st : SymState}
    (hm : SymStateMatches s0 sp ret env st s) (m' : Memory) :
    SymStateMatches s0 sp ret env st (s.setMem m') :=
  ⟨hm.hsp, hm.hsp_al, hm.hx19, hm.hunsp, hm.hvregs, hm.hx0, hm.hx1, hm.hx2, hm.hx8, hm.hx9, hm.hx20⟩

theorem matches_getGpr_const {s0 s : State} {sp ret : BitVec 64} {env : SymEnv}
    {st : SymState} (hm : SymStateMatches s0 sp ret env st s) {rn : BitVec 5} {v : BitVec 64}
    (hg : st.gprs.get? rn = some (.const64 v)) :
    s.readReg64 (Reg.fromZRBits rn) = v := by
  unfold SymGprs.get? at hg
  rcases hm with ⟨_, _, _, _, _, hx0, hx1, hx2, hx8, hx9, hx20⟩
  cases h0 : (rn == 0#5)
  · simp only [h0, Bool.false_eq_true, ↓reduceIte] at hg
    cases h1 : (rn == 1#5)
    · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hg
      cases h2 : (rn == 2#5)
      · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hg
        cases h8 : (rn == 8#5)
        · simp only [h8, Bool.false_eq_true, ↓reduceIte] at hg
          cases h9 : (rn == 9#5)
          · simp only [h9, Bool.false_eq_true, ↓reduceIte] at hg
            cases h20 : (rn == 20#5)
            · simp [h20] at hg
            · simp only [h20, ↓reduceIte, Option.some.injEq] at hg
              rw [beq_iff_eq.mp h20]; rw [hg] at hx20; exact hx20
          · simp only [h9, ↓reduceIte, Option.some.injEq] at hg
            rw [beq_iff_eq.mp h9]; rw [hg] at hx9; exact hx9
        · simp only [h8, ↓reduceIte, Option.some.injEq] at hg
          rw [beq_iff_eq.mp h8]; rw [hg] at hx8; exact hx8
      · simp only [h2, ↓reduceIte, Option.some.injEq] at hg
        rw [beq_iff_eq.mp h2]; rw [hg] at hx2; exact hx2
    · simp only [h1, ↓reduceIte, Option.some.injEq] at hg
      rw [beq_iff_eq.mp h1]; rw [hg] at hx1; exact hx1
  · simp only [h0, ↓reduceIte, Option.some.injEq] at hg
    rw [beq_iff_eq.mp h0]; rw [hg] at hx0; exact hx0

theorem matches_setGpr {s0 s : State} {sp ret : BitVec 64} {env : SymEnv} {st : SymState}
    (hm : SymStateMatches s0 sp ret env st s) {rd : BitVec 5} {sg : SymGpr} {g' : SymGprs}
    {val : BitVec 64} (hset : st.gprs.set? rd sg = some g') (hsg : SymGprMatches sp val sg) :
    SymStateMatches s0 sp ret env { st with gprs := g' } (s.writeReg64 (.gpr rd) val) := by
  unfold SymGprs.set? at hset
  cases h0 : (rd == 0#5)
  · simp only [h0, Bool.false_eq_true, ↓reduceIte] at hset
    cases h1 : (rd == 1#5)
    · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hset
      cases h2 : (rd == 2#5)
      · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hset
        cases h8 : (rd == 8#5)
        · simp only [h8, Bool.false_eq_true, ↓reduceIte] at hset
          cases h9 : (rd == 9#5)
          · simp only [h9, Bool.false_eq_true, ↓reduceIte] at hset
            cases h20 : (rd == 20#5)
            · simp [h20] at hset
            · simp only [h20, ↓reduceIte, Option.some.injEq] at hset; subst hset; rw [beq_iff_eq.mp h20]
              exact ⟨hm.hsp, hm.hsp_al, hm.hx19, hm.hunsp, hm.hvregs, hm.hx0, hm.hx1, hm.hx2, hm.hx8, hm.hx9, hsg⟩
          · simp only [h9, ↓reduceIte, Option.some.injEq] at hset; subst hset; rw [beq_iff_eq.mp h9]
            exact ⟨hm.hsp, hm.hsp_al, hm.hx19, hm.hunsp, hm.hvregs, hm.hx0, hm.hx1, hm.hx2, hm.hx8, hsg, hm.hx20⟩
        · simp only [h8, ↓reduceIte, Option.some.injEq] at hset; subst hset; rw [beq_iff_eq.mp h8]
          exact ⟨hm.hsp, hm.hsp_al, hm.hx19, hm.hunsp, hm.hvregs, hm.hx0, hm.hx1, hm.hx2, hsg, hm.hx9, hm.hx20⟩
      · simp only [h2, ↓reduceIte, Option.some.injEq] at hset; subst hset; rw [beq_iff_eq.mp h2]
        exact ⟨hm.hsp, hm.hsp_al, hm.hx19, hm.hunsp, hm.hvregs, hm.hx0, hm.hx1, hsg, hm.hx8, hm.hx9, hm.hx20⟩
    · simp only [h1, ↓reduceIte, Option.some.injEq] at hset; subst hset; rw [beq_iff_eq.mp h1]
      exact ⟨hm.hsp, hm.hsp_al, hm.hx19, hm.hunsp, hm.hvregs, hm.hx0, hsg, hm.hx2, hm.hx8, hm.hx9, hm.hx20⟩
  · simp only [h0, ↓reduceIte, Option.some.injEq] at hset; subst hset; rw [beq_iff_eq.mp h0]
    exact ⟨hm.hsp, hm.hsp_al, hm.hx19, hm.hunsp, hm.hvregs, hsg, hm.hx1, hm.hx2, hm.hx8, hm.hx9, hm.hx20⟩

theorem setPC_self {s : State} {pc : BitVec 64} (h : s.pc = pc) : s.setPC pc = s := by
  cases s; subst h; rfl

theorem sp_spill_off {sp off : BitVec 64} (ho : off.toNat < 208) (hm : off.toNat % 16 = 0) :
    off.toNat / 16 < 13 ∧ sp + BitVec.ofNat 64 (16 * (off.toNat / 16)) = sp + off := by
  refine ⟨by omega, ?_⟩
  have heq : BitVec.ofNat 64 (16 * (off.toNat / 16)) = off := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofNat]; omega
  rw [heq]

theorem sp_spill_off16 {sp off : BitVec 64} (ho : off.toNat + 16 < 208) (hm : off.toNat % 16 = 0) :
    off.toNat / 16 + 1 < 13 ∧ (sp + off) + 16#64 = sp + BitVec.ofNat 64 (16 * (off.toNat / 16 + 1)) := by
  refine ⟨by omega, ?_⟩
  have heq : off + 16#64 = BitVec.ofNat 64 (16 * (off.toNat / 16 + 1)) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [BitVec.add_assoc, heq]

theorem sp_poly_off {sp off : BitVec 64}
    (hlo : 2928 ≤ off.toNat) (hhi : off.toNat < 3440) (hm : (off.toNat - 2928) % 16 = 0) :
    (off.toNat - 2928) / 16 < 32 ∧
      (sp + 2928#64) + BitVec.ofNat 64 (16 * ((off.toNat - 2928) / 16)) = sp + off := by
  refine ⟨by omega, ?_⟩
  have heq : 2928#64 + BitVec.ofNat 64 (16 * ((off.toNat - 2928) / 16)) = off := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [BitVec.add_assoc, heq]

theorem sp_poly_off16 {sp off : BitVec 64}
    (hlo : 2928 ≤ off.toNat) (hhi : off.toNat + 16 < 3440) (hm : (off.toNat - 2928) % 16 = 0) :
    (off.toNat - 2928) / 16 + 1 < 32 ∧
      (sp + off) + 16#64 = (sp + 2928#64) + BitVec.ofNat 64 (16 * ((off.toNat - 2928) / 16 + 1)) := by
  refine ⟨by omega, ?_⟩
  have heq : off + 16#64 = 2928#64 + BitVec.ofNat 64 (16 * ((off.toNat - 2928) / 16 + 1)) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [BitVec.add_assoc, heq, ← BitVec.add_assoc]

theorem evalAdd64_val (x y : BitVec 64) :
    (evalAddSub .W64 .ADD x y none).1 = x + y := by
  simp

theorem writeReg32_zext16 (s : State) (r : Reg) (imm16 : BitVec 16) :
    s.writeReg .W32 r (imm16.zeroExtend 64) = s.writeReg64 r (imm16.zeroExtend 64) := by
  simp [State.writeReg]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4SymBridge
