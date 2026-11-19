/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakAnf -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.BTreeMem -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp

/-!
# `generate_keypair_compressed` (`B05`) — Symbolic Keccak `SepWP` & 24-Round Bridge (`KeccakSymBridge`)

Connects the pure `KState` / `stepKInst` / `runKRange` stepper (`KeccakSymDefs`), the `GF(2)`
ANF decision procedure (`KeccakAnf`), and `TreeMem` (`BTreeMem`) to `Arm64.SepWP` for both
straight-line NEON blocks and all 8 2-way `keccak_f1600` 24-round loops in `Seg2`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymBridge

open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemData01Bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemPlacement)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables
  (keccakRcAt mlkemData01Bytes_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps (step_simdLd1r_2d)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec
  (KeccakState keccakF1600 keccakF1600Round)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round
  (keccakF1600Round_getD keccakF1600Round_size keccakState_eq_of_getD
   keccakRunFrom keccakRunFrom_zero keccakRunFrom_24 keccakRunFrom_step)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (blkPC05)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs
  (BTree KExpr KEnv evalKExpr eval_smartAdd64 eval_smartUsra usraShift?
   KCfg KState KSlot resolveByteOff? resolveMemIdx? readMemWord writeMemWord
   fetchWordTree05 stepKInst runKRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakAnf
  (toAnf? anfBeq keccakSpecRoundExpr anf_eq_keccakRoundLane)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.BTreeMem
  (fetch_blk05_seg2 TreeMem sepLoad64_treeMem sepStore64_treeMem)

/-! ## 1. Pure Bitvector, Register, & `PState` Lemmas -/

theorem setPC_self {s : State} {pc : BitVec 64} (hpc : s.pc = pc) :
    s.setPC pc = s := by
  cases s; cases hpc; rfl

theorem ne31_of_beq_false {r : BitVec 5} (hr : (r == 31#5) = false) :
    r ≠ 31#5 := by
  intro heq; subst heq; simp at hr

theorem lt31_of_beq_false {r : BitVec 5} (hr : (r == 31#5) = false) :
    r.toNat < 31 := by
  have hlt := r.isLt
  have hne : r.toNat ≠ 31 := fun h =>
    ne31_of_beq_false hr (BitVec.eq_of_toNat_eq (by simpa using h))
  omega

theorem fromZRBits_of_beq_false {r : BitVec 5} (hr : (r == 31#5) = false) :
    Reg.fromZRBits r = .gpr r := by
  simp [Reg.fromZRBits, ne31_of_beq_false hr]

theorem condHolds_HI_255 (x : BitVec 64) :
    ConditionHolds .HI (AddWithCarry64 x (~~~255#64) true).2 = decide (255#64 < x) := by
  unfold ConditionHolds AddWithCarry64
  simp only [↓reduceIte]
  have hnot : (~~~(255#64 : BitVec 64)).toNat = 18446744073709551360 := by decide
  have hx := x.isLt
  have hsum : ((1#65 : BitVec 65) + ((~~~(255#64 : BitVec 64)).zeroExtend 65 + x.zeroExtend 65)).toNat =
      18446744073709551361 + x.toNat := by
    simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat,
      BitVec.toNat_setWidth, hnot]
    omega
  have hc : ((1#65 : BitVec 65) + ((~~~(255#64 : BitVec 64)).zeroExtend 65 + x.zeroExtend 65)).msb =
      decide (255 ≤ x.toNat) := by
    rw [BitVec.msb_eq_toNat, hsum]
    by_cases h : 255 ≤ x.toNat <;> simp [h] <;> omega
  have hz : (((1#65 : BitVec 65) + ((~~~(255#64 : BitVec 64)).zeroExtend 65 + x.zeroExtend 65)).truncate 64 == 0#64) =
      decide (x.toNat = 255) := by
    have htr : (((1#65 : BitVec 65) + ((~~~(255#64 : BitVec 64)).zeroExtend 65 + x.zeroExtend 65)).truncate 64).toNat =
        (18446744073709551361 + x.toNat) % 18446744073709551616 := by
      rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, hsum]
    by_cases he : x.toNat = 255
    · simp only [he, decide_true, beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [htr, show (0#64 : BitVec 64).toNat = 0 from rfl]; omega
    · simp only [he, decide_false, beq_eq_false_iff_ne]
      intro h0
      have h0n := congrArg BitVec.toNat h0
      rw [htr, show (0#64 : BitVec 64).toNat = 0 from rfl] at h0n
      omega
  rw [hc, hz, show decide (255#64 < x) = decide (255 < x.toNat) from rfl]
  by_cases h1 : 255 < x.toNat
  · have h2 : 255 ≤ x.toNat := by omega
    have h3 : x.toNat ≠ 255 := by omega
    simp [h1, h2, h3]
  · by_cases h2 : x.toNat = 255
    · simp [h2]
    · have h3 : ¬(255 ≤ x.toNat) := by omega
      simp [h1, h2, h3]

theorem condHolds_NE_sub (x y : BitVec 64) :
    ConditionHolds .NE (AddWithCarry64 x (~~~y) true).2 = decide (x ≠ y) := by
  unfold ConditionHolds AddWithCarry64
  simp only [↓reduceIte]
  have hx := x.isLt
  have hy := y.isLt
  have hnot : (~~~y).toNat = 18446744073709551615 - y.toNat := by
    rw [BitVec.toNat_not]
  have htr : (((1#65 : BitVec 65) + ((~~~y).zeroExtend 65 + x.zeroExtend 65)).truncate 64).toNat =
      (18446744073709551616 + x.toNat - y.toNat) % 18446744073709551616 := by
    rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
    simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat,
      BitVec.toNat_setWidth, hnot]
    omega
  by_cases hxy : x = y
  · subst hxy
    have h0 : ((1#65 : BitVec 65) + ((~~~x).zeroExtend 65 + x.zeroExtend 65)).truncate 64 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [htr, show (0#64 : BitVec 64).toNat = 0 from rfl]; omega
    simp [h0]
  · have hne_nat : x.toNat ≠ y.toNat := fun h => hxy (BitVec.eq_of_toNat_eq h)
    have hnz : (((1#65 : BitVec 65) + ((~~~y).zeroExtend 65 + x.zeroExtend 65)).truncate 64 == 0#64) = false := by
      rw [beq_eq_false_iff_ne]
      intro h0
      have h0n := congrArg BitVec.toNat h0
      rw [htr, show (0#64 : BitVec 64).toNat = 0 from rfl] at h0n
      omega
    simp [hxy, hnz]

/-! ## 2. `KStateMatches`, `KSpatial`, & `resolveMemIdx?` Routing -/

@[expose] def KCfgWf (cfg : KCfg) : Prop :=
  cfg.offA % 8 = 0 ∧ cfg.lenA ≤ 512 ∧ cfg.offB % 8 = 0 ∧ cfg.lenB ≤ 512

structure KStateMatches (env : KEnv) (st : KState) (s : State) : Prop where
  hsp     : s.sp = env.sp
  hsp_al  : s.spAligned = true
  hvregs  : ∀ r : BitVec 5,
    s.readVReg128 r = evalKExpr env (st.vregs.get r.toNat).2 ++ evalKExpr env (st.vregs.get r.toNat).1
  hgprs   : ∀ r : BitVec 5, r.toNat < 31 →
    s.readReg64 (.gpr r) = evalKExpr env (st.gprs.get r.toNat)
  hpstate : ∀ lhs rhs : KExpr, st.pstate = some (lhs, rhs) →
    s.pstate = (AddWithCarry64 (evalKExpr env lhs) (~~~(evalKExpr env rhs)) true).2

@[expose] def KSpatial (cfg : KCfg) (env : KEnv) (st : KState) (F : SepProp) : SepProp :=
  (env.rcBase ↦ᵣ mlkemData01Bytes) ∗
    TreeMem (env.sp + BitVec.ofNat 64 cfg.offA) cfg.lenA (st.memA.map (evalKExpr env)) ∗
    TreeMem (env.sp + BitVec.ofNat 64 cfg.offB) cfg.lenB (st.memB.map (evalKExpr env)) ∗ F

theorem sepLoad64_rcBase {cfg : KCfg} {env : KEnv} {st : KState} {F : SepProp}
    {ea : BitVec 64} {k : Nat} (hk : k < 24)
    (hea : env.rcBase + BitVec.ofNat 64 (8 * k) = ea) :
    SepLoad64 ea (KSpatial cfg env st F) (keccakRcAt k) :=
  SepLoad64.congr_val
    (SepLoad64.of_pointsToBytesRO rfl (by rw [mlkemData01Bytes_length]; omega) hea)
    (ByteSlice.pack64_eq_readLE_8 mlkemData01Bytes (8 * k))

theorem matches_writeVReg {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) (rd : BitVec 5) (p : KExpr × KExpr)
    {val : BitVec 128} (hval : val = evalKExpr env p.2 ++ evalKExpr env p.1) :
    KStateMatches env { st with vregs := st.vregs.set rd.toNat p } (s.writeVReg128 rd val) := by
  refine ⟨hm.hsp, hm.hsp_al, ?_, hm.hgprs, hm.hpstate⟩
  intro r
  rw [BTree.get_set st.vregs rd.toNat p (by have := rd.isLt; omega) r.toNat (by have := r.isLt; omega)]
  by_cases h : r.toNat = rd.toNat
  · have hrd : r = rd := BitVec.eq_of_toNat_eq h
    subst hrd; simp [hval]
  · have hrd : r ≠ rd := fun heq => h (congrArg BitVec.toNat heq)
    simp [h, hrd, hm.hvregs r]

theorem matches_writeGpr {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) {rd : BitVec 5} (hrd : rd.toNat < 31)
    (e : KExpr) {val : BitVec 64} (hval : val = evalKExpr env e) :
    KStateMatches env { st with gprs := st.gprs.set rd.toNat e } (s.writeReg64 (.gpr rd) val) := by
  refine ⟨hm.hsp, hm.hsp_al, hm.hvregs, ?_, hm.hpstate⟩
  intro r hr
  rw [BTree.get_set st.gprs rd.toNat e (by omega) r.toNat (by omega)]
  by_cases h : r.toNat = rd.toNat
  · have heq : r = rd := BitVec.eq_of_toNat_eq h
    subst heq
    have hr31 : r ≠ 31#5 := fun he => by subst he; simp at hr
    simp [hr31, hval]
  · have hne : Reg.gpr r ≠ Reg.gpr rd := fun heq => by cases heq; exact h rfl
    rw [State.readReg64_writeReg64_ne _ _ _ _ hne]
    simp [h, hm.hgprs r hr]

theorem matches_setPState {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) (lhs rhs : KExpr) {pst : PState}
    (hpst : pst = (AddWithCarry64 (evalKExpr env lhs) (~~~(evalKExpr env rhs)) true).2) :
    KStateMatches env { st with pstate := some (lhs, rhs) } (s.setPState pst) := by
  refine ⟨hm.hsp, hm.hsp_al, hm.hvregs, hm.hgprs, ?_⟩
  intro l r h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩
  exact hpst

theorem matches_orFpsr {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) (fl : BitVec 32) :
    KStateMatches env st (s.orFpsr fl) :=
  ⟨hm.hsp, hm.hsp_al, hm.hvregs, hm.hgprs, hm.hpstate⟩

theorem matches_setPC {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) (pc' : BitVec 64) :
    KStateMatches env st (s.setPC pc') :=
  ⟨hm.hsp, hm.hsp_al, hm.hvregs, hm.hgprs, hm.hpstate⟩

theorem matches_advancePC {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) :
    KStateMatches env st s.advancePC :=
  ⟨hm.hsp, hm.hsp_al, hm.hvregs, hm.hgprs, hm.hpstate⟩

theorem matches_setMem {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) (m' : Memory) :
    KStateMatches env st (s.setMem m') :=
  ⟨hm.hsp, hm.hsp_al, hm.hvregs, hm.hgprs, hm.hpstate⟩

theorem matches_writeMemWord {env : KEnv} {st : KState} {s : State}
    (hm : KStateMatches env st s) (inB : Bool) (idx : Nat) (val : KExpr) :
    KStateMatches env (writeMemWord st inB idx val) s := by
  unfold writeMemWord
  cases inB <;> exact ⟨hm.hsp, hm.hsp_al, hm.hvregs, hm.hgprs, hm.hpstate⟩

private theorem resolveByteOff_ok {env : KEnv} {st : KState} {s : State}
    {addr : AddrMode} {byteOff : Nat}
    (hm : KStateMatches env st s) (hbo : resolveByteOff? st addr = some byteOff) :
    checkAddrSPAligned s addr = true ∧
      evalAddrMode s addr = (env.sp + BitVec.ofNat 64 byteOff, none) := by
  unfold resolveByteOff? at hbo
  cases addr with
  | Offset base off64 | UnscaledOffset base off64 =>
    dsimp only at hbo
    cases base with
    | sp =>
      dsimp only at hbo
      split at hbo <;> [skip; contradiction]
      next hc =>
        simp only [Option.some.injEq] at hbo; subst hbo
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        refine ⟨hm.hsp_al, ?_⟩
        simp [evalAddrMode, State.readReg64, hm.hsp, ← hc.2]
    | gpr r =>
      dsimp only at hbo
      by_cases hr31 : (r == 31#5) = true
      · simp [hr31] at hbo
      · have hrF : (r == 31#5) = false := Bool.eq_false_iff.mpr hr31
        simp only [hrF, Bool.false_eq_true, ↓reduceIte] at hbo
        cases hg : st.gprs.get r.toNat with
        | spAdd bOff =>
          simp only [hg] at hbo
          split at hbo <;> [skip; contradiction]
          next hc =>
            simp only [Option.some.injEq] at hbo; subst hbo
            simp only [Bool.and_eq_true, beq_iff_eq] at hc
            have hlt : r.toNat < 31 := lt31_of_beq_false hrF
            have hread : s.readReg64 (.gpr r) = env.sp + bOff := by
              rw [hm.hgprs r hlt, hg]; rfl
            refine ⟨rfl, ?_⟩
            simp only [evalAddrMode, hread, BitVec.add_assoc]
            exact Prod.ext (congrArg (env.sp + ·) hc.2) rfl
        | _ => simp [hg] at hbo
    | xzr => simp at hbo
  | _ => simp at hbo

theorem resolveMemIdx_bounds {cfg : KCfg} {env : KEnv} {st : KState} {s : State}
    {addr : AddrMode} {words : Nat} {inB : Bool} {idx : Nat}
    (hcfg : KCfgWf cfg) (hm : KStateMatches env st s)
    (hmi : resolveMemIdx? cfg st addr words = some (inB, idx)) :
    ∃ byteOff : Nat,
      checkAddrSPAligned s addr = true ∧
      evalAddrMode s addr = (env.sp + BitVec.ofNat 64 byteOff, none) ∧
      (if inB then cfg.offB else cfg.offA) + 8 * idx = byteOff ∧
      idx + words ≤ (if inB then cfg.lenB else cfg.lenA) := by
  unfold resolveMemIdx? at hmi
  cases hbo : resolveByteOff? st addr with
  | none => simp [hbo] at hmi
  | some byteOff =>
    simp only [hbo] at hmi
    rcases resolveByteOff_ok hm hbo with ⟨hsp, haddr⟩
    rcases hcfg with ⟨hoA, hlA, hoB, hlB⟩
    by_cases hmod : (!(Nat.beq (byteOff % 8) 0)) = true
    · simp [hmod] at hmi
    · have hmod8 : byteOff % 8 = 0 := by
        cases hm8 : Nat.beq (byteOff % 8) 0
        · simp [hm8] at hmod
        · exact Nat.eq_of_beq_eq_true hm8
      have hmodF : (!(Nat.beq (byteOff % 8) 0)) = false := Bool.eq_false_iff.mpr hmod
      simp only [hmodF, Bool.false_eq_true, ↓reduceIte] at hmi
      split at hmi
      · next hcA =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hmi
          rcases hmi with ⟨rfl, rfl⟩
          simp only [Bool.and_eq_true, Nat.ble_eq] at hcA
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact ⟨byteOff, hsp, haddr, by omega, by omega⟩
      · split at hmi
        · next _ hcB =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hmi
            rcases hmi with ⟨rfl, rfl⟩
            simp only [Bool.and_eq_true, Nat.ble_eq] at hcB
            simp only [↓reduceIte]
            exact ⟨byteOff, hsp, haddr, by omega, by omega⟩
        · contradiction

theorem sepLoad64_kmem {cfg : KCfg} {env : KEnv} {F : SepProp}
    {inB : Bool} {idx words byteOff : Nat} (st : KState)
    (hcfg : KCfgWf cfg)
    (hoff : (if inB then cfg.offB else cfg.offA) + 8 * idx = byteOff)
    (hbnd : idx + words ≤ (if inB then cfg.lenB else cfg.lenA))
    {j : Nat} (hj : j < words) {ea : BitVec 64}
    (hea : env.sp + BitVec.ofNat 64 byteOff + BitVec.ofNat 64 (8 * j) = ea) :
    SepLoad64 ea (KSpatial cfg env st F) (evalKExpr env (readMemWord st inB (idx + j))) := by
  rcases hcfg with ⟨_, hlA, _, hlB⟩
  cases inB with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hoff hbnd
    have hP : KSpatial cfg env st F =
        TreeMem (env.sp + BitVec.ofNat 64 cfg.offA) cfg.lenA (st.memA.map (evalKExpr env)) ∗
          ((env.rcBase ↦ᵣ mlkemData01Bytes) ∗
            TreeMem (env.sp + BitVec.ofNat 64 cfg.offB) cfg.lenB (st.memB.map (evalKExpr env)) ∗ F) := by
      unfold KSpatial
      rw [← sepConj_assoc, sepConj_comm (env.rcBase ↦ᵣ mlkemData01Bytes), sepConj_assoc]
    have ha : (env.sp + BitVec.ofNat 64 cfg.offA) + BitVec.ofNat 64 (8 * (idx + j)) = ea := by
      rw [← hea, BitVec.add_assoc, BitVec.add_assoc]; congr 1
      rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]; congr 1; omega
    exact SepLoad64.congr_val
      (sepLoad64_treeMem (idx := idx + j) (by omega) hlA hP ha)
      (by simp [readMemWord, BTree.get_map])
  | true =>
    simp only [↓reduceIte] at hoff hbnd
    have hP : KSpatial cfg env st F =
        TreeMem (env.sp + BitVec.ofNat 64 cfg.offB) cfg.lenB (st.memB.map (evalKExpr env)) ∗
          ((env.rcBase ↦ᵣ mlkemData01Bytes) ∗
            TreeMem (env.sp + BitVec.ofNat 64 cfg.offA) cfg.lenA (st.memA.map (evalKExpr env)) ∗ F) := by
      unfold KSpatial
      rw [← sepConj_assoc (TreeMem (env.sp + BitVec.ofNat 64 cfg.offA) _ _),
          sepConj_comm (TreeMem (env.sp + BitVec.ofNat 64 cfg.offA) _ _),
          sepConj_assoc (TreeMem (env.sp + BitVec.ofNat 64 cfg.offB) _ _),
          ← sepConj_assoc (env.rcBase ↦ᵣ mlkemData01Bytes),
          sepConj_comm (env.rcBase ↦ᵣ mlkemData01Bytes),
          sepConj_assoc]
    have ha : (env.sp + BitVec.ofNat 64 cfg.offB) + BitVec.ofNat 64 (8 * (idx + j)) = ea := by
      rw [← hea, BitVec.add_assoc, BitVec.add_assoc]; congr 1
      rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]; congr 1; omega
    exact SepLoad64.congr_val
      (sepLoad64_treeMem (idx := idx + j) (by omega) hlB hP ha)
      (by simp [readMemWord, BTree.get_map])

theorem sepStore64_kmem {cfg : KCfg} {env : KEnv} {F : SepProp}
    {inB : Bool} {idx words byteOff : Nat} (st : KState) (val : KExpr)
    (hcfg : KCfgWf cfg)
    (hoff : (if inB then cfg.offB else cfg.offA) + 8 * idx = byteOff)
    (hbnd : idx + words ≤ (if inB then cfg.lenB else cfg.lenA))
    {j : Nat} (hj : j < words) {ea : BitVec 64}
    (hea : env.sp + BitVec.ofNat 64 byteOff + BitVec.ofNat 64 (8 * j) = ea) :
    SepStore64 ea (evalKExpr env val)
      (KSpatial cfg env st F)
      (KSpatial cfg env (writeMemWord st inB (idx + j) val) F) := by
  rcases hcfg with ⟨_, hlA, _, hlB⟩
  cases inB with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hoff hbnd
    have hP : KSpatial cfg env st F =
        TreeMem (env.sp + BitVec.ofNat 64 cfg.offA) cfg.lenA (st.memA.map (evalKExpr env)) ∗
          ((env.rcBase ↦ᵣ mlkemData01Bytes) ∗
            TreeMem (env.sp + BitVec.ofNat 64 cfg.offB) cfg.lenB (st.memB.map (evalKExpr env)) ∗ F) := by
      unfold KSpatial
      rw [← sepConj_assoc, sepConj_comm (env.rcBase ↦ᵣ mlkemData01Bytes), sepConj_assoc]
    have hP' : KSpatial cfg env (writeMemWord st false (idx + j) val) F =
        TreeMem (env.sp + BitVec.ofNat 64 cfg.offA) cfg.lenA
          ((st.memA.map (evalKExpr env)).set (idx + j) (evalKExpr env val)) ∗
          ((env.rcBase ↦ᵣ mlkemData01Bytes) ∗
            TreeMem (env.sp + BitVec.ofNat 64 cfg.offB) cfg.lenB (st.memB.map (evalKExpr env)) ∗ F) := by
      unfold KSpatial writeMemWord
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [BTree.map_set, ← sepConj_assoc, sepConj_comm (env.rcBase ↦ᵣ mlkemData01Bytes), sepConj_assoc]
    have ha : (env.sp + BitVec.ofNat 64 cfg.offA) + BitVec.ofNat 64 (8 * (idx + j)) = ea := by
      rw [← hea, BitVec.add_assoc, BitVec.add_assoc]; congr 1
      rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]; congr 1; omega
    exact sepStore64_treeMem (idx := idx + j) (by omega) hlA hP hP' ha
  | true =>
    simp only [↓reduceIte] at hoff hbnd
    have hP : KSpatial cfg env st F =
        TreeMem (env.sp + BitVec.ofNat 64 cfg.offB) cfg.lenB (st.memB.map (evalKExpr env)) ∗
          ((env.rcBase ↦ᵣ mlkemData01Bytes) ∗
            TreeMem (env.sp + BitVec.ofNat 64 cfg.offA) cfg.lenA (st.memA.map (evalKExpr env)) ∗ F) := by
      unfold KSpatial
      rw [← sepConj_assoc (TreeMem (env.sp + BitVec.ofNat 64 cfg.offA) _ _),
          sepConj_comm (TreeMem (env.sp + BitVec.ofNat 64 cfg.offA) _ _),
          sepConj_assoc (TreeMem (env.sp + BitVec.ofNat 64 cfg.offB) _ _),
          ← sepConj_assoc (env.rcBase ↦ᵣ mlkemData01Bytes),
          sepConj_comm (env.rcBase ↦ᵣ mlkemData01Bytes),
          sepConj_assoc]
    have hP' : KSpatial cfg env (writeMemWord st true (idx + j) val) F =
        TreeMem (env.sp + BitVec.ofNat 64 cfg.offB) cfg.lenB
          ((st.memB.map (evalKExpr env)).set (idx + j) (evalKExpr env val)) ∗
          ((env.rcBase ↦ᵣ mlkemData01Bytes) ∗
            TreeMem (env.sp + BitVec.ofNat 64 cfg.offA) cfg.lenA (st.memA.map (evalKExpr env)) ∗ F) := by
      unfold KSpatial writeMemWord
      simp only [↓reduceIte]
      rw [BTree.map_set,
          ← sepConj_assoc (TreeMem (env.sp + BitVec.ofNat 64 cfg.offA) _ _),
          sepConj_comm (TreeMem (env.sp + BitVec.ofNat 64 cfg.offA) _ _),
          sepConj_assoc (TreeMem (env.sp + BitVec.ofNat 64 cfg.offB) _ _),
          ← sepConj_assoc (env.rcBase ↦ᵣ mlkemData01Bytes),
          sepConj_comm (env.rcBase ↦ᵣ mlkemData01Bytes),
          sepConj_assoc]
    have ha : (env.sp + BitVec.ofNat 64 cfg.offB) + BitVec.ofNat 64 (8 * (idx + j)) = ea := by
      rw [← hea, BitVec.add_assoc, BitVec.add_assoc]; congr 1
      rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]; congr 1; omega
    exact sepStore64_treeMem (idx := idx + j) (by omega) hlB hP hP' ha

/-! ## 3. Pure SIMD & GPR Evaluation Lemmas for `stepKInst` -/

theorem bit_append (d1 d0 n1 n0 m1 m0 : BitVec 64) :
    (d1 ++ d0) ^^^ (((d1 ++ d0) ^^^ (n1 ++ n0)) &&& (m1 ++ m0)) =
      (((n1 ^^^ d1) &&& m1) ^^^ d1) ++ (((n0 ^^^ d0) &&& m0) ^^^ d0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_append]
  split
  · cases d0.getLsbD i <;> cases n0.getLsbD i <;> cases m0.getLsbD i <;> rfl
  · cases d1.getLsbD (i - 64) <;> cases n1.getLsbD (i - 64) <;> cases m1.getLsbD (i - 64) <;> rfl

theorem bsl_append (d1 d0 n1 n0 m1 m0 : BitVec 64) :
    (((n1 ++ n0) ^^^ (m1 ++ m0)) &&& (d1 ++ d0)) ^^^ (m1 ++ m0) =
      (((n1 ^^^ m1) &&& d1) ^^^ m1) ++ (((n0 ^^^ m0) &&& d0) ^^^ m0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_append]
  split <;> rfl

theorem ins_b0_append (d1 d0 r : BitVec 64) :
    ((d1 ++ d0) &&& ~~~(((1#128 <<< 8) - 1#128) <<< 0)) |||
        (((r.zeroExtend 128) &&& ((1#128 <<< 8) - 1#128)) <<< 0) =
      d1 ++ ((d0 &&& 0xffffffffffffff00#64) ||| (r &&& 0xff#64)) := by
  bv_bits

theorem dupScalar_d1_append (n1 n0 : BitVec 64) :
    evalSimdDupScalar 0x18#5 (n1 ++ n0) = 0#64 ++ n1 := by
  unfold evalSimdDupScalar getSimdLane
  simp only [show (0x18#5 : BitVec 5).getLsbD 0 = false from rfl,
    show (0x18#5 : BitVec 5).getLsbD 1 = false from rfl,
    show (0x18#5 : BitVec 5).getLsbD 2 = false from rfl,
    show (0x18#5 : BitVec 5).toNat >>> 4 = 1 from rfl, Bool.false_eq_true, ↓reduceIte]
  bv_bits

theorem umov_d1_append (n1 n0 : BitVec 64) :
    (getSimdLane (n1 ++ n0) 64 1).truncate 64 = n1 := by
  unfold getSimdLane
  bv_bits

theorem fmov_d0_append (s : State) (rn : BitVec 5) (n1 n0 : BitVec 64)
    (h : s.readVReg128 rn = n1 ++ n0) :
    s.readVReg64 rn = n0 := by
  unfold State.readVReg64
  rw [h]
  bv_bits

theorem immhb_eq_mul_add (immh : BitVec 4) (immb : BitVec 3) :
    (immh ++ immb).toNat = immh.toNat * 8 + immb.toNat := by
  revert immh immb; decide

theorem shl_2d_eval (immh : BitVec 4) (immb : BitVec 3) (hge : ¬(immh.toNat < 8))
    (n1 n0 : BitVec 64) :
    let immhb := (immh ++ immb).toNat
    let esize := if immhb >= 64 then 64 else if immhb >= 32 then 32 else if immhb >= 16 then 16 else 8
    mapSimdLanes true esize (n1 ++ n0) (fun lane => lane <<< (immhb - esize)) =
      (n1 <<< (immh.toNat * 8 + immb.toNat - 64)) ++
        (n0 <<< (immh.toNat * 8 + immb.toNat - 64)) := by
  have hb := immhb_eq_mul_add immh immb
  have hge64 : immh.toNat * 8 + immb.toNat ≥ 64 := by omega
  dsimp only
  simp only [hb, hge64, ↓reduceIte, mapSimdLanes_true_64, mapLanes, laneMask_64,
    Nat.zero_mul, Nat.one_mul,
    LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp.shl_2d_lanes,
    LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp.extractLsb_hi_append,
    LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp.extractLsb_lo_append]

theorem usra_2d_eval {immh : BitVec 4} {immb : BitVec 3} {r : Nat}
    (hr : usraShift? immh immb = some r) (d1 d0 n1 n0 : BitVec 64) :
    immh ≠ 0#4 ∧
      evalSimdImmShiftNonZeroExt true true immh immb 0x02#5 (d1 ++ d0) (n1 ++ n0) =
        .ok ((d1 + (n1 >>> r)) ++ (d0 + (n0 >>> r))) := by
  unfold usraShift? at hr
  split at hr <;> try contradiction
  all_goals
    simp only [Option.some.injEq] at hr
    subst hr
    exact ⟨by decide, by simp⟩

theorem addSubImm_delta_eq (imm12 : BitVec 12) (shift12 : Bool) :
    (if shift12 then (imm12.zeroExtend 64) <<< 12 else imm12.zeroExtend 64) =
      BitVec.ofNat 64 (if shift12 then imm12.toNat <<< 12 else imm12.toNat) := by
  have hlt := imm12.isLt
  cases shift12
  · apply BitVec.eq_of_toNat_eq
    simp only [Bool.false_eq_true, ↓reduceIte, BitVec.zeroExtend_eq_setWidth,
      BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  · apply BitVec.eq_of_toNat_eq
    simp only [↓reduceIte, BitVec.toNat_shiftLeft, BitVec.zeroExtend_eq_setWidth,
      BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have hm : imm12.toNat % 18446744073709551616 = imm12.toNat := by omega
    rw [hm]

theorem movz_w32_eq_writeReg64 (s : State) (rd : BitVec 5) (imm16 : BitVec 16) :
    s.writeReg .W32 (.gpr rd) ((imm16.zeroExtend 64) <<< 0) =
      s.writeReg64 (.gpr rd) (imm16.zeroExtend 64) := by
  simp only [State.writeReg]
  congr 1
  bv_bits

theorem writeReg_w32_zero_eq_writeReg64 (s : State) (rd : BitVec 5) :
    s.writeReg .W32 (.gpr rd) 0#64 = s.writeReg64 (.gpr rd) 0#64 :=
  rfl

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymBridge
