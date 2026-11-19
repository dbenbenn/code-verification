/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.BTreeMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakLoop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakProg -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Base -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Init -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Clamp -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymStep

/-!
# `generate_keypair_compressed` (`B05`): `Seg2` `init3` clamp and 6-permutation spec

Proves `seg2_row_clamp_init3` (`+0x2290 → +0x3048 / +0x2300`), `SitePreserved` transfers, and
`specEnv_stepsInit_vars` (`A1..A3, B1..B3` `rowPermState` identification).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2RowInit

open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (KeccakState keccakF1600)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LaneMem (
  MultiLaneSampled MultiLaneSlots)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.SiteStep (
  RejSiteConfig SitePreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework (
  MultiLaneRawXofInv allLanesDone)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (blkPC05)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymDefs (
  BTree KCfg KEnv KExpr KSlot KState evalKExpr runKRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.BTreeMem (TreeMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymBridge (
  KSpatial matches_setPC)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakSymStep (
  sepWP_of_runKRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakLoop (
  readSlot slotHolds)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.KeccakProg (
  slotsA1 slotsA2 slotsA3 slotsB1 slotsB2 slotsB3 stepKLoopSym)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Base (
  KProgStep evalExprList25 eval_checked_pstate extendLoopVars preAbsorbLane preAbsorbState
  preAbsorbState_getD preAbsorbState_size rhoW rowPermState rowPermState_succ rowPermState_zero
  rowSeeds specEnvSteps)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Init (
  Seg2ConstWordsInv Seg2LoopState Seg2RegInv Seg2RowDone cfgClamp cfgClamp_wf cfgInit
  condCC_256_of_le271 condCS_256_of_le271 condHI_255_of_le271 keccakRc_intro
  multiLaneSampled3_eq_treeMem raw_sampled_le271 rowPermState_size slotHoldsLo
  step_bCond_seg2 step_b_seg2)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2Clamp (
  eq_some_getD finish_clamp_branch mkSegEnv mkSegState mkSegState_matches
  preClamp01Slots preClamp2Slots with_frozen_env)

attribute [local irreducible] keccakF1600 blkPC05

/-! ## 1. `+0x2290 → +0x3048 / +0x2300` Clamp Dispatch & `SitePreserved` Transfers -/

@[expose] def stInitClamp0 : KState := mkSegState cfgClamp true preClamp01Slots preClamp2Slots
@[expose] def stInitC1 : KState := (runKRange cfgClamp 2212 17 stInitClamp0).getD stInitClamp0
@[expose] def stInitCLo : KState := (runKRange cfgClamp 2235 2 stInitC1).getD stInitC1
@[expose] def stInitCHi : KState := (runKRange cfgClamp 2230 3 stInitC1).getD stInitC1
@[expose] def stInitCEnd : KState := (runKRange cfgClamp 2238 1 stInitCHi).getD stInitCHi

private theorem cert_initC1 : runKRange cfgClamp 2212 17 stInitClamp0 = some stInitC1 :=
  eq_some_getD (o := runKRange cfgClamp 2212 17 stInitClamp0) stInitClamp0 (by decide +kernel)
private theorem cert_initCLo : runKRange cfgClamp 2235 2 stInitC1 = some stInitCLo :=
  eq_some_getD (o := runKRange cfgClamp 2235 2 stInitC1) stInitC1 (by decide +kernel)
private theorem cert_initCHi : runKRange cfgClamp 2230 3 stInitC1 = some stInitCHi :=
  eq_some_getD (o := runKRange cfgClamp 2230 3 stInitC1) stInitC1 (by decide +kernel)
private theorem cert_initCEnd : runKRange cfgClamp 2238 1 stInitCHi = some stInitCEnd :=
  eq_some_getD (o := runKRange cfgClamp 2238 1 stInitCHi) stInitCHi (by decide +kernel)
@[expose] def checkPStateEq (st : KState) (eL eR : KExpr) : Bool :=
  match st.pstate with
  | some (l, r) => l.beq eL && r.beq eR
  | none => false

private theorem cert_pstateC1 : checkPStateEq stInitC1 (.var 902) (.const64 256#64) = true := by decide +kernel
private theorem cert_pstateCHi : checkPStateEq stInitCHi (.var 901) (.const64 256#64) = true := by decide +kernel
private theorem cert_pstateCEnd : checkPStateEq stInitCEnd (.var 900) (.const64 255#64) = true := by decide +kernel
private theorem cert_chkCLo : Seg2Clamp.checkClampEnd stInitCLo (!false) = true := by decide +kernel
private theorem cert_chkCHi : Seg2Clamp.checkClampEnd stInitCHi (!false) = true := by decide +kernel
private theorem cert_chkCEndT : Seg2Clamp.checkClampEnd stInitCEnd (!true) = true := by decide +kernel
private theorem cert_chkCEndF : Seg2Clamp.checkClampEnd stInitCEnd (!false) = true := by decide +kernel

attribute [local irreducible] stInitC1 stInitCLo stInitCHi stInitCEnd

theorem status_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).status = s.status := rfl

theorem pc_of_eq {b x y : BitVec 64} {s : State} (hpc : s.pc = b + x)
    (h : (x == y) = true) : s.pc = b + y := by
  rw [hpc, eq_of_beq h]

theorem pc_add_eq {b : BitVec 64} {w1 w2 : Nat} {s : State}
    (hpc : s.pc = b + BitVec.ofNat 64 (4 * w1))
    (h : (4#64 * BitVec.ofNat 64 w1 == 4#64 * BitVec.ofNat 64 w2) = true) :
    s.pc = b + BitVec.ofNat 64 (4 * w2) := by
  rw [hpc, BitVec.ofNat_mul 4 w1, BitVec.ofNat_mul 4 w2, eq_of_beq h]

theorem setPC_disp_eq (s : State) (b : BitVec 64) (w1 : Nat) (disp y : BitVec 64)
    (h : (4#64 * BitVec.ofNat 64 w1 + disp == y) = true) :
    (s.setPC (b + BitVec.ofNat 64 (4 * w1) + disp)).pc = b + y := by
  change b + BitVec.ofNat 64 (4 * w1) + disp = b + y
  rw [BitVec.add_assoc, BitVec.ofNat_mul 4 w1, eq_of_beq h]

theorem setPC_disp_w_eq (s : State) (b : BitVec 64) (w1 : Nat) (disp : BitVec 64) (w2 : Nat)
    (h : (4#64 * BitVec.ofNat 64 w1 + disp == 4#64 * BitVec.ofNat 64 w2) = true) :
    (s.setPC (b + BitVec.ofNat 64 (4 * w1) + disp)).pc = b + BitVec.ofNat 64 (4 * w2) := by
  rw [BitVec.ofNat_mul 4 w2]; exact setPC_disp_eq s b w1 disp _ h

theorem setPC_fall_eq (s : State) (b : BitVec 64) (w1 : Nat) (y : BitVec 64)
    (h : (4#64 * (BitVec.ofNat 64 w1 + 1#64) == y) = true) :
    (s.setPC (b + BitVec.ofNat 64 (4 * (w1 + 1)))).pc = b + y := by
  change b + BitVec.ofNat 64 (4 * (w1 + 1)) = b + y
  rw [BitVec.ofNat_mul 4 (w1 + 1), BitVec.ofNat_add w1 1, eq_of_beq h]

theorem setPC_fall_w_eq (s : State) (b : BitVec 64) (w1 w2 : Nat)
    (h : (4#64 * (BitVec.ofNat 64 w1 + 1#64) == 4#64 * BitVec.ofNat 64 w2) = true) :
    (s.setPC (b + BitVec.ofNat 64 (4 * (w1 + 1)))).pc = b + BitVec.ofNat 64 (4 * w2) := by
  rw [BitVec.ofNat_mul 4 w2]; exact setPC_fall_eq s b w1 _ h

theorem seg2_row_clamp_init3 [MlKemPlacement] {b sp fpVal : BitVec 64} {rho : List (BitVec 8)}
    {row : Nat} {F : SepProp} {tA : BTree (BitVec 64) 9}
    {sampled : Nat → Nat} {hws : Nat → List (BitVec 16)} {s : State}
    (hpc : s.pc = b + 0x2290#64) (hrun : s.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hreg : Seg2RegInv sp fpVal s) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (row + 1))
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 row)
    (htA : Seg2ConstWordsInv sp rho tA)
    (hraw : MultiLaneRawXofInv 3 (rowSeeds rho row) 0 sampled hws)
    (hs01 : ∀ idx, idx < 25 → slotHolds cfgClamp s tA (preClamp01Slots.getD idx (.vreg 0))
      ((rowPermState rho row 0 2).getD idx 0#64) ((rowPermState rho row 1 2).getD idx 0#64))
    (hs2 : ∀ idx, idx < 25 → slotHoldsLo cfgClamp s tA (preClamp2Slots.getD idx (.vreg 0))
      ((rowPermState rho row 2 2).getD idx 0#64)) :
    SepWP (blkPC05.rebase b (fun _ => none))
      (if allLanesDone 3 (rowSeeds rho row) 0 then b + 0x3048#64 else b + 0x2300#64) s
      (TreeMem (sp + 64#64) 268 tA ∗ memRegion (sp + 9984#64) 1512 ∗
        MultiLaneSlots (sp + 17376#64) 544 3 hws ∗ memRegion (sp + 27840#64) 504 ∗
        MultiLaneSampled (sp + 29024#64) 3 sampled ∗ F)
      (fun sf Pf =>
        if allLanesDone 3 (rowSeeds rho row) 0 then Seg2RowDone b sp fpVal rho row F sf Pf
        else Seg2LoopState b sp fpVal rho row F 0 sf Pf) := by
  let tB : BTree (BitVec 64) 9 := BTree.ofFn 9 fun i =>
    if i < 3 then BitVec.ofNat 64 (sampled i) else 0#64
  have htB : ∀ i, i < 3 → tB.get i = BitVec.ofNat 64 (sampled i) := fun i hi => by
    rw [BTree.get_ofFn 9 _ i (by omega)]; simp [hi]
  let k2Hi : Nat → BitVec 64 := fun idx =>
    if h : idx < 25 then Classical.choose (hs2 idx h) else 0#64
  let env := mkSegEnv sp fpVal row rho (rowPermState rho row 0 2) (rowPermState rho row 1 2)
    (rowPermState rho row 2 2) k2Hi s tA tB
  rcases mkSegState_matches (cfg := cfgClamp) (hasConsts := true)
    (slots01 := preClamp01Slots) (slots2 := preClamp2Slots)
    (k0 := rowPermState rho row 0 2) (k1 := rowPermState rho row 1 2)
    (k2 := rowPermState rho row 2 2) (k2Hi := k2Hi) (tA := tA) (tB := tB)
    (by decide) (by decide) hreg hx22 (fun _ => htA)
    (fun i hi => hs01 i (by simpa [preClamp01Slots] using hi))
    (fun i hi => by
      have hi25 : i < 25 := by simpa [preClamp2Slots] using hi
      simpa [k2Hi, hi25] using Classical.choose_spec (hs2 i hi25)) with ⟨hm0, htA_eq, htB_eq⟩
  apply with_frozen_env hcl hro
  apply keccakRc_intro hro
  let FF := memRegion (sp + 9984#64) 1512 ∗
    MultiLaneSlots (sp + 17376#64) 544 3 hws ∗ memRegion (sp + 27840#64) 504 ∗ F
  refine SepWP.congr_pre (P1 := KSpatial cfgClamp env stInitClamp0 FF) ?_ ?_
  · dsimp only [KSpatial, stInitClamp0, FF]
    rw [multiLaneSampled3_eq_treeMem sp sampled tB
      (htB 0 (by decide)) (htB 1 (by decide)) (htB 2 (by decide)), htA_eq, htB_eq]
    dsimp only [cfgClamp]
    rw [show env.rcBase = mlkemMpl.ρ "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.29" from rfl,
      show env.sp = sp from rfl,
      show sp + BitVec.ofNat 64 64 = sp + 64#64 from rfl,
      show sp + BitVec.ofNat 64 29024 = sp + 29024#64 from rfl]
    apply sepProp_ext <;> sep_frame
  have hb0 : env.vars 900 = BitVec.ofNat 64 (sampled 0) := by
    simpa [env, mkSegEnv] using htB 0 (by decide)
  have hb1 : env.vars 901 = BitVec.ofNat 64 (sampled 1) := by
    simpa [env, mkSegEnv] using htB 1 (by decide)
  have hb2 : env.vars 902 = BitVec.ofNat 64 (sampled 2) := by
    simpa [env, mkSegEnv] using htB 2 (by decide)
  have hv0 : ∀ idx, idx < 25 → env.vars idx = (rowPermState rho row 0 2).getD idx 0#64 :=
    fun idx h => by simp [env, mkSegEnv, h]
  have hv1 : ∀ idx, idx < 25 → env.vars (25 + idx) = (rowPermState rho row 1 2).getD idx 0#64 :=
    fun idx h => by simp [env, mkSegEnv, show ¬(25 + idx < 25) by omega,
      show 25 + idx < 50 by omega, show 25 + idx - 25 = idx by omega]
  have hv2 : ∀ idx, idx < 25 → env.vars (50 + idx) = (rowPermState rho row 2 2).getD idx 0#64 :=
    fun idx h => by simp [env, mkSegEnv, show ¬(50 + idx < 25) by omega,
      show ¬(50 + idx < 50) by omega, show 50 + idx < 75 by omega, show 50 + idx - 50 = idx by omega]
  have hr0 : env.rLoop < 24 := show (0 : Nat) < 24 by decide
  refine sepWP_of_runKRange cfgClamp_wf hr0 (w := 2212) (count := 17)
    (st := stInitClamp0) (st' := stInitC1) (s := s)
    (by omega) (by omega) cert_initC1
    (by rw [BitVec.ofNat_mul 4 2212]; exact pc_of_eq hpc (by decide +kernel)) hrun hm0 ?_
  intro s1 hpc1 hrun1 hm1
  have hp1 := eval_checked_pstate (ok := fun _ => true) (envSpec := env) hm1
    (fun _ _ => rfl) (.var 902) (.const64 256#64) cert_pstateC1 rfl rfl
  refine step_bCond_seg2 (w := 2229) (cond := .CC) (disp := 24#64)
    (by omega) (by omega) (by decide +kernel)
    (pc_add_eq hpc1 (by decide +kernel)) hrun1 ?_ ?_
  · intro hcc
    rw [hp1, evalKExpr, evalKExpr, hb2, condCC_256_of_le271 (raw_sampled_le271 hraw (by decide))] at hcc
    have hs2lt : sampled 2 < 256 := of_decide_eq_true hcc
    have hdone : allLanesDone 3 (rowSeeds rho row) 0 = false :=
      Bool.eq_false_iff.mpr fun hd => absurd ((hraw.allLanesDone_iff_ge256.mp hd) 2 (by decide)) (by omega)
    refine sepWP_of_runKRange cfgClamp_wf hr0 (w := 2235) (count := 2)
      (st := stInitC1) (st' := stInitCLo) (s := s1.setPC (b + BitVec.ofNat 64 (4 * 2229) + 24#64))
      (by omega) (by omega) cert_initCLo
      (setPC_disp_w_eq s1 b 2229 24#64 2235 (by decide +kernel)) ((status_setPC _ _).trans hrun1) (matches_setPC hm1 _) ?_
    intro s2 hpc2 hrun2 hm2
    refine step_b_seg2 (w := 2237) (disp := 12#64) (by omega) (by omega) (by decide +kernel)
      (pc_add_eq hpc2 (by decide +kernel)) hrun2 ?_
    exact finish_clamp_branch hraw (matches_setPC hm2 _) rfl rfl
      (by simp [env, mkSegEnv]) (by simpa [env, mkSegEnv] using hx1) (by simp [env, mkSegEnv])
      (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv])
      (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv])
      hv0 hv1 hv2 hb0 hb1 hb2 false hdone
      (setPC_disp_eq s2 b 2237 12#64 0x2300#64 (by decide +kernel)) ((status_setPC _ _).trans hrun2) cert_chkCLo
  · intro hccF
    rw [hp1, evalKExpr, evalKExpr, hb2, condCC_256_of_le271 (raw_sampled_le271 hraw (by decide))] at hccF
    have hs2ge : 256 ≤ sampled 2 := by have := of_decide_eq_false hccF; omega
    refine sepWP_of_runKRange cfgClamp_wf hr0 (w := 2230) (count := 3)
      (st := stInitC1) (st' := stInitCHi) (s := s1.setPC (b + BitVec.ofNat 64 (4 * (2229 + 1))))
      (by omega) (by omega) cert_initCHi
      (setPC_fall_w_eq s1 b 2229 2230 (by decide +kernel)) ((status_setPC _ _).trans hrun1) (matches_setPC hm1 _) ?_
    intro s2 hpc2 hrun2 hm2
    have hp2 := eval_checked_pstate (ok := fun _ => true) (envSpec := env) hm2
      (fun _ _ => rfl) (.var 901) (.const64 256#64) cert_pstateCHi rfl rfl
    refine step_bCond_seg2 (w := 2233) (cond := .CS) (disp := 20#64)
      (by omega) (by omega) (by decide +kernel)
      (pc_add_eq hpc2 (by decide +kernel)) hrun2 ?_ ?_
    · intro hcs
      rw [hp2, evalKExpr, evalKExpr, hb1, condCS_256_of_le271 (raw_sampled_le271 hraw (by decide))] at hcs
      have hs1ge : 256 ≤ sampled 1 := of_decide_eq_true hcs
      refine sepWP_of_runKRange cfgClamp_wf hr0 (w := 2238) (count := 1)
        (st := stInitCHi) (st' := stInitCEnd) (s := s2.setPC (b + BitVec.ofNat 64 (4 * 2233) + 20#64))
        (by omega) (by omega) cert_initCEnd
        (setPC_disp_w_eq s2 b 2233 20#64 2238 (by decide +kernel)) ((status_setPC _ _).trans hrun2) (matches_setPC hm2 _) ?_
      intro s3 hpc3 hrun3 hm3
      have hp3 := eval_checked_pstate (ok := fun _ => true) (envSpec := env) hm3
        (fun _ _ => rfl) (.var 900) (.const64 255#64) cert_pstateCEnd rfl rfl
      refine step_bCond_seg2 (w := 2239) (cond := .HI) (disp := 3404#64)
        (by omega) (by omega) (by decide +kernel)
        (pc_add_eq hpc3 (by decide +kernel)) hrun3 ?_ ?_
      · intro hhi
        rw [hp3, evalKExpr, evalKExpr, hb0, condHI_255_of_le271 (raw_sampled_le271 hraw (by decide))] at hhi
        have hs0ge : 256 ≤ sampled 0 := of_decide_eq_true hhi
        have hdone : allLanesDone 3 (rowSeeds rho row) 0 = true :=
          hraw.allLanesDone_iff_ge256.mpr fun i hi => by
            rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl <;> assumption
        exact finish_clamp_branch hraw (matches_setPC hm3 _) rfl rfl
          (by simp [env, mkSegEnv]) (by simpa [env, mkSegEnv] using hx1) (by simp [env, mkSegEnv])
          (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv])
          (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv])
          hv0 hv1 hv2 hb0 hb1 hb2 true hdone
          (setPC_disp_eq s3 b 2239 3404#64 0x3048#64 (by decide +kernel)) ((status_setPC _ _).trans hrun3) cert_chkCEndT
      · intro hhiF
        rw [hp3, evalKExpr, evalKExpr, hb0, condHI_255_of_le271 (raw_sampled_le271 hraw (by decide))] at hhiF
        have hs0lt : sampled 0 < 256 := by have := of_decide_eq_false hhiF; omega
        have hdone : allLanesDone 3 (rowSeeds rho row) 0 = false :=
          Bool.eq_false_iff.mpr fun hd => absurd ((hraw.allLanesDone_iff_ge256.mp hd) 0 (by decide)) (by omega)
        exact finish_clamp_branch hraw (matches_setPC hm3 _) rfl rfl
          (by simp [env, mkSegEnv]) (by simpa [env, mkSegEnv] using hx1) (by simp [env, mkSegEnv])
          (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv])
          (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv])
          hv0 hv1 hv2 hb0 hb1 hb2 false hdone
          (setPC_fall_eq s3 b 2239 0x2300#64 (by decide +kernel)) ((status_setPC _ _).trans hrun3) cert_chkCEndF
    · intro hcsF
      rw [hp2, evalKExpr, evalKExpr, hb1, condCS_256_of_le271 (raw_sampled_le271 hraw (by decide))] at hcsF
      have hs1lt : sampled 1 < 256 := by have := of_decide_eq_false hcsF; omega
      have hdone : allLanesDone 3 (rowSeeds rho row) 0 = false :=
        Bool.eq_false_iff.mpr fun hd => absurd ((hraw.allLanesDone_iff_ge256.mp hd) 1 (by decide)) (by omega)
      refine step_b_seg2 (w := 2234) (disp := 24#64) (by omega) (by omega) (by decide +kernel)
        (setPC_fall_w_eq s2 b 2233 2234 (by decide +kernel)) ((status_setPC _ _).trans hrun2) ?_
      exact finish_clamp_branch hraw (matches_setPC (matches_setPC hm2 _) _) rfl rfl
        (by simp [env, mkSegEnv]) (by simpa [env, mkSegEnv] using hx1) (by simp [env, mkSegEnv])
        (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv])
        (by simp [env, mkSegEnv]) (by simp [env, mkSegEnv])
        hv0 hv1 hv2 hb0 hb1 hb2 false hdone
        (setPC_disp_eq (s2.setPC _) b 2234 24#64 0x2300#64 (by decide +kernel))
        ((status_setPC _ _).trans ((status_setPC _ _).trans hrun2)) cert_chkCHi

theorem slotHolds_of_sitePreserved {cfgK : KCfg} {cfgS : RejSiteConfig} {s0 sF : State}
    {pc : BitVec 64} {tA : BTree (BitVec 64) 9} {sl : KSlot} {vLo vHi : BitVec 64}
    (hp : SitePreserved cfgS s0 sF) (hsl : slotHolds cfgK s0 tA sl vLo vHi) :
    slotHolds cfgK (sF.setPC pc) tA sl vLo vHi := by
  have hv : (sF.setPC pc).vregs = s0.vregs := hp.2.2.1
  cases sl with
  | vreg r => exact ⟨hsl.1, by simp [State.readVReg128, VRegFile.read, hv, ← hsl.2]⟩
  | spillQ _ => exact hsl

theorem slotHoldsLo_of_sitePreserved {cfgK : KCfg} {cfgS : RejSiteConfig} {s0 sF : State}
    {pc : BitVec 64} {tA : BTree (BitVec 64) 9} {sl : KSlot} {vLo : BitVec 64}
    (hp : SitePreserved cfgS s0 sF) (hsl : slotHoldsLo cfgK s0 tA sl vLo) :
    slotHoldsLo cfgK (sF.setPC pc) tA sl vLo := by
  rcases hsl with ⟨vHi, h⟩; exact ⟨vHi, slotHolds_of_sitePreserved hp h⟩

theorem segRegInv_of_sitePreserved [MlKemPlacement] {cfgS : RejSiteConfig}
    {sp fpVal pc : BitVec 64} {row : Nat} {s0 sF : State}
    (hp : SitePreserved cfgS s0 sF)
    (hn1 : Reg.x1 ∉ cfgS.siteClobberedRegs) (hn29 : Reg.fp ∉ cfgS.siteClobberedRegs)
    (hn19 : Reg.x19 ∉ cfgS.siteClobberedRegs) (hn20 : Reg.x20 ∉ cfgS.siteClobberedRegs)
    (hn21 : Reg.x21 ∉ cfgS.siteClobberedRegs) (hn22 : Reg.x22 ∉ cfgS.siteClobberedRegs)
    (hn23 : Reg.x23 ∉ cfgS.siteClobberedRegs) (hn24 : Reg.x24 ∉ cfgS.siteClobberedRegs)
    (hn26 : Reg.x26 ∉ cfgS.siteClobberedRegs) (hn27 : Reg.x27 ∉ cfgS.siteClobberedRegs)
    (hn28 : Reg.x28 ∉ cfgS.siteClobberedRegs)
    (hreg : Seg2RegInv sp fpVal s0) (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 (row + 1))
    (hx22 : s0.readReg64 .x22 = BitVec.ofNat 64 row) :
    Seg2RegInv sp fpVal (sF.setPC pc) ∧
      (sF.setPC pc).readReg64 .x1 = BitVec.ofNat 64 (row + 1) ∧
      (sF.setPC pc).readReg64 .x22 = BitVec.ofNat 64 row := by
  rcases hreg with ⟨⟨hsp, hspA, r29, r19, r21, r24, r26, r27, r28⟩, r20, r23⟩
  have hspF : (sF.setPC pc).sp = sp := hp.2.1.trans hsp
  have hspAF : (sF.setPC pc).spAligned = true := by
    unfold State.spAligned at hspA ⊢; rwa [hspF, ← hsp]
  exact ⟨⟨⟨hspF, hspAF, (hp.2.2.2 _ hn29).trans r29, (hp.2.2.2 _ hn19).trans r19,
    (hp.2.2.2 _ hn21).trans r21, (hp.2.2.2 _ hn24).trans r24, (hp.2.2.2 _ hn26).trans r26,
    (hp.2.2.2 _ hn27).trans r27, (hp.2.2.2 _ hn28).trans r28⟩,
    (hp.2.2.2 _ hn20).trans r20, (hp.2.2.2 _ hn23).trans r23⟩,
    (hp.2.2.2 _ hn1).trans hx1, (hp.2.2.2 _ hn22).trans hx22⟩

/-! ## 2. 6-Permutation `A1..A3, B1..B3` Symbolic Program (`+0x02dc → +0x1f5c`) -/

@[expose] def stInit0 : KState := mkSegState cfgInit true [] []
@[expose] def stAt219 : KState := (runKRange cfgInit 183 36 stInit0).getD stInit0
@[expose] def expA1Lo : List KExpr := slotsA1.map fun sl => (readSlot cfgInit stAt219 sl).1
@[expose] def expA1Hi : List KExpr := slotsA1.map fun sl => (readSlot cfgInit stAt219 sl).2
@[expose] def stPostA1 : KState := (stepKLoopSym cfgInit 219 194 8#5 slotsA1 2000 stAt219).getD stAt219
@[expose] def stAt461 : KState := (runKRange cfgInit 414 47 stPostA1).getD stPostA1
@[expose] def expA2Lo : List KExpr := slotsA2.map fun sl => (readSlot cfgInit stAt461 sl).1
@[expose] def expA2Hi : List KExpr := slotsA2.map fun sl => (readSlot cfgInit stAt461 sl).2
@[expose] def expVarRange (base : Nat) : List KExpr := (List.range 25).map fun idx => .var (base + idx)

@[expose] def stepsInit : List KProgStep :=
  [.range 183 36,
   .loop 219 194 8#5 slotsA1 expA1Lo expA1Hi 2000,
   .range 414 47,
   .loop 461 199 8#5 slotsA2 expA2Lo expA2Hi 3000,
   .range 661 46,
   .loop 707 202 8#5 slotsA3 (expVarRange 2000) (expVarRange 2025) 4000,
   .range 910 29,
   .loop 939 201 8#5 slotsB1 (expVarRange 4000) (expVarRange 4025) 5000,
   .range 1141 43,
   .loop 1184 203 8#5 slotsB2 (expVarRange 3000) (expVarRange 3025) 6000,
   .range 1388 37,
   .loop 1425 201 8#5 slotsB3 (expVarRange 6000) (expVarRange 6025) 7000,
   .range 1627 380]

@[expose] def exprOnlyVar100 : KExpr → Bool
  | .var id => id == 100
  | .const64 _ | .rcVal _ => true
  | .xor a b | .bic a b | .and64 a b | .or64 a b | .add64 a b | .insByte0 a b =>
      exprOnlyVar100 a && exprOnlyVar100 b
  | .bsl m a b | .bitOp m a b | .selHi255 m a b =>
      exprOnlyVar100 m && exprOnlyVar100 a && exprOnlyVar100 b
  | .shl a _ | .ushr a _ | .rotl a _ => exprOnlyVar100 a
  | _ => false

@[expose] def envRow (row : Nat) : KEnv :=
  { sp := 0#64, rcBase := 0#64, rLoop := 0,
    vars := fun id => if id == 100 then BitVec.ofNat 64 row else 0#64 }

theorem evalKExpr_eq_envRow {env : KEnv} {row : Nat} (h100 : env.vars 100 = BitVec.ofNat 64 row) :
    ∀ {e : KExpr}, exprOnlyVar100 e = true → evalKExpr env e = evalKExpr (envRow row) e
  | .var id, h => by have hid : id = 100 := beq_iff_eq.mp h; subst hid; simp [evalKExpr, envRow, h100]
  | .const64 _, _ | .rcVal _, _ => rfl
  | .spAdd _, h | .rcAdd _, h | .rcLoopOff, h | .rcLoopPtr, h | .rcLoopNext, h | .rcLoopVal, h =>
      nomatch h
  | .xor _ _, h | .bic _ _, h | .and64 _ _, h | .or64 _ _, h | .add64 _ _, h | .insByte0 _ _, h => by
      simp only [exprOnlyVar100, Bool.and_eq_true] at h
      simp [evalKExpr, evalKExpr_eq_envRow h100 h.1, evalKExpr_eq_envRow h100 h.2]
  | .bsl _ _ _, h | .bitOp _ _ _, h | .selHi255 _ _ _, h => by
      simp only [exprOnlyVar100, Bool.and_eq_true] at h
      simp [evalKExpr, evalKExpr_eq_envRow h100 h.1.1, evalKExpr_eq_envRow h100 h.1.2,
        evalKExpr_eq_envRow h100 h.2]
  | .shl _ _, h | .ushr _ _, h | .rotl _ _, h => by
      simp only [exprOnlyVar100] at h
      simp [evalKExpr, evalKExpr_eq_envRow h100 h]

@[expose] def checkPreAbsorb (es : List KExpr) (col : Nat) : Bool :=
  (List.range 4).all (fun k => (es.getD k (.const64 0#64)).beq (.var (103 + k))) &&
  (List.range 3).all (fun r =>
    (List.range 21).all (fun j =>
      let idx := 4 + j
      let e := es.getD idx (.const64 0#64)
      exprOnlyVar100 e && (evalKExpr (envRow r) e == preAbsorbLane [] r col idx)))

private theorem array_getElem_eq_getD64 (a : Array (BitVec 64)) (idx : Nat) (h : idx < a.size) :
    a[idx]'h = a.getD idx 0#64 := by
  simp only [Array.getD, h, ↓reduceDIte]; rfl

private theorem evalExprList25_getD (env : KEnv) (es : List KExpr) (idx : Nat) (hidx : idx < 25) :
    (evalExprList25 env es).getD idx 0#64 = evalKExpr env (es.getD idx (.const64 0#64)) := by
  simp [evalExprList25, Array.getD, hidx]

theorem preAbsorb_eq_of_check {rho : List (BitVec 8)} (hrho : rho.length = 32)
    {row col : Nat} (hrow : row < 3) {env : KEnv} {es : List KExpr}
    (hv100 : env.vars 100 = BitVec.ofNat 64 row)
    (hvRho : ∀ k, k < 4 → env.vars (103 + k) = rhoW rho k)
    (hchk : checkPreAbsorb es col = true) :
    keccakF1600 (evalExprList25 env es) = rowPermState rho row col 0 := by
  rw [rowPermState_zero hrho row col]
  simp only [checkPreAbsorb, Bool.and_eq_true] at hchk
  apply congrArg keccakF1600
  apply Array.ext
  · simp [evalExprList25, preAbsorbState_size]
  · intro idx hi1 hi2
    have hidx : idx < 25 := by simpa [evalExprList25] using hi1
    rw [array_getElem_eq_getD64 _ idx hi1, evalExprList25_getD env es idx hidx,
        array_getElem_eq_getD64 _ idx hi2, preAbsorbState_getD rho row col hidx]
    by_cases hk4 : idx < 4
    · have hbeq := (List.all_eq_true.mp hchk.1) idx (List.mem_range.mpr hk4)
      rw [KeccakSymDefs.KExpr.beq_eq_true hbeq, evalKExpr, hvRho idx hk4]
      simp [preAbsorbLane, hk4]
    · have hr := (List.all_eq_true.mp hchk.2) row (List.mem_range.mpr hrow)
      have hj := (List.all_eq_true.mp hr) (idx - 4) (List.mem_range.mpr (by omega))
      simp only [show 4 + (idx - 4) = idx by omega, Bool.and_eq_true, beq_iff_eq] at hj
      rw [evalKExpr_eq_envRow hv100 hj.1, hj.2]
      simp [preAbsorbLane, hk4]

theorem evalExprList25_varRange {env : KEnv} {base : Nat} {st : KeccakState}
    (hst : st.size = 25) (hvars : ∀ idx, idx < 25 → env.vars (base + idx) = st.getD idx 0#64) :
    evalExprList25 env (expVarRange base) = st := by
  apply Array.ext
  · simp [evalExprList25, hst]
  · intro idx hi1 hi2
    have hidx : idx < 25 := by simpa [evalExprList25] using hi1
    have hget : (expVarRange base).getD idx (.const64 0#64) = .var (base + idx) := by
      simp [expVarRange, List.getD_eq_getElem?_getD, hidx]
    rw [array_getElem_eq_getD64 _ idx hi1, evalExprList25_getD env _ idx hidx, hget, evalKExpr,
      hvars idx hidx, array_getElem_eq_getD64 st idx hi2]

private theorem extendLoopVars_lt (e : KEnv) (b : Nat) (lo hi : KeccakState) {id : Nat}
    (h : id < b) : (extendLoopVars e b lo hi).vars id = e.vars id := by
  simp [extendLoopVars, h]

private theorem extendLoopVars_lo (e : KEnv) (b : Nat) (lo hi : KeccakState) {idx : Nat}
    (h : idx < 25) : (extendLoopVars e b lo hi).vars (b + idx) = (keccakF1600 lo).getD idx 0#64 := by
  simp only [extendLoopVars, show ¬(b + idx < b) by omega,
    show b + idx < b + 25 by omega, show b + idx - b = idx by omega, ↓reduceIte, Array.getD]

private theorem extendLoopVars_hi (e : KEnv) (b : Nat) (lo hi : KeccakState) {idx : Nat}
    (h : idx < 25) : (extendLoopVars e b lo hi).vars (b + 25 + idx) = (keccakF1600 hi).getD idx 0#64 := by
  simp only [extendLoopVars, show ¬(b + 25 + idx < b) by omega,
    show ¬(b + 25 + idx < b + 25) by omega, show b + 25 + idx < b + 50 by omega,
    show b + 25 + idx - (b + 25) = idx by omega, ↓reduceIte, Array.getD]

theorem specEnv_stepsInit_vars {rho : List (BitVec 8)} (hrho : rho.length = 32)
    {row : Nat} (hrow : row < 3) {env0 : KEnv}
    (hv100 : env0.vars 100 = BitVec.ofNat 64 row)
    (hvRho : ∀ k, k < 4 → env0.vars (103 + k) = rhoW rho k) :
    let envS := specEnvSteps env0 stepsInit
    envS.vars 100 = BitVec.ofNat 64 row ∧
    envS.vars 102 = env0.vars 102 ∧
    (∀ k, k < 4 → envS.vars (103 + k) = rhoW rho k) ∧
    (∀ idx, idx < 25 → envS.vars (2000 + idx) = (rowPermState rho row 0 0).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (2025 + idx) = (rowPermState rho row 1 0).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (3000 + idx) = (rowPermState rho row 2 0).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (3025 + idx) = (rowPermState rho row 2 0).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (4000 + idx) = (rowPermState rho row 0 1).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (4025 + idx) = (rowPermState rho row 1 1).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (5000 + idx) = (rowPermState rho row 0 2).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (5025 + idx) = (rowPermState rho row 1 2).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (6000 + idx) = (rowPermState rho row 2 1).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (6025 + idx) = (rowPermState rho row 2 1).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (7000 + idx) = (rowPermState rho row 2 2).getD idx 0#64) ∧
    (∀ idx, idx < 25 → envS.vars (7025 + idx) = (rowPermState rho row 2 2).getD idx 0#64) := by
  dsimp only [stepsInit, specEnvSteps]
  set e1 := extendLoopVars env0 2000 (evalExprList25 env0 expA1Lo) (evalExprList25 env0 expA1Hi) with he1
  set e2 := extendLoopVars e1 3000 (evalExprList25 e1 expA2Lo) (evalExprList25 e1 expA2Hi) with he2
  set e3 := extendLoopVars e2 4000 (evalExprList25 e2 (expVarRange 2000)) (evalExprList25 e2 (expVarRange 2025)) with he3
  set e4 := extendLoopVars e3 5000 (evalExprList25 e3 (expVarRange 4000)) (evalExprList25 e3 (expVarRange 4025)) with he4
  set e5 := extendLoopVars e4 6000 (evalExprList25 e4 (expVarRange 3000)) (evalExprList25 e4 (expVarRange 3025)) with he5
  set e6 := extendLoopVars e5 7000 (evalExprList25 e5 (expVarRange 6000)) (evalExprList25 e5 (expVarRange 6025)) with he6
  have hp10 : keccakF1600 (evalExprList25 env0 expA1Lo) = rowPermState rho row 0 0 :=
    preAbsorb_eq_of_check hrho hrow hv100 hvRho (by decide +kernel)
  have hp11 : keccakF1600 (evalExprList25 env0 expA1Hi) = rowPermState rho row 1 0 :=
    preAbsorb_eq_of_check hrho hrow hv100 hvRho (by decide +kernel)
  have hp20 : keccakF1600 (evalExprList25 e1 expA2Lo) = rowPermState rho row 2 0 :=
    preAbsorb_eq_of_check hrho hrow (by rw [he1, extendLoopVars_lt _ _ _ _ (by omega), hv100])
      (fun k hk => by rw [he1, extendLoopVars_lt _ _ _ _ (by omega), hvRho k hk]) (by decide +kernel)
  have hp21 : keccakF1600 (evalExprList25 e1 expA2Hi) = rowPermState rho row 2 0 :=
    preAbsorb_eq_of_check hrho hrow (by rw [he1, extendLoopVars_lt _ _ _ _ (by omega), hv100])
      (fun k hk => by rw [he1, extendLoopVars_lt _ _ _ _ (by omega), hvRho k hk]) (by decide +kernel)
  have hp30 : keccakF1600 (evalExprList25 e2 (expVarRange 2000)) = rowPermState rho row 0 1 := by
    rw [evalExprList25_varRange (rowPermState_size hrho row 0 0) fun idx h => by
      rw [he2, extendLoopVars_lt _ _ _ _ (by omega), he1, extendLoopVars_lo _ _ _ _ h, hp10], rowPermState_succ]
  have hp31 : keccakF1600 (evalExprList25 e2 (expVarRange 2025)) = rowPermState rho row 1 1 := by
    rw [evalExprList25_varRange (rowPermState_size hrho row 1 0) fun idx h => by
      rw [he2, extendLoopVars_lt _ _ _ _ (by omega), he1, extendLoopVars_hi _ _ _ _ h, hp11], rowPermState_succ]
  have hp40 : keccakF1600 (evalExprList25 e3 (expVarRange 4000)) = rowPermState rho row 0 2 := by
    rw [evalExprList25_varRange (rowPermState_size hrho row 0 1) fun idx h => by
      rw [he3, extendLoopVars_lo _ _ _ _ h, hp30], rowPermState_succ]
  have hp41 : keccakF1600 (evalExprList25 e3 (expVarRange 4025)) = rowPermState rho row 1 2 := by
    rw [evalExprList25_varRange (rowPermState_size hrho row 1 1) fun idx h => by
      rw [he3, extendLoopVars_hi _ _ _ _ h, hp31], rowPermState_succ]
  have hp50 : keccakF1600 (evalExprList25 e4 (expVarRange 3000)) = rowPermState rho row 2 1 := by
    rw [evalExprList25_varRange (rowPermState_size hrho row 2 0) fun idx h => by
      rw [he4, extendLoopVars_lt _ _ _ _ (by omega), he3, extendLoopVars_lt _ _ _ _ (by omega),
        he2, extendLoopVars_lo _ _ _ _ h, hp20], rowPermState_succ]
  have hp51 : keccakF1600 (evalExprList25 e4 (expVarRange 3025)) = rowPermState rho row 2 1 := by
    rw [evalExprList25_varRange (rowPermState_size hrho row 2 0) fun idx h => by
      rw [he4, extendLoopVars_lt _ _ _ _ (by omega), he3, extendLoopVars_lt _ _ _ _ (by omega),
        he2, extendLoopVars_hi _ _ _ _ h, hp21], rowPermState_succ]
  have hp60 : keccakF1600 (evalExprList25 e5 (expVarRange 6000)) = rowPermState rho row 2 2 := by
    rw [evalExprList25_varRange (rowPermState_size hrho row 2 1) fun idx h => by
      rw [he5, extendLoopVars_lo _ _ _ _ h, hp50], rowPermState_succ]
  have hp61 : keccakF1600 (evalExprList25 e5 (expVarRange 6025)) = rowPermState rho row 2 2 := by
    rw [evalExprList25_varRange (rowPermState_size hrho row 2 1) fun idx h => by
      rw [he5, extendLoopVars_hi _ _ _ _ h, hp51], rowPermState_succ]
  have hlt : ∀ id, id < 2000 → e6.vars id = env0.vars id := fun id h => by
    rw [he6, extendLoopVars_lt _ _ _ _ (by omega), he5, extendLoopVars_lt _ _ _ _ (by omega),
      he4, extendLoopVars_lt _ _ _ _ (by omega), he3, extendLoopVars_lt _ _ _ _ (by omega),
      he2, extendLoopVars_lt _ _ _ _ (by omega), he1, extendLoopVars_lt _ _ _ _ h]
  refine ⟨by rw [hlt 100 (by omega), hv100], hlt 102 (by omega),
    fun k hk => by rw [hlt _ (by omega), hvRho k hk],
    fun idx h => by rw [he6, extendLoopVars_lt _ _ _ _ (by omega), he5, extendLoopVars_lt _ _ _ _ (by omega),
      he4, extendLoopVars_lt _ _ _ _ (by omega), he3, extendLoopVars_lt _ _ _ _ (by omega),
      he2, extendLoopVars_lt _ _ _ _ (by omega), he1, extendLoopVars_lo _ _ _ _ h, hp10],
    fun idx h => by rw [he6, extendLoopVars_lt _ _ _ _ (by omega), he5, extendLoopVars_lt _ _ _ _ (by omega),
      he4, extendLoopVars_lt _ _ _ _ (by omega), he3, extendLoopVars_lt _ _ _ _ (by omega),
      he2, extendLoopVars_lt _ _ _ _ (by omega), he1, extendLoopVars_hi _ _ _ _ h, hp11],
    fun idx h => by rw [he6, extendLoopVars_lt _ _ _ _ (by omega), he5, extendLoopVars_lt _ _ _ _ (by omega),
      he4, extendLoopVars_lt _ _ _ _ (by omega), he3, extendLoopVars_lt _ _ _ _ (by omega),
      he2, extendLoopVars_lo _ _ _ _ h, hp20],
    fun idx h => by rw [he6, extendLoopVars_lt _ _ _ _ (by omega), he5, extendLoopVars_lt _ _ _ _ (by omega),
      he4, extendLoopVars_lt _ _ _ _ (by omega), he3, extendLoopVars_lt _ _ _ _ (by omega),
      he2, extendLoopVars_hi _ _ _ _ h, hp21],
    fun idx h => by rw [he6, extendLoopVars_lt _ _ _ _ (by omega), he5, extendLoopVars_lt _ _ _ _ (by omega),
      he4, extendLoopVars_lt _ _ _ _ (by omega), he3, extendLoopVars_lo _ _ _ _ h, hp30],
    fun idx h => by rw [he6, extendLoopVars_lt _ _ _ _ (by omega), he5, extendLoopVars_lt _ _ _ _ (by omega),
      he4, extendLoopVars_lt _ _ _ _ (by omega), he3, extendLoopVars_hi _ _ _ _ h, hp31],
    fun idx h => by rw [he6, extendLoopVars_lt _ _ _ _ (by omega), he5, extendLoopVars_lt _ _ _ _ (by omega),
      he4, extendLoopVars_lo _ _ _ _ h, hp40],
    fun idx h => by rw [he6, extendLoopVars_lt _ _ _ _ (by omega), he5, extendLoopVars_lt _ _ _ _ (by omega),
      he4, extendLoopVars_hi _ _ _ _ h, hp41],
    fun idx h => by rw [he6, extendLoopVars_lt _ _ _ _ (by omega), he5, extendLoopVars_lo _ _ _ _ h, hp50],
    fun idx h => by rw [he6, extendLoopVars_lt _ _ _ _ (by omega), he5, extendLoopVars_hi _ _ _ _ h, hp51],
    fun idx h => by rw [he6, extendLoopVars_lo _ _ _ _ h, hp60],
    fun idx h => by rw [he6, extendLoopVars_hi _ _ _ _ h, hp61]⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg2RowInit
