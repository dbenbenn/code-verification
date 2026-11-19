/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Field51Base
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Layer0
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `Scalar52` Machine-Code Proofs

Machine-code proofs in `dalekCliMultiLib` for `Scalar52` arithmetic and `Scalar::reduce`:
1. `sc52_montgomery_mul_core_ok : Sc52MontgomeryMulCoreOk` (`B06`, 329 insns)
2. `sc52_montgomery_mul_ro_right_ok : Sc52MontgomeryMulRoRightOk` (`B06`, 329 insns, RO rhs)
3. `sc52_mul_core_ok : Sc52MulCoreOk` (`B07`, 662 insns)
4. `sc52_mul_ok : Sc52MulOk` (`B07` `< edOrderL` corollary)
5. `scalar_reduce_ok : ScalarReduceOk` (`B16`, 427 insns)
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Scalar52

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj ProofLib
open VerifiedLibraries.Common (edOrderL leBytesToNat natToLeBytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CommonBase (sc52Val sc52ValOfBytes)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedObjDefs (dalekCliMultiLib)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (
  DalekCliPlacement dalekCliMpl DalekBase DalekBlockOk DalekBlockConstOk
  dalekLeaf_ok dalekCaller_ok dalekBlockPlacement_ρ)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.SliceBase (
  addWithCarry64_false_c stackFrame_eq_stackFrameAt stack_fold_step stack_fold_last
  stack_swap_slice pointsToBytesRO40_eq_cells)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.InternalSpecs (
  sc52LimbsBounded sc52MulCoreSpec sc52MulSpec
  Sc52MontgomeryMulCoreOk Sc52MontgomeryMulRoRightOk Sc52MulCoreOk Sc52MulOk ScalarReduceOk)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Layer0 (black_box_u8_ok)

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 06 dalekCliMultiLib DalekCliPlacement 329 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem dalekCliPl06_rho_norm [DalekCliPlacement] (sym : String) :
    dalekCliPl06.ρ sym = dalekCliMultiLib.resolve dalekCliMpl sym := rfl

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 07 dalekCliMultiLib DalekCliPlacement 662 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem dalekCliPl07_rho_norm [DalekCliPlacement] (sym : String) :
    dalekCliPl07.ρ sym = dalekCliMultiLib.resolve dalekCliMpl sym := rfl

open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.PlacedCodeBase (dalekCliMpl) in
gen_block_fetches dalekCli 16 dalekCliMultiLib DalekCliPlacement 427 rebase rho sub

@[local simp, local arm64_norm, local wp_norm]
private theorem dalekCliPl16_rho_norm [DalekCliPlacement] (sym : String) :
    dalekCliPl16.ρ sym = dalekCliMultiLib.resolve dalekCliMpl sym := rfl

set_option allowUnsafeReducibility true in
attribute [local irreducible] Arm64.Program.fetch
attribute [local irreducible] MultiPlacedLib.CodeLoaded

public section
open Lean Meta in
local simproc [wp_norm] reduceStackFrameFVar (stackFrame _ _) := fun e => do
  let e ← instantiateMVars e
  unless e.isAppOfArity ``Arm64.stackFrame 2 do return .continue
  let sExpr := (e.getArg! 0).consumeMData
  let nExpr := e.getArg! 1
  let some n := nExpr.nat? | return .continue
  if (sExpr.isFVar || n ≤ 16) && n ≤ 2 ^ 64 then
    let spExpr := mkApp (mkConst ``Arm64.State.sp) sExpr
    let rhs := mkApp2 (mkConst ``Arm64.stackFrameAt) spExpr nExpr
    let hn ← mkDecideProof (← mkAppM ``LE.le #[nExpr, mkNatLit (2 ^ 64)])
    let prf := mkApp3 (mkConst ``stackFrame_eq_stackFrameAt) sExpr nExpr hn
    return .visit { expr := rhs, proof? := some prf }
  else
    let spExpr := mkApp (mkConst ``Arm64.State.sp) sExpr
    let offExpr := toExpr (BitVec.ofNat 64 n)
    let subExpr ← mkAppM ``HSub.hSub #[spExpr, offExpr]
    let rhs := mkApp2 (mkConst ``Arm64.memRegion) subExpr nExpr
    return .visit { expr := rhs, proof? := none }
theorem SepWP.congr_state_pre {prog : Program} {target_pc : BitVec 64} {s1 s2 : State} {P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hs : s1 = s2) (hP : P1 = P2) (h : SepWP prog target_pc s1 P1 post oom) :
    SepWP prog target_pc s2 P2 post oom :=
  hs ▸ hP ▸ h
private meta def isSimpleCheckpointVal (e : Lean.Expr) : Bool :=
  let e := e.consumeMData
  let isBase (b : Lean.Expr) : Bool :=
    let b := b.consumeMData
    b.isFVar || (b.isAppOfArity ``Arm64.State.sp 1 && (b.getArg! 0).consumeMData.isFVar)
  if isBase e then true
  else if (ProofLib.evalBitVecLitPure? e).isSome then true
  else if e.isAppOfArity ``Arm64.State.readReg64 2 && (e.getArg! 0).consumeMData.isFVar then true
  else if (e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HSub.hSub 6) &&
          isBase (e.getArg! 4) &&
          (ProofLib.evalBitVecLitPure? (e.getArg! 5)).isSome then true
  else if e.isAppOfArity ``Obj.MultiPlacement.ρ 2 || e.isAppOfArity ``Obj.Placement.ρ 2 || e.isAppOfArity ``Obj.MultiPlacedLib.resolve 3 then true
  else false
@[expose] def CheckpointEq {α : Type} (x val : α) : Prop := x = val
theorem CheckpointEq.to_eq {α : Type} {x val : α} (h : CheckpointEq x val) : x = val := h
theorem CheckpointEq.refl {α : Type} (x : α) : CheckpointEq x x := rfl
theorem CheckpointEq.elim {α : Type} {P : Prop} (val : α) (k : ∀ (x : α), CheckpointEq x val → P) : P :=
  k val rfl
private meta structure CheckpointItem where
  xName : Lean.Name
  hName : Lean.Name
  ty : Lean.Expr
  val : Lean.Expr
private meta partial def checkpointCollectState (recordVal : Lean.Expr → Lean.MetaM Unit) (st : Lean.Expr) : Lean.MetaM Unit := do
  let st := st.consumeMData
  if st.isAppOfArity ``Arm64.State.writeReg64 3 then
    checkpointCollectState recordVal (st.getArg! 0)
    recordVal (st.getArg! 2)
  else if st.isAppOfArity ``Arm64.State.setPState 2 then
    checkpointCollectState recordVal (st.getArg! 0)
    let p := (st.getArg! 1).consumeMData
    if p.isAppOfArity ``ProofLib.addsPState64 2 || p.isAppOfArity ``ProofLib.subsPState64 2 then
      recordVal (p.getArg! 0)
      recordVal (p.getArg! 1)
  else if st.isAppOfArity ``Arm64.State.setPC 2 ||
          st.isAppOfArity ``Arm64.State.setMem 2 ||
          st.isAppOfArity ``Arm64.State.writeVReg128 3 then
    checkpointCollectState recordVal (st.getArg! 0)
private meta partial def checkpointCollectPre (recordVal : Lean.Expr → Lean.MetaM Unit) (pr : Lean.Expr) : Lean.MetaM Unit := do
  let pr := pr.consumeMData
  if pr.isAppOfArity ``SepProp.sepConj 2 then
    checkpointCollectPre recordVal (pr.getArg! 0)
    checkpointCollectPre recordVal (pr.getArg! 1)
  else if pr.isAppOfArity ``Arm64.pointsTo64 2 then
    recordVal (pr.getArg! 1)
private meta partial def checkpointRebuildState (lookupVal : Lean.Expr → Lean.MetaM (Lean.Expr × Lean.Expr)) (st : Lean.Expr) : Lean.MetaM (Lean.Expr × Lean.Expr) := do
  let st := st.consumeMData
  if st.isAppOfArity ``Arm64.State.writeReg64 3 then
    let s1 := st.getArg! 0
    let r := st.getArg! 1
    let v := st.getArg! 2
    let (s1', hs1) ← checkpointRebuildState lookupVal s1
    let (v', hv) ← lookupVal v
    let st' := Lean.mkApp3 (Lean.mkConst ``Arm64.State.writeReg64) s1' r v'
    let c1 ← Lean.Meta.mkCongrArg (Lean.mkConst ``Arm64.State.writeReg64) hs1
    let c2 ← Lean.Meta.mkCongr c1 (← Lean.Meta.mkEqRefl r)
    let hst ← Lean.Meta.mkCongr c2 hv
    return (st', hst)
  else if st.isAppOfArity ``Arm64.State.setPState 2 then
    let s1 := st.getArg! 0
    let p := (st.getArg! 1).consumeMData
    let (s1', hs1) ← checkpointRebuildState lookupVal s1
    if p.isAppOfArity ``ProofLib.addsPState64 2 || p.isAppOfArity ``ProofLib.subsPState64 2 then
      let fn := p.getAppFn
      let (a', ha) ← lookupVal (p.getArg! 0)
      let (b', hb) ← lookupVal (p.getArg! 1)
      let p' := Lean.mkApp2 fn a' b'
      let hp ← Lean.Meta.mkCongr (← Lean.Meta.mkCongrArg fn ha) hb
      let st' := Lean.mkApp2 (Lean.mkConst ``Arm64.State.setPState) s1' p'
      let hst ← Lean.Meta.mkCongr (← Lean.Meta.mkCongrArg (Lean.mkConst ``Arm64.State.setPState) hs1) hp
      return (st', hst)
    else
      let st' := Lean.mkApp2 (Lean.mkConst ``Arm64.State.setPState) s1' p
      let c1 ← Lean.Meta.mkCongrArg (Lean.mkConst ``Arm64.State.setPState) hs1
      let hst ← Lean.Meta.mkCongr c1 (← Lean.Meta.mkEqRefl p)
      return (st', hst)
  else if st.isAppOfArity ``Arm64.State.setPC 2 ||
          st.isAppOfArity ``Arm64.State.setMem 2 then
    let fn := st.getAppFn
    let s1 := st.getArg! 0
    let a := st.getArg! 1
    let (s1', hs1) ← checkpointRebuildState lookupVal s1
    let st' := Lean.mkApp2 fn s1' a
    let c1 ← Lean.Meta.mkCongrArg fn hs1
    let hst ← Lean.Meta.mkCongr c1 (← Lean.Meta.mkEqRefl a)
    return (st', hst)
  else if st.isAppOfArity ``Arm64.State.writeVReg128 3 then
    let fn := st.getAppFn
    let s1 := st.getArg! 0
    let r := st.getArg! 1
    let v := st.getArg! 2
    let (s1', hs1) ← checkpointRebuildState lookupVal s1
    let st' := Lean.mkApp3 fn s1' r v
    let c1 ← Lean.Meta.mkCongrArg fn hs1
    let c2 ← Lean.Meta.mkCongr c1 (← Lean.Meta.mkEqRefl r)
    let hst ← Lean.Meta.mkCongr c2 (← Lean.Meta.mkEqRefl v)
    return (st', hst)
  else
    return (st, ← Lean.Meta.mkEqRefl st)
private meta partial def checkpointRebuildPre (lookupVal : Lean.Expr → Lean.MetaM (Lean.Expr × Lean.Expr)) (pr : Lean.Expr) : Lean.MetaM (Lean.Expr × Lean.Expr) := do
  let pr := pr.consumeMData
  if pr.isAppOfArity ``SepProp.sepConj 2 then
    let (a', ha) ← checkpointRebuildPre lookupVal (pr.getArg! 0)
    let (b', hb) ← checkpointRebuildPre lookupVal (pr.getArg! 1)
    let pr' := Lean.mkApp2 (Lean.mkConst ``SepProp.sepConj) a' b'
    let hpr ← Lean.Meta.mkCongr (← Lean.Meta.mkCongrArg (Lean.mkConst ``SepProp.sepConj) ha) hb
    return (pr', hpr)
  else if pr.isAppOfArity ``Arm64.pointsTo64 2 then
    let addr := pr.getArg! 0
    let (v', hv) ← lookupVal (pr.getArg! 1)
    let pr' := Lean.mkApp2 (Lean.mkConst ``Arm64.pointsTo64) addr v'
    let hpr ← Lean.Meta.mkCongrArg (Lean.mkApp (Lean.mkConst ``Arm64.pointsTo64) addr) hv
    return (pr', hpr)
  else
    return (pr, ← Lean.Meta.mkEqRefl pr)
/-- Abstract compound register values in the `SepWP` state spine `s` and 64-bit stack cells in `P`
    into fresh local variables `v_cp_N` with equations `hv_cp_N : CheckpointEq v_cp_N <expr>`. -/
local elab "wp_checkpoint" : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  g.withContext do
    let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
    if !ty.isAppOfArity ``SepWP 6 then return
    let prog := ty.getArg! 0
    let targetPc := ty.getArg! 1
    let s := ty.getArg! 2
    let P := ty.getArg! 3
    let post := ty.getArg! 4
    let oom := ty.getArg! 5
    let lctx ← Lean.MonadLCtx.getLCtx
    let mut baseIdx : Nat := 0
    for decl in lctx do
      if !decl.isImplementationDetail then
        if decl.type.consumeMData.isAppOfArity ``CheckpointEq 3 then
          baseIdx := baseIdx + 1
    let itemsRef ← IO.mkRef (#[] : Array CheckpointItem)
    let mapRef ← IO.mkRef ({} : Std.HashMap Lean.Expr Nat)
    let recordVal (v : Lean.Expr) : Lean.MetaM Unit := do
      let v := v.consumeMData
      if isSimpleCheckpointVal v then return
      let m ← mapRef.get
      if m.contains v then return
      let idx := (← itemsRef.get).size
      let n := baseIdx + idx
      let xName := Lean.Name.mkSimple s!"v_cp_{n}"
      let hName := Lean.Name.mkSimple s!"hv_cp_{n}"
      let vTy ← Lean.Meta.inferType v
      itemsRef.modify (·.push { xName, hName, ty := vTy, val := v })
      mapRef.modify (·.insert v idx)
    checkpointCollectState recordVal s
    checkpointCollectPre recordVal P
    let items ← itemsRef.get
    if items.isEmpty then return
    let idxMap ← mapRef.get
    let rec withItems (i : Nat) (xFVars hFVars : Array Lean.Expr) : Lean.MetaM (Lean.Expr × Lean.MVarId) := do
      if h : i < items.size then
        let item := items[i]
        Lean.Meta.withLocalDeclD item.xName item.ty fun x => do
          let eqTy := Lean.mkApp3 (Lean.mkConst ``CheckpointEq) item.ty x item.val
          Lean.Meta.withLocalDeclD item.hName eqTy fun hx => do
            let hxEq := Lean.mkApp4 (Lean.mkConst ``CheckpointEq.to_eq) item.ty x item.val hx
            let (innerPrf, gNew) ← withItems (i + 1) (xFVars.push x) (hFVars.push hxEq)
            let cont ← Lean.Meta.mkLambdaFVars #[x, hx] innerPrf
            let prf := Lean.mkApp4 (Lean.mkConst ``CheckpointEq.elim) item.ty ty item.val cont
            return (prf, gNew)
      else
        let lookupVal (v : Lean.Expr) : Lean.MetaM (Lean.Expr × Lean.Expr) := do
          let v := v.consumeMData
          if let some idx := idxMap[v]? then
            return (xFVars[idx]!, hFVars[idx]!)
          else
            return (v, ← Lean.Meta.mkEqRefl v)
        let (s', hs) ← checkpointRebuildState lookupVal s
        let (P', hP) ← checkpointRebuildPre lookupVal P
        let newGoalTy := Lean.mkApp6 (Lean.mkConst ``SepWP) prog targetPc s' P' post oom
        let gNew ← Lean.Meta.mkFreshExprMVar newGoalTy .syntheticOpaque (← g.getTag)
        let body := Lean.mkAppN (Lean.mkConst ``SepWP.congr_state_pre)
          #[prog, targetPc, s', s, P', P, post, oom, hs, hP, gNew]
        return (body, gNew.mvarId!)
    let (prf, gNew) ← withItems 0 #[] #[]
    g.assign prf
    Lean.Elab.Tactic.replaceMainGoal [gNew]
@[expose] def sc52Pack5 (r0 r1 r2 r3 r4 : BitVec 64) : List (BitVec 8) :=
  unpack64 r0 ++ unpack64 r1 ++ unpack64 r2 ++ unpack64 r3 ++ unpack64 r4
theorem sc52Pack5_length (r0 r1 r2 r3 r4 : BitVec 64) : (sc52Pack5 r0 r1 r2 r3 r4).length = 40 := by
  simp [sc52Pack5, unpack64_length]
theorem sc52Pack5_cells_eq (a : BitVec 64) (r0 r1 r2 r3 r4 : BitVec 64) : ((a ↦₆₄ r0) ∗ ((a + 8#64) ↦₆₄ r1) ∗ ((a + 16#64) ↦₆₄ r2) ∗ ((a + 24#64) ↦₆₄ r3) ∗ ((a + 32#64) ↦₆₄ r4)) =
    (a ↦ₛ sc52Pack5 r0 r1 r2 r3 r4) := by
  unfold sc52Pack5
  repeat rw [pointsToBytes_append]
  simp only [List.length_append, unpack64_length,
    ← pointsTo64_eq_pointsToBytes, sepConj_assoc]
theorem exists_cells_of_length_40 {bs : List (BitVec 8)} (h : bs.length = 40) : ∃ w0 w1 w2 w3 w4 : BitVec 64, ∀ a : BitVec 64, (a ↦ₛ bs) = ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
            ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4)) := by
  have h0 : (bs.take 32).length = 32 := (by simp [h]); have h1 : (bs.drop 32).length = 8 := (by simp [h]); obtain ⟨w0, w1, w2, w3, _, hp0⟩ := exists_unpack64_of_length_32 h0
  obtain ⟨w4, hw4⟩ := exists_unpack64_of_length_8 h1
  refine ⟨w0, w1, w2, w3, w4, fun a => ?_⟩
  have hsplit : bs = bs.take 32 ++ bs.drop 32 := (List.take_append_drop 32 bs).symm; rw [hsplit, pointsToBytes_append, h0, hp0, hw4, ← pointsTo64_eq_pointsToBytes]; simp only [sepConj_assoc]
theorem readLE_unpack64_zero (w : BitVec 64) : ByteSlice.readLE (unpack64 w) 0 8 = w :=
  ByteSlice.readLE_unpackLE_64 8 w
theorem sc52Pack5_readLE_0 (r0 r1 r2 r3 r4 : BitVec 64) : ByteSlice.readLE (sc52Pack5 r0 r1 r2 r3 r4) 0 8 = r0 :=
  readLE_unpack64_zero r0
theorem sc52Pack5_readLE_8 (r0 r1 r2 r3 r4 : BitVec 64) : ByteSlice.readLE (sc52Pack5 r0 r1 r2 r3 r4) 8 8 = r1 :=
  readLE_unpack64_zero r1
theorem sc52Pack5_readLE_16 (r0 r1 r2 r3 r4 : BitVec 64) : ByteSlice.readLE (sc52Pack5 r0 r1 r2 r3 r4) 16 8 = r2 :=
  readLE_unpack64_zero r2
theorem sc52Pack5_readLE_24 (r0 r1 r2 r3 r4 : BitVec 64) : ByteSlice.readLE (sc52Pack5 r0 r1 r2 r3 r4) 24 8 = r3 :=
  readLE_unpack64_zero r3
theorem sc52Pack5_readLE_32 (r0 r1 r2 r3 r4 : BitVec 64) : ByteSlice.readLE (sc52Pack5 r0 r1 r2 r3 r4) 32 8 = r4 :=
  readLE_unpack64_zero r4
theorem sc52ValOfBytes_sc52Pack5 (r0 r1 r2 r3 r4 : BitVec 64) : sc52ValOfBytes (sc52Pack5 r0 r1 r2 r3 r4) = sc52Val r0 r1 r2 r3 r4 := by
  unfold sc52ValOfBytes; rw [sc52Pack5_readLE_0, sc52Pack5_readLE_8, sc52Pack5_readLE_16, sc52Pack5_readLE_24, sc52Pack5_readLE_32]
theorem sc52LimbsBounded_sc52Pack5 (r0 r1 r2 r3 r4 : BitVec 64) (bound : Nat) : sc52LimbsBounded (sc52Pack5 r0 r1 r2 r3 r4) bound ↔ (r0.toNat < bound ∧ r1.toNat < bound ∧ r2.toNat < bound ∧
       r3.toNat < bound ∧ r4.toNat < bound) := by
  unfold sc52LimbsBounded; rw [sc52Pack5_length, sc52Pack5_readLE_0, sc52Pack5_readLE_8, sc52Pack5_readLE_16, sc52Pack5_readLE_24, sc52Pack5_readLE_32]
  simp
theorem sc52Pack5_cells_eq_rest (a : BitVec 64) (r0 r1 r2 r3 r4 : BitVec 64) (rest : SepProp) : ((a ↦₆₄ r0) ∗ ((a + 8#64) ↦₆₄ r1) ∗ ((a + 16#64) ↦₆₄ r2) ∗ ((a + 24#64) ↦₆₄ r3) ∗ ((a + 32#64) ↦₆₄ r4) ∗ rest) =
    ((a ↦ₛ sc52Pack5 r0 r1 r2 r3 r4) ∗ rest) := by
  simp only [← sepConj_assoc, ← sc52Pack5_cells_eq]
theorem stack_swap_slice_ro (sp off v : BitVec 64) (p : BitVec 64) (bs : List (BitVec 8)) (rest : SepProp) :
    (((sp - off) ↦₆₄ v) ∗ ((p ↦ᵣ bs) ∗ rest)) = ((p ↦ᵣ bs) ∗ (((sp - off) ↦₆₄ v) ∗ rest)) :=
  sepConj_left_comm _ _ _
private meta def matchStackCell? (e : Lean.Expr) : Option (Lean.Expr × Nat × Lean.Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``Arm64.pointsTo64 2 then
    let addr := (e.getArg! 0).consumeMData
    let v := e.getArg! 1
    if addr.isAppOfArity ``HSub.hSub 6 then
      let sp := addr.getArg! 4
      match ProofLib.evalBitVecLitPure? (addr.getArg! 5) with
      | some (64, n) => some (sp, n, v)
      | _ => none
    else none
  else none
private meta def matchStackRegion? (e : Lean.Expr) : Option (Lean.Expr × Nat) :=
  let e := e.consumeMData
  if e.isAppOfArity ``Arm64.memRegion 2 then
    let addr := (e.getArg! 0).consumeMData
    let kExpr := (e.getArg! 1).consumeMData
    if addr.isAppOfArity ``HSub.hSub 6 then
      let sp := addr.getArg! 4
      match ProofLib.evalBitVecLitPure? (addr.getArg! 5), kExpr.nat? with
      | some (64, n), some k => if n == k then some (sp, k) else none
      | _, _ => none
    else none
  else none
private meta partial def foldStackEntails (e : Lean.Expr) : Lean.MetaM (Lean.Expr × Lean.Expr) := do
  let e := e.consumeMData
  if e.isAppOfArity ``SepProp.sepConj 2 then
    let P := e.getArg! 0
    let Q := e.getArg! 1
    let (Q', hQ) ← foldStackEntails Q
    let step1 := Lean.mkApp4 (Lean.mkConst ``sepConj_mono_right) P Q Q' hQ
    let mid := Lean.mkApp2 (Lean.mkConst ``SepProp.sepConj) P Q'
    if let (some (sp1, n, v), some (sp2, k)) := (matchStackCell? P, matchStackRegion? Q') then
      if sp1 == sp2 && 8 + k == n && n ≤ 2 ^ 64 then
        let nExpr := Lean.mkNatLit n
        let kExpr := Lean.mkNatLit k
        let hmk ← Lean.Meta.mkEqRefl nExpr
        let hn ← Lean.Meta.mkDecideProof (← Lean.Meta.mkAppM ``LE.le #[nExpr, Lean.mkNatLit (2 ^ 64)])
        let step2 := Lean.mkApp6 (Lean.mkConst ``stack_fold_step) sp1 v nExpr kExpr hmk hn
        let offN := Lean.ToExpr.toExpr (BitVec.ofNat 64 n)
        let subN ← Lean.Meta.mkAppM ``HSub.hSub #[sp1, offN]
        let rhs := Lean.mkApp2 (Lean.mkConst ``Arm64.memRegion) subN nExpr
        let prf := Lean.mkApp5 (Lean.mkConst ``Entails.trans) e mid rhs step1 step2
        return (rhs, prf)
    return (mid, step1)
  else if let some (sp, 8, v) := matchStackCell? e then
    let off8 := Lean.ToExpr.toExpr (8#64)
    let sub8 ← Lean.Meta.mkAppM ``HSub.hSub #[sp, off8]
    let rhs := Lean.mkApp2 (Lean.mkConst ``Arm64.memRegion) sub8 (Lean.mkNatLit 8)
    let prf := Lean.mkApp2 (Lean.mkConst ``stack_fold_last) sp v
    return (rhs, prf)
  else
    return (e, Lean.mkApp (Lean.mkConst ``Entails.refl) e)
local elab "wp_fold_stack" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| wp_conv_pre => simp only [stack_swap_slice, stack_swap_slice_ro, sepConj_assoc]))
  let g ← Lean.Elab.Tactic.getMainGoal
  g.withContext do
    let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
    if !ty.isAppOfArity ``SepWP 6 then return
    let prog := ty.getArg! 0
    let targetPc := ty.getArg! 1
    let s := ty.getArg! 2
    let P := ty.getArg! 3
    let post := ty.getArg! 4
    let oom := ty.getArg! 5
    let (P', hent) ← foldStackEntails P
    let newGoalTy := Lean.mkApp6 (Lean.mkConst ``SepWP) prog targetPc s P' post oom
    let gNew ← Lean.Meta.mkFreshExprMVar newGoalTy .syntheticOpaque (← g.getTag)
    let prf := Lean.mkAppN (Lean.mkConst ``SepWP.weaken_pre)
      #[prog, targetPc, s, P, P', post, oom, hent, gNew]
    g.assign prf
    Lean.Elab.Tactic.replaceMainGoal [gNew.mvarId!]
private theorem mul_umulh_toNat (u v : BitVec 64) :
    (BitVec.setWidth 64 ((BitVec.setWidth 128 u * BitVec.setWidth 128 v) >>> 64)).toNat * 2 ^ 64 + (u * v).toNat = u.toNat * v.toNat ∧ (BitVec.setWidth 64 ((BitVec.setWidth 128 u * BitVec.setWidth 128 v) >>> 64)).toNat ≤ u.toNat := by
  rw [BitVec.setWidth_umulh]; have hu := u.isLt; have hv := v.isLt; have hprod : u.toNat * v.toNat ≤ u.toNat * (2 ^ 64 - 1) := Nat.mul_le_mul_left u.toNat (by omega)
  have hdiv : (u.toNat * v.toNat) / 2 ^ 64 ≤ u.toNat := by
    have : u.toNat * (2 ^ 64 - 1) < (u.toNat + 1) * 2 ^ 64 := by omega
    omega
  rw [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega), BitVec.toNat_mul]
  omega
private theorem mul_umulh_const_toNat (u : BitVec 64) (c : Nat) (hc : c < 2 ^ 64 := by decide) :
    (BitVec.setWidth 64 ((BitVec.setWidth 128 u * BitVec.ofNat 128 c) >>> 64)).toNat * 2 ^ 64 + (u * BitVec.ofNat 64 c).toNat = u.toNat * c ∧ (BitVec.setWidth 64 ((BitVec.setWidth 128 u * BitVec.ofNat 128 c) >>> 64)).toNat ≤ u.toNat := by
  have h128 : BitVec.ofNat 128 c = BitVec.setWidth 128 (BitVec.ofNat 64 c) := by
    apply BitVec.eq_of_toNat_eq
    simp [Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt (by omega : c < 2 ^ 128)]
  rw [h128]; have h := mul_umulh_toNat u (BitVec.ofNat 64 c)
  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc] at h
private theorem adc64_toNat (x y : BitVec 64) : (if (AddWithCarry64 x y false).snd.c = true then 1#64 else 0#64).toNat * 2 ^ 64 + (x + y).toNat = x.toNat + y.toNat := by
  rw [addWithCarry64_false_c]; have hx := x.isLt; have hy := y.isLt
  by_cases h : BitVec.ult (x + y) x = true
  · simp only [h, ↓reduceIte]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, BitVec.toNat_add] at h; rw [BitVec.toNat_add]; change 1 * 2 ^ 64 + (x.toNat + y.toNat) % 2 ^ 64 = x.toNat + y.toNat
    omega
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    rw [BitVec.ult_eq_decide, decide_eq_true_iff, BitVec.toNat_add] at h; rw [BitVec.toNat_add]; change 0 * 2 ^ 64 + (x.toNat + y.toNat) % 2 ^ 64 = x.toNat + y.toNat
    omega
private theorem pair128_add_toNat (hi1 lo1 hi2 lo2 : BitVec 64)
    (hbound : hi1.toNat + hi2.toNat + 1 < 2 ^ 64) : (hi1 + hi2 + if (AddWithCarry64 lo1 lo2 false).snd.c = true then 1#64 else 0#64).toNat * 2 ^ 64 + (lo1 + lo2).toNat = (hi1.toNat * 2 ^ 64 + lo1.toNat) + (hi2.toNat * 2 ^ 64 + lo2.toNat) ∧ (hi1 + hi2 + if (AddWithCarry64 lo1 lo2 false).snd.c = true then 1#64 else 0#64).toNat ≤
      hi1.toNat + hi2.toNat + 1 := by
  have hadc := adc64_toNat lo1 lo2
  have hc : (if (AddWithCarry64 lo1 lo2 false).snd.c = true then 1#64 else 0#64).toNat ≤ 1 := by
    split <;> decide
  have hhi12 : (hi1 + hi2).toNat = hi1.toNat + hi2.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hhi : (hi1 + hi2 + if (AddWithCarry64 lo1 lo2 false).snd.c = true then 1#64 else 0#64).toNat =
      hi1.toNat + hi2.toNat + (if (AddWithCarry64 lo1 lo2 false).snd.c = true then 1#64 else 0#64).toNat := by
    rw [BitVec.toNat_add, hhi12, Nat.mod_eq_of_lt (by omega)]
  omega
theorem mask52_toNat (x : BitVec 64) : (x &&& 4503599627370495#64).toNat = x.toNat % 2 ^ 52 := by
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 52
private theorem mask32_toNat (x : BitVec 64) : (x &&& 4294967295#64).toNat = x.toNat % 2 ^ 32 := by
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 32
private theorem l4_shift_toNat (w : BitVec 64) : (w >>> 20 &&& 4294967295#64).toNat * 2 ^ 64 + (w <<< 44).toNat = (w &&& 4503599627370495#64).toNat * 17592186044416 ∧ (w >>> 20 &&& 4294967295#64).toNat < 2 ^ 32 := by
  rw [mask32_toNat, mask52_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega
private theorem extr52_toNat (hi lo : BitVec 64) : ((hi >>> 52).toNat * 2 ^ 64 + (BitVec.setWidth 64 ((hi ++ lo) >>> 52)).toNat) * 2 ^ 52 + (lo &&& 4503599627370495#64).toNat = hi.toNat * 2 ^ 64 + lo.toNat ∧
    (hi >>> 52).toNat = hi.toNat / 2 ^ 52 := by
  have hhi := hi.isLt; have hlo := lo.isLt; rw [mask52_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ProofLib.BV.Bits.BVLemmas.toNat_append_mul]
  omega
private theorem mont_u_mod52_zero (lo : BitVec 64) : (((lo * 1439961107955227#64 &&& 4503599627370495#64) * 671914833335277#64 + lo) &&& 4503599627370495#64).toNat = 0 := by
  rw [mask52_toNat, BitVec.toNat_add, BitVec.toNat_mul, mask52_toNat, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega
private theorem mont_red_step (hi lo u prod_lo prod_hi carry_lo carry_hi : BitVec 64)
    (hhi : hi.toNat < 2 ^ 56) (hu : u = lo * 1439961107955227#64 &&& 4503599627370495#64) (hplo : prod_lo = u * 671914833335277#64) (hphi : prod_hi = BitVec.setWidth 64 ((BitVec.setWidth 128 u * 671914833335277#128) >>> 64)) (hclo : carry_lo = BitVec.setWidth 64 (((prod_hi + hi + if (AddWithCarry64 prod_lo lo false).snd.c = true then 1#64 else 0#64) ++ (prod_lo + lo)) >>> 52)) (hchi : carry_hi = (prod_hi + hi + if (AddWithCarry64 prod_lo lo false).snd.c = true then 1#64 else 0#64) >>> 52) : (carry_hi.toNat * 2 ^ 64 + carry_lo.toNat) * 2 ^ 52 = (hi.toNat * 2 ^ 64 + lo.toNat) + u.toNat * 671914833335277 ∧ u.toNat < 2 ^ 52 ∧ carry_hi.toNat < 32 := by
  have hu_lt : u.toNat < 2 ^ 52 := by rw [hu, mask52_toNat]; omega
  have hprod : prod_hi.toNat * 2 ^ 64 + prod_lo.toNat = u.toNat * 671914833335277 ∧ prod_hi.toNat ≤ u.toNat := by
    rw [hphi, hplo]; exact mul_umulh_const_toNat u 671914833335277
  have hadd := pair128_add_toNat prod_hi prod_lo hi lo (by omega); have hextr := extr52_toNat (prod_hi + hi + if (AddWithCarry64 prod_lo lo false).snd.c = true then 1#64 else 0#64) (prod_lo + lo); rw [← hchi, ← hclo] at hextr
  have hzero : ((prod_lo + lo) &&& 4503599627370495#64).toNat = 0 := by
    rw [hplo, hu]; exact mont_u_mod52_zero lo
  rw [hzero] at hextr
  generalize (prod_hi + hi + if (AddWithCarry64 prod_lo lo false).snd.c = true then 1#64 else 0#64).toNat = shi at hadd hextr
  generalize (prod_lo + lo).toNat = slo at hadd hextr
  clear hu hplo hphi hclo hchi hzero; rcases hprod with ⟨hprod_eq, hprod_le⟩; rcases hadd with ⟨hadd_eq, hadd_le⟩; rcases hextr with ⟨hextr_eq, hextr_div⟩
  refine ⟨?_, hu_lt, ?_⟩
  · rw [Nat.add_zero] at hextr_eq
    rw [hextr_eq, hadd_eq, hprod_eq, Nat.add_comm]
  · clear hextr_eq hadd_eq hprod_eq
    omega
private theorem mul_pair_52 {x y x' y' hi lo : BitVec 64}
    (hx : x.toNat < 2 ^ 52) (hx_eq : x' = x) (hy_eq : y' = y) (hhi : hi = BitVec.setWidth 64 ((BitVec.setWidth 128 x' * BitVec.setWidth 128 y') >>> 64)) (hlo : lo = x' * y') :
    hi.toNat * 2 ^ 64 + lo.toNat = x.toNat * y.toNat ∧ hi.toNat ≤ 2 ^ 52 - 1 := by
  have h := mul_umulh_toNat x y; rw [hhi, hlo, hx_eq, hy_eq]
  exact ⟨h.1, by omega⟩
private theorem mul_pair_40 {x y x' y' hi lo : BitVec 64}
    (hx : x.toNat < 2 ^ 52) (hy : y.toNat < 2 ^ 52) (hx_eq : x' = x) (hy_eq : y' = y) (hhi : hi = BitVec.setWidth 64 ((BitVec.setWidth 128 x' * BitVec.setWidth 128 y') >>> 64)) (hlo : lo = x' * y') :
    hi.toNat * 2 ^ 64 + lo.toNat = x.toNat * y.toNat ∧ hi.toNat ≤ 2 ^ 40 := by
  have h := mul_umulh_toNat x y; have hxy : x.toNat * y.toNat < 2 ^ 52 * 2 ^ 52 := Nat.mul_lt_mul'' hx hy; rw [hhi, hlo, hx_eq, hy_eq]
  exact ⟨h.1, by omega⟩
private theorem mul_const_pair_52 {x hi lo : BitVec 64} (c : Nat)
    (hx : x.toNat < 2 ^ 52) (hc : c < 2 ^ 52) (hhi : hi = BitVec.setWidth 64 ((BitVec.setWidth 128 x * BitVec.ofNat 128 c) >>> 64)) (hlo : lo = x * BitVec.ofNat 64 c) :
    hi.toNat * 2 ^ 64 + lo.toNat = x.toNat * c ∧ hi.toNat ≤ c := by
  have h := mul_umulh_const_toNat x c (by omega); have hxc : x.toNat * c ≤ 2 ^ 52 * c := Nat.mul_le_mul_right c (by omega); have h1 := h.1; rw [hhi, hlo]
  exact ⟨h1, by omega⟩
private theorem l4_shift_pair {raw lo_in u hi lo : BitVec 64}
    (hraw : raw = lo_in * 1439961107955227#64) (hu : u = lo_in * 1439961107955227#64 &&& 4503599627370495#64) (hhi : hi = raw >>> 20 &&& 4294967295#64) (hlo : lo = raw <<< 44) :
    hi.toNat * 2 ^ 64 + lo.toNat = u.toNat * 17592186044416 ∧ hi.toNat ≤ 2 ^ 32 := by
  rw [hhi, hlo, hu, ← hraw]; have h := l4_shift_toNat raw
  exact ⟨h.1, by omega⟩
private theorem acc128_step_eq {hi1 lo1 hi2 lo2 hi_out lo_out : BitVec 64} {v1 v2 b1 b2 : Nat}
    (h1 : hi1.toNat * 2 ^ 64 + lo1.toNat = v1 ∧ hi1.toNat ≤ b1) (h2 : hi2.toNat * 2 ^ 64 + lo2.toNat = v2 ∧ hi2.toNat ≤ b2) (hb : b1 + b2 + 1 < 2 ^ 64) (hhi : hi_out = hi1 + hi2 + if (AddWithCarry64 lo1 lo2 false).snd.c = true then 1#64 else 0#64) (hlo : lo_out = lo1 + lo2) :
    hi_out.toNat * 2 ^ 64 + lo_out.toNat = v1 + v2 ∧ hi_out.toNat ≤ b1 + b2 + 1 := by
  have hp := pair128_add_toNat hi1 lo1 hi2 lo2 (by omega); rw [hhi, hlo]
  exact ⟨by omega, by omega⟩
private theorem mont_red_step_eq {hi lo u prod_lo prod_hi carry_hi carry_lo : BitVec 64} {S B : Nat}
    (hacc : hi.toNat * 2 ^ 64 + lo.toNat = S ∧ hi.toNat ≤ B) (hb : B < 2 ^ 56) (hu : u = lo * 1439961107955227#64 &&& 4503599627370495#64) (hplo : prod_lo = u * 671914833335277#64) (hphi : prod_hi = BitVec.setWidth 64 ((BitVec.setWidth 128 u * 671914833335277#128) >>> 64)) (hchi : carry_hi = (prod_hi + hi + if (AddWithCarry64 prod_lo lo false).snd.c = true then 1#64 else 0#64) >>> 52) (hclo : carry_lo = BitVec.setWidth 64 (((prod_hi + hi + if (AddWithCarry64 prod_lo lo false).snd.c = true then 1#64 else 0#64) ++ (prod_lo + lo)) >>> 52)) : (carry_hi.toNat * 2 ^ 64 + carry_lo.toNat = carry_hi.toNat * 2 ^ 64 + carry_lo.toNat ∧ carry_hi.toNat ≤ 32) ∧
    u.toNat < 2 ^ 52 ∧ (carry_hi.toNat * 2 ^ 64 + carry_lo.toNat) * 2 ^ 52 = S + u.toNat * 671914833335277 := by
  have hm := mont_red_step hi lo u prod_lo prod_hi carry_lo carry_hi (by omega) hu hplo hphi hclo hchi
  refine ⟨⟨rfl, by omega⟩, hm.2.1, ?_⟩
  rw [hm.1, hacc.1]
private theorem acc128_cinc_step_eq {hi1 lo1 lo2 hi_out lo_out : BitVec 64} {v1 b1 : Nat}
    (h1 : hi1.toNat * 2 ^ 64 + lo1.toNat = v1 ∧ hi1.toNat ≤ b1) (hb : b1 + 1 < 2 ^ 64) (hhi : hi_out = if lo1.ule (lo1 + lo2) = true then hi1 else hi1 + 1#64) (hlo : lo_out = lo1 + lo2) :
    hi_out.toNat * 2 ^ 64 + lo_out.toNat = v1 + lo2.toNat ∧ hi_out.toNat ≤ b1 + 1 := by
  have hlo1 := lo1.isLt; have hlo2 := lo2.isLt; rw [hhi, hlo, BitVec.toNat_add]
  by_cases h : lo1.ule (lo1 + lo2) = true
  · simp only [h, ↓reduceIte]
    rw [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_add] at h
    exact ⟨by omega, by omega⟩
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    rw [BitVec.ule_eq_decide, decide_eq_true_iff, BitVec.toNat_add] at h; rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    exact ⟨by omega, by omega⟩
set_option exponentiation.threshold 512 in
private theorem mont_red_step_hi0_eq {hi lo u prod_lo prod_hi carry_lo : BitVec 64} {S B : Nat}
    (hacc : hi.toNat * 2 ^ 64 + lo.toNat = S ∧ hi.toNat ≤ B) (hb : B ≤ 2 ^ 51 + 2 ^ 50) (hu : u = lo * 1439961107955227#64 &&& 4503599627370495#64) (hplo : prod_lo = u * 671914833335277#64) (hphi : prod_hi = BitVec.setWidth 64 ((BitVec.setWidth 128 u * 671914833335277#128) >>> 64)) (hclo : carry_lo = BitVec.setWidth 64 (((prod_hi + hi + if (AddWithCarry64 prod_lo lo false).snd.c = true then 1#64 else 0#64) ++ (prod_lo + lo)) >>> 52)) :
    u.toNat < 2 ^ 52 ∧ carry_lo.toNat * 2 ^ 52 = S + u.toNat * 671914833335277 := by
  have hm := mont_red_step hi lo u prod_lo prod_hi carry_lo ((prod_hi + hi + if (AddWithCarry64 prod_lo lo false).snd.c = true then 1#64 else 0#64) >>> 52) (by omega) hu hplo hphi hclo rfl
  generalize ((prod_hi + hi + if (AddWithCarry64 prod_lo lo false).snd.c = true then 1#64 else 0#64) >>> 52).toNat = chi at hm
  have hlo_lt := lo.isLt; have hhi_le := hacc.2; have h1 := hm.1; have h2 := hm.2.1; clear hu hplo hphi hclo hm
  have hlt2 : chi * 2 ^ 64 + carry_lo.toNat < 2 ^ 64 := Nat.lt_of_mul_lt_mul_right (a := 2 ^ 52) (by rw [h1]; omega)
  have hchi : chi = 0 := by omega
  rw [hchi, Nat.zero_mul, Nat.zero_add, hacc.1] at h1
  exact ⟨h2, h1⟩
private theorem extr52_step_eq {hi lo n carry_hi carry_lo : BitVec 64} {S B : Nat}
    (hacc : hi.toNat * 2 ^ 64 + lo.toNat = S ∧ hi.toNat ≤ B) (hb : B < 2 ^ 56) (hn : n = lo &&& 4503599627370495#64) (hchi : carry_hi = hi >>> 52) (hclo : carry_lo = BitVec.setWidth 64 ((hi ++ lo) >>> 52)) : (carry_hi.toNat * 2 ^ 64 + carry_lo.toNat = carry_hi.toNat * 2 ^ 64 + carry_lo.toNat ∧ carry_hi.toNat ≤ 32) ∧
    n.toNat < 2 ^ 52 ∧ (carry_hi.toNat * 2 ^ 64 + carry_lo.toNat) * 2 ^ 52 + n.toNat = S := by
  have hextr := extr52_toNat hi lo; rw [← hn, ← hchi, ← hclo, hacc.1] at hextr; have hn_lt : n.toNat < 2 ^ 52 := by rw [hn, mask52_toNat]; omega
  refine ⟨⟨rfl, ?_⟩, hn_lt, hextr.1⟩
  have hdiv := hextr.2; have h1 : hi.toNat ≤ B := hacc.2
  omega
private theorem extr52_last_step_eq {hi lo n3 n4 : BitVec 64} {S B : Nat}
    (hacc : hi.toNat * 2 ^ 64 + lo.toNat = S ∧ hi.toNat ≤ B) (hb : B < 2 ^ 52) (hn3 : n3 = lo &&& 4503599627370495#64) (hn4 : n4 = BitVec.setWidth 64 ((hi ++ lo) >>> 52)) :
    n3.toNat < 2 ^ 52 ∧ n4.toNat * 2 ^ 52 + n3.toNat = S := by
  have hextr := extr52_toNat hi lo; rw [← hn3, ← hn4, hacc.1] at hextr; have hn3_lt : n3.toNat < 2 ^ 52 := by rw [hn3, mask52_toNat]; omega
  have hchi0 : (hi >>> 52).toNat = 0 := by
    have hdiv := hextr.2; have h1 : hi.toNat ≤ B := hacc.2
    omega
  rw [hchi0, Nat.zero_mul, Nat.zero_add] at hextr
  exact ⟨hn3_lt, hextr.1⟩
set_option exponentiation.threshold 512 in
private theorem sc52_schoolbook_mul (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : BitVec 64) :
    (b0.toNat * a0.toNat) + (a1.toNat * b0.toNat + b1.toNat * a0.toNat) * 2 ^ 52 + (b2.toNat * a0.toNat + a1.toNat * b1.toNat + a2.toNat * b0.toNat) * 2 ^ 104 + (a2.toNat * b1.toNat + b2.toNat * a1.toNat + b3.toNat * a0.toNat + a3.toNat * b0.toNat) * 2 ^ 156 + ((b3.toNat * a1.toNat + a2.toNat * b2.toNat) + a3.toNat * b1.toNat + b4.toNat * a0.toNat + a4.toNat * b0.toNat) * 2 ^ 208 + (a3.toNat * b2.toNat + b3.toNat * a2.toNat + b4.toNat * a1.toNat + a4.toNat * b1.toNat) * 2 ^ 260 + (b4.toNat * a2.toNat + a3.toNat * b3.toNat + a4.toNat * b2.toNat) * 2 ^ 312 + (a4.toNat * b3.toNat + b4.toNat * a3.toNat) * 2 ^ 364 +
    (a4.toNat * b4.toNat) * 2 ^ 416 =
    sc52Val a0 a1 a2 a3 a4 * sc52Val b0 b1 b2 b3 b4 := by
  unfold sc52Val
  grind
set_option exponentiation.threshold 512 in
private theorem sc52_schoolbook_mul_rr (t0 t1 t2 t3 t4 : BitVec 64) :
    (t0.toNat * 2764609938444603) + (t1.toNat * 2764609938444603 + t0.toNat * 3768881411696287) * 2 ^ 52 + (t1.toNat * 3768881411696287 + t0.toNat * 1616719297148420 + t2.toNat * 2764609938444603) * 2 ^ 104 + (t1.toNat * 1616719297148420 + t0.toNat * 1087343033131391 + t2.toNat * 3768881411696287 + t3.toNat * 2764609938444603) * 2 ^ 156 + ((t1.toNat * 1087343033131391 + t0.toNat * 10175238647962) + t2.toNat * 1616719297148420 + t3.toNat * 3768881411696287 + t4.toNat * 2764609938444603) * 2 ^ 208 +
    (t2.toNat * 1087343033131391 + t1.toNat * 10175238647962 + t3.toNat * 1616719297148420 + t4.toNat * 3768881411696287) * 2 ^ 260 + (t3.toNat * 1087343033131391 + t2.toNat * 10175238647962 + t4.toNat * 1616719297148420) * 2 ^ 312 + (t4.toNat * 1087343033131391 + t3.toNat * 10175238647962) * 2 ^ 364 + (t4.toNat * 10175238647962) * 2 ^ 416 =
    sc52Val t0 t1 t2 t3 t4 * sc52Val 2764609938444603#64 3768881411696287#64 1616719297148420#64 1087343033131391#64 10175238647962#64 := by
  unfold sc52Val; simp only [BitVec.toNat_ofNat]
  grind
set_option exponentiation.threshold 512 in
private theorem sc52_mont_telescope (u0 u1 u2 u3 u4 n0 n1 n2 n3 n4 : BitVec 64) {c0 c1 c2 c3 c4a c4b1 c4b2 c4b3 c5 c6 c7 c8 C0 C1 C2 C3 C4 C5 C6 C7 P : Nat}
    (hu0 : u0.toNat < 2 ^ 52) (hu1 : u1.toNat < 2 ^ 52) (hu2 : u2.toNat < 2 ^ 52) (hu3 : u3.toNat < 2 ^ 52) (hu4 : u4.toNat < 2 ^ 52) (hP : c0 + c1 * 2 ^ 52 + c2 * 2 ^ 104 + c3 * 2 ^ 156 + (c4a + c4b1 + c4b2 + c4b3) * 2 ^ 208 + c5 * 2 ^ 260 + c6 * 2 ^ 312 + c7 * 2 ^ 364 + c8 * 2 ^ 416 = P) (hP_lt : P < 2 ^ 260 * edOrderL) (h0 : C0 * 2 ^ 52 = c0 + u0.toNat * 671914833335277) (h1 : C1 * 2 ^ 52 = c1 + u0.toNat * 3916664325105025 + C0 + u1.toNat * 671914833335277)
    (h2 : C2 * 2 ^ 52 = c2 + u0.toNat * 1367801 + u1.toNat * 3916664325105025 + C1 + u2.toNat * 671914833335277) (h3 : C3 * 2 ^ 52 = c3 + u1.toNat * 1367801 + u2.toNat * 3916664325105025 + C2 + u3.toNat * 671914833335277) (h4 : C4 * 2 ^ 52 = c4a + u0.toNat * 17592186044416 + c4b1 + c4b2 + c4b3 + u2.toNat * 1367801 + u3.toNat * 3916664325105025 + C3 + u4.toNat * 671914833335277) (h5 : C5 * 2 ^ 52 + n0.toNat = c5 + u1.toNat * 17592186044416 + u3.toNat * 1367801 + u4.toNat * 3916664325105025 + C4)
    (h6 : C6 * 2 ^ 52 + n1.toNat = c6 + u2.toNat * 17592186044416 + u4.toNat * 1367801 + C5) (h7 : C7 * 2 ^ 52 + n2.toNat = c7 + u3.toNat * 17592186044416 + C6) (h8 : n4.toNat * 2 ^ 52 + n3.toNat = c8 + u4.toNat * 17592186044416 + C7) :
    sc52Val n0 n1 n2 n3 n4 < 2 * edOrderL ∧ sc52Val n0 n1 n2 n3 n4 * 2 ^ 260 = P + sc52Val u0 u1 u2 u3 u4 * edOrderL := by
  unfold edOrderL at hP_lt; unfold sc52Val edOrderL
  omega
private theorem sshiftRight_63_eq (x : BitVec 64) : x.sshiftRight 63 = if 2 ^ 63 ≤ x.toNat then 18446744073709551615#64 else 0#64 := by
  have h : x.sshiftRight 63 = if x.msb then 18446744073709551615#64 else 0#64 := (by bv_slice); rw [h, BitVec.msb_eq_decide]
  by_cases hle : 2 ^ 63 ≤ x.toNat <;> simp [hle]
private theorem sub_limb_borrow (n b_prev neg_c s d : BitVec 64) (bin c : Nat)
    (hn : n.toNat < 2 ^ 52) (hbin : (bin = 0 ∧ b_prev = 0#64) ∨ (bin = 1 ∧ b_prev = 18446744073709551615#64)) (hc : c < 2 ^ 52) (hneg : neg_c.toNat = (2 ^ 64 - c) % 2 ^ 64) (hs : s = n + b_prev + neg_c) (hd : d = s &&& 4503599627370495#64) :
    ∃ bout : Nat,
      d.toNat < 2 ^ 52 ∧
      d.toNat + bin + c = n.toNat + bout * 2 ^ 52 ∧
      ((bout = 0 ∧ s.sshiftRight 63 = 0#64 ∧ s >>> 63 = 0#64 ∧ s = d) ∨
       (bout = 1 ∧ s.sshiftRight 63 = 18446744073709551615#64 ∧ s >>> 63 = 1#64)) := by
  refine ⟨if n.toNat < bin + c then 1 else 0, ?_⟩
  have hs_toNat : s.toNat = (n.toNat + b_prev.toNat + neg_c.toNat) % 2 ^ 64 := by
    rw [hs, BitVec.toNat_add, BitVec.toNat_add]
    omega
  have hd_toNat : d.toNat = s.toNat % 2 ^ 52 := (by rw [hd, mask52_toNat]); have hss : s.sshiftRight 63 = if 2 ^ 63 ≤ s.toNat then 18446744073709551615#64 else 0#64 := sshiftRight_63_eq s
  have hlsr : (s >>> 63).toNat = s.toNat / 2 ^ 63 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hs_lt : s.toNat < 2 ^ 64 := s.isLt; rcases hbin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hbp : (0#64).toNat = 0 := rfl
    by_cases hlt : n.toNat < 0 + c
    · simp only [hlt, ↓reduceIte]
      have hs_ge : 2 ^ 63 ≤ s.toNat := by omega
      have hlsr_eq : s >>> 63 = 1#64 := by
        apply BitVec.eq_of_toNat_eq; change (s >>> 63).toNat = 1; omega
      refine ⟨by omega, by omega, Or.inr ⟨ trivial, ?_, hlsr_eq⟩⟩
      simp [hss, hs_ge]
    · simp only [hlt, ↓reduceIte]
      have hs_not_ge : ¬(2 ^ 63 ≤ s.toNat) := by omega
      have hlsr_eq : s >>> 63 = 0#64 := by
        apply BitVec.eq_of_toNat_eq; change (s >>> 63).toNat = 0; omega
      have hsd : s = d := by apply BitVec.eq_of_toNat_eq; omega
      refine ⟨by omega, by omega, Or.inl ⟨trivial, ?_, hlsr_eq, hsd⟩⟩
      simp [hss, hs_not_ge]
  · have hbp : (18446744073709551615#64).toNat = 2 ^ 64 - 1 := rfl
    by_cases hlt : n.toNat < 1 + c
    · simp only [hlt, ↓reduceIte]
      have hs_ge : 2 ^ 63 ≤ s.toNat := by omega
      have hlsr_eq : s >>> 63 = 1#64 := by
        apply BitVec.eq_of_toNat_eq; change (s >>> 63).toNat = 1; omega
      refine ⟨by omega, by omega, Or.inr ⟨trivial, ?_, hlsr_eq⟩⟩
      simp [hss, hs_ge]
    · simp only [hlt, ↓reduceIte]
      have hs_not_ge : ¬(2 ^ 63 ≤ s.toNat) := by omega
      have hlsr_eq : s >>> 63 = 0#64 := by
        apply BitVec.eq_of_toNat_eq; change (s >>> 63).toNat = 0; omega
      have hsd : s = d := by apply BitVec.eq_of_toNat_eq; omega
      refine ⟨by omega, by omega, Or.inl ⟨trivial, ?_, hlsr_eq, hsd⟩⟩
      simp [hss, hs_not_ge]
private theorem and_mask52_of_lt {x : BitVec 64} (hx : x.toNat < 2 ^ 52) : x &&& 4503599627370495#64 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [mask52_toNat, Nat.mod_eq_of_lt hx]
private theorem lsr52_of_lt {x : BitVec 64} (hx : x.toNat < 2 ^ 52) : x >>> 52 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; change x.toNat / 2 ^ 52 = 0
  omega
private theorem add_limb_carry (d n : BitVec 64) (bin c bout : Nat)
    (hn : n.toNat < 2 ^ 52) (hbin : bin ≤ 1) (hc : c < 2 ^ 52) (hbout : bout ≤ 1) (heq : d.toNat + bin + c = n.toNat + bout * 2 ^ 52) : (d + BitVec.ofNat 64 c + BitVec.ofNat 64 bin) &&& 4503599627370495#64 = n ∧
    (d + BitVec.ofNat 64 c + BitVec.ofNat 64 bin) >>> 52 = BitVec.ofNat 64 bout := by
  have hd := d.isLt; have hsum_toNat : (d + BitVec.ofNat 64 c + BitVec.ofNat 64 bin).toNat =
      n.toNat + bout * 2 ^ 52 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [mask52_toNat, hsum_toNat]
    omega
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hsum_toNat, BitVec.toNat_ofNat]
    omega
private theorem neg_zero_64_eq : -BitVec.setWidth 64 (BitVec.zeroExtend 8 0#64) = 0#64 := by
  apply BitVec.eq_of_toNat_eq; rfl
private theorem neg_one_64_and (x : BitVec 64) : -BitVec.setWidth 64 (BitVec.zeroExtend 8 1#64) &&& x = x := by
  have hall : -BitVec.setWidth 64 (BitVec.zeroExtend 8 1#64) = BitVec.allOnes 64 := by
    apply BitVec.eq_of_toNat_eq; rfl
  rw [hall, BitVec.allOnes_and]
set_option exponentiation.threshold 512 in
private theorem sc52_borrow_val_toNat
    (n0 n1 n2 n3 n4 d0 d1 d2 d3 d4 : BitVec 64) (b0 b1 b2 b3 b4 : Nat) (hn_val : sc52Val n0 n1 n2 n3 n4 < 2 * edOrderL) (hd0_lt : d0.toNat < 2 ^ 52) (hd1_lt : d1.toNat < 2 ^ 52) (hd2_lt : d2.toNat < 2 ^ 52) (hd3_lt : d3.toNat < 2 ^ 52) (hd4_lt : d4.toNat < 2 ^ 52) (hd0_eq : d0.toNat + 0 + 671914833335277 = n0.toNat + b0 * 2 ^ 52) (hd1_eq : d1.toNat + b0 + 3916664325105025 = n1.toNat + b1 * 2 ^ 52) (hd2_eq : d2.toNat + b1 + 1367801 = n2.toNat + b2 * 2 ^ 52) (hd3_eq : d3.toNat + b2 + 0 = n3.toNat + b3 * 2 ^ 52)
    (hd4_eq : d4.toNat + b3 + 17592186044416 = n4.toNat + b4 * 2 ^ 52) :
    n4.toNat < 2 ^ 52 ∧ (b4 = 0 → sc52Val d0 d1 d2 d3 d4 < edOrderL ∧ sc52Val d0 d1 d2 d3 d4 + 1 * edOrderL = sc52Val n0 n1 n2 n3 n4) ∧ (b4 = 1 → sc52Val n0 n1 n2 n3 n4 < edOrderL) := by
  unfold sc52Val edOrderL at hn_val ⊢
  omega
set_option exponentiation.threshold 512 in
private theorem sc52_limb4_lt (n0 n1 n2 n3 n4 : BitVec 64) (hn_val : sc52Val n0 n1 n2 n3 n4 < 2 * edOrderL) : n4.toNat < 2 ^ 52 := by
  unfold sc52Val edOrderL at hn_val
  omega
private theorem sub_1367801_eq (x : BitVec 64) : x - 1367801#64 = x + 18446744073708183815#64 := by
  rw [BitVec.sub_eq_add_neg]; rfl
private theorem s4_cancel_0 (n4 : BitVec 64) : n4 + 0#64 + 18446726481523507200#64 + 17592186044416#64 + BitVec.ofNat 64 0 = n4 := by
  rw [BitVec.add_zero, BitVec.add_zero, BitVec.add_assoc]; have h : 18446726481523507200#64 + 17592186044416#64 = 0#64 := (by decide); rw [h, BitVec.add_zero]
private theorem s4_cancel_1 (n4 : BitVec 64) : n4 + 18446744073709551615#64 + 18446726481523507200#64 + 17592186044416#64 + BitVec.ofNat 64 1 = n4 := by
  rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]; have h : 18446744073709551615#64 + (18446726481523507200#64 + (17592186044416#64 + BitVec.ofNat 64 1)) = 0#64 := by decide
  rw [h, BitVec.add_zero]
set_option exponentiation.threshold 512 in
theorem sc52_cond_sub_l
    (n0 n1 n2 n3 n4 d0 s1 d1 s2 d2 s3 d3 s4 b4_bv w0 r0 r1 r2 r3 r4 : BitVec 64) (hn0 : n0.toNat < 2 ^ 52) (hn1 : n1.toNat < 2 ^ 52) (hn2 : n2.toNat < 2 ^ 52) (hn3 : n3.toNat < 2 ^ 52) (hn_val : sc52Val n0 n1 n2 n3 n4 < 2 * edOrderL) (hd0 : d0 = (n0 + 18446072158876216339#64) &&& 4503599627370495#64) (hs1 : s1 = n1 + (n0 + 18446072158876216339#64).sshiftRight 63 + 18442827409384446591#64) (hd1 : d1 = s1 &&& 4503599627370495#64) (hs2 : s2 = n2 + s1.sshiftRight 63 - 1367801#64) (hd2 : d2 = s2 &&& 4503599627370495#64)
    (hs3 : s3 = n3 + s2.sshiftRight 63) (hd3 : d3 = s3 &&& 4503599627370495#64) (hs4 : s4 = n4 + s3.sshiftRight 63 + 18446726481523507200#64) (hb4 : b4_bv = s4 >>> 63) (hpost : BitVec.zeroExtend 8 w0 = BitVec.zeroExtend 8 b4_bv) (hr0 : r0 = (d0 + (-BitVec.setWidth 64 (BitVec.zeroExtend 8 b4_bv) &&& 671914833335277#64)) &&& 4503599627370495#64) (hr1 : r1 = ((-BitVec.setWidth 64 (BitVec.zeroExtend 8 b4_bv) &&& 3916664325105025#64) + (d0 + (-BitVec.setWidth 64 (BitVec.zeroExtend 8 b4_bv) &&& 671914833335277#64)) >>> 52 + d1) &&& 4503599627370495#64)
    (hr2 : r2 = (d2 + (-BitVec.setWidth 64 (BitVec.zeroExtend 8 b4_bv) &&& 1367801#64) + ((-BitVec.setWidth 64 (BitVec.zeroExtend 8 b4_bv) &&& 3916664325105025#64) + (d0 + (-BitVec.setWidth 64 (BitVec.zeroExtend 8 b4_bv) &&& 671914833335277#64)) >>> 52 + d1) >>> 52) &&& 4503599627370495#64) (hr3 : r3 = (d3 + (d2 + (-BitVec.setWidth 64 (BitVec.zeroExtend 8 b4_bv) &&& 1367801#64) + ((-BitVec.setWidth 64 (BitVec.zeroExtend 8 b4_bv) &&& 3916664325105025#64) + (d0 + (-BitVec.setWidth 64 (BitVec.zeroExtend 8 b4_bv) &&& 671914833335277#64)) >>> 52 + d1) >>> 52) >>> 52) &&& 4503599627370495#64) (hr4 : r4 = (s4 + (-BitVec.setWidth 64 (BitVec.setWidth 8 w0) &&& 17592186044416#64) + (d3 + (d2 + (-BitVec.setWidth 64 (BitVec.setWidth 8 w0) &&& 1367801#64) + ((-BitVec.setWidth 64 (BitVec.setWidth 8 w0) &&& 3916664325105025#64) + (d0 + (-BitVec.setWidth 64 (BitVec.setWidth 8 w0) &&& 671914833335277#64)) >>> 52 + d1) >>> 52) >>> 52) >>> 52) &&& 4503599627370495#64) :
    r0.toNat < 2 ^ 52 ∧ r1.toNat < 2 ^ 52 ∧ r2.toNat < 2 ^ 52 ∧ r3.toNat < 2 ^ 52 ∧ r4.toNat < 2 ^ 52 ∧ sc52Val r0 r1 r2 r3 r4 < edOrderL ∧ ∃ q : Nat, q ≤ 1 ∧ sc52Val r0 r1 r2 r3 r4 + q * edOrderL = sc52Val n0 n1 n2 n3 n4 := by
  have hn4 : n4.toNat < 2 ^ 52 := sc52_limb4_lt n0 n1 n2 n3 n4 hn_val; have hw0_eq : BitVec.setWidth 8 w0 = BitVec.zeroExtend 8 b4_bv := hpost; rw [hw0_eq] at hr4; obtain ⟨b0, hd0_lt, hd0_eq, hb0_cases⟩ := sub_limb_borrow n0 0#64 18446072158876216339#64 (n0 + 18446072158876216339#64) d0 0 671914833335277 hn0 (Or.inl ⟨rfl, rfl⟩) (by decide) rfl (by rw [BitVec.add_zero]) hd0; have hb0_bin : (b0 = 0 ∧ (n0 + 18446072158876216339#64).sshiftRight 63 = 0#64) ∨
      (b0 = 1 ∧ (n0 + 18446072158876216339#64).sshiftRight 63 = 18446744073709551615#64) := by
    rcases hb0_cases with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  obtain ⟨b1, hd1_lt, hd1_eq, hb1_cases⟩ := sub_limb_borrow n1 ((n0 + 18446072158876216339#64).sshiftRight 63) 18442827409384446591#64 s1 d1 b0 3916664325105025 hn1 hb0_bin (by decide) rfl hs1 hd1; have hb1_bin : (b1 = 0 ∧ s1.sshiftRight 63 = 0#64) ∨
      (b1 = 1 ∧ s1.sshiftRight 63 = 18446744073709551615#64) := by
    rcases hb1_cases with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  obtain ⟨b2, hd2_lt, hd2_eq, hb2_cases⟩ := sub_limb_borrow n2 (s1.sshiftRight 63) 18446744073708183815#64 s2 d2 b1 1367801 hn2 hb1_bin (by decide) rfl (by rw [hs2, sub_1367801_eq]) hd2; have hb2_bin : (b2 = 0 ∧ s2.sshiftRight 63 = 0#64) ∨
      (b2 = 1 ∧ s2.sshiftRight 63 = 18446744073709551615#64) := by
    rcases hb2_cases with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  obtain ⟨b3, hd3_lt, hd3_eq, hb3_cases⟩ := sub_limb_borrow n3 (s2.sshiftRight 63) 0#64 s3 d3 b2 0 hn3 hb2_bin (by decide) rfl (by rw [hs3, BitVec.add_zero]) hd3; have hb3_bin : (b3 = 0 ∧ s3.sshiftRight 63 = 0#64) ∨
      (b3 = 1 ∧ s3.sshiftRight 63 = 18446744073709551615#64) := by
    rcases hb3_cases with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  obtain ⟨b4, hd4_lt, hd4_eq, hb4_cases⟩ := sub_limb_borrow n4 (s3.sshiftRight 63) 18446726481523507200#64 s4 (s4 &&& 4503599627370495#64) b3 17592186044416 hn4 hb3_bin (by decide) rfl hs4 rfl; have hval := sc52_borrow_val_toNat n0 n1 n2 n3 n4 d0 d1 d2 d3 (s4 &&& 4503599627370495#64) b0 b1 b2 b3 b4 hn_val hd0_lt hd1_lt hd2_lt hd3_lt hd4_lt hd0_eq hd1_eq hd2_eq hd3_eq hd4_eq
  have hb0_le : b0 ≤ 1 := (by rcases hb0_bin with ⟨h, _⟩ | ⟨h, _⟩ <;> omega); have hb1_le : b1 ≤ 1 := (by rcases hb1_bin with ⟨h, _⟩ | ⟨h, _⟩ <;> omega)
  have hb2_le : b2 ≤ 1 := (by rcases hb2_bin with ⟨h, _⟩ | ⟨h, _⟩ <;> omega); have hb3_le : b3 ≤ 1 := (by rcases hb3_bin with ⟨h, _⟩ | ⟨h, _⟩ <;> omega)
  rcases hb4_cases with ⟨hb4_0, _, hlsr4, _⟩ | ⟨hb4_1, _, hlsr4⟩
  · have hb4_bv : b4_bv = 0#64 := by rw [hb4, hlsr4]
    rw [hb4_bv] at hr0 hr1 hr2 hr3 hr4; rw [neg_zero_64_eq] at hr0 hr1 hr2 hr3 hr4; simp only [BitVec.zero_and, BitVec.add_zero, BitVec.zero_add] at hr0 hr1 hr2 hr3 hr4; have hc0 : d0 >>> 52 = 0#64 := lsr52_of_lt hd0_lt; rw [hc0, BitVec.zero_add] at hr1 hr2 hr3 hr4; have hc1 : d1 >>> 52 = 0#64 := lsr52_of_lt hd1_lt; rw [hc1, BitVec.add_zero] at hr2 hr3 hr4; have hc2 : d2 >>> 52 = 0#64 := lsr52_of_lt hd2_lt; rw [hc2, BitVec.add_zero] at hr3 hr4; have hc3 : d3 >>> 52 = 0#64 := lsr52_of_lt hd3_lt; rw [hc3, BitVec.add_zero] at hr4
    have hr0_eq : r0 = d0 := by rw [hr0, and_mask52_of_lt hd0_lt]
    have hr1_eq : r1 = d1 := by rw [hr1, and_mask52_of_lt hd1_lt]
    have hr2_eq : r2 = d2 := by rw [hr2, and_mask52_of_lt hd2_lt]
    have hr3_eq : r3 = d3 := by rw [hr3, and_mask52_of_lt hd3_lt]
    rw [hr0_eq, hr1_eq, hr2_eq, hr3_eq, hr4]; have hv0 := hval.2.1 hb4_0
    exact ⟨hd0_lt, hd1_lt, hd2_lt, hd3_lt, hd4_lt, hv0.1, 1, Nat.le_refl 1, hv0.2⟩
  · have hb4_bv : b4_bv = 1#64 := by rw [hb4, hlsr4]
    rw [hb4_bv] at hr0 hr1 hr2 hr3 hr4; simp only [neg_one_64_and] at hr0 hr1 hr2 hr3 hr4; have hadd0 := add_limb_carry d0 n0 0 671914833335277 b0 hn0 (by omega) (by decide) hb0_le hd0_eq; change (d0 + 671914833335277#64 + 0#64) &&& 4503599627370495#64 = n0 ∧
      (d0 + 671914833335277#64 + 0#64) >>> 52 = BitVec.ofNat 64 b0 at hadd0
    rw [BitVec.add_zero] at hadd0
    have hr0_eq : r0 = n0 := by rw [hr0, hadd0.1]
    rw [hadd0.2] at hr1 hr2 hr3 hr4; have hcomm1 : 3916664325105025#64 + BitVec.ofNat 64 b0 + d1 =
        d1 + 3916664325105025#64 + BitVec.ofNat 64 b0 := by
      rw [BitVec.add_comm (3916664325105025#64 + BitVec.ofNat 64 b0) d1, ← BitVec.add_assoc]
    rw [hcomm1] at hr1 hr2 hr3 hr4; have hadd1 := add_limb_carry d1 n1 b0 3916664325105025 b1 hn1 hb0_le (by decide) hb1_le hd1_eq
    have hr1_eq : r1 = n1 := by rw [hr1, hadd1.1]
    rw [hadd1.2] at hr2 hr3 hr4; have hadd2 := add_limb_carry d2 n2 b1 1367801 b2 hn2 hb1_le (by decide) hb2_le hd2_eq
    have hr2_eq : r2 = n2 := by rw [hr2, hadd2.1]
    rw [hadd2.2] at hr3 hr4; have hadd3 := add_limb_carry d3 n3 b2 0 b3 hn3 hb2_le (by decide) hb3_le hd3_eq; change (d3 + 0#64 + BitVec.ofNat 64 b2) &&& 4503599627370495#64 = n3 ∧
      (d3 + 0#64 + BitVec.ofNat 64 b2) >>> 52 = BitVec.ofNat 64 b3 at hadd3
    rw [BitVec.add_zero] at hadd3
    have hr3_eq : r3 = n3 := by rw [hr3, hadd3.1]
    rw [hadd3.2] at hr4
    have hs4_add : s4 + 17592186044416#64 + BitVec.ofNat 64 b3 = n4 := by
      rcases hb3_bin with ⟨rfl, hs3_ss⟩ | ⟨rfl, hs3_ss⟩
      · rw [hs4, hs3_ss, s4_cancel_0]
      · rw [hs4, hs3_ss, s4_cancel_1]
    have hr4_eq : r4 = n4 := by rw [hr4, hs4_add, and_mask52_of_lt hn4]
    rw [hr0_eq, hr1_eq, hr2_eq, hr3_eq, hr4_eq]
    exact ⟨hn0, hn1, hn2, hn3, hn4, hval.2.2 hb4_1, 0, Nat.zero_le 1, by rw [Nat.zero_mul, Nat.add_zero]⟩
private theorem mod_eq_of_mont {R q N K P U L : Nat} (hq : R + q * L = N) (hN : N * K = P + U * L) : R * K % L = P % L := by
  have h1 : R * K + q * K * L = P + U * L := by
    calc R * K + q * K * L
      _ = R * K + q * L * K := by rw [Nat.mul_assoc q K L, Nat.mul_comm K L, ← Nat.mul_assoc q L K]
      _ = (R + q * L) * K := by rw [Nat.add_mul]
      _ = N * K := by rw [hq]
      _ = P + U * L := hN
  have h2 := congrArg (· % L) h1; rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right] at h2
  exact h2
set_option exponentiation.threshold 512 in
theorem sc52_mul_bound_of_right_lt_l {a b : Nat} (ha : a < 2 ^ 260) (hb : b < edOrderL) : a * b < 2 ^ 260 * edOrderL := by
  have h1 : a * b ≤ a * edOrderL := Nat.mul_le_mul_left a (Nat.le_of_lt hb); have h2 : a * edOrderL < 2 ^ 260 * edOrderL := Nat.mul_lt_mul_of_pos_right ha (by unfold edOrderL; omega)
  omega
set_option exponentiation.threshold 512 in
theorem sc52_mul_bound_of_lt_256 {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) : a * b < 2 ^ 260 * edOrderL := by
  have h1 : a * b < 2 ^ 256 * 2 ^ 256 := Nat.mul_lt_mul'' ha hb; unfold edOrderL
  omega
set_option exponentiation.threshold 512 in
private theorem sc52_mul_rr_bound {T : Nat} (hT : T < edOrderL) : T * sc52Val 2764609938444603#64 3768881411696287#64 1616719297148420#64
      1087343033131391#64 10175238647962#64 < 2 ^ 260 * edOrderL :=
  sc52_mul_bound_of_right_lt_l (by unfold edOrderL at hT; omega) (by decide)
set_option exponentiation.threshold 512 in
private theorem cancel_mont_rr {A_B T Out : Nat}
    (hOut_lt : Out < edOrderL) (h1 : T * 2 ^ 260 % edOrderL = A_B % edOrderL) (h2 : Out * 2 ^ 260 % edOrderL = T * sc52Val 2764609938444603#64 3768881411696287#64 1616719297148420#64 1087343033131391#64 10175238647962#64 % edOrderL) :
    Out = A_B % edOrderL := by
  let inv := 5706410653605570882457795059301885719620630590890452783038400561109479083972
  have hrr : sc52Val 2764609938444603#64 3768881411696287#64 1616719297148420#64 1087343033131391#64 10175238647962#64 % edOrderL = (2 ^ 260 * 2 ^ 260) % edOrderL := by decide
  have hinv : (2 ^ 260 * inv) % edOrderL = 1 := by decide
  have h2' : (Out * 2 ^ 260) % edOrderL = (A_B * 2 ^ 260) % edOrderL := by
    rw [h2, ← Nat.mul_mod_mod, hrr, Nat.mul_mod_mod, ← Nat.mul_assoc, ← Nat.mod_mul_mod, h1, Nat.mod_mul_mod]
  have h3 : (Out * (2 ^ 260 * inv)) % edOrderL = (A_B * (2 ^ 260 * inv)) % edOrderL := by
    rw [← Nat.mul_assoc, ← Nat.mod_mul_mod, h2', Nat.mod_mul_mod, Nat.mul_assoc]
  rw [← Nat.mul_mod_mod, hinv, Nat.mul_one, Nat.mod_eq_of_lt hOut_lt] at h3; rw [← Nat.mul_mod_mod, hinv, Nat.mul_one] at h3
  exact h3
set_option maxHeartbeats 800000 in set_option exponentiation.threshold 512 in
theorem sc52_montgomery_mul_core_ok : Sc52MontgomeryMulCoreOk := by
  intro _
  apply dalekCaller_ok dalekCliPC06 dalekCliPl06
  intro b hb hbase
  wp_init
  obtain ⟨ow0, ow1, ow2, ow3, ow4, hout_cells⟩ := exists_cells_of_length_40 h_5; rw [hout_cells a_1]; have ha_len : a_4.length = 40 := h_6.1; have hb_len : a_rest.length = 40 := h_7.1; wp_cut_codeLoaded; wp_sym_steps 65; wp_checkpoint; wp_sym_steps 28; wp_checkpoint; wp_sym_steps 16; wp_checkpoint; wp_sym_steps 14; wp_checkpoint; wp_sym_steps 11; wp_checkpoint; wp_sym_steps 10; wp_checkpoint; wp_sym_steps 10; wp_checkpoint; wp_sym_steps 22; wp_checkpoint; wp_sym_steps 18; wp_checkpoint; wp_sym_steps 20; wp_checkpoint; wp_sym_steps 9; wp_checkpoint; wp_sym_steps 28; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 21; wp_checkpoint; wp_sym_steps 11; wp_checkpoint; wp_sym_steps 6; wp_checkpoint
  wp_steps 1; wp_dalek_call black_box_u8_ok
  wp_sym_steps; wp_checkpoint
  wp_conv_pre => simp only [sc52Pack5_cells_eq_rest]
  wp_fold_stack; have h_res :
      sc52LimbsBounded (sc52Pack5 v_cp_170 v_cp_171 v_cp_167 v_cp_168 v_cp_172) (2 ^ 52) ∧
      sc52ValOfBytes (sc52Pack5 v_cp_170 v_cp_171 v_cp_167 v_cp_168 v_cp_172) < edOrderL ∧
      sc52ValOfBytes (sc52Pack5 v_cp_170 v_cp_171 v_cp_167 v_cp_168 v_cp_172) * 2 ^ 260 % edOrderL =
        sc52ValOfBytes a_4 * sc52ValOfBytes a_rest % edOrderL := by
    rcases h_6 with ⟨_, ha0, ha1, ha2, ha3, ha4⟩; rcases h_7 with ⟨_, hb0, hb1, hb2, hb3, hb4⟩; have hp_b0a0 := mul_pair_52 hb0 rfl rfl hv_cp_28 hv_cp_8; have hp_a1b0 := mul_pair_52 ha1 rfl rfl hv_cp_36 hv_cp_10; have hp_b1a0 := mul_pair_52 hb1 rfl rfl hv_cp_9 hv_cp_37; have hp_b2a0 := mul_pair_52 hb2 rfl rfl hv_cp_31 hv_cp_13; have hp_a1b1 := mul_pair_52 ha1 rfl rfl hv_cp_12 hv_cp_11; have hp_a2b0 := mul_pair_52 ha2 rfl rfl hv_cp_26 hv_cp_14; have hp_a2b1 := mul_pair_52 ha2 rfl rfl hv_cp_25 hv_cp_27; have hp_b2a1 := mul_pair_52 hb2 hv_cp_5 hv_cp_0 hv_cp_76 hv_cp_79; have hp_b3a0 := mul_pair_52 hb3 rfl rfl hv_cp_30 hv_cp_29; have hp_a3b0 := mul_pair_52 ha3 hv_cp_4 hv_cp_1 hv_cp_88 hv_cp_82; have hp_b3a1 := mul_pair_52 hb3 rfl rfl hv_cp_33 hv_cp_32; have hp_a2b2 := mul_pair_52 ha2 hv_cp_3 hv_cp_5 hv_cp_58 hv_cp_59; have hp_a3b1 := mul_pair_52 ha3 hv_cp_4 hv_cp_2 hv_cp_94 hv_cp_106; have hp_b4a0 := mul_pair_52 hb4 rfl rfl hv_cp_35 hv_cp_34; have hp_a4b0 := mul_pair_52 ha4 hv_cp_7 hv_cp_1 hv_cp_95 hv_cp_96; have hp_a3b2 := mul_pair_52 ha3 hv_cp_4 hv_cp_5 hv_cp_116 hv_cp_120
    have hp_b3a2 := mul_pair_52 hb3 rfl rfl hv_cp_39 hv_cp_38; have hp_b4a1 := mul_pair_52 hb4 hv_cp_6 hv_cp_0 hv_cp_108 hv_cp_115; have hp_a4b1 := mul_pair_52 ha4 hv_cp_7 hv_cp_2 hv_cp_121 hv_cp_125; have hp_b4a2 := mul_pair_52 hb4 rfl rfl hv_cp_24 hv_cp_16; have hp_a3b3 := mul_pair_52 ha3 rfl rfl hv_cp_17 hv_cp_15; have hp_a4b2 := mul_pair_52 ha4 rfl rfl hv_cp_21 hv_cp_20; have hp_a4b3 := mul_pair_52 ha4 rfl rfl hv_cp_18 hv_cp_19; have hp_b4a3 := mul_pair_52 hb4 rfl rfl hv_cp_23 hv_cp_22; have hp_a4b4 := mul_pair_40 ha4 hb4 hv_cp_7 hv_cp_6 hv_cp_146 hv_cp_145; rw [← hv_cp_43] at hv_cp_45 hv_cp_48; have st0 := mont_red_step_eq hp_b0a0 (by decide) hv_cp_43 hv_cp_45 hv_cp_48 hv_cp_55 hv_cp_54; have hu0 := st0.2.1; have hc1_1 := acc128_step_eq hp_a1b0 hp_b1a0 (by decide) hv_cp_42 hv_cp_40; have hu0_l1 := mul_const_pair_52 3916664325105025 hu0 (by decide) hv_cp_53 hv_cp_52; have hc1_2 := acc128_step_eq hc1_1 hu0_l1 (by decide) hv_cp_60 hv_cp_68; rw [← hv_cp_61] at hv_cp_62 hv_cp_66 hv_cp_67; rw [← hv_cp_66] at hv_cp_67; rw [← hv_cp_60] at hv_cp_63
    rw [← hv_cp_68] at hv_cp_63 hv_cp_61; have hc1_3 := acc128_step_eq hc1_2 st0.1 (by decide) hv_cp_63 hv_cp_61; have st1 := mont_red_step_eq hc1_3 (by decide) hv_cp_66 hv_cp_67 rfl hv_cp_74 hv_cp_72; have hu1 := st1.2.1; have hc2_1 := acc128_step_eq hp_b2a0 hp_a1b1 (by decide) rfl rfl; have hc2_2 := acc128_step_eq hc2_1 hp_a2b0 (by decide) hv_cp_44 hv_cp_51; have hu0_l2 := mul_const_pair_52 1367801 hu0 (by decide) hv_cp_64 hv_cp_65; have hc2_3 := acc128_step_eq hc2_2 hu0_l2 (by decide) hv_cp_73 hv_cp_77; have hu1_l1 := mul_const_pair_52 3916664325105025 hu1 (by decide) hv_cp_71 hv_cp_70; rw [← hv_cp_77, ← hv_cp_70] at hv_cp_75; have hc2_4 := acc128_step_eq hc2_3 hu1_l1 (by decide) rfl hv_cp_75; have hc2_5 := acc128_step_eq hc2_4 st1.1 (by decide) hv_cp_80 hv_cp_78; rw [← hv_cp_78] at hv_cp_81 hv_cp_84 hv_cp_85 hv_cp_86; rw [← hv_cp_84] at hv_cp_85 hv_cp_86; have st2 := mont_red_step_eq hc2_5 (by decide) hv_cp_84 hv_cp_85 hv_cp_86 hv_cp_91 hv_cp_90; have hu2 := st2.2.1; have hc3_1 := acc128_step_eq hp_a2b1 hp_b2a1 (by decide) rfl hv_cp_92; have hc3_2 := acc128_step_eq hc3_1 hp_b3a0 (by decide) rfl rfl
    have hc3_3 := acc128_step_eq hc3_2 hp_a3b0 (by decide) rfl rfl; have hu1_l2 := mul_const_pair_52 1367801 hu1 (by decide) hv_cp_83 hv_cp_87; have hc3_4 := acc128_step_eq hc3_3 hu1_l2 (by decide) rfl rfl; have hu2_l1 := mul_const_pair_52 3916664325105025 hu2 (by decide) hv_cp_93 hv_cp_89; have hc3_5 := acc128_step_eq hc3_4 hu2_l1 (by decide) rfl rfl; have hc3_6 := acc128_step_eq hc3_5 st2.1 (by decide) hv_cp_100 hv_cp_98; rw [← hv_cp_98] at hv_cp_99 hv_cp_103 hv_cp_104; rw [← hv_cp_103] at hv_cp_104; have st3 := mont_red_step_eq hc3_6 (by decide) hv_cp_103 hv_cp_104 rfl hv_cp_112 hv_cp_109; have hu3 := st3.2.1; have hc4_1 := acc128_step_eq hp_b3a1 hp_a2b2 (by decide) rfl rfl; have hu0_l4 := l4_shift_pair hv_cp_41 hv_cp_43 rfl rfl; have hc4_2 := acc128_step_eq hc4_1 hu0_l4 (by decide) hv_cp_110 hv_cp_114; rw [← hv_cp_114, ← hv_cp_106] at hv_cp_113; have hc4_3 := acc128_step_eq hc4_2 hp_a3b1 (by decide) rfl hv_cp_113; have hc4_4 := acc128_step_eq hc4_3 hp_b4a0 (by decide) rfl rfl; have hc4_5 := acc128_step_eq hc4_4 hp_a4b0 (by decide) rfl rfl; have hu2_l2 := mul_const_pair_52 1367801 hu2 (by decide) hv_cp_101 hv_cp_102
    have hc4_6 := acc128_step_eq hc4_5 hu2_l2 (by decide) rfl rfl; have hu3_l1 := mul_const_pair_52 3916664325105025 hu3 (by decide) hv_cp_111 hv_cp_107; have hc4_7 := acc128_step_eq hc4_6 hu3_l1 (by decide) rfl rfl; have hc4_8 := acc128_step_eq hc4_7 st3.1 (by decide) hv_cp_119 hv_cp_117; rw [← hv_cp_117] at hv_cp_118 hv_cp_122 hv_cp_123; rw [← hv_cp_122] at hv_cp_123; have st4 := mont_red_step_eq hc4_8 (by decide) hv_cp_122 hv_cp_123 rfl hv_cp_128 hv_cp_127; have hu4 := st4.2.1; have hc5_1 := acc128_step_eq hp_a3b2 hp_b3a2 (by decide) rfl hv_cp_129; have hc5_2 := acc128_step_eq hc5_1 hp_b4a1 (by decide) rfl rfl; have hc5_3 := acc128_step_eq hc5_2 hp_a4b1 (by decide) rfl rfl; have hu1_l4 := l4_shift_pair hv_cp_62 hv_cp_66 rfl rfl; have hc5_4 := acc128_step_eq hc5_3 hu1_l4 (by decide) rfl rfl; have hu3_l2 := mul_const_pair_52 1367801 hu3 (by decide) hv_cp_126 rfl; have hc5_5 := acc128_step_eq hc5_4 hu3_l2 (by decide) rfl rfl; have hu4_l1 := mul_const_pair_52 3916664325105025 hu4 (by decide) rfl rfl; have hc5_6 := acc128_step_eq hc5_5 hu4_l1 (by decide) rfl rfl; have hc5_7 := acc128_step_eq hc5_6 st4.1 (by decide) rfl rfl
    have st5 := extr52_step_eq hc5_7 (by decide) hv_cp_136 hv_cp_134 hv_cp_133; have hn0 := st5.2.1; have hc6_1 := acc128_step_eq hp_b4a2 hp_a3b3 (by decide) rfl rfl; have hc6_2 := acc128_step_eq hc6_1 hp_a4b2 (by decide) hv_cp_49 hv_cp_47; have hu2_l4 := l4_shift_pair hv_cp_81 hv_cp_84 rfl rfl; have hc6_3 := acc128_step_eq hc6_2 hu2_l4 (by decide) rfl rfl; have hu4_l2 := mul_const_pair_52 1367801 hu4 (by decide) rfl rfl; have hc6_4 := acc128_step_eq hc6_3 hu4_l2 (by decide) hv_cp_137 hv_cp_135; have hc6_5 := acc128_step_eq hc6_4 st5.1 (by decide) rfl rfl; have st6 := extr52_step_eq hc6_5 (by decide) hv_cp_142 hv_cp_141 hv_cp_140; have hn1 := st6.2.1; have hc7_1 := acc128_step_eq hp_a4b3 hp_b4a3 (by decide) hv_cp_56 hv_cp_57; have hu3_l4 := l4_shift_pair hv_cp_99 hv_cp_103 hv_cp_139 hv_cp_144; rw [← hv_cp_144] at hv_cp_143; have hc7_2 := acc128_step_eq hc7_1 hu3_l4 (by decide) rfl hv_cp_143; have hc7_3 := acc128_step_eq hc7_2 st6.1 (by decide) hv_cp_147 rfl; rw [← hv_cp_147] at hv_cp_153; have st7 := extr52_step_eq hc7_3 (by decide) hv_cp_152 rfl hv_cp_153
    have hn2 := st7.2.1; have hu4_l4 := l4_shift_pair hv_cp_118 hv_cp_122 hv_cp_149 hv_cp_154; rw [BitVec.add_comm v_cp_149 v_cp_146] at hv_cp_158; rw [← hv_cp_145, ← hv_cp_154] at hv_cp_148; have hc8_1 := acc128_step_eq hp_a4b4 hu4_l4 (by decide) rfl hv_cp_148; have hc8_2 := acc128_step_eq hc8_1 st7.1 (by decide) rfl rfl; have st8 := extr52_last_step_eq hc8_2 (by decide) hv_cp_156 hv_cp_158; have hn3 := st8.1; have h_sb := sc52_schoolbook_mul (ByteSlice.readLE a_4 0 8) (ByteSlice.readLE a_4 8 8) (ByteSlice.readLE a_4 16 8) (ByteSlice.readLE a_4 24 8) (ByteSlice.readLE a_4 32 8) (ByteSlice.readLE a_rest 0 8) (ByteSlice.readLE a_rest 8 8) (ByteSlice.readLE a_rest 16 8) (ByteSlice.readLE a_rest 24 8) (ByteSlice.readLE a_rest 32 8); have h_tele := sc52_mont_telescope v_cp_43 v_cp_66 v_cp_84 v_cp_103 v_cp_122 v_cp_136 v_cp_142 v_cp_152 v_cp_156 v_cp_158 hu0 hu1 hu2 hu3 hu4 h_sb h_1 st0.2.2 st1.2.2 st2.2.2 st3.2.2 st4.2.2 st5.2.2 st6.2.2 st7.2.2 st8.2; rw [← hv_cp_159] at hv_cp_162 hv_cp_163 hv_cp_164; rw [← hv_cp_163] at hv_cp_164; have h_sub := sc52_cond_sub_l v_cp_136 v_cp_142 v_cp_152 v_cp_156 v_cp_158 v_cp_150 v_cp_151 v_cp_155 v_cp_157 v_cp_160 v_cp_159 v_cp_162 v_cp_163 v_cp_164 _ v_cp_170 v_cp_171 v_cp_167 v_cp_168 v_cp_172 hn0 hn1 hn2 hn3 h_tele.1 hv_cp_150 hv_cp_151 hv_cp_155 hv_cp_157 hv_cp_160 hv_cp_159 hv_cp_162 hv_cp_163 hv_cp_164 hpost hv_cp_170 hv_cp_171 hv_cp_167 hv_cp_168 hv_cp_172; rcases h_sub with ⟨hr0, hr1, hr2, hr3, hr4, hr_lt, q, _, hq_eq⟩; rw [sc52ValOfBytes_sc52Pack5, sc52LimbsBounded_sc52Pack5]
    refine ⟨⟨hr0, hr1, hr2, hr3, hr4⟩, hr_lt, ?_⟩
    exact mod_eq_of_mont hq_eq h_tele.2
  rcases h_res with ⟨h_res_limb, h_res_lt, h_res_mod⟩; rcases h_res_limb with ⟨h_len, h_l0, h_l1, h_l2, h_l3, h_l4⟩
  wp_done
set_option maxHeartbeats 800000 in set_option exponentiation.threshold 512 in
theorem sc52_montgomery_mul_ro_right_ok : Sc52MontgomeryMulRoRightOk := by
  intro _
  apply dalekCaller_ok dalekCliPC06 dalekCliPl06
  intro b hb hbase
  wp_init
  obtain ⟨ow0, ow1, ow2, ow3, ow4, hout_cells⟩ := exists_cells_of_length_40 h_5; have ha_len : a_4.length = 40 := h_6.1; have hb_len : a_rest.length = 40 := h_7.1; rw [hout_cells a_1, pointsToBytesRO40_eq_cells a_2 a_rest hb_len]; wp_cut_codeLoaded; wp_sym_steps 65; wp_checkpoint; wp_sym_steps 28; wp_checkpoint; wp_sym_steps 16; wp_checkpoint; wp_sym_steps 14; wp_checkpoint; wp_sym_steps 11; wp_checkpoint; wp_sym_steps 10; wp_checkpoint; wp_sym_steps 10; wp_checkpoint; wp_sym_steps 22; wp_checkpoint; wp_sym_steps 18; wp_checkpoint; wp_sym_steps 20; wp_checkpoint; wp_sym_steps 9; wp_checkpoint; wp_sym_steps 28; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 21; wp_checkpoint; wp_sym_steps 11; wp_checkpoint; wp_sym_steps 6; wp_checkpoint
  wp_steps 1; wp_dalek_call black_box_u8_ok; wp_sym_steps; wp_checkpoint; wp_conv_pre => simp only [sc52Pack5_cells_eq_rest]
  wp_fold_stack; have h_res :
      sc52LimbsBounded (sc52Pack5 v_cp_170 v_cp_171 v_cp_167 v_cp_168 v_cp_172) (2 ^ 52) ∧
      sc52ValOfBytes (sc52Pack5 v_cp_170 v_cp_171 v_cp_167 v_cp_168 v_cp_172) < edOrderL ∧
      sc52ValOfBytes (sc52Pack5 v_cp_170 v_cp_171 v_cp_167 v_cp_168 v_cp_172) * 2 ^ 260 % edOrderL = sc52ValOfBytes a_4 * sc52ValOfBytes a_rest % edOrderL := by
    rcases h_6 with ⟨_, ha0, ha1, ha2, ha3, ha4⟩; rcases h_7 with ⟨_, hb0, hb1, hb2, hb3, hb4⟩; have hp_b0a0 := mul_pair_52 hb0 rfl rfl hv_cp_28 hv_cp_8; have hp_a1b0 := mul_pair_52 ha1 rfl rfl hv_cp_36 hv_cp_10; have hp_b1a0 := mul_pair_52 hb1 rfl rfl hv_cp_9 hv_cp_37; have hp_b2a0 := mul_pair_52 hb2 rfl rfl hv_cp_31 hv_cp_13; have hp_a1b1 := mul_pair_52 ha1 rfl rfl hv_cp_12 hv_cp_11; have hp_a2b0 := mul_pair_52 ha2 rfl rfl hv_cp_26 hv_cp_14; have hp_a2b1 := mul_pair_52 ha2 rfl rfl hv_cp_25 hv_cp_27; have hp_b2a1 := mul_pair_52 hb2 hv_cp_5 hv_cp_0 hv_cp_76 hv_cp_79; have hp_b3a0 := mul_pair_52 hb3 rfl rfl hv_cp_30 hv_cp_29; have hp_a3b0 := mul_pair_52 ha3 hv_cp_4 hv_cp_1 hv_cp_88 hv_cp_82; have hp_b3a1 := mul_pair_52 hb3 rfl rfl hv_cp_33 hv_cp_32; have hp_a2b2 := mul_pair_52 ha2 hv_cp_3 hv_cp_5 hv_cp_58 hv_cp_59; have hp_a3b1 := mul_pair_52 ha3 hv_cp_4 hv_cp_2 hv_cp_94 hv_cp_106; have hp_b4a0 := mul_pair_52 hb4 rfl rfl hv_cp_35 hv_cp_34; have hp_a4b0 := mul_pair_52 ha4 hv_cp_7 hv_cp_1 hv_cp_95 hv_cp_96; have hp_a3b2 := mul_pair_52 ha3 hv_cp_4 hv_cp_5 hv_cp_116 hv_cp_120
    have hp_b3a2 := mul_pair_52 hb3 rfl rfl hv_cp_39 hv_cp_38; have hp_b4a1 := mul_pair_52 hb4 hv_cp_6 hv_cp_0 hv_cp_108 hv_cp_115; have hp_a4b1 := mul_pair_52 ha4 hv_cp_7 hv_cp_2 hv_cp_121 hv_cp_125; have hp_b4a2 := mul_pair_52 hb4 rfl rfl hv_cp_24 hv_cp_16; have hp_a3b3 := mul_pair_52 ha3 rfl rfl hv_cp_17 hv_cp_15; have hp_a4b2 := mul_pair_52 ha4 rfl rfl hv_cp_21 hv_cp_20; have hp_a4b3 := mul_pair_52 ha4 rfl rfl hv_cp_18 hv_cp_19; have hp_b4a3 := mul_pair_52 hb4 rfl rfl hv_cp_23 hv_cp_22; have hp_a4b4 := mul_pair_40 ha4 hb4 hv_cp_7 hv_cp_6 hv_cp_146 hv_cp_145; rw [← hv_cp_43] at hv_cp_45 hv_cp_48; have st0 := mont_red_step_eq hp_b0a0 (by decide) hv_cp_43 hv_cp_45 hv_cp_48 hv_cp_55 hv_cp_54; have hu0 := st0.2.1; have hc1_1 := acc128_step_eq hp_a1b0 hp_b1a0 (by decide) hv_cp_42 hv_cp_40; have hu0_l1 := mul_const_pair_52 3916664325105025 hu0 (by decide) hv_cp_53 hv_cp_52; have hc1_2 := acc128_step_eq hc1_1 hu0_l1 (by decide) hv_cp_60 hv_cp_68; rw [← hv_cp_61] at hv_cp_62 hv_cp_66 hv_cp_67; rw [← hv_cp_66] at hv_cp_67; rw [← hv_cp_60] at hv_cp_63
    rw [← hv_cp_68] at hv_cp_63 hv_cp_61; have hc1_3 := acc128_step_eq hc1_2 st0.1 (by decide) hv_cp_63 hv_cp_61; have st1 := mont_red_step_eq hc1_3 (by decide) hv_cp_66 hv_cp_67 rfl hv_cp_74 hv_cp_72; have hu1 := st1.2.1; have hc2_1 := acc128_step_eq hp_b2a0 hp_a1b1 (by decide) rfl rfl; have hc2_2 := acc128_step_eq hc2_1 hp_a2b0 (by decide) hv_cp_44 hv_cp_51; have hu0_l2 := mul_const_pair_52 1367801 hu0 (by decide) hv_cp_64 hv_cp_65; have hc2_3 := acc128_step_eq hc2_2 hu0_l2 (by decide) hv_cp_73 hv_cp_77; have hu1_l1 := mul_const_pair_52 3916664325105025 hu1 (by decide) hv_cp_71 hv_cp_70; rw [← hv_cp_77, ← hv_cp_70] at hv_cp_75; have hc2_4 := acc128_step_eq hc2_3 hu1_l1 (by decide) rfl hv_cp_75; have hc2_5 := acc128_step_eq hc2_4 st1.1 (by decide) hv_cp_80 hv_cp_78; rw [← hv_cp_78] at hv_cp_81 hv_cp_84 hv_cp_85 hv_cp_86; rw [← hv_cp_84] at hv_cp_85 hv_cp_86; have st2 := mont_red_step_eq hc2_5 (by decide) hv_cp_84 hv_cp_85 hv_cp_86 hv_cp_91 hv_cp_90; have hu2 := st2.2.1; have hc3_1 := acc128_step_eq hp_a2b1 hp_b2a1 (by decide) rfl hv_cp_92; have hc3_2 := acc128_step_eq hc3_1 hp_b3a0 (by decide) rfl rfl
    have hc3_3 := acc128_step_eq hc3_2 hp_a3b0 (by decide) rfl rfl; have hu1_l2 := mul_const_pair_52 1367801 hu1 (by decide) hv_cp_83 hv_cp_87; have hc3_4 := acc128_step_eq hc3_3 hu1_l2 (by decide) rfl rfl; have hu2_l1 := mul_const_pair_52 3916664325105025 hu2 (by decide) hv_cp_93 hv_cp_89; have hc3_5 := acc128_step_eq hc3_4 hu2_l1 (by decide) rfl rfl; have hc3_6 := acc128_step_eq hc3_5 st2.1 (by decide) hv_cp_100 hv_cp_98; rw [← hv_cp_98] at hv_cp_99 hv_cp_103 hv_cp_104; rw [← hv_cp_103] at hv_cp_104; have st3 := mont_red_step_eq hc3_6 (by decide) hv_cp_103 hv_cp_104 rfl hv_cp_112 hv_cp_109; have hu3 := st3.2.1; have hc4_1 := acc128_step_eq hp_b3a1 hp_a2b2 (by decide) rfl rfl; have hu0_l4 := l4_shift_pair hv_cp_41 hv_cp_43 rfl rfl; have hc4_2 := acc128_step_eq hc4_1 hu0_l4 (by decide) hv_cp_110 hv_cp_114; rw [← hv_cp_114, ← hv_cp_106] at hv_cp_113; have hc4_3 := acc128_step_eq hc4_2 hp_a3b1 (by decide) rfl hv_cp_113; have hc4_4 := acc128_step_eq hc4_3 hp_b4a0 (by decide) rfl rfl; have hc4_5 := acc128_step_eq hc4_4 hp_a4b0 (by decide) rfl rfl; have hu2_l2 := mul_const_pair_52 1367801 hu2 (by decide) hv_cp_101 hv_cp_102
    have hc4_6 := acc128_step_eq hc4_5 hu2_l2 (by decide) rfl rfl; have hu3_l1 := mul_const_pair_52 3916664325105025 hu3 (by decide) hv_cp_111 hv_cp_107; have hc4_7 := acc128_step_eq hc4_6 hu3_l1 (by decide) rfl rfl; have hc4_8 := acc128_step_eq hc4_7 st3.1 (by decide) hv_cp_119 hv_cp_117; rw [← hv_cp_117] at hv_cp_118 hv_cp_122 hv_cp_123; rw [← hv_cp_122] at hv_cp_123; have st4 := mont_red_step_eq hc4_8 (by decide) hv_cp_122 hv_cp_123 rfl hv_cp_128 hv_cp_127; have hu4 := st4.2.1; have hc5_1 := acc128_step_eq hp_a3b2 hp_b3a2 (by decide) rfl hv_cp_129; have hc5_2 := acc128_step_eq hc5_1 hp_b4a1 (by decide) rfl rfl; have hc5_3 := acc128_step_eq hc5_2 hp_a4b1 (by decide) rfl rfl; have hu1_l4 := l4_shift_pair hv_cp_62 hv_cp_66 rfl rfl; have hc5_4 := acc128_step_eq hc5_3 hu1_l4 (by decide) rfl rfl; have hu3_l2 := mul_const_pair_52 1367801 hu3 (by decide) hv_cp_126 rfl; have hc5_5 := acc128_step_eq hc5_4 hu3_l2 (by decide) rfl rfl; have hu4_l1 := mul_const_pair_52 3916664325105025 hu4 (by decide) rfl rfl; have hc5_6 := acc128_step_eq hc5_5 hu4_l1 (by decide) rfl rfl; have hc5_7 := acc128_step_eq hc5_6 st4.1 (by decide) rfl rfl
    have st5 := extr52_step_eq hc5_7 (by decide) hv_cp_136 hv_cp_134 hv_cp_133; have hn0 := st5.2.1; have hc6_1 := acc128_step_eq hp_b4a2 hp_a3b3 (by decide) rfl rfl; have hc6_2 := acc128_step_eq hc6_1 hp_a4b2 (by decide) hv_cp_49 hv_cp_47; have hu2_l4 := l4_shift_pair hv_cp_81 hv_cp_84 rfl rfl; have hc6_3 := acc128_step_eq hc6_2 hu2_l4 (by decide) rfl rfl; have hu4_l2 := mul_const_pair_52 1367801 hu4 (by decide) rfl rfl; have hc6_4 := acc128_step_eq hc6_3 hu4_l2 (by decide) hv_cp_137 hv_cp_135; have hc6_5 := acc128_step_eq hc6_4 st5.1 (by decide) rfl rfl; have st6 := extr52_step_eq hc6_5 (by decide) hv_cp_142 hv_cp_141 hv_cp_140; have hn1 := st6.2.1; have hc7_1 := acc128_step_eq hp_a4b3 hp_b4a3 (by decide) hv_cp_56 hv_cp_57; have hu3_l4 := l4_shift_pair hv_cp_99 hv_cp_103 hv_cp_139 hv_cp_144; rw [← hv_cp_144] at hv_cp_143; have hc7_2 := acc128_step_eq hc7_1 hu3_l4 (by decide) rfl hv_cp_143; have hc7_3 := acc128_step_eq hc7_2 st6.1 (by decide) hv_cp_147 rfl; rw [← hv_cp_147] at hv_cp_153; have st7 := extr52_step_eq hc7_3 (by decide) hv_cp_152 rfl hv_cp_153
    have hn2 := st7.2.1; have hu4_l4 := l4_shift_pair hv_cp_118 hv_cp_122 hv_cp_149 hv_cp_154; rw [BitVec.add_comm v_cp_149 v_cp_146] at hv_cp_158; rw [← hv_cp_145, ← hv_cp_154] at hv_cp_148; have hc8_1 := acc128_step_eq hp_a4b4 hu4_l4 (by decide) rfl hv_cp_148; have hc8_2 := acc128_step_eq hc8_1 st7.1 (by decide) rfl rfl; have st8 := extr52_last_step_eq hc8_2 (by decide) hv_cp_156 hv_cp_158; have hn3 := st8.1; have h_sb := sc52_schoolbook_mul (ByteSlice.readLE a_4 0 8) (ByteSlice.readLE a_4 8 8) (ByteSlice.readLE a_4 16 8) (ByteSlice.readLE a_4 24 8) (ByteSlice.readLE a_4 32 8) (ByteSlice.readLE a_rest 0 8) (ByteSlice.readLE a_rest 8 8) (ByteSlice.readLE a_rest 16 8) (ByteSlice.readLE a_rest 24 8) (ByteSlice.readLE a_rest 32 8); have h_tele := sc52_mont_telescope v_cp_43 v_cp_66 v_cp_84 v_cp_103 v_cp_122 v_cp_136 v_cp_142 v_cp_152 v_cp_156 v_cp_158 hu0 hu1 hu2 hu3 hu4 h_sb h_1 st0.2.2 st1.2.2 st2.2.2 st3.2.2 st4.2.2 st5.2.2 st6.2.2 st7.2.2 st8.2; rw [← hv_cp_159] at hv_cp_162 hv_cp_163 hv_cp_164; rw [← hv_cp_163] at hv_cp_164; have h_sub := sc52_cond_sub_l v_cp_136 v_cp_142 v_cp_152 v_cp_156 v_cp_158 v_cp_150 v_cp_151 v_cp_155 v_cp_157 v_cp_160 v_cp_159 v_cp_162 v_cp_163 v_cp_164 _ v_cp_170 v_cp_171 v_cp_167 v_cp_168 v_cp_172 hn0 hn1 hn2 hn3 h_tele.1 hv_cp_150 hv_cp_151 hv_cp_155 hv_cp_157 hv_cp_160 hv_cp_159 hv_cp_162 hv_cp_163 hv_cp_164 hpost hv_cp_170 hv_cp_171 hv_cp_167 hv_cp_168 hv_cp_172; rcases h_sub with ⟨hr0, hr1, hr2, hr3, hr4, hr_lt, q, _, hq_eq⟩; rw [sc52ValOfBytes_sc52Pack5, sc52LimbsBounded_sc52Pack5]
    exact ⟨⟨hr0, hr1, hr2, hr3, hr4⟩, hr_lt, mod_eq_of_mont hq_eq h_tele.2⟩
  rcases h_res with ⟨⟨h_len, h_l0, h_l1, h_l2, h_l3, h_l4⟩, h_res_lt, h_res_mod⟩; wp_done
set_option maxHeartbeats 800000 in set_option exponentiation.threshold 512 in
theorem sc52_mul_core_ok : Sc52MulCoreOk := by
  intro _
  apply dalekCaller_ok dalekCliPC07 dalekCliPl07
  intro b hb hbase
  wp_init
  obtain ⟨ow0, ow1, ow2, ow3, ow4, hout_cells⟩ := exists_cells_of_length_40 h_5; have ha_len : a_4.length = 40 := h_6.1; have hb_len : a_rest.length = 40 := h_7.1; wp_cut_codeLoaded; wp_sym_steps 35; wp_checkpoint; wp_sym_steps 16; wp_checkpoint; wp_sym_steps 14; wp_checkpoint; wp_sym_steps 13; wp_checkpoint; wp_sym_steps 12; wp_checkpoint; wp_sym_steps 10; wp_checkpoint; wp_sym_steps 6; wp_checkpoint; wp_sym_steps 9; wp_checkpoint; wp_sym_steps 4; wp_checkpoint; wp_sym_steps 7; wp_checkpoint; wp_sym_steps 9; wp_checkpoint; wp_sym_steps 5; wp_checkpoint; wp_sym_steps 7; wp_checkpoint; wp_sym_steps 3; wp_checkpoint; wp_sym_steps 6; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 10; wp_checkpoint; wp_sym_steps 7; wp_checkpoint; wp_sym_steps 4; wp_checkpoint; wp_sym_steps 3; wp_checkpoint; wp_sym_steps 4; wp_checkpoint; wp_sym_steps 5; wp_checkpoint; wp_sym_steps 3; wp_checkpoint; wp_sym_steps 7; wp_checkpoint; wp_sym_steps 7; wp_checkpoint; wp_sym_steps 6; wp_checkpoint; wp_sym_steps 5; wp_checkpoint; wp_sym_steps 4; wp_checkpoint; wp_sym_steps 3; wp_checkpoint; wp_sym_steps 3; wp_checkpoint; wp_sym_steps 3; wp_checkpoint; wp_sym_steps 4; wp_checkpoint; wp_sym_steps 3; wp_checkpoint; wp_sym_steps 3; wp_checkpoint; wp_sym_steps 7; wp_checkpoint; wp_sym_steps 7; wp_checkpoint; wp_sym_steps 16; wp_checkpoint; wp_sym_steps 4; wp_checkpoint; wp_sym_steps 10; wp_checkpoint
  wp_steps 1; wp_dalek_call black_box_u8_ok
  wp_simp_pre [hsp_sf, bitvec64_sub_sub_fold]
  wp_cut_codeLoaded; wp_sym_steps 25; wp_checkpoint; wp_sym_steps 26; wp_checkpoint; wp_sym_steps 24; wp_checkpoint; rw [← hv_cp_223] at hv_cp_224; rw [← hv_cp_243] at hv_cp_246 hv_cp_248 hv_cp_252; rw [← hv_cp_244] at hv_cp_247 hv_cp_249 hv_cp_250; have h_mont1 : v_cp_223.toNat < 2 ^ 52 ∧ v_cp_226.toNat < 2 ^ 52 ∧ v_cp_243.toNat < 2 ^ 52 ∧ v_cp_244.toNat < 2 ^ 52 ∧ v_cp_251.toNat < 2 ^ 52 ∧ sc52Val v_cp_223 v_cp_226 v_cp_243 v_cp_244 v_cp_251 < edOrderL ∧ sc52Val v_cp_223 v_cp_226 v_cp_243 v_cp_244 v_cp_251 * 2 ^ 260 % edOrderL =
        sc52ValOfBytes a_4 * sc52ValOfBytes a_rest % edOrderL := by
    rcases h_6 with ⟨_, ha0, ha1, ha2, ha3, ha4⟩; rcases h_7 with ⟨_, hb0, hb1, hb2, hb3, hb4⟩; have hp_b0a0 := mul_pair_52 hb0 rfl rfl hv_cp_22 hv_cp_10; have hp_a1b0 := mul_pair_52 ha1 rfl rfl hv_cp_23 hv_cp_19; have hp_b1a0 := mul_pair_52 hb1 rfl rfl hv_cp_11 hv_cp_20; have hp_b2a0 := mul_pair_52 hb2 rfl rfl hv_cp_21 hv_cp_12; have hp_a1b1 := mul_pair_52 ha1 rfl rfl hv_cp_17 hv_cp_15; have hp_a2b0 := mul_pair_52 ha2 hv_cp_8 hv_cp_3 hv_cp_27 hv_cp_29; have hp_a2b1 := mul_pair_52 ha2 hv_cp_8 hv_cp_4 hv_cp_37 hv_cp_39; have hp_b2a1 := mul_pair_52 hb2 hv_cp_5 hv_cp_1 hv_cp_90 hv_cp_86; have hp_b3a0 := mul_pair_52 hb3 rfl rfl hv_cp_13 hv_cp_14; have hp_a3b0 := mul_pair_52 ha3 hv_cp_9 hv_cp_3 hv_cp_96 hv_cp_94; have hp_b3a1 := mul_pair_52 hb3 hv_cp_6 hv_cp_1 hv_cp_26 hv_cp_28; have hp_a2b2 := mul_pair_52 ha2 hv_cp_8 hv_cp_5 hv_cp_64 hv_cp_71; have hp_a3b1 := mul_pair_52 ha3 hv_cp_9 hv_cp_4 hv_cp_124 hv_cp_122; have hp_b4a0 := mul_pair_52 hb4 hv_cp_2 hv_cp_0 hv_cp_32 hv_cp_31; have hp_a4b0 := mul_pair_52 ha4 hv_cp_7 hv_cp_3 hv_cp_106 hv_cp_112; have hp_a3b2 := mul_pair_52 ha3 hv_cp_9 hv_cp_5 hv_cp_147 hv_cp_152
    have hp_b3a2 := mul_pair_52 hb3 hv_cp_6 hv_cp_8 hv_cp_43 hv_cp_42; have hp_b4a1 := mul_pair_52 hb4 hv_cp_2 hv_cp_1 hv_cp_130 hv_cp_141; have hp_a4b1 := mul_pair_52 ha4 hv_cp_7 hv_cp_4 hv_cp_153 hv_cp_157; have hp_b4a2 := mul_pair_52 hb4 hv_cp_2 hv_cp_8 hv_cp_44 hv_cp_35; have hp_a3b3 := mul_pair_52 ha3 hv_cp_9 hv_cp_6 hv_cp_36 hv_cp_30; have hp_a4b2 := mul_pair_52 ha4 hv_cp_7 hv_cp_5 hv_cp_48 hv_cp_45; have hp_a4b3 := mul_pair_52 ha4 hv_cp_7 hv_cp_6 hv_cp_40 hv_cp_41; have hp_b4a3 := mul_pair_52 hb4 hv_cp_2 hv_cp_9 hv_cp_51 hv_cp_55; have hp_a4b4 := mul_pair_40 ha4 hb4 hv_cp_7 hv_cp_2 hv_cp_206 hv_cp_201; rw [hv_cp_46] at hv_cp_50 hv_cp_53; rw [← hv_cp_50] at hv_cp_53; rw [hv_cp_59, hv_cp_57] at hv_cp_61; rw [hv_cp_59] at hv_cp_62; have st0 := mont_red_step_eq hp_b0a0 (by decide) hv_cp_50 hv_cp_53 rfl hv_cp_62 hv_cp_61; have hu0 := st0.2.1; rw [← hv_cp_23, ← hv_cp_11, ← hv_cp_19, ← hv_cp_20] at hv_cp_18; rw [← hv_cp_19, ← hv_cp_20] at hv_cp_16; have hc1_1 := acc128_step_eq hp_a1b0 hp_b1a0 (by decide) hv_cp_18 hv_cp_16
    have hu0_l1 := mul_const_pair_52 3916664325105025 hu0 (by decide) hv_cp_58 hv_cp_56; have hc1_2 := acc128_step_eq hc1_1 hu0_l1 (by decide) hv_cp_65 hv_cp_63; have hc1_3 := acc128_step_eq hc1_2 st0.1 (by decide) hv_cp_68 hv_cp_66; rw [← hv_cp_66] at hv_cp_69 hv_cp_72 hv_cp_73 hv_cp_74; rw [← hv_cp_72] at hv_cp_73 hv_cp_74; rw [hv_cp_78, hv_cp_76] at hv_cp_79; rw [hv_cp_78] at hv_cp_80; have st1 := mont_red_step_eq hc1_3 (by decide) hv_cp_72 hv_cp_73 hv_cp_74 hv_cp_80 hv_cp_79; have hu1 := st1.2.1; have hc2_1 := acc128_step_eq hp_b2a0 hp_a1b1 (by decide) hv_cp_25 hv_cp_24; have hc2_2 := acc128_step_eq hc2_1 hp_a2b0 (by decide) hv_cp_34 hv_cp_33; have hu0_l2 := mul_const_pair_52 1367801 hu0 (by decide) hv_cp_67 hv_cp_70; have hc2_3 := acc128_step_eq hc2_2 hu0_l2 (by decide) rfl hv_cp_84; have hu1_l1 := mul_const_pair_52 3916664325105025 hu1 (by decide) hv_cp_77 hv_cp_75; rw [← hv_cp_84] at hv_cp_83 hv_cp_81; have hc2_4 := acc128_step_eq hc2_3 hu1_l1 (by decide) hv_cp_83 hv_cp_81; have hc2_5 := acc128_step_eq hc2_4 st1.1 (by decide) hv_cp_87 hv_cp_85; rw [← hv_cp_85] at hv_cp_88 hv_cp_91 hv_cp_92 hv_cp_93
    rw [← hv_cp_91] at hv_cp_92 hv_cp_93; rw [hv_cp_97, hv_cp_95] at hv_cp_101; rw [hv_cp_97] at hv_cp_102; have st2 := mont_red_step_eq hc2_5 (by decide) hv_cp_91 hv_cp_92 hv_cp_93 hv_cp_102 hv_cp_101; have hu2 := st2.2.1; have hc3_1 := acc128_step_eq hp_a2b1 hp_b2a1 (by decide) hv_cp_99 hv_cp_98; have hc3_2 := acc128_step_eq hc3_1 hp_b3a0 (by decide) hv_cp_105 hv_cp_104; have hc3_3 := acc128_step_eq hc3_2 hp_a3b0 (by decide) hv_cp_107 hv_cp_110; have hu1_l2 := mul_const_pair_52 1367801 hu1 (by decide) hv_cp_82 hv_cp_89; rw [← hv_cp_107, ← hv_cp_110] at hv_cp_109; rw [← hv_cp_110] at hv_cp_108; have hc3_4 := acc128_step_eq hc3_3 hu1_l2 (by decide) hv_cp_109 hv_cp_108; have hu2_l1 := mul_const_pair_52 3916664325105025 hu2 (by decide) hv_cp_103 hv_cp_100; have hc3_5 := acc128_step_eq hc3_4 hu2_l1 (by decide) hv_cp_113 hv_cp_111; rw [← hv_cp_113, ← hv_cp_111] at hv_cp_116; rw [← hv_cp_111] at hv_cp_114 hv_cp_115; have hc3_6 := acc128_step_eq hc3_5 st2.1 (by decide) hv_cp_116 hv_cp_114; rw [← hv_cp_114] at hv_cp_115
    rw [hv_cp_115] at hv_cp_119 hv_cp_120 hv_cp_121 hv_cp_123 hv_cp_125; rw [← hv_cp_119] at hv_cp_120 hv_cp_121 hv_cp_123 hv_cp_125; rw [← hv_cp_120] at hv_cp_123 hv_cp_125; rw [← hv_cp_121] at hv_cp_125; rw [hv_cp_125, hv_cp_123] at hv_cp_127; rw [hv_cp_125] at hv_cp_128; have st3 := mont_red_step_eq hc3_6 (by decide) hv_cp_119 hv_cp_120 hv_cp_121 hv_cp_128 hv_cp_127; have hu3 := st3.2.1; have hc4_1 := acc128_step_eq hp_b3a1 hp_a2b2 (by decide) hv_cp_131 hv_cp_129; have hu0_l4 := l4_shift_pair hv_cp_46 hv_cp_50 hv_cp_133 hv_cp_135; rw [← hv_cp_133, ← hv_cp_135] at hv_cp_134; rw [← hv_cp_135] at hv_cp_132; have hc4_2 := acc128_step_eq hc4_1 hu0_l4 (by decide) hv_cp_134 hv_cp_132; have hc4_3 := acc128_step_eq hc4_2 hp_a3b1 (by decide) hv_cp_138 hv_cp_136; have hc4_4 := acc128_step_eq hc4_3 hp_b4a0 (by decide) hv_cp_140 hv_cp_139; have hc4_5 := acc128_step_eq hc4_4 hp_a4b0 (by decide) hv_cp_142 hv_cp_145; have hu2_l2 := mul_const_pair_52 1367801 hu2 (by decide) hv_cp_117 hv_cp_118; rw [← hv_cp_142, ← hv_cp_145] at hv_cp_144
    rw [← hv_cp_145] at hv_cp_143; have hc4_6 := acc128_step_eq hc4_5 hu2_l2 (by decide) hv_cp_144 hv_cp_143; have hu3_l1 := mul_const_pair_52 3916664325105025 hu3 (by decide) hv_cp_137 hv_cp_126; have hc4_7 := acc128_step_eq hc4_6 hu3_l1 (by decide) hv_cp_148 hv_cp_146; have hc4_8 := acc128_step_eq hc4_7 st3.1 (by decide) hv_cp_151 hv_cp_149; rw [← hv_cp_149] at hv_cp_150 hv_cp_154; rw [← hv_cp_155] at hv_cp_158 hv_cp_160; rw [← hv_cp_156] at hv_cp_160; rw [hv_cp_160, hv_cp_158] at hv_cp_163; rw [hv_cp_160] at hv_cp_164; have st4 := mont_red_step_eq hc4_8 (by decide) hv_cp_154 hv_cp_155 hv_cp_156 hv_cp_164 hv_cp_163; have hu4 := st4.2.1; have hc5_1 := acc128_step_eq hp_a3b2 hp_b3a2 (by decide) hv_cp_165 hv_cp_161; have hc5_2 := acc128_step_eq hc5_1 hp_b4a1 (by decide) hv_cp_166 hv_cp_170; rw [← hv_cp_166, ← hv_cp_170] at hv_cp_169; rw [← hv_cp_170] at hv_cp_167; have hc5_3 := acc128_step_eq hc5_2 hp_a4b1 (by decide) hv_cp_169 hv_cp_167; have hu1_l4 := l4_shift_pair hv_cp_69 hv_cp_72 hv_cp_171 hv_cp_175
    rw [← hv_cp_171, ← hv_cp_175] at hv_cp_174; rw [← hv_cp_175] at hv_cp_172; have hc5_4 := acc128_step_eq hc5_3 hu1_l4 (by decide) hv_cp_174 hv_cp_172; have hu3_l2 := mul_const_pair_52 1367801 hu3 (by decide) hv_cp_162 hv_cp_159; have hc5_5 := acc128_step_eq hc5_4 hu3_l2 (by decide) hv_cp_178 hv_cp_176; have hu4_l1 := mul_const_pair_52 3916664325105025 hu4 (by decide) hv_cp_173 hv_cp_168; have hc5_6 := acc128_step_eq hc5_5 hu4_l1 (by decide) hv_cp_181 hv_cp_179; have hc5_7 := acc128_step_eq hc5_6 st4.1 (by decide) hv_cp_184 hv_cp_182; have st5 := extr52_step_eq hc5_7 (by decide) hv_cp_191 hv_cp_188 hv_cp_186; rw [← hv_cp_44] at hv_cp_47; rw [← hv_cp_35] at hv_cp_38; have hc6_1 := acc128_step_eq hp_b4a2 hp_a3b3 (by decide) hv_cp_47 hv_cp_38; have hc6_2 := acc128_step_eq hc6_1 hp_a4b2 (by decide) hv_cp_52 hv_cp_49; have hu2_l4 := l4_shift_pair hv_cp_88 hv_cp_91 hv_cp_183 hv_cp_189; rw [← hv_cp_189] at hv_cp_187 hv_cp_185; have hc6_3 := acc128_step_eq hc6_2 hu2_l4 (by decide) hv_cp_187 hv_cp_185; have hu4_l2 := mul_const_pair_52 1367801 hu4 (by decide) hv_cp_180 hv_cp_177; have hc6_4 := acc128_step_eq hc6_3 hu4_l2 (by decide) hv_cp_192 hv_cp_190
    have hc6_5 := acc128_step_eq hc6_4 st5.1 (by decide) hv_cp_194 hv_cp_193; have st6 := extr52_step_eq hc6_5 (by decide) hv_cp_197 hv_cp_196 hv_cp_195; rw [← hv_cp_55] at hv_cp_54; have hc7_1 := acc128_step_eq hp_a4b3 hp_b4a3 (by decide) hv_cp_60 hv_cp_54; have hu3_l4 := l4_shift_pair hv_cp_115 hv_cp_119 rfl hv_cp_200; rw [← hv_cp_200] at hv_cp_199 hv_cp_198; have hc7_2 := acc128_step_eq hc7_1 hu3_l4 (by decide) hv_cp_199 hv_cp_198; have hc7_3 := acc128_step_eq hc7_2 st6.1 (by decide) hv_cp_203 hv_cp_202; have st7 := extr52_step_eq hc7_3 (by decide) rfl hv_cp_205 hv_cp_204; have hu4_l4 := l4_shift_pair hv_cp_150 hv_cp_154 rfl hv_cp_213; rw [← hv_cp_206, ← hv_cp_213, BitVec.add_comm (v_cp_150 >>> 20 &&& 4294967295#64) v_cp_206] at hv_cp_212; rw [← hv_cp_213] at hv_cp_207; have hc8_1 := acc128_step_eq hp_a4b4 hu4_l4 (by decide) hv_cp_212 hv_cp_207; have hc8_2 := acc128_step_eq hc8_1 st7.1 (by decide) hv_cp_215 hv_cp_214; have st8 := extr52_last_step_eq hc8_2 (by decide) rfl rfl; have h_school : (ByteSlice.readLE a_rest 0 8).toNat * (ByteSlice.readLE a_4 0 8).toNat + ((ByteSlice.readLE a_4 8 8).toNat * (ByteSlice.readLE a_rest 0 8).toNat + (ByteSlice.readLE a_rest 8 8).toNat * (ByteSlice.readLE a_4 0 8).toNat) * 2 ^ 52 + ((ByteSlice.readLE a_rest 16 8).toNat * (ByteSlice.readLE a_4 0 8).toNat + (ByteSlice.readLE a_4 8 8).toNat * (ByteSlice.readLE a_rest 8 8).toNat + (ByteSlice.readLE a_4 16 8).toNat * (ByteSlice.readLE a_rest 0 8).toNat) * 2 ^ 104 + ((ByteSlice.readLE a_4 16 8).toNat * (ByteSlice.readLE a_rest 8 8).toNat + (ByteSlice.readLE a_rest 16 8).toNat * (ByteSlice.readLE a_4 8 8).toNat + (ByteSlice.readLE a_rest 24 8).toNat * (ByteSlice.readLE a_4 0 8).toNat + (ByteSlice.readLE a_4 24 8).toNat * (ByteSlice.readLE a_rest 0 8).toNat) * 2 ^ 156 + (((ByteSlice.readLE a_rest 24 8).toNat * (ByteSlice.readLE a_4 8 8).toNat + (ByteSlice.readLE a_4 16 8).toNat * (ByteSlice.readLE a_rest 16 8).toNat) + (ByteSlice.readLE a_4 24 8).toNat * (ByteSlice.readLE a_rest 8 8).toNat + (ByteSlice.readLE a_rest 32 8).toNat * (ByteSlice.readLE a_4 0 8).toNat + (ByteSlice.readLE a_4 32 8).toNat * (ByteSlice.readLE a_rest 0 8).toNat) * 2 ^ 208 + ((ByteSlice.readLE a_4 24 8).toNat * (ByteSlice.readLE a_rest 16 8).toNat + (ByteSlice.readLE a_rest 24 8).toNat * (ByteSlice.readLE a_4 16 8).toNat + (ByteSlice.readLE a_rest 32 8).toNat * (ByteSlice.readLE a_4 8 8).toNat + (ByteSlice.readLE a_4 32 8).toNat * (ByteSlice.readLE a_rest 8 8).toNat) * 2 ^ 260 + ((ByteSlice.readLE a_rest 32 8).toNat * (ByteSlice.readLE a_4 16 8).toNat + (ByteSlice.readLE a_4 24 8).toNat * (ByteSlice.readLE a_rest 24 8).toNat + (ByteSlice.readLE a_4 32 8).toNat * (ByteSlice.readLE a_rest 16 8).toNat) * 2 ^ 312 + ((ByteSlice.readLE a_4 32 8).toNat * (ByteSlice.readLE a_rest 24 8).toNat + (ByteSlice.readLE a_rest 32 8).toNat * (ByteSlice.readLE a_4 24 8).toNat) * 2 ^ 364 + ((ByteSlice.readLE a_4 32 8).toNat * (ByteSlice.readLE a_rest 32 8).toNat) * 2 ^ 416 = sc52ValOfBytes a_4 * sc52ValOfBytes a_rest := sc52_schoolbook_mul (ByteSlice.readLE a_4 0 8) (ByteSlice.readLE a_4 8 8) (ByteSlice.readLE a_4 16 8) (ByteSlice.readLE a_4 24 8) (ByteSlice.readLE a_4 32 8) (ByteSlice.readLE a_rest 0 8) (ByteSlice.readLE a_rest 8 8) (ByteSlice.readLE a_rest 16 8) (ByteSlice.readLE a_rest 24 8) (ByteSlice.readLE a_rest 32 8); have h_tele := sc52_mont_telescope v_cp_50 v_cp_72 v_cp_91 v_cp_119 v_cp_154 v_cp_191 v_cp_197 (v_cp_202 &&& 4503599627370495#64) (v_cp_214 &&& 4503599627370495#64) (BitVec.setWidth 64 ((v_cp_215 ++ v_cp_214) >>> 52)) hu0 hu1 hu2 hu3 hu4 h_school h_1 st0.2.2 st1.2.2 st2.2.2 st3.2.2 st4.2.2 st5.2.2 st6.2.2 st7.2.2 st8.2; have hw0_eq : BitVec.setWidth 8 (sf.readReg64 (Reg.gpr 0#5)) = BitVec.zeroExtend 8 v_cp_221 := hpost
    rw [hw0_eq] at hv_cp_222 hv_cp_223 hv_cp_225 hv_cp_226; rw [hv_cp_222, hv_cp_225] at hv_cp_243 hv_cp_244 hv_cp_245 hv_cp_251; rw [← hv_cp_209] at hv_cp_210 hv_cp_211; rw [← hv_cp_216] at hv_cp_218 hv_cp_219 hv_cp_220 hv_cp_221; rw [← hv_cp_220] at hv_cp_221; have h_sub1 := sc52_cond_sub_l v_cp_191 v_cp_197 (v_cp_202 &&& 4503599627370495#64) (v_cp_214 &&& 4503599627370495#64) (BitVec.setWidth 64 ((v_cp_215 ++ v_cp_214) >>> 52)) v_cp_208 v_cp_209 v_cp_211 (v_cp_210 - 1367801#64) v_cp_217 v_cp_216 v_cp_219 v_cp_220 v_cp_221 v_cp_221 v_cp_223 v_cp_226 v_cp_243 v_cp_244 v_cp_251 st5.2.1 st6.2.1 st7.2.1 st8.1 h_tele.1 hv_cp_208 hv_cp_209 hv_cp_211 (by rw [hv_cp_210]) hv_cp_217 hv_cp_216 hv_cp_219 hv_cp_220 hv_cp_221 rfl hv_cp_223 hv_cp_226 hv_cp_243 hv_cp_244 hv_cp_251; rcases h_sub1 with ⟨ht0, ht1, ht2, ht3, ht4, ht_lt, q, _, hq_eq⟩
    exact ⟨ht0, ht1, ht2, ht3, ht4, ht_lt, mod_eq_of_mont hq_eq h_tele.2⟩
  rcases h_mont1 with ⟨ht0, ht1, ht2, ht3, ht4, ht_lt, ht_mod⟩; wp_sym_steps 11; wp_checkpoint; wp_sym_steps 7; wp_checkpoint; wp_sym_steps 9; wp_checkpoint; wp_sym_steps 3; wp_checkpoint; wp_sym_steps 6; wp_checkpoint; wp_sym_steps 15; wp_checkpoint; wp_sym_steps 7; wp_checkpoint; wp_sym_steps 3; wp_checkpoint; wp_sym_steps 3; wp_checkpoint; wp_sym_steps 5; wp_checkpoint; wp_sym_steps 6; wp_checkpoint; wp_sym_steps 5; wp_checkpoint; wp_sym_steps 10; wp_checkpoint; wp_sym_steps 7; wp_checkpoint; wp_sym_steps 5; wp_checkpoint; wp_sym_steps 5; wp_checkpoint; wp_sym_steps 7; wp_checkpoint; wp_sym_steps 7; wp_checkpoint; wp_sym_steps 3; wp_checkpoint; wp_sym_steps 2; wp_checkpoint; wp_sym_steps 3; wp_checkpoint; wp_sym_steps 6; wp_checkpoint; wp_sym_steps 6; wp_checkpoint; wp_sym_steps 6; wp_checkpoint; wp_sym_steps 3; wp_checkpoint; wp_sym_steps 3; wp_checkpoint; wp_sym_steps 4; wp_checkpoint; wp_sym_steps 5; wp_checkpoint; wp_sym_steps 6; wp_checkpoint; wp_sym_steps 3; wp_checkpoint; wp_sym_steps 2; wp_checkpoint; wp_sym_steps 3; wp_checkpoint; wp_sym_steps 3; wp_checkpoint; wp_sym_steps 2; wp_checkpoint; wp_sym_steps 3; wp_checkpoint; wp_sym_steps 2; wp_checkpoint; wp_sym_steps 6; wp_checkpoint; wp_sym_steps 5; wp_checkpoint; wp_sym_steps 3; wp_checkpoint; wp_sym_steps 3; wp_checkpoint; wp_sym_steps 3; wp_checkpoint; wp_sym_steps 6; wp_checkpoint; wp_sym_steps 2; wp_checkpoint; wp_sym_steps 3; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 6; wp_checkpoint; wp_sym_steps 16; wp_checkpoint; wp_sym_steps 6; wp_checkpoint; wp_sym_steps 10; wp_checkpoint
  wp_steps 1; wp_dalek_call black_box_u8_ok
  wp_simp_pre [hsp_sf_1, hsp_sf, bitvec64_sub_sub_fold]
  rw [hout_cells a_1]; wp_sym_steps; wp_checkpoint
  wp_conv_pre => simp only [sepConj_assoc, sc52Pack5_cells_eq_rest]
  wp_fold_stack; have h_res :
      sc52LimbsBounded (sc52Pack5 v_cp_448 v_cp_449 v_cp_445 v_cp_446 v_cp_450) (2 ^ 52) ∧
      sc52ValOfBytes (sc52Pack5 v_cp_448 v_cp_449 v_cp_445 v_cp_446 v_cp_450) =
        sc52ValOfBytes a_4 * sc52ValOfBytes a_rest % edOrderL := by
    have hp2_t0r0 := mul_const_pair_52 2764609938444603 ht0 (by decide) hv_cp_224 hv_cp_227; have hp2_t1r0 := mul_const_pair_52 2764609938444603 ht1 (by decide) hv_cp_228 hv_cp_241; have hp2_t0r1 := mul_const_pair_52 3768881411696287 ht0 (by decide) hv_cp_229 hv_cp_230; have hp2_t1r1 := mul_const_pair_52 3768881411696287 ht1 (by decide) hv_cp_239 hv_cp_237; have hp2_t0r2 := mul_const_pair_52 1616719297148420 ht0 (by decide) hv_cp_240 hv_cp_238; have hp2_t2r0 := mul_const_pair_52 2764609938444603 ht2 (by decide) hv_cp_315 hv_cp_311; have hp2_t1r2 := mul_const_pair_52 1616719297148420 ht1 (by decide) hv_cp_234 hv_cp_231; have hp2_t0r3 := mul_const_pair_52 1087343033131391 ht0 (by decide) hv_cp_236 hv_cp_235; have hp2_t2r1 := mul_const_pair_52 3768881411696287 ht2 (by decide) hv_cp_246 hv_cp_257; have hp2_t3r0 := mul_const_pair_52 2764609938444603 ht3 (by decide) hv_cp_247 hv_cp_249; have hp2_t1r3 := mul_const_pair_52 1087343033131391 ht1 (by decide) hv_cp_256 hv_cp_255; have hp2_t0r4 := mul_const_pair_52 10175238647962 ht0 (by decide) hv_cp_232 hv_cp_233; have hp2_t2r2 := mul_const_pair_52 1616719297148420 ht2 (by decide) hv_cp_323 hv_cp_335; have hp2_t3r1 := mul_const_pair_52 3768881411696287 ht3 (by decide) hv_cp_344 hv_cp_326; have hp2_t4r0 := mul_const_pair_52 2764609938444603 ht4 (by decide) hv_cp_349 hv_cp_354; have hp2_t2r3 := mul_const_pair_52 1087343033131391 ht2 (by decide) hv_cp_252 hv_cp_248; have hp2_t1r4 := mul_const_pair_52 10175238647962 ht1 (by decide) hv_cp_254 hv_cp_253; have hp2_t3r2 := mul_const_pair_52 1616719297148420 ht3 (by decide) hv_cp_258 hv_cp_250
    have hp2_t4r1 := mul_const_pair_52 3768881411696287 ht4 (by decide) hv_cp_270 hv_cp_262; have hp2_t3r3 := mul_const_pair_52 1087343033131391 ht3 (by decide) hv_cp_263 hv_cp_264; have hp2_t2r4 := mul_const_pair_52 10175238647962 ht2 (by decide) hv_cp_277 hv_cp_274; have hp2_t4r2 := mul_const_pair_52 1616719297148420 ht4 (by decide) hv_cp_280 hv_cp_279; have hp2_t4r3 := mul_const_pair_52 1087343033131391 ht4 (by decide) hv_cp_267 hv_cp_268; have hp2_t3r4 := mul_const_pair_52 10175238647962 ht3 (by decide) hv_cp_283 hv_cp_285; have hp2_t4r4 := mul_const_pair_52 10175238647962 ht4 (by decide) rfl hv_cp_421; rw [hv_cp_259] at hv_cp_278; rw [hv_cp_302, hv_cp_300] at hv_cp_303; have st2_0 := mont_red_step_hi0_eq hp2_t0r0 (by decide) hv_cp_278 hv_cp_290 hv_cp_293 hv_cp_303; have hu2_0 := st2_0.1; have hc2_1_1 := acc128_step_eq hp2_t1r0 hp2_t0r1 (by decide) hv_cp_261 hv_cp_260; have hu2_0_l1 := mul_const_pair_52 3916664325105025 hu2_0 (by decide) hv_cp_301 hv_cp_297; have hc2_1_2 := acc128_step_eq hc2_1_1 hu2_0_l1 (by decide) hv_cp_305 hv_cp_304; have hc2_1_3 := acc128_cinc_step_eq hc2_1_2 (by decide) hv_cp_308 hv_cp_306; rw [← hv_cp_313] at hv_cp_316 hv_cp_318; rw [← hv_cp_314] at hv_cp_318; rw [hv_cp_318, hv_cp_316] at hv_cp_320
    rw [hv_cp_318] at hv_cp_321; have st2_1 := mont_red_step_eq hc2_1_3 (by decide) hv_cp_312 hv_cp_313 hv_cp_314 hv_cp_321 hv_cp_320; have hu2_1 := st2_1.2.1; have hc2_2_1 := acc128_step_eq hp2_t1r1 hp2_t0r2 (by decide) hv_cp_265 hv_cp_266; have hu2_0_l2 := mul_const_pair_52 1367801 hu2_0 (by decide) hv_cp_307 hv_cp_310; have hc2_2_2 := acc128_step_eq hc2_2_1 hu2_0_l2 (by decide) hv_cp_324 hv_cp_322; have hc2_2_3 := acc128_step_eq hc2_2_2 hp2_t2r0 (by decide) hv_cp_327 hv_cp_325; have hu2_1_l1 := mul_const_pair_52 3916664325105025 hu2_1 (by decide) hv_cp_319 hv_cp_317; have hc2_2_4 := acc128_step_eq hc2_2_3 hu2_1_l1 (by decide) hv_cp_329 hv_cp_328; have hc2_2_5 := acc128_step_eq hc2_2_4 st2_1.1 (by decide) hv_cp_332 hv_cp_330; rw [← hv_cp_337] at hv_cp_340 hv_cp_342; rw [← hv_cp_338] at hv_cp_342; rw [hv_cp_342, hv_cp_340] at hv_cp_345; rw [hv_cp_342] at hv_cp_346; have st2_2 := mont_red_step_eq hc2_2_5 (by decide) hv_cp_336 hv_cp_337 hv_cp_338 hv_cp_346 hv_cp_345; have hu2_2 := st2_2.2.1; have hst2_2_eq := st2_2.2.2; rw [Nat.add_right_comm (v_cp_226.toNat * 3768881411696287 + v_cp_223.toNat * 1616719297148420) (v_cp_278.toNat * 1367801) (v_cp_243.toNat * 2764609938444603)] at hst2_2_eq
    have hc2_3_1 := acc128_step_eq hp2_t1r2 hp2_t0r3 (by decide) hv_cp_271 hv_cp_269; have hc2_3_2 := acc128_step_eq hc2_3_1 hp2_t2r1 (by decide) hv_cp_273 hv_cp_272; have hc2_3_3 := acc128_step_eq hc2_3_2 hp2_t3r0 (by decide) hv_cp_275 hv_cp_276; have hu2_1_l2 := mul_const_pair_52 1367801 hu2_1 (by decide) hv_cp_331 hv_cp_334; have hc2_3_4 := acc128_step_eq hc2_3_3 hu2_1_l2 (by decide) hv_cp_347 hv_cp_343; have hu2_2_l1 := mul_const_pair_52 3916664325105025 hu2_2 (by decide) hv_cp_341 hv_cp_339; have hc2_3_5 := acc128_step_eq hc2_3_4 hu2_2_l1 (by decide) hv_cp_350 hv_cp_348; have hc2_3_6 := acc128_step_eq hc2_3_5 st2_2.1 (by decide) hv_cp_353 hv_cp_351; rw [← hv_cp_351] at hv_cp_352; rw [hv_cp_352] at hv_cp_356; rw [← hv_cp_357] at hv_cp_360 hv_cp_361; rw [← hv_cp_358] at hv_cp_361; rw [hv_cp_361, hv_cp_360] at hv_cp_364; rw [hv_cp_361] at hv_cp_373; have st2_3 := mont_red_step_eq hc2_3_6 (by decide) hv_cp_356 hv_cp_357 hv_cp_358 hv_cp_373 hv_cp_364; have hu2_3 := st2_3.2.1; have hc2_4_1 := acc128_step_eq hp2_t1r3 hp2_t0r4 (by decide) hv_cp_281 hv_cp_282; have hu2_0_l4 := l4_shift_pair hv_cp_259 hv_cp_278 rfl hv_cp_366
    rw [← hv_cp_366] at hv_cp_365 hv_cp_362; have hc2_4_2 := acc128_step_eq hc2_4_1 hu2_0_l4 (by decide) hv_cp_365 hv_cp_362; have hc2_4_3 := acc128_step_eq hc2_4_2 hp2_t2r2 (by decide) hv_cp_369 hv_cp_367; have hc2_4_4 := acc128_step_eq hc2_4_3 hp2_t3r1 (by decide) hv_cp_371 hv_cp_370; have hc2_4_5 := acc128_step_eq hc2_4_4 hp2_t4r0 (by decide) hv_cp_374 hv_cp_372; have hu2_2_l2 := mul_const_pair_52 1367801 hu2_2 (by decide) hv_cp_355 hv_cp_359; have hc2_4_6 := acc128_step_eq hc2_4_5 hu2_2_l2 (by decide) hv_cp_377 hv_cp_375; have hu2_3_l1 := mul_const_pair_52 3916664325105025 hu2_3 (by decide) hv_cp_368 hv_cp_363; have hc2_4_7 := acc128_step_eq hc2_4_6 hu2_3_l1 (by decide) hv_cp_379 hv_cp_378; have hc2_4_8 := acc128_step_eq hc2_4_7 st2_3.1 (by decide) hv_cp_382 hv_cp_380; rw [← hv_cp_390] at hv_cp_387 hv_cp_389; rw [← hv_cp_385] at hv_cp_389; rw [hv_cp_389, hv_cp_387] at hv_cp_392; rw [hv_cp_389] at hv_cp_393; have st2_4 := mont_red_step_eq hc2_4_8 (by decide) hv_cp_384 hv_cp_390 hv_cp_385 hv_cp_393 hv_cp_392; have hu2_4 := st2_4.2.1; have hc2_5_1 := acc128_step_eq hp2_t2r3 hp2_t1r4 (by decide) hv_cp_286 hv_cp_284; have hc2_5_2 := acc128_step_eq hc2_5_1 hp2_t3r2 (by decide) hv_cp_288 hv_cp_287
    have hc2_5_3 := acc128_step_eq hc2_5_2 hp2_t4r1 (by decide) hv_cp_291 hv_cp_289; have hu2_1_l4 := l4_shift_pair hv_cp_309 hv_cp_312 rfl hv_cp_395; rw [← hv_cp_395] at hv_cp_394 hv_cp_391; have hc2_5_4 := acc128_step_eq hc2_5_3 hu2_1_l4 (by decide) hv_cp_394 hv_cp_391; have hu2_3_l2 := mul_const_pair_52 1367801 hu2_3 (by decide) hv_cp_381 hv_cp_376; have hc2_5_5 := acc128_step_eq hc2_5_4 hu2_3_l2 (by decide) hv_cp_398 hv_cp_396; have hu2_4_l1 := mul_const_pair_52 3916664325105025 hu2_4 (by decide) hv_cp_386 hv_cp_388; have hc2_5_6 := acc128_step_eq hc2_5_5 hu2_4_l1 (by decide) hv_cp_401 hv_cp_399; have hc2_5_7 := acc128_step_eq hc2_5_6 st2_4.1 (by decide) hv_cp_404 hv_cp_402; have st2_5 := extr52_step_eq hc2_5_7 (by decide) hv_cp_409 hv_cp_407 hv_cp_406; have hc2_6_1 := acc128_step_eq hp2_t3r3 hp2_t2r4 (by decide) hv_cp_294 hv_cp_292; have hc2_6_2 := acc128_step_eq hc2_6_1 hp2_t4r2 (by decide) hv_cp_296 hv_cp_295; have hu2_2_l4 := l4_shift_pair hv_cp_333 hv_cp_336 hv_cp_403 hv_cp_410; rw [← hv_cp_410] at hv_cp_408 hv_cp_405; have hc2_6_3 := acc128_step_eq hc2_6_2 hu2_2_l4 (by decide) hv_cp_408 hv_cp_405; have hu2_4_l2 := mul_const_pair_52 1367801 hu2_4 (by decide) hv_cp_400 hv_cp_397; have hc2_6_4 := acc128_step_eq hc2_6_3 hu2_4_l2 (by decide) hv_cp_412 hv_cp_411; have hc2_6_5 := acc128_step_eq hc2_6_4 st2_5.1 (by decide) hv_cp_414 hv_cp_413
    have st2_6 := extr52_step_eq hc2_6_5 (by decide) hv_cp_422 hv_cp_418 hv_cp_416; have hc2_7_1 := acc128_step_eq hp2_t4r3 hp2_t3r4 (by decide) hv_cp_299 hv_cp_298; have hu2_3_l4 := l4_shift_pair hv_cp_352 hv_cp_356 rfl hv_cp_419; rw [← hv_cp_419] at hv_cp_417 hv_cp_415; have hc2_7_2 := acc128_step_eq hc2_7_1 hu2_3_l4 (by decide) hv_cp_417 hv_cp_415; have hc2_7_3 := acc128_step_eq hc2_7_2 st2_6.1 (by decide) hv_cp_423 hv_cp_420; have st2_7 := extr52_last_step_eq hc2_7_3 (by decide) hv_cp_424 hv_cp_425; have hu2_4_l4 := l4_shift_pair hv_cp_383 hv_cp_384 hv_cp_426 hv_cp_431; rw [← hv_cp_426, ← hv_cp_431, BitVec.add_comm v_cp_426 (BitVec.setWidth 64 ((BitVec.setWidth 128 v_cp_251 * 10175238647962#128) >>> 64))] at hv_cp_430; rw [← hv_cp_431] at hv_cp_427; have hc2_8_1 := acc128_step_eq hp2_t4r4 hu2_4_l4 (by decide) hv_cp_430 hv_cp_427; have hc2_8_2 := acc128_cinc_step_eq hc2_8_1 (by decide) hv_cp_434 hv_cp_433; rw [← hv_cp_433] at hv_cp_435; have st2_8 := extr52_last_step_eq hc2_8_2 (by decide) hv_cp_435 rfl; have h_school2 := sc52_schoolbook_mul_rr v_cp_223 v_cp_226 v_cp_243 v_cp_244 v_cp_251; have hP2_lt := sc52_mul_rr_bound ht_lt; have h_tele2 := sc52_mont_telescope v_cp_278 v_cp_312 v_cp_336 v_cp_356 v_cp_384 v_cp_409 v_cp_422 v_cp_424 v_cp_435 (BitVec.setWidth 64 ((v_cp_434 ++ v_cp_433) >>> 52)) hu2_0 hu2_1 hu2_2 hu2_3 hu2_4 h_school2 hP2_lt st2_0.2 st2_1.2.2 hst2_2_eq st2_3.2.2 st2_4.2.2 st2_5.2.2 st2_6.2.2 st2_7.2 st2_8.2; rw [← hv_cp_437] at hv_cp_439 hv_cp_440 hv_cp_441 hv_cp_442
    rw [← hv_cp_441] at hv_cp_442; have h_sub2 := sc52_cond_sub_l v_cp_409 v_cp_422 v_cp_424 v_cp_435 (BitVec.setWidth 64 ((v_cp_434 ++ v_cp_433) >>> 52)) v_cp_428 v_cp_429 v_cp_436 (v_cp_432 - 1367801#64) v_cp_438 v_cp_437 v_cp_440 v_cp_441 v_cp_442 (sf_1.readReg64 (Reg.gpr 0#5)) v_cp_448 v_cp_449 v_cp_445 v_cp_446 v_cp_450 st2_5.2.1 st2_6.2.1 st2_7.1 st2_8.1 h_tele2.1 hv_cp_428 hv_cp_429 hv_cp_436 (by rw [hv_cp_432]) hv_cp_438 hv_cp_437 hv_cp_440 hv_cp_441 hv_cp_442 hpost_1 hv_cp_448 hv_cp_449 hv_cp_445 hv_cp_446 hv_cp_450; rcases h_sub2 with ⟨hr0, hr1, hr2, hr3, hr4, hr_lt, q, _, hq_eq⟩; rw [sc52ValOfBytes_sc52Pack5, sc52LimbsBounded_sc52Pack5]
    refine ⟨⟨hr0, hr1, hr2, hr3, hr4⟩, ?_⟩
    exact cancel_mont_rr hr_lt ht_mod (mod_eq_of_mont hq_eq h_tele2.2)
  rcases h_res with ⟨h_res_limb, h_res_mod⟩; rcases h_res_limb with ⟨h_len, h_l0, h_l1, h_l2, h_l3, h_l4⟩
  wp_done
set_option exponentiation.threshold 512 in
theorem sc52_mul_ok : Sc52MulOk := by
  intro _
  apply subroutine_ok_mono_sp sc52_mul_core_ok
  · rintro ⟨out, a, b_ptr, out_bs, a_bs, b_bs⟩ s0
    dsimp only [MultiPlacedLib.withCodeLoaded]
    apply sepConj_mono_left
    apply Entails.pure_left
    rintro ⟨h0, h1, h2, hlen, ha, hb_lim, ha_val, hb_val⟩
    refine Entails.pure_right ⟨h0, h1, h2, hlen, ha, hb_lim, ?_⟩ (ProofLib.Entails.refl _)
    exact sc52_mul_bound_of_right_lt_l (by unfold edOrderL at ha_val; omega) hb_val
  · intro _ _ _ _
    dsimp only [MultiPlacedLib.withCodeLoaded]
    exact ProofLib.Entails.refl _
private theorem lsl52_and_mask52 (y : BitVec 64) : (y &&& 4503599627370495#64) <<< 52 = y <<< 52 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, mask52_toNat, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  omega
private theorem lsl44_and_mask52 (y : BitVec 64) : (y &&& 4503599627370495#64) <<< 44 = y <<< 44 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, mask52_toNat, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  omega
private theorem lsl52_or_32_40_48 (w b4 b5 b6 : BitVec 64) : (w ||| b4 <<< 32 ||| b5 <<< 40 ||| b6 <<< 48) <<< 52 = w <<< 52 := by
  ext i hi
  simp only [BitVec.getElem_shiftLeft, BitVec.getElem_or]
  by_cases h52 : i < 52
  · simp [h52]
  · have h32 : i - 52 < 32 := by omega
    have h40 : i - 52 < 40 := by omega
    have h48 : i - 52 < 48 := by omega
    simp [h52, h32, h40, h48]
private theorem lsl44_or_32_40_48 (w b4 b5 b6 : BitVec 64) : (w ||| b4 <<< 32 ||| b5 <<< 40 ||| b6 <<< 48) <<< 44 = w <<< 44 := by
  ext i hi
  simp only [BitVec.getElem_shiftLeft, BitVec.getElem_or]
  by_cases h44 : i < 44
  · simp [h44]
  · have h32 : i - 44 < 32 := by omega
    have h40 : i - 44 < 40 := by omega
    have h48 : i - 44 < 48 := by omega
    simp [h44, h32, h40, h48]
private theorem lsl52_or_32_40 (w b4 b5 : BitVec 64) : (w ||| b4 <<< 32 ||| b5 <<< 40) <<< 52 = w <<< 52 := by
  ext i hi
  simp only [BitVec.getElem_shiftLeft, BitVec.getElem_or]
  by_cases h52 : i < 52
  · simp [h52]
  · have h32 : i - 52 < 32 := by omega
    have h40 : i - 52 < 40 := by omega
    simp [h52, h32, h40]
private theorem lsl44_or_32_40 (w b4 b5 : BitVec 64) : (w ||| b4 <<< 32 ||| b5 <<< 40) <<< 44 = w <<< 44 := by
  ext i hi
  simp only [BitVec.getElem_shiftLeft, BitVec.getElem_or]
  by_cases h44 : i < 44
  · simp [h44]
  · have h32 : i - 44 < 32 := by omega
    have h40 : i - 44 < 40 := by omega
    simp [h44, h32, h40]
private theorem sub_lsl52_eq_mul (x : BitVec 64) : x <<< 52 - x = x * 4503599627370495#64 := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt; rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega
private theorem sub_lsl44_eq_mul (x : BitVec 64) : x <<< 44 - x = x * 17592186044415#64 := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt; rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega
set_option exponentiation.threshold 512 in
private theorem sc52_schoolbook_mul_r (a0 a1 a2 a3 a4 : BitVec 64) :
    (a0.toNat * 4302102966953709) + (a1.toNat * 4302102966953709 + a0.toNat * 1049714374468698) * 2 ^ 52 + (a1.toNat * 1049714374468698 + a0.toNat * 4503599278581019 + a2.toNat * 4302102966953709) * 2 ^ 104 + (a1.toNat * 4503599278581019 + a0.toNat * 4503599627370495 + a2.toNat * 1049714374468698 + a3.toNat * 4302102966953709) * 2 ^ 156 + ((a1.toNat * 4503599627370495 + a0.toNat * 17592186044415) + a2.toNat * 4503599278581019 + a3.toNat * 1049714374468698 + a4.toNat * 4302102966953709) * 2 ^ 208 +
    (a2.toNat * 4503599627370495 + a1.toNat * 17592186044415 + a3.toNat * 4503599278581019 + a4.toNat * 1049714374468698) * 2 ^ 260 + (a3.toNat * 4503599627370495 + a2.toNat * 17592186044415 + a4.toNat * 4503599278581019) * 2 ^ 312 + (a4.toNat * 4503599627370495 + a3.toNat * 17592186044415) * 2 ^ 364 + (a4.toNat * 17592186044415) * 2 ^ 416 =
    sc52Val a0 a1 a2 a3 a4 *
      sc52Val 4302102966953709#64 1049714374468698#64 4503599278581019#64 4503599627370495#64 17592186044415#64 := by
  unfold sc52Val; simp only [BitVec.toNat_ofNat]
  grind
theorem exists_bytes32 {bs : List (BitVec 8)} (h : bs.length = 32) : ∃ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : BitVec 8,
      bs = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
            b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31] := by
  have h0 : (bs.take 16).length = 16 := (by simp [h]); have h1 : (bs.drop 16).length = 16 := (by simp [h]); have h00 : ((bs.take 16).take 8).length = 8 := (by simp [h0])
  have h01 : ((bs.take 16).drop 8).length = 8 := (by simp [h0]); have h10 : ((bs.drop 16).take 8).length = 8 := (by simp [h1]); have h11 : ((bs.drop 16).drop 8).length = 8 := (by simp [h])
  rcases h00_eq : (bs.take 16).take 8 with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (rw [h00_eq] at h00; simp at h00; done)
  rcases h01_eq : (bs.take 16).drop 8 with _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (rw [h01_eq] at h01; simp at h01; done)
  rcases h10_eq : (bs.drop 16).take 8 with _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (rw [h10_eq] at h10; simp at h10; done)
  rcases h11_eq : (bs.drop 16).drop 8 with _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (rw [h11_eq] at h11; simp at h11; done)
  refine ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, ?_⟩
  have ht16 : bs.take 16 = (bs.take 16).take 8 ++ (bs.take 16).drop 8 := (List.take_append_drop 8 _).symm; have hd16 : bs.drop 16 = (bs.drop 16).take 8 ++ (bs.drop 16).drop 8 := (List.take_append_drop 8 _).symm; have hbs : bs = bs.take 16 ++ bs.drop 16 := (List.take_append_drop 16 bs).symm; rw [hbs, ht16, hd16, h00_eq, h01_eq, h10_eq, h11_eq]
  rfl
theorem or_shiftLeft_toNat {w : Nat} {a b : BitVec w} {sh : Nat} (ha : a.toNat < 2 ^ sh) (hb : b.toNat * 2 ^ sh < 2 ^ w) : (a ||| (b <<< sh)).toNat = a.toNat + b.toNat * 2 ^ sh := by
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hb]
  exact ProofLib.BV.Bits.NatLemmas.or_eq_add_of_lt_dvd ha (Nat.mul_mod_left b.toNat (2 ^ sh))
theorem zext_toNat_eq {v w : Nat} (x : BitVec v) (h : v ≤ w) : (BitVec.zeroExtend w x).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) h))]
private theorem byte_low52 (x : BitVec 64) (sh : Nat) (hsh : sh + 8 ≤ 52) : (BitVec.zeroExtend 8 (x >>> sh)).toNat = ((x &&& 4503599627370495#64).toNat / 2 ^ sh) % 256 := by
  have h_eq : BitVec.zeroExtend 8 (x >>> sh) =
      BitVec.zeroExtend 8 ((x &&& 4503599627370495#64) >>> sh) := by
    ext i hi
    simp only [BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and]
    have hbit : (4503599627370495#64).getLsbD (sh + i) = true := by
      change ((BitVec.allOnes 52).setWidth 64).getLsbD (sh + i) = true
      simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, Bool.and_eq_true, decide_eq_true_eq]
      omega
    simp [hbit]
  rw [h_eq, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
private theorem byte_low64 (x : BitVec 64) (sh : Nat) : (BitVec.zeroExtend 8 (x >>> sh)).toNat = (x.toNat / 2 ^ sh) % 256 := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
private theorem bfi_byte_eq_or (x y : BitVec 64) : BitVec.zeroExtend 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (x >>> 48)) &&& 18446744069414584335#64 |||
        (BitVec.setWidth 64 (BitVec.setWidth 32 y) &&& 268435455#64) <<< 4) =
    BitVec.zeroExtend 8 (((x &&& 4503599627370495#64) >>> 48) ||| ((y &&& 15#64) <<< 4)) := by
  ext i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp
private theorem or_shiftLeft4_toNat (a b : BitVec 64) (ha : a.toNat < 16) (hb : b.toNat < 16) : (BitVec.zeroExtend 8 (a ||| (b <<< 4))).toNat = a.toNat + b.toNat * 16 := by
  rw [BitVec.toNat_setWidth, or_shiftLeft_toNat (by omega) (by omega)]
  omega
private theorem byte_bfi_6 (x y : BitVec 64) :
    (BitVec.zeroExtend 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (x >>> 48)) &&& 18446744069414584335#64 ||| (BitVec.setWidth 64 (BitVec.setWidth 32 y) &&& 268435455#64) <<< 4)).toNat =
    (x &&& 4503599627370495#64).toNat / 2 ^ 48 + ((y &&& 4503599627370495#64).toNat % 16) * 16 := by
  rw [bfi_byte_eq_or]
  have hx : ((x &&& 4503599627370495#64) >>> 48).toNat = (x &&& 4503599627370495#64).toNat / 2 ^ 48 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hx_lt : ((x &&& 4503599627370495#64) >>> 48).toNat < 16 := by
    rw [hx, mask52_toNat]; omega
  have hy : (y &&& 15#64).toNat = (y &&& 4503599627370495#64).toNat % 16 := by
    have : (y &&& 15#64).toNat = y.toNat % 16 := by
      rw [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod y.toNat 4
    rw [this, mask52_toNat]; omega
  have hy_lt : (y &&& 15#64).toNat < 16 := (by rw [hy]; omega); rw [or_shiftLeft4_toNat _ _ hx_lt hy_lt, hx, hy]
private theorem byte_bfi_19 (x y : BitVec 64) :
    (BitVec.zeroExtend 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (x >>> 48)) &&& 18446744069414584335#64 ||| (BitVec.setWidth 64 (BitVec.setWidth 32 y) &&& 268435455#64) <<< 4)))).toNat =
    (x &&& 4503599627370495#64).toNat / 2 ^ 48 + ((y &&& 4503599627370495#64).toNat % 16) * 16 := by
  have htrunc : BitVec.zeroExtend 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (x >>> 48)) &&& 18446744069414584335#64 ||| (BitVec.setWidth 64 (BitVec.setWidth 32 y) &&& 268435455#64) <<< 4))) = BitVec.zeroExtend 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (x >>> 48)) &&& 18446744069414584335#64 |||
          (BitVec.setWidth 64 (BitVec.setWidth 32 y) &&& 268435455#64) <<< 4) := by
    ext i hi
    simp
  rw [htrunc, byte_bfi_6]
theorem pack16_toNat (b0 b1 : BitVec 8) : (pack16 b0 b1).toNat = b0.toNat + b1.toNat * 2 ^ 8 := by
  unfold pack16; rw [ProofLib.BV.Bits.BVLemmas.toNat_append_mul]; omega
theorem pack32_toNat (b0 b1 b2 b3 : BitVec 8) : (pack32 b0 b1 b2 b3).toNat = b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24 := by
  unfold pack32; repeat rw [ProofLib.BV.Bits.BVLemmas.toNat_append_mul]
  omega
theorem setWidth64_extr128_toNat (hi lo : BitVec 64) (sh : Nat) (h : (hi.toNat * 2 ^ 64 + lo.toNat) / 2 ^ sh < 2 ^ 64) : (BitVec.setWidth 64 (((hi ++ lo) : BitVec 128) >>> sh)).toNat =
      (hi.toNat * 2 ^ 64 + lo.toNat) / 2 ^ sh := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, ProofLib.BV.Bits.BVLemmas.toNat_append_mul, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt h]
set_option exponentiation.threshold 512 in
private theorem unpack_pair01 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : BitVec 8)
    (a0 a1 : BitVec 64) (ha0 : a0 = (BitVec.zeroExtend 64 (pack32 b0 b1 b2 b3) ||| BitVec.zeroExtend 64 b4 <<< 32 ||| BitVec.zeroExtend 64 b5 <<< 40 ||| BitVec.zeroExtend 64 b6 <<< 48) &&& 4503599627370495#64) (ha1 : a1 = BitVec.setWidth 64 (((BitVec.zeroExtend 64 (pack32 b8 b9 b10 b11) ||| BitVec.zeroExtend 64 b12 <<< 32) ++ (BitVec.zeroExtend 64 (pack32 b0 b1 b2 b3) ||| BitVec.zeroExtend 64 b4 <<< 32 ||| BitVec.zeroExtend 64 b5 <<< 40 ||| BitVec.zeroExtend 64 b6 <<< 48 ||| BitVec.zeroExtend 64 b7 <<< 56)) >>> 52)) :
    a0.toNat < 2 ^ 52 ∧ a1.toNat < 2 ^ 52 ∧
    a0.toNat + a1.toNat * 2 ^ 52 =
      b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24 +
      b4.toNat * 2 ^ 32 + b5.toNat * 2 ^ 40 + b6.toNat * 2 ^ 48 + b7.toNat * 2 ^ 56 +
      b8.toNat * 2 ^ 64 + b9.toNat * 2 ^ 72 + b10.toNat * 2 ^ 80 + b11.toNat * 2 ^ 88 +
      b12.toNat * 2 ^ 96 := by
  have hp0 := zext_toNat_eq (pack32 b0 b1 b2 b3) (w := 64) (by decide); rw [pack32_toNat] at hp0; have hp8 := zext_toNat_eq (pack32 b8 b9 b10 b11) (w := 64) (by decide); rw [pack32_toNat] at hp8; have hb4 := zext_toNat_eq b4 (w := 64) (by decide); have hb5 := zext_toNat_eq b5 (w := 64) (by decide); have hb6 := zext_toNat_eq b6 (w := 64) (by decide); have hb7 := zext_toNat_eq b7 (w := 64) (by decide); have hb12 := zext_toNat_eq b12 (w := 64) (by decide); have s4 : (BitVec.zeroExtend 64 (pack32 b0 b1 b2 b3) ||| BitVec.zeroExtend 64 b4 <<< 32).toNat =
      (BitVec.zeroExtend 64 (pack32 b0 b1 b2 b3)).toNat + b4.toNat * 2 ^ 32 := by
    rw [or_shiftLeft_toNat (by omega) (by omega), hb4]
  have s5 : (BitVec.zeroExtend 64 (pack32 b0 b1 b2 b3) ||| BitVec.zeroExtend 64 b4 <<< 32 ||| BitVec.zeroExtend 64 b5 <<< 40).toNat =
      (BitVec.zeroExtend 64 (pack32 b0 b1 b2 b3)).toNat + b4.toNat * 2 ^ 32 + b5.toNat * 2 ^ 40 := by
    rw [or_shiftLeft_toNat (by omega) (by omega), s4, hb5]
  have s6 : (BitVec.zeroExtend 64 (pack32 b0 b1 b2 b3) ||| BitVec.zeroExtend 64 b4 <<< 32 ||| BitVec.zeroExtend 64 b5 <<< 40 ||| BitVec.zeroExtend 64 b6 <<< 48).toNat = (BitVec.zeroExtend 64 (pack32 b0 b1 b2 b3)).toNat + b4.toNat * 2 ^ 32 +
      b5.toNat * 2 ^ 40 + b6.toNat * 2 ^ 48 := by
    rw [or_shiftLeft_toNat (by omega) (by omega), s5, hb6]
  have s7 : (BitVec.zeroExtend 64 (pack32 b0 b1 b2 b3) ||| BitVec.zeroExtend 64 b4 <<< 32 ||| BitVec.zeroExtend 64 b5 <<< 40 ||| BitVec.zeroExtend 64 b6 <<< 48 ||| BitVec.zeroExtend 64 b7 <<< 56).toNat = (BitVec.zeroExtend 64 (pack32 b0 b1 b2 b3)).toNat + b4.toNat * 2 ^ 32 +
      b5.toNat * 2 ^ 40 + b6.toNat * 2 ^ 48 + b7.toNat * 2 ^ 56 := by
    rw [or_shiftLeft_toNat (by omega) (by omega), s6, hb7]
  have s12 : (BitVec.zeroExtend 64 (pack32 b8 b9 b10 b11) ||| BitVec.zeroExtend 64 b12 <<< 32).toNat =
      (BitVec.zeroExtend 64 (pack32 b8 b9 b10 b11)).toNat + b12.toNat * 2 ^ 32 := by
    rw [or_shiftLeft_toNat (by omega) (by omega), hb12]
  have ha0' : a0.toNat = ((BitVec.zeroExtend 64 (pack32 b0 b1 b2 b3)).toNat + b4.toNat * 2 ^ 32 +
       b5.toNat * 2 ^ 40 + b6.toNat * 2 ^ 48) % 2 ^ 52 := by
    rw [ha0, mask52_toNat, s6]
  have ha1' : a1.toNat = (((BitVec.zeroExtend 64 (pack32 b8 b9 b10 b11)).toNat + b12.toNat * 2 ^ 32) * 2 ^ 64 + ((BitVec.zeroExtend 64 (pack32 b0 b1 b2 b3)).toNat + b4.toNat * 2 ^ 32 +
        b5.toNat * 2 ^ 40 + b6.toNat * 2 ^ 48 + b7.toNat * 2 ^ 56)) / 2 ^ 52 := by
    rw [ha1, setWidth64_extr128_toNat _ _ 52 (by omega), s12, s7]
  omega
set_option exponentiation.threshold 512 in
private theorem unpack_pair23 (b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 : BitVec 8)
    (a2 a3 : BitVec 64) (ha2 : a2 = BitVec.setWidth 64 ((BitVec.zeroExtend 64 (pack32 b16 b17 b18 b19) ++ (BitVec.zeroExtend 64 b13 <<< 40 ||| BitVec.zeroExtend 64 b14 <<< 48 ||| BitVec.zeroExtend 64 b15 <<< 56)) >>> 40) &&& 4503599627370495#64) (ha3 : a3 = BitVec.setWidth 64 ((BitVec.zeroExtend 64 (pack16 b24 b25) ++ (BitVec.zeroExtend 64 (pack32 b16 b17 b18 b19) ||| BitVec.zeroExtend 64 (pack32 b20 b21 b22 b23) <<< 32)) >>> 28)) :
    a2.toNat < 2 ^ 52 ∧ a3.toNat < 2 ^ 52 ∧
    a2.toNat + a3.toNat * 2 ^ 52 =
      b13.toNat + b14.toNat * 2 ^ 8 + b15.toNat * 2 ^ 16 + b16.toNat * 2 ^ 24 +
      b17.toNat * 2 ^ 32 + b18.toNat * 2 ^ 40 + b19.toNat * 2 ^ 48 + b20.toNat * 2 ^ 56 +
      b21.toNat * 2 ^ 64 + b22.toNat * 2 ^ 72 + b23.toNat * 2 ^ 80 + b24.toNat * 2 ^ 88 +
      b25.toNat * 2 ^ 96 := by
  have hp16 := zext_toNat_eq (pack32 b16 b17 b18 b19) (w := 64) (by decide); rw [pack32_toNat] at hp16; have hp20 := zext_toNat_eq (pack32 b20 b21 b22 b23) (w := 64) (by decide); rw [pack32_toNat] at hp20; have hp24 := zext_toNat_eq (pack16 b24 b25) (w := 64) (by decide); rw [pack16_toNat] at hp24
  have hb13 : (BitVec.zeroExtend 64 b13 <<< 40).toNat = b13.toNat * 2 ^ 40 := by
    rw [BitVec.toNat_shiftLeft, zext_toNat_eq b13 (w := 64) (by decide), Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  have hb14 := zext_toNat_eq b14 (w := 64) (by decide); have hb15 := zext_toNat_eq b15 (w := 64) (by decide); have s14 : (BitVec.zeroExtend 64 b13 <<< 40 ||| BitVec.zeroExtend 64 b14 <<< 48).toNat =
      b13.toNat * 2 ^ 40 + b14.toNat * 2 ^ 48 := by
    rw [or_shiftLeft_toNat (by omega) (by omega), hb13, hb14]
  have s15 : (BitVec.zeroExtend 64 b13 <<< 40 ||| BitVec.zeroExtend 64 b14 <<< 48 ||| BitVec.zeroExtend 64 b15 <<< 56).toNat =
      b13.toNat * 2 ^ 40 + b14.toNat * 2 ^ 48 + b15.toNat * 2 ^ 56 := by
    rw [or_shiftLeft_toNat (by omega) (by omega), s14, hb15]
  have s20 : (BitVec.zeroExtend 64 (pack32 b16 b17 b18 b19) ||| BitVec.zeroExtend 64 (pack32 b20 b21 b22 b23) <<< 32).toNat = (BitVec.zeroExtend 64 (pack32 b16 b17 b18 b19)).toNat +
      (BitVec.zeroExtend 64 (pack32 b20 b21 b22 b23)).toNat * 2 ^ 32 := by
    rw [or_shiftLeft_toNat (by omega) (by omega)]
  have ha2' : a2.toNat = ((BitVec.zeroExtend 64 (pack32 b16 b17 b18 b19)).toNat * 2 ^ 64 +
      (b13.toNat * 2 ^ 40 + b14.toNat * 2 ^ 48 + b15.toNat * 2 ^ 56)) / 2 ^ 40 % 2 ^ 52 := by
    rw [ha2, mask52_toNat, setWidth64_extr128_toNat _ _ 40 (by omega), s15]
  have ha3' : a3.toNat = ((BitVec.zeroExtend 64 (pack16 b24 b25)).toNat * 2 ^ 64 + ((BitVec.zeroExtend 64 (pack32 b16 b17 b18 b19)).toNat +
       (BitVec.zeroExtend 64 (pack32 b20 b21 b22 b23)).toNat * 2 ^ 32)) / 2 ^ 28 := by
    rw [ha3, setWidth64_extr128_toNat _ _ 28 (by omega), s20]
  omega
set_option exponentiation.threshold 512 in
private theorem unpack_limb4 (b26 b27 b28 b29 b30 b31 : BitVec 8) (a4 : BitVec 64)
    (ha4 : a4 = BitVec.zeroExtend 64 (pack32 b26 b27 b28 b29) ||| BitVec.zeroExtend 64 b30 <<< 32 ||| BitVec.zeroExtend 64 b31 <<< 40) :
    a4.toNat < 2 ^ 48 ∧
    a4.toNat =
      b26.toNat + b27.toNat * 2 ^ 8 + b28.toNat * 2 ^ 16 + b29.toNat * 2 ^ 24 +
      b30.toNat * 2 ^ 32 + b31.toNat * 2 ^ 40 := by
  have hp26 := zext_toNat_eq (pack32 b26 b27 b28 b29) (w := 64) (by decide); rw [pack32_toNat] at hp26; have hb30 := zext_toNat_eq b30 (w := 64) (by decide); have hb31 := zext_toNat_eq b31 (w := 64) (by decide); have s30 : (BitVec.zeroExtend 64 (pack32 b26 b27 b28 b29) ||| BitVec.zeroExtend 64 b30 <<< 32).toNat =
      (BitVec.zeroExtend 64 (pack32 b26 b27 b28 b29)).toNat + b30.toNat * 2 ^ 32 := by
    rw [or_shiftLeft_toNat (by omega) (by omega), hb30]
  have ha4' : a4.toNat = (BitVec.zeroExtend 64 (pack32 b26 b27 b28 b29)).toNat +
      b30.toNat * 2 ^ 32 + b31.toNat * 2 ^ 40 := by
    rw [ha4, or_shiftLeft_toNat (by omega) (by omega), s30, hb31]
  omega
set_option exponentiation.threshold 512 in
theorem sc52_unpack_bytes32 (bs : List (BitVec 8)) (h : bs.length = 32)
    (a0 a1 a2 a3 a4 : BitVec 64) (ha0 : a0 = (BitVec.zeroExtend 64 (pack32 (bs.getD 0 0#8) (bs.getD 1 0#8) (bs.getD 2 0#8) (bs.getD 3 0#8)) ||| BitVec.zeroExtend 64 (bs.getD 4 0#8) <<< 32 ||| BitVec.zeroExtend 64 (bs.getD 5 0#8) <<< 40 ||| BitVec.zeroExtend 64 (bs.getD 6 0#8) <<< 48) &&& 4503599627370495#64) (ha1 : a1 = BitVec.setWidth 64 (((BitVec.zeroExtend 64 (pack32 (bs.getD 8 0#8) (bs.getD 9 0#8) (bs.getD 10 0#8) (bs.getD 11 0#8)) ||| BitVec.zeroExtend 64 (bs.getD 12 0#8) <<< 32) ++ (BitVec.zeroExtend 64 (pack32 (bs.getD 0 0#8) (bs.getD 1 0#8) (bs.getD 2 0#8) (bs.getD 3 0#8)) ||| BitVec.zeroExtend 64 (bs.getD 4 0#8) <<< 32 ||| BitVec.zeroExtend 64 (bs.getD 5 0#8) <<< 40 ||| BitVec.zeroExtend 64 (bs.getD 6 0#8) <<< 48 ||| BitVec.zeroExtend 64 (bs.getD 7 0#8) <<< 56)) >>> 52)) (ha2 : a2 = BitVec.setWidth 64 ((BitVec.zeroExtend 64 (pack32 (bs.getD 16 0#8) (bs.getD 17 0#8) (bs.getD 18 0#8) (bs.getD 19 0#8)) ++ (BitVec.zeroExtend 64 (bs.getD 13 0#8) <<< 40 ||| BitVec.zeroExtend 64 (bs.getD 14 0#8) <<< 48 ||| BitVec.zeroExtend 64 (bs.getD 15 0#8) <<< 56)) >>> 40) &&& 4503599627370495#64) (ha3 : a3 = BitVec.setWidth 64 ((BitVec.zeroExtend 64 (pack16 (bs.getD 24 0#8) (bs.getD 25 0#8)) ++ (BitVec.zeroExtend 64 (pack32 (bs.getD 16 0#8) (bs.getD 17 0#8) (bs.getD 18 0#8) (bs.getD 19 0#8)) ||| BitVec.zeroExtend 64 (pack32 (bs.getD 20 0#8) (bs.getD 21 0#8) (bs.getD 22 0#8) (bs.getD 23 0#8)) <<< 32)) >>> 28))
    (ha4 : a4 = BitVec.zeroExtend 64 (pack32 (bs.getD 26 0#8) (bs.getD 27 0#8) (bs.getD 28 0#8) (bs.getD 29 0#8)) ||| BitVec.zeroExtend 64 (bs.getD 30 0#8) <<< 32 ||| BitVec.zeroExtend 64 (bs.getD 31 0#8) <<< 40) :
    a0.toNat < 2 ^ 52 ∧ a1.toNat < 2 ^ 52 ∧ a2.toNat < 2 ^ 52 ∧ a3.toNat < 2 ^ 52 ∧ a4.toNat < 2 ^ 52 ∧ sc52Val a0 a1 a2 a3 a4 = leBytesToNat bs ∧ leBytesToNat bs < 2 ^ 256 := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, rfl⟩ := exists_bytes32 h; have hp01 := unpack_pair01 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 a0 a1 ha0 ha1; have hp23 := unpack_pair23 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 a2 a3 ha2 ha3; have hp4 := unpack_limb4 b26 b27 b28 b29 b30 b31 a4 ha4; have hle : leBytesToNat [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31] = (a0.toNat + a1.toNat * 2 ^ 52) + (a2.toNat + a3.toNat * 2 ^ 52) * 2 ^ 104 +
      a4.toNat * 2 ^ 208 := by
    unfold leBytesToNat; simp only [List.foldr]
    omega
  unfold sc52Val
  refine ⟨hp01.1, hp01.2.1, hp23.1, hp23.2.1, by omega, by omega, by omega⟩
@[expose] def sc52BfiByte (x y : BitVec 64) : BitVec 8 :=
  BitVec.zeroExtend 8
    (BitVec.setWidth 64 (BitVec.setWidth 32 (x >>> 48)) &&& 18446744069414584335#64 ||| (BitVec.setWidth 64 (BitVec.setWidth 32 y) &&& 268435455#64) <<< 4)
@[expose] def sc52PackBytes32 (add0 add1 add2 add3 add4 : BitVec 64) : List (BitVec 8) :=
  [ BitVec.zeroExtend 8 add0,
    BitVec.zeroExtend 8 (add0 >>> 8), BitVec.zeroExtend 8 (add0 >>> 16), BitVec.zeroExtend 8 (add0 >>> 24), BitVec.zeroExtend 8 (add0 >>> 32), BitVec.zeroExtend 8 (add0 >>> 40), sc52BfiByte add0 add1,
    BitVec.zeroExtend 8 (add1 >>> 4), BitVec.zeroExtend 8 (add1 >>> 12), BitVec.zeroExtend 8 (add1 >>> 20), BitVec.zeroExtend 8 (add1 >>> 28), BitVec.zeroExtend 8 (add1 >>> 36), BitVec.zeroExtend 8 (add1 >>> 44),
    BitVec.zeroExtend 8 add2, BitVec.zeroExtend 8 (add2 >>> 8), BitVec.zeroExtend 8 (add2 >>> 16), BitVec.zeroExtend 8 (add2 >>> 24), BitVec.zeroExtend 8 (add2 >>> 32), BitVec.zeroExtend 8 (add2 >>> 40),
    sc52BfiByte add2 add3, BitVec.zeroExtend 8 (add3 >>> 4), BitVec.zeroExtend 8 (add3 >>> 12), BitVec.zeroExtend 8 (add3 >>> 20), BitVec.zeroExtend 8 (add3 >>> 28), BitVec.zeroExtend 8 (add3 >>> 36),
    BitVec.zeroExtend 8 (add3 >>> 44), BitVec.zeroExtend 8 add4, BitVec.zeroExtend 8 (add4 >>> 8), BitVec.zeroExtend 8 (add4 >>> 16), BitVec.zeroExtend 8 (add4 >>> 24), BitVec.zeroExtend 8 (add4 >>> 32),
    BitVec.zeroExtend 8 (add4 >>> 40) ]
private theorem bv8_eq_ofNat {b : BitVec 8} {m : Nat} (h : b.toNat = m % 256) : b = BitVec.ofNat 8 (m % 256) := by
  apply BitVec.eq_of_toNat_eq
  rw [h, BitVec.toNat_ofNat]; change m % 256 = (m % 256) % 256
  omega
private theorem byte_low52_0 (x : BitVec 64) : (BitVec.zeroExtend 8 x).toNat = (x &&& 4503599627370495#64).toNat % 256 := by
  have h := byte_low52 x 0 (by decide)
  simpa using h
set_option exponentiation.threshold 512 in
private theorem pack_pair_13 (x y rx ry : BitVec 64) (V : Nat)
    (hrx : rx = x &&& 4503599627370495#64) (hry : ry = y &&& 4503599627370495#64) (hV : V % 2 ^ 104 = rx.toNat + ry.toNat * 2 ^ 52) :
    BitVec.zeroExtend 8 x = BitVec.ofNat 8 ((V / 256 ^ 0) % 256) ∧ BitVec.zeroExtend 8 (x >>> 8) = BitVec.ofNat 8 ((V / 256 ^ 1) % 256) ∧ BitVec.zeroExtend 8 (x >>> 16) = BitVec.ofNat 8 ((V / 256 ^ 2) % 256) ∧
    BitVec.zeroExtend 8 (x >>> 24) = BitVec.ofNat 8 ((V / 256 ^ 3) % 256) ∧ BitVec.zeroExtend 8 (x >>> 32) = BitVec.ofNat 8 ((V / 256 ^ 4) % 256) ∧ BitVec.zeroExtend 8 (x >>> 40) = BitVec.ofNat 8 ((V / 256 ^ 5) % 256) ∧
    sc52BfiByte x y = BitVec.ofNat 8 ((V / 256 ^ 6) % 256) ∧ BitVec.zeroExtend 8 (y >>> 4) = BitVec.ofNat 8 ((V / 256 ^ 7) % 256) ∧ BitVec.zeroExtend 8 (y >>> 12) = BitVec.ofNat 8 ((V / 256 ^ 8) % 256) ∧
    BitVec.zeroExtend 8 (y >>> 20) = BitVec.ofNat 8 ((V / 256 ^ 9) % 256) ∧ BitVec.zeroExtend 8 (y >>> 28) = BitVec.ofNat 8 ((V / 256 ^ 10) % 256) ∧ BitVec.zeroExtend 8 (y >>> 36) = BitVec.ofNat 8 ((V / 256 ^ 11) % 256) ∧
    BitVec.zeroExtend 8 (y >>> 44) = BitVec.ofNat 8 ((V / 256 ^ 12) % 256) := by
  have hx_lt : rx.toNat < 2 ^ 52 := (by rw [hrx, mask52_toNat]; omega); have hy_lt : ry.toNat < 2 ^ 52 := (by rw [hry, mask52_toNat]; omega); have h0 := byte_low52_0 x; rw [← hrx] at h0
  have h1 := byte_low52 x 8 (by decide); rw [← hrx] at h1; have h2 := byte_low52 x 16 (by decide); rw [← hrx] at h2; have h3 := byte_low52 x 24 (by decide); rw [← hrx] at h3; have h4 := byte_low52 x 32 (by decide); rw [← hrx] at h4; have h5 := byte_low52 x 40 (by decide); rw [← hrx] at h5
  have h6 : (sc52BfiByte x y).toNat = rx.toNat / 2 ^ 48 + (ry.toNat % 16) * 16 := by
    unfold sc52BfiByte; rw [byte_bfi_6, ← hrx, ← hry]
  have h7 := byte_low52 y 4 (by decide); rw [← hry] at h7; have h8 := byte_low52 y 12 (by decide); rw [← hry] at h8; have h9 := byte_low52 y 20 (by decide); rw [← hry] at h9; have h10 := byte_low52 y 28 (by decide); rw [← hry] at h10; have h11 := byte_low52 y 36 (by decide); rw [← hry] at h11; have h12 := byte_low52 y 44 (by decide); rw [← hry] at h12
  refine ⟨bv8_eq_ofNat (by omega), bv8_eq_ofNat (by omega), bv8_eq_ofNat (by omega), bv8_eq_ofNat (by omega), bv8_eq_ofNat (by omega), bv8_eq_ofNat (by omega), bv8_eq_ofNat (by omega), bv8_eq_ofNat (by omega), bv8_eq_ofNat (by omega), bv8_eq_ofNat (by omega), bv8_eq_ofNat (by omega), bv8_eq_ofNat (by omega), bv8_eq_ofNat (by omega)⟩
set_option exponentiation.threshold 512 in
private theorem pack_pair_23 (x y rx ry : BitVec 64) (V : Nat)
    (hrx : rx = x &&& 4503599627370495#64) (hry : ry = y &&& 4503599627370495#64) (hV : (V / 2 ^ 104) % 2 ^ 104 = rx.toNat + ry.toNat * 2 ^ 52) :
    BitVec.zeroExtend 8 x = BitVec.ofNat 8 ((V / 256 ^ 13) % 256) ∧ BitVec.zeroExtend 8 (x >>> 8) = BitVec.ofNat 8 ((V / 256 ^ 14) % 256) ∧ BitVec.zeroExtend 8 (x >>> 16) = BitVec.ofNat 8 ((V / 256 ^ 15) % 256) ∧
    BitVec.zeroExtend 8 (x >>> 24) = BitVec.ofNat 8 ((V / 256 ^ 16) % 256) ∧ BitVec.zeroExtend 8 (x >>> 32) = BitVec.ofNat 8 ((V / 256 ^ 17) % 256) ∧ BitVec.zeroExtend 8 (x >>> 40) = BitVec.ofNat 8 ((V / 256 ^ 18) % 256) ∧
    sc52BfiByte x y = BitVec.ofNat 8 ((V / 256 ^ 19) % 256) ∧ BitVec.zeroExtend 8 (y >>> 4) = BitVec.ofNat 8 ((V / 256 ^ 20) % 256) ∧ BitVec.zeroExtend 8 (y >>> 12) = BitVec.ofNat 8 ((V / 256 ^ 21) % 256) ∧
    BitVec.zeroExtend 8 (y >>> 20) = BitVec.ofNat 8 ((V / 256 ^ 22) % 256) ∧ BitVec.zeroExtend 8 (y >>> 28) = BitVec.ofNat 8 ((V / 256 ^ 23) % 256) ∧ BitVec.zeroExtend 8 (y >>> 36) = BitVec.ofNat 8 ((V / 256 ^ 24) % 256) ∧
    BitVec.zeroExtend 8 (y >>> 44) = BitVec.ofNat 8 ((V / 256 ^ 25) % 256) := by
  have hx_lt : rx.toNat < 2 ^ 52 := (by rw [hrx, mask52_toNat]; omega); have hy_lt : ry.toNat < 2 ^ 52 := (by rw [hry, mask52_toNat]; omega); have h0 := byte_low52_0 x; rw [← hrx] at h0
  have h1 := byte_low52 x 8 (by decide); rw [← hrx] at h1; have h2 := byte_low52 x 16 (by decide); rw [← hrx] at h2; have h3 := byte_low52 x 24 (by decide); rw [← hrx] at h3; have h4 := byte_low52 x 32 (by decide); rw [← hrx] at h4; have h5 := byte_low52 x 40 (by decide); rw [← hrx] at h5
  have h6 : (sc52BfiByte x y).toNat = rx.toNat / 2 ^ 48 + (ry.toNat % 16) * 16 := by
    unfold sc52BfiByte; rw [byte_bfi_6, ← hrx, ← hry]
  have h7 := byte_low52 y 4 (by decide); rw [← hry] at h7; have h8 := byte_low52 y 12 (by decide); rw [← hry] at h8; have h9 := byte_low52 y 20 (by decide); rw [← hry] at h9; have h10 := byte_low52 y 28 (by decide); rw [← hry] at h10; have h11 := byte_low52 y 36 (by decide); rw [← hry] at h11; have h12 := byte_low52 y 44 (by decide); rw [← hry] at h12
  refine ⟨bv8_eq_ofNat (by omega), bv8_eq_ofNat (by omega), bv8_eq_ofNat (by omega), bv8_eq_ofNat (by omega), bv8_eq_ofNat (by omega), bv8_eq_ofNat (by omega), bv8_eq_ofNat (by omega), bv8_eq_ofNat (by omega), bv8_eq_ofNat (by omega), bv8_eq_ofNat (by omega), bv8_eq_ofNat (by omega), bv8_eq_ofNat (by omega), bv8_eq_ofNat (by omega)⟩
set_option exponentiation.threshold 512 in
private theorem pack_limb4_6 (z rz : BitVec 64) (V : Nat) (hrz : rz = z &&& 4503599627370495#64) (hV : V / 2 ^ 208 = rz.toNat) :
    BitVec.zeroExtend 8 z = BitVec.ofNat 8 ((V / 256 ^ 26) % 256) ∧ BitVec.zeroExtend 8 (z >>> 8) = BitVec.ofNat 8 ((V / 256 ^ 27) % 256) ∧ BitVec.zeroExtend 8 (z >>> 16) = BitVec.ofNat 8 ((V / 256 ^ 28) % 256) ∧
    BitVec.zeroExtend 8 (z >>> 24) = BitVec.ofNat 8 ((V / 256 ^ 29) % 256) ∧ BitVec.zeroExtend 8 (z >>> 32) = BitVec.ofNat 8 ((V / 256 ^ 30) % 256) ∧ BitVec.zeroExtend 8 (z >>> 40) = BitVec.ofNat 8 ((V / 256 ^ 31) % 256) := by
  have h0 := byte_low52_0 z; rw [← hrz] at h0; have h1 := byte_low52 z 8 (by decide); rw [← hrz] at h1; have h2 := byte_low52 z 16 (by decide); rw [← hrz] at h2; have h3 := byte_low52 z 24 (by decide); rw [← hrz] at h3; have h4 := byte_low52 z 32 (by decide); rw [← hrz] at h4; have h5 := byte_low52 z 40 (by decide); rw [← hrz] at h5
  refine ⟨bv8_eq_ofNat (by omega), bv8_eq_ofNat (by omega), bv8_eq_ofNat (by omega), bv8_eq_ofNat (by omega), bv8_eq_ofNat (by omega), bv8_eq_ofNat (by omega)⟩
set_option exponentiation.threshold 512 in
theorem sc52PackBytes32_eq_natToLeBytes
    (add0 add1 add2 add3 add4 r0 r1 r2 r3 r4 : BitVec 64) (hr0 : r0 = add0 &&& 4503599627370495#64) (hr1 : r1 = add1 &&& 4503599627370495#64) (hr2 : r2 = add2 &&& 4503599627370495#64) (hr3 : r3 = add3 &&& 4503599627370495#64) (hr4 : r4 = add4 &&& 4503599627370495#64) :
    sc52PackBytes32 add0 add1 add2 add3 add4 =
      natToLeBytes 32 (sc52Val r0 r1 r2 r3 r4) := by
  have hr0_lt : r0.toNat < 2 ^ 52 := (by rw [hr0, mask52_toNat]; omega); have hr1_lt : r1.toNat < 2 ^ 52 := (by rw [hr1, mask52_toNat]; omega)
  have hr2_lt : r2.toNat < 2 ^ 52 := (by rw [hr2, mask52_toNat]; omega); have hr3_lt : r3.toNat < 2 ^ 52 := (by rw [hr3, mask52_toNat]; omega)
  have hV01 : sc52Val r0 r1 r2 r3 r4 % 2 ^ 104 = r0.toNat + r1.toNat * 2 ^ 52 := by
    unfold sc52Val; omega
  have hV23 : (sc52Val r0 r1 r2 r3 r4 / 2 ^ 104) % 2 ^ 104 = r2.toNat + r3.toNat * 2 ^ 52 := by
    unfold sc52Val; omega
  have hV4 : sc52Val r0 r1 r2 r3 r4 / 2 ^ 208 = r4.toNat := by
    unfold sc52Val; omega
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ := pack_pair_13 add0 add1 r0 r1 (sc52Val r0 r1 r2 r3 r4) hr0 hr1 hV01; obtain ⟨e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25⟩ := pack_pair_23 add2 add3 r2 r3 (sc52Val r0 r1 r2 r3 r4) hr2 hr3 hV23; obtain ⟨e26, e27, e28, e29, e30, e31⟩ := pack_limb4_6 add4 r4 (sc52Val r0 r1 r2 r3 r4) hr4 hV4; unfold sc52PackBytes32; rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31]
  rfl
private theorem mul_const_pair_40 {x hi lo : BitVec 64} (c : Nat)
    (hx : x.toNat < 2 ^ 52) (hc : c < 2 ^ 52) (hhi : hi = BitVec.setWidth 64 ((BitVec.setWidth 128 x * BitVec.ofNat 128 c) >>> 64)) (hlo : lo = x * BitVec.ofNat 64 c) :
    hi.toNat * 2 ^ 64 + lo.toNat = x.toNat * c ∧ hi.toNat ≤ 2 ^ 40 := by
  have h := mul_umulh_const_toNat x c (by omega); have hxc : x.toNat * c < 2 ^ 52 * 2 ^ 52 := Nat.mul_lt_mul'' hx hc; rw [hhi, hlo]
  exact ⟨h.1, by omega⟩
set_option exponentiation.threshold 512 in
private theorem sc52_reduce_bound {A : Nat} (hA : A < 2 ^ 256) : A * sc52Val 4302102966953709#64 1049714374468698#64 4503599278581019#64
      4503599627370495#64 17592186044415#64 < 2 ^ 260 * edOrderL :=
  sc52_mul_bound_of_lt_256 hA (by decide)
set_option exponentiation.threshold 512 in
private theorem cancel_mont_r {A Out : Nat}
    (hOut_lt : Out < edOrderL) (h1 : Out * 2 ^ 260 % edOrderL = A * sc52Val 4302102966953709#64 1049714374468698#64 4503599278581019#64 4503599627370495#64 17592186044415#64 % edOrderL) :
    Out = A % edOrderL := by
  let inv := 5706410653605570882457795059301885719620630590890452783038400561109479083972
  have hr : sc52Val 4302102966953709#64 1049714374468698#64 4503599278581019#64 4503599627370495#64 17592186044415#64 = 2 ^ 260 % edOrderL := by decide
  have hinv : (2 ^ 260 * inv) % edOrderL = 1 := by decide
  have h1' : (Out * 2 ^ 260) % edOrderL = (A * 2 ^ 260) % edOrderL := by
    rw [h1, hr, Nat.mul_mod_mod]
  have h2 : (Out * (2 ^ 260 * inv)) % edOrderL = (A * (2 ^ 260 * inv)) % edOrderL := by
    rw [← Nat.mul_assoc, ← Nat.mod_mul_mod, h1', Nat.mod_mul_mod, Nat.mul_assoc]
  rw [← Nat.mul_mod_mod, hinv, Nat.mul_one, Nat.mod_eq_of_lt hOut_lt] at h2; rw [← Nat.mul_mod_mod, hinv, Nat.mul_one] at h2
  exact h2
theorem write8_32_order (bs : List (BitVec 8)) (h : bs.length = 32) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
     x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : BitVec 8) :
    ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 bs 0 x0) 1 x1) 2 x2) 3 x3) 5 x5) 4 x4) 7 x7) 8 x8) 6 x6) 11 x11) 9 x9) 10 x10) 12 x12) 13 x13) 14 x14) 15 x15) 18 x18) 17 x17) 21 x21) 20 x20) 22 x22) 24 x24) 23 x23) 25 x25) 26 x26) 27 x27) 16 x16) 19 x19) 28 x28) 29 x29) 30 x30) 31 x31 =
    [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15,
     x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, rfl⟩ := exists_bytes32 h
  simp only [ByteSlice.write8, ByteSlice.write, List.take, List.drop, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
theorem write8_32_reduce (bs : List (BitVec 8)) (h : bs.length = 32) (add0 add1 add2 add3 add4 : BitVec 64) : ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 bs 0 (BitVec.zeroExtend 8 add0)) 1 (BitVec.zeroExtend 8 (add0 >>> 8))) 2 (BitVec.zeroExtend 8 (add0 >>> 16))) 3 (BitVec.zeroExtend 8 (add0 >>> 24))) 5 (BitVec.zeroExtend 8 (add0 >>> 40))) 4 (BitVec.zeroExtend 8 (add0 >>> 32))) 7 (BitVec.zeroExtend 8 (add1 >>> 4))) 8 (BitVec.zeroExtend 8 (add1 >>> 12))) 6 (BitVec.zeroExtend 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (add0 >>> 48)) &&& 18446744069414584335#64 ||| (BitVec.setWidth 64 (BitVec.setWidth 32 add1) &&& 268435455#64) <<< 4))) 11 (BitVec.zeroExtend 8 (add1 >>> 36))) 9 (BitVec.zeroExtend 8 (add1 >>> 20))) 10 (BitVec.zeroExtend 8 (add1 >>> 28))) 12 (BitVec.zeroExtend 8 (add1 >>> 44))) 13 (BitVec.zeroExtend 8 add2)) 14 (BitVec.zeroExtend 8 (add2 >>> 8))) 15 (BitVec.zeroExtend 8 (add2 >>> 16))) 18 (BitVec.zeroExtend 8 (add2 >>> 40))) 17 (BitVec.zeroExtend 8 (add2 >>> 32))) 21 (BitVec.zeroExtend 8 (add3 >>> 12))) 20 (BitVec.zeroExtend 8 (add3 >>> 4))) 22 (BitVec.zeroExtend 8 (add3 >>> 20))) 24 (BitVec.zeroExtend 8 (add3 >>> 36))) 23 (BitVec.zeroExtend 8 (add3 >>> 28))) 25 (BitVec.zeroExtend 8 (add3 >>> 44))) 26 (BitVec.zeroExtend 8 add4)) 27 (BitVec.zeroExtend 8 (add4 >>> 8))) 16 (BitVec.zeroExtend 8 (add2 >>> 24))) 19 (BitVec.zeroExtend 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (add2 >>> 48)) &&& 18446744069414584335#64 ||| (BitVec.setWidth 64 (BitVec.setWidth 32 add3) &&& 268435455#64) <<< 4))) 28 (BitVec.zeroExtend 8 (add4 >>> 16))) 29 (BitVec.zeroExtend 8 (add4 >>> 24))) 30 (BitVec.zeroExtend 8 (add4 >>> 32))) 31 (BitVec.zeroExtend 8 (add4 >>> 40)) =
    sc52PackBytes32 add0 add1 add2 add3 add4 :=
  write8_32_order bs h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
set_option maxHeartbeats 800000 in
theorem scalar_reduce_ok : ScalarReduceOk := by
  intro _
  apply dalekCaller_ok dalekCliPC16 dalekCliPl16
  intro b hb hbase
  wp_init
  wp_cut_codeLoaded; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 8; wp_checkpoint; wp_sym_steps 5; wp_checkpoint; have h_res :
      sc52PackBytes32
        (v_cp_212 + (-BitVec.setWidth 64 (BitVec.zeroExtend 8 v_cp_234) &&& 671914833335277#64))
        ((-BitVec.setWidth 64 (BitVec.zeroExtend 8 v_cp_234) &&& 3916664325105025#64) +
          (v_cp_212 + (-BitVec.setWidth 64 (BitVec.zeroExtend 8 v_cp_234) &&& 671914833335277#64)) >>> 52 +
          v_cp_227)
        (v_cp_230 + (-BitVec.setWidth 64 (BitVec.zeroExtend 8 v_cp_234) &&& 1367801#64) +
          ((-BitVec.setWidth 64 (BitVec.zeroExtend 8 v_cp_234) &&& 3916664325105025#64) +
            (v_cp_212 + (-BitVec.setWidth 64 (BitVec.zeroExtend 8 v_cp_234) &&& 671914833335277#64)) >>> 52 +
            v_cp_227) >>> 52)
        (v_cp_232 +
          (v_cp_230 + (-BitVec.setWidth 64 (BitVec.zeroExtend 8 v_cp_234) &&& 1367801#64) +
            ((-BitVec.setWidth 64 (BitVec.zeroExtend 8 v_cp_234) &&& 3916664325105025#64) +
              (v_cp_212 + (-BitVec.setWidth 64 (BitVec.zeroExtend 8 v_cp_234) &&& 671914833335277#64)) >>> 52 +
              v_cp_227) >>> 52) >>> 52)
        (v_cp_233 + (-BitVec.setWidth 64 (BitVec.zeroExtend 8 v_cp_234) &&& 17592186044416#64) +
          (v_cp_232 +
            (v_cp_230 + (-BitVec.setWidth 64 (BitVec.zeroExtend 8 v_cp_234) &&& 1367801#64) +
              ((-BitVec.setWidth 64 (BitVec.zeroExtend 8 v_cp_234) &&& 3916664325105025#64) +
                (v_cp_212 + (-BitVec.setWidth 64 (BitVec.zeroExtend 8 v_cp_234) &&& 671914833335277#64)) >>> 52 +
                v_cp_227) >>> 52) >>> 52) >>> 52) =
      natToLeBytes 32 (leBytesToNat a_rest % edOrderL) := by
    obtain ⟨ha0, ha1, ha2, ha3, ha4, ha_val, ha_lt⟩ := sc52_unpack_bytes32 a_rest h_1 v_cp_9 v_cp_17 v_cp_34 v_cp_32 v_cp_43 (by rw [hv_cp_9, hv_cp_5, hv_cp_3, hv_cp_1, hv_cp_2]) (by rw [hv_cp_17, hv_cp_10, hv_cp_8, hv_cp_4, hv_cp_7, hv_cp_5, hv_cp_3, hv_cp_1, hv_cp_2]) (by rw [hv_cp_34, hv_cp_30, hv_cp_23, hv_cp_19]) (by rw [hv_cp_32, hv_cp_31]) (by rw [hv_cp_43, hv_cp_6, hv_cp_33])
    have hv_cp_49_eq : v_cp_49 = v_cp_9 * 4503599627370495#64 := by
      rw [hv_cp_49, hv_cp_47, ← sub_lsl52_eq_mul v_cp_9, hv_cp_9, lsl52_and_mask52, hv_cp_5, hv_cp_3, ← hv_cp_0, lsl52_or_32_40_48]
    have hv_cp_58_eq : v_cp_58 = v_cp_9 * 17592186044415#64 := by
      rw [hv_cp_58, hv_cp_55, ← sub_lsl44_eq_mul v_cp_9, hv_cp_9, lsl44_and_mask52, hv_cp_5, hv_cp_3, ← hv_cp_0, lsl44_or_32_40_48]
    have hv_cp_64_eq : v_cp_64 = v_cp_17 * 4503599627370495#64 := by rw [hv_cp_64, hv_cp_60, sub_lsl52_eq_mul]
    have hv_cp_74_eq : v_cp_74 = v_cp_17 * 17592186044415#64 := by rw [hv_cp_74, hv_cp_62, sub_lsl44_eq_mul]
    have hv_cp_73_eq : v_cp_73 = v_cp_34 * 4503599627370495#64 := by
      rw [hv_cp_73, hv_cp_63, ← sub_lsl52_eq_mul v_cp_34, hv_cp_34, lsl52_and_mask52]
    have hv_cp_78_eq : v_cp_78 = v_cp_34 * 17592186044415#64 := by
      rw [hv_cp_78, hv_cp_72, ← sub_lsl44_eq_mul v_cp_34, hv_cp_34, lsl44_and_mask52]
    have hv_cp_79_eq : v_cp_79 = v_cp_32 * 4503599627370495#64 := by rw [hv_cp_79, hv_cp_68, sub_lsl52_eq_mul]
    have hv_cp_94_eq : v_cp_94 = v_cp_32 * 17592186044415#64 := by rw [hv_cp_94, hv_cp_84, sub_lsl44_eq_mul]
    have hv_cp_90_eq : v_cp_90 = v_cp_43 * 4503599627370495#64 := by
      rw [hv_cp_90, hv_cp_85, ← sub_lsl52_eq_mul v_cp_43, hv_cp_43, lsl52_or_32_40]
    have hv_cp_220_eq : v_cp_220 = v_cp_43 * 17592186044415#64 := by
      rw [hv_cp_220, hv_cp_209, ← sub_lsl44_eq_mul v_cp_43, hv_cp_43, lsl44_or_32_40]
    have p00 := mul_const_pair_40 4302102966953709 ha0 (by decide) hv_cp_15 hv_cp_13; have p01 := mul_const_pair_52 1049714374468698 ha0 (by decide) hv_cp_11 hv_cp_12; have p02 := mul_const_pair_52 4503599278581019 ha0 (by decide) hv_cp_16 hv_cp_18; have p03 := mul_const_pair_52 4503599627370495 ha0 (by decide) hv_cp_14 hv_cp_49_eq; have p04 := mul_const_pair_52 17592186044415 ha0 (by decide) hv_cp_54 hv_cp_58_eq; have p10 := mul_const_pair_52 4302102966953709 ha1 (by decide) hv_cp_21 (hv_cp_20.trans (by rw [← hv_cp_17])); have p11 := mul_const_pair_52 1049714374468698 ha1 (by decide) hv_cp_22 hv_cp_24; have p12 := mul_const_pair_52 4503599278581019 ha1 (by decide) hv_cp_26 hv_cp_25; have p13 := mul_const_pair_52 4503599627370495 ha1 (by decide) hv_cp_27 hv_cp_64_eq; have p14 := mul_const_pair_52 17592186044415 ha1 (by decide) hv_cp_57 hv_cp_74_eq; have p20 := mul_const_pair_52 4302102966953709 ha2 (by decide) hv_cp_108 hv_cp_100; have p21 := mul_const_pair_52 1049714374468698 ha2 (by decide) (hv_cp_37.trans (by rw [← hv_cp_34])) (hv_cp_35.trans (by rw [← hv_cp_34])); have p22 := mul_const_pair_52 4503599278581019 ha2 (by decide) hv_cp_117 hv_cp_122; have p23 := mul_const_pair_52 4503599627370495 ha2 (by decide) (hv_cp_38.trans (by rw [← hv_cp_34])) hv_cp_73_eq; have p24 := mul_const_pair_52 17592186044415 ha2 (by decide) hv_cp_59 hv_cp_78_eq; have p30 := mul_const_pair_52 4302102966953709 ha3 (by decide) (hv_cp_36.trans (by rw [← hv_cp_32])) hv_cp_42; have p31 := mul_const_pair_52 1049714374468698 ha3 (by decide) hv_cp_140 hv_cp_142; have p32 := mul_const_pair_52 4503599278581019 ha3 (by decide) hv_cp_50 hv_cp_44
    have p33 := mul_const_pair_52 4503599627370495 ha3 (by decide) hv_cp_40 hv_cp_79_eq; have p34 := mul_const_pair_52 17592186044415 ha3 (by decide) hv_cp_80 hv_cp_94_eq; have p40 := mul_const_pair_52 4302102966953709 ha4 (by decide) hv_cp_149 hv_cp_148; have p41 := mul_const_pair_52 1049714374468698 ha4 (by decide) hv_cp_177 hv_cp_168; have p42 := mul_const_pair_52 4503599278581019 ha4 (by decide) hv_cp_75 hv_cp_69; have p43 := mul_const_pair_52 4503599627370495 ha4 (by decide) hv_cp_46 hv_cp_90_eq; have p44 := mul_const_pair_52 17592186044415 ha4 (by decide) hv_cp_217 hv_cp_220_eq; have st0 := mont_red_step_hi0_eq p00 (by decide) (hv_cp_81.trans (by rw [hv_cp_65])) hv_cp_86 hv_cp_89 (hv_cp_103.trans (by rw [hv_cp_97, hv_cp_96])); have ul01 := mul_const_pair_52 3916664325105025 st0.1 (by decide) hv_cp_95 hv_cp_93; have ul02 := mul_const_pair_52 1367801 st0.1 (by decide) hv_cp_104 hv_cp_107; have ul04 := l4_shift_pair hv_cp_65 (hv_cp_81.trans (by rw [hv_cp_65])) hv_cp_158 hv_cp_160; have c1_1 := acc128_step_eq p10 p01 (by decide) hv_cp_45 hv_cp_39; have c1_2 := acc128_step_eq c1_1 ul01 (by decide) hv_cp_101 hv_cp_99; have c1_3 := acc128_cinc_step_eq c1_2 (by decide) hv_cp_105 (hv_cp_102.trans (by rw [← hv_cp_99, ← hv_cp_103])); have st1 := mont_red_step_eq c1_3 (by decide) hv_cp_109 (hv_cp_110.trans (by rw [← hv_cp_109])) (hv_cp_111.trans (by rw [← hv_cp_109])) (hv_cp_125.trans (by rw [hv_cp_115])) (hv_cp_120.trans (by rw [hv_cp_115, hv_cp_113])); have ul11 := mul_const_pair_52 3916664325105025 st1.2.1 (by decide) hv_cp_114 hv_cp_112; have ul12 := mul_const_pair_52 1367801 st1.2.1 (by decide) hv_cp_129 hv_cp_130; have ul14 := l4_shift_pair hv_cp_106 hv_cp_109 hv_cp_184 hv_cp_187
    have c2_1 := acc128_step_eq p11 p02 (by decide) hv_cp_51 hv_cp_48; have c2_2 := acc128_step_eq c2_1 ul02 (by decide) hv_cp_118 hv_cp_116; have c2_3 := acc128_step_eq c2_2 p20 (by decide) hv_cp_121 hv_cp_119; have c2_4 := acc128_step_eq c2_3 ul11 (by decide) (hv_cp_123.trans (by rw [← hv_cp_121, ← hv_cp_119])) (hv_cp_126.trans (by rw [← hv_cp_119])); have c2_5 := acc128_step_eq c2_4 st1.1 (by decide) hv_cp_128 (hv_cp_124.trans (by rw [← hv_cp_126, ← hv_cp_120])); have st2 := mont_red_step_eq c2_5 (by decide) (hv_cp_131.trans (by rw [hv_cp_127])) (hv_cp_137.trans (by rw [← hv_cp_131])) (hv_cp_132.trans (by rw [← hv_cp_131])) (hv_cp_141.trans (by rw [hv_cp_136, ← hv_cp_132, ← hv_cp_137])) (hv_cp_139.trans (by rw [hv_cp_136, hv_cp_134, ← hv_cp_132, ← hv_cp_137])); have ul21 := mul_const_pair_52 3916664325105025 st2.2.1 (by decide) (hv_cp_135.trans (by rw [← hv_cp_131])) (hv_cp_133.trans (by rw [← hv_cp_131])); have ul22 := mul_const_pair_52 1367801 st2.2.1 (by decide) hv_cp_155 hv_cp_153; have ul24 := l4_shift_pair hv_cp_127 (hv_cp_131.trans (by rw [hv_cp_127])) hv_cp_198 hv_cp_201; have c3_1 := acc128_step_eq p12 p03 (by decide) rfl (hv_cp_52.trans (by rw [← hv_cp_49])); have c3_2 := acc128_step_eq c3_1 p21 (by decide) hv_cp_56 hv_cp_53; have c3_3 := acc128_step_eq c3_2 p30 (by decide) hv_cp_66 hv_cp_61; have c3_4 := acc128_step_eq c3_3 ul12 (by decide) rfl hv_cp_138; have c3_5 := acc128_step_eq c3_4 ul21 (by decide) (hv_cp_144.trans (by rw [← hv_cp_138])) (hv_cp_143.trans (by rw [← hv_cp_138])); have c3_6 := acc128_step_eq c3_5 st2.1 (by decide) hv_cp_147 hv_cp_145; have st3 := mont_red_step_eq c3_6 (by decide) (hv_cp_150.trans (by rw [← hv_cp_145])) (hv_cp_151.trans (by rw [← hv_cp_150])) hv_cp_152 (hv_cp_162.trans (by rw [hv_cp_156, ← hv_cp_152])) (hv_cp_161.trans (by rw [hv_cp_156, hv_cp_154, ← hv_cp_152])); have ul31 := mul_const_pair_52 3916664325105025 st3.2.1 (by decide) hv_cp_164 hv_cp_159; have ul32 := mul_const_pair_52 1367801 st3.2.1 (by decide) hv_cp_178 hv_cp_171
    have ul34 := l4_shift_pair (hv_cp_146.trans (by rw [← hv_cp_145])) (hv_cp_150.trans (by rw [← hv_cp_145])) hv_cp_205 hv_cp_210; have c4_1 := acc128_step_eq p13 p04 (by decide) hv_cp_70 (hv_cp_67.trans (by rw [← hv_cp_64])); have c4_2 := acc128_step_eq c4_1 ul04 (by decide) hv_cp_163 (hv_cp_157.trans (by rw [← hv_cp_160])); have c4_3 := acc128_step_eq c4_2 p22 (by decide) (hv_cp_165.trans (by rw [← hv_cp_163])) hv_cp_167; have c4_4 := acc128_step_eq c4_3 p31 (by decide) rfl (hv_cp_166.trans (by rw [← hv_cp_167])); have c4_5 := acc128_step_eq c4_4 p40 (by decide) rfl rfl; have c4_6 := acc128_step_eq c4_5 ul22 (by decide) hv_cp_169 hv_cp_172; have c4_7 := acc128_step_eq c4_6 ul31 (by decide) hv_cp_173 (hv_cp_170.trans (by rw [← hv_cp_172])); have c4_8 := acc128_step_eq c4_7 st3.1 (by decide) (hv_cp_176.trans (by rw [← hv_cp_173])) hv_cp_174; have st4 := mont_red_step_eq c4_8 (by decide) (hv_cp_179.trans (by rw [← hv_cp_174])) (hv_cp_180.trans (by rw [← hv_cp_179])) rfl (hv_cp_188.trans (by rw [hv_cp_183])) hv_cp_186; have ul41 := mul_const_pair_52 3916664325105025 st4.2.1 (by decide) hv_cp_182 hv_cp_181; have ul42 := mul_const_pair_52 1367801 st4.2.1 (by decide) hv_cp_195 hv_cp_190; have ul44 := l4_shift_pair (hv_cp_175.trans (by rw [← hv_cp_174])) (hv_cp_179.trans (by rw [← hv_cp_174])) hv_cp_219 hv_cp_221; have c5_1 := acc128_step_eq p23 p14 (by decide) hv_cp_76 (hv_cp_71.trans (by rw [← hv_cp_73, ← hv_cp_74])); have c5_2 := acc128_step_eq c5_1 p32 (by decide) hv_cp_82 hv_cp_77; have c5_3 := acc128_step_eq c5_2 ul14 (by decide) hv_cp_189 (hv_cp_185.trans (by rw [← hv_cp_187])); have c5_4 := acc128_step_eq c5_3 p41 (by decide) rfl hv_cp_193; have c5_5 := acc128_step_eq c5_4 ul32 (by decide) (hv_cp_192.trans (by rw [← hv_cp_189, ← hv_cp_193])) (hv_cp_191.trans (by rw [← hv_cp_193]))
    have c5_6 := acc128_step_eq c5_5 ul41 (by decide) rfl hv_cp_194; have c5_7 := acc128_step_eq c5_6 st4.1 (by decide) (hv_cp_197.trans (by rw [← hv_cp_194])) (hv_cp_196.trans (by rw [← hv_cp_194])); have st5 := extr52_step_eq c5_7 (by decide) hv_cp_202 rfl (hv_cp_200.trans (by rw [← hv_cp_197, ← hv_cp_196])); have c6_1 := acc128_step_eq p33 p24 (by decide) hv_cp_87 hv_cp_83; have c6_2 := acc128_step_eq c6_1 p42 (by decide) hv_cp_91 hv_cp_88; have c6_3 := acc128_step_eq c6_2 ul24 (by decide) rfl (hv_cp_199.trans (by rw [← hv_cp_201])); have c6_4 := acc128_step_eq c6_3 ul42 (by decide) rfl hv_cp_206; have c6_5 := acc128_step_eq c6_4 st5.1 (by decide) (hv_cp_204.trans (by rw [← hv_cp_206])) (hv_cp_203.trans (by rw [← hv_cp_206])); have st6 := extr52_step_eq c6_5 (by decide) rfl hv_cp_211 hv_cp_215; have c7_1 := acc128_step_eq p43 p34 (by decide) hv_cp_98 (hv_cp_92.trans (by rw [← hv_cp_90, ← hv_cp_94])); have c7_2 := acc128_step_eq c7_1 ul34 (by decide) (hv_cp_208.trans (by rw [← hv_cp_210])) (hv_cp_207.trans (by rw [← hv_cp_210])); have c7_3 := acc128_step_eq c7_2 st6.1 (by decide) hv_cp_216 (hv_cp_213.trans (by rw [← hv_cp_215])); have st7 := extr52_step_eq c7_3 (by decide) rfl hv_cp_223 hv_cp_226; have c8_1 := acc128_step_eq p44 ul44 (by decide) (hv_cp_224.trans (by rw [BitVec.add_comm v_cp_219 v_cp_217])) (hv_cp_218.trans (by rw [← hv_cp_220, ← hv_cp_221])); have c8_2 := acc128_step_eq c8_1 st7.1 (by decide) rfl (hv_cp_225.trans (by rw [← hv_cp_226])); have st8 := extr52_last_step_eq c8_2 (by decide) rfl hv_cp_228; have hst2 := st2.2.2; rw [Nat.add_right_comm _ (v_cp_81.toNat * 1367801) _] at hst2; have hst5 := st5.2.2; rw [Nat.add_right_comm _ (v_cp_109.toNat * 17592186044416) _] at hst5
    have h_tele := sc52_mont_telescope v_cp_81 v_cp_109 v_cp_131 v_cp_150 v_cp_179 v_cp_202 (v_cp_203 &&& 4503599627370495#64) (v_cp_213 &&& 4503599627370495#64) (v_cp_225 &&& 4503599627370495#64) v_cp_228 st0.1 st1.2.1 st2.2.1 st3.2.1 st4.2.1 (sc52_schoolbook_mul_r v_cp_9 v_cp_17 v_cp_34 v_cp_32 v_cp_43) (by rw [ha_val]; exact sc52_reduce_bound ha_lt) st0.2 st1.2.2 hst2 st3.2.2 st4.2.2 hst5 st6.2.2 st7.2.2 st8.2; rw [← hv_cp_233] at hv_cp_234
    let add0 := v_cp_212 + (-BitVec.setWidth 64 (BitVec.zeroExtend 8 v_cp_234) &&& 671914833335277#64)
    let add1 := (-BitVec.setWidth 64 (BitVec.zeroExtend 8 v_cp_234) &&& 3916664325105025#64) + add0 >>> 52 + v_cp_227
    let add2 := v_cp_230 + (-BitVec.setWidth 64 (BitVec.zeroExtend 8 v_cp_234) &&& 1367801#64) + add1 >>> 52
    let add3 := v_cp_232 + add2 >>> 52
    let add4 := v_cp_233 + (-BitVec.setWidth 64 (BitVec.zeroExtend 8 v_cp_234) &&& 17592186044416#64) + add3 >>> 52
    let r0 := add0 &&& 4503599627370495#64
    let r1 := add1 &&& 4503599627370495#64
    let r2 := add2 &&& 4503599627370495#64
    let r3 := add3 &&& 4503599627370495#64
    let r4 := add4 &&& 4503599627370495#64
    have h_sub := sc52_cond_sub_l v_cp_202 (v_cp_203 &&& 4503599627370495#64) (v_cp_213 &&& 4503599627370495#64) (v_cp_225 &&& 4503599627370495#64) v_cp_228 v_cp_212 (v_cp_214 + 18442827409384446591#64) v_cp_227 (v_cp_222 - 1367801#64) v_cp_230 v_cp_229 v_cp_232 v_cp_233 v_cp_234 v_cp_234 r0 r1 r2 r3 r4 st5.2.1 st6.2.1 st7.2.1 st8.1 h_tele.1 hv_cp_212 (by rw [hv_cp_214]) hv_cp_227 (by rw [hv_cp_222]) hv_cp_230 hv_cp_229 hv_cp_232 hv_cp_233 hv_cp_234 rfl rfl rfl rfl rfl rfl; rcases h_sub with ⟨_, _, _, _, _, hr_lt, q, _, hq_eq⟩; rw [sc52PackBytes32_eq_natToLeBytes add0 add1 add2 add3 add4 r0 r1 r2 r3 r4 rfl rfl rfl rfl rfl]; have hmod := cancel_mont_r hr_lt (mod_eq_of_mont hq_eq h_tele.2); rw [hmod, ha_val]
  wp_clear_temps
  wp_steps 1; wp_dalek_call black_box_u8_ok
  wp_sym_steps 77; wp_checkpoint; wp_sym_steps 8
  wp_conv_pre => simp only [write8_32_reduce a_2 h_4]
  wp_fold_stack; rw [h_res]
  wp_done

end
end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Scalar52
