/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Ref
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Cells
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512RoundDefs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Code
import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Fetch
meta import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Cells
meta import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512RoundDefs

/-!
# Single-block symbolic execution of `sha2::sha512::compress512`

Verifies one 80-round iteration (`0x0038 → 0x2580` / `0x0038`, `2,385` symbolic steps including
the relaxable `ADRP`+`ADD` / `NOP`+`ADR` pair at `0x0048`) of
`_RNvNtCsbvWyylYiyxg_4sha26sha51211compress512`. Defines `sha512LoopStack`, `sha2K64AllCells`,
and `compress512_one_block`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Step

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Ref
  (sha512K sha512CompressBlock)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Cells
  (readLE64 pointsToBytesRO_128_eq_cells64
   sha2K64Cells0 sha2K64Cells1 sha2K64Cells2 sha2K64Cells3 sha2K64Cells4
   SepWP.rw_top_reg)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512RoundDefs
  (sha512W sha512W_init_off sha512W_step1 sha512W_step2 sha512W_add_k
   sha512T1 sha512T2 sha512T2_eq
   sha512T1_eq1 sha512T1_eq2 sha512T1_eq3 sha512T1_eq4 sha512T1_eq5 sha512T1_eq6
   sha512A sha512E sha512A_0 sha512A_1 sha512A_2 sha512A_3
   sha512E_0 sha512E_1 sha512E_2 sha512E_3
   sha512E_from_t1 sha512A_from_t1_t2 sha512Final0 sha512Final4
   sha512CompressBlock_eq_sha512AE)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Code
  (Compress512Placement compress512PC)

arm64_proof_prelude

section Sha512Tactic
open Lean Meta Elab Tactic

private theorem sha512W_init_off_norm (block : List (BitVec 8)) (off i : Nat)
    (hblock : block.length = 128) (hi : i < 16) (hoff : 8 * i = off) :
    rev64 (readLE64 block off) = sha512W block i :=
  sha512W_init_off block off i hblock hi hoff

private theorem sha512W_init_off_setWidth (block : List (BitVec 8)) (off i : Nat)
    (hblock : block.length = 128) (hi : i < 16) (hoff : 8 * i = off) :
    rev64 (BitVec.setWidth 64 (readLE64 block off)) = sha512W block i := by
  simp only [BitVec.setWidth_eq]
  exact sha512W_init_off block off i hblock hi hoff

private theorem sha512W_init_off_zext (block : List (BitVec 8)) (off i : Nat)
    (hblock : block.length = 128) (hi : i < 16) (hoff : 8 * i = off) :
    rev64 (BitVec.zeroExtend 64 (readLE64 block off)) = sha512W block i :=
  sha512W_init_off block off i hblock hi hoff

private theorem sha512Final0' (st : List (BitVec 64)) (block : List (BitVec 8)) :
    ((((sha512A st block 82 &&& (sha512A st block 81 ^^^ sha512A st block 80)) ^^^
        (sha512A st block 81 &&& sha512A st block 80)) + sha512A st block 3) +
      ((BitVec.setWidth 64 ((sha512A st block 82 ++ sha512A st block 82) >>> 28) ^^^
        (sha512A st block 82).rotateRight 34) ^^^ (sha512A st block 82).rotateRight 39)) +
      sha512T1 (sha512E st block 82) (sha512E st block 81) (sha512E st block 80)
        (sha512E st block 79) (sha512K.getD 79 0#64) (sha512W block 79) =
      st.getD 0 0#64 + sha512A st block 83 := by
  rw [← sha512A_3, sha512Final0]

private theorem sha512Final1' (st : List (BitVec 64)) (block : List (BitVec 8)) :
    sha512A st block 82 + sha512A st block 2 = st.getD 1 0#64 + sha512A st block 82 := by
  rw [← sha512A_2, BitVec.add_comm]

private theorem sha512Final2' (st : List (BitVec 64)) (block : List (BitVec 8)) :
    sha512A st block 81 + sha512A st block 1 = st.getD 2 0#64 + sha512A st block 81 := by
  rw [← sha512A_1, BitVec.add_comm]

private theorem sha512Final3' (st : List (BitVec 64)) (block : List (BitVec 8)) :
    sha512A st block 80 + sha512A st block 0 = st.getD 3 0#64 + sha512A st block 80 := by
  rw [← sha512A_0, BitVec.add_comm]

private theorem sha512Final4' (st : List (BitVec 64)) (block : List (BitVec 8)) :
    (sha512A st block 79 + sha512E st block 3) +
      sha512T1 (sha512E st block 82) (sha512E st block 81) (sha512E st block 80)
        (sha512E st block 79) (sha512K.getD 79 0#64) (sha512W block 79) =
      st.getD 4 0#64 + sha512E st block 83 := by
  rw [← sha512E_3, sha512Final4]

private theorem sha512Final5' (st : List (BitVec 64)) (block : List (BitVec 8)) :
    sha512E st block 82 + sha512E st block 2 = st.getD 5 0#64 + sha512E st block 82 := by
  rw [← sha512E_2, BitVec.add_comm]

private theorem sha512Final6' (st : List (BitVec 64)) (block : List (BitVec 8)) :
    sha512E st block 81 + sha512E st block 1 = st.getD 6 0#64 + sha512E st block 81 := by
  rw [← sha512E_1, BitVec.add_comm]

private theorem sha512Final7' (st : List (BitVec 64)) (block : List (BitVec 8)) :
    sha512E st block 80 + sha512E st block 0 = st.getD 7 0#64 + sha512E st block 80 := by
  rw [← sha512E_0, BitVec.add_comm]

attribute [local irreducible] sha512K

private meta def tryApplyPureEqThm (thmName : Name) (v : Expr) : MetaM (Option (Expr × Expr)) := do
  withoutModifyingState do
    let info ← getConstInfo thmName
    let (mvars, _, ty) ← forallMetaTelescope info.type
    let some (_, lhs, rhs) := ty.eq? | return none
    unless ← withReducible (isDefEq lhs v) do return none
    let prf ← instantiateMVars (mkAppN (mkConst thmName) mvars)
    let rhs' ← instantiateMVars rhs
    if prf.hasExprMVar || rhs'.hasExprMVar then return none
    if rhs'.isAppOfArity ``sha512T1 6 then
      unless (rhs'.getArg! 3).isAppOfArity ``sha512E 3 &&
             (rhs'.getArg! 4).isAppOfArity ``List.getD 4 &&
             (rhs'.getArg! 5).isAppOfArity ``sha512W 2 do
        return none
    return some (prf, rhs')

private meta def tryApplyIdxEqThm (thmName : Name) (v : Expr)
    (srcIdxPos dstIdxPos : Nat) (offset : Nat) (decideStart : Nat) :
    MetaM (Option (Expr × Expr)) := do
  withoutModifyingState do
    let info ← getConstInfo thmName
    let (mvars, _, ty) ← forallMetaTelescope info.type
    let some (_, lhs, rhs) := ty.eq? | return none
    unless ← withReducible (isDefEq lhs v) do return none
    let srcExpr ← instantiateMVars mvars[srcIdxPos]!
    let some srcVal := srcExpr.nat? | return none
    mvars[dstIdxPos]!.mvarId!.assign (toExpr (srcVal + offset))
    for k in [decideStart : mvars.size] do
      let m := mvars[k]!.mvarId!
      if !(← m.isAssigned) then
        let p ← instantiateMVars (← m.getType)
        let dp ← mkDecideProof p
        m.assign dp
    let prf ← instantiateMVars (mkAppN (mkConst thmName) mvars)
    let rhs' ← instantiateMVars rhs
    if prf.hasExprMVar || rhs'.hasExprMVar then return none
    return some (prf, rhs')

private meta def tryFoldTopRegExpr (v : Expr) (hblock : Expr) : MetaM (Option (Expr × Expr)) := do
  if v.isAppOfArity ``Arm64.rev64 1 then
    let inner := v.getArg! 0
    if inner.isAppOfArity ``readLE64 2 then
      let block := inner.getArg! 0
      let offExpr := inner.getArg! 1
      let some off := offExpr.nat? | return none
      let iExpr := toExpr (off / 8)
      let hi ← mkDecideProof (← mkAppM ``LT.lt #[iExpr, toExpr (16 : Nat)])
      let hoff ← mkDecideProof (← mkEq (← mkAppM ``HMul.hMul #[toExpr (8 : Nat), iExpr]) offExpr)
      let prf := mkApp6 (mkConst ``sha512W_init_off_norm) block offExpr iExpr hblock hi hoff
      let rhs := mkApp2 (mkConst ``sha512W) block iExpr
      return some (prf, rhs)
    if inner.isAppOfArity ``BitVec.setWidth 3 then
      let rle := inner.getArg! 2
      if rle.isAppOfArity ``readLE64 2 then
        let block := rle.getArg! 0
        let offExpr := rle.getArg! 1
        let some off := offExpr.nat? | return none
        let iExpr := toExpr (off / 8)
        let hi ← mkDecideProof (← mkAppM ``LT.lt #[iExpr, toExpr (16 : Nat)])
        let hoff ← mkDecideProof (← mkEq (← mkAppM ``HMul.hMul #[toExpr (8 : Nat), iExpr]) offExpr)
        let prf := mkApp6 (mkConst ``sha512W_init_off_setWidth) block offExpr iExpr hblock hi hoff
        let rhs := mkApp2 (mkConst ``sha512W) block iExpr
        return some (prf, rhs)
    if inner.isAppOfArity ``BitVec.zeroExtend 3 then
      let rle := inner.getArg! 2
      if rle.isAppOfArity ``readLE64 2 then
        let block := rle.getArg! 0
        let offExpr := rle.getArg! 1
        let some off := offExpr.nat? | return none
        let iExpr := toExpr (off / 8)
        let hi ← mkDecideProof (← mkAppM ``LT.lt #[iExpr, toExpr (16 : Nat)])
        let hoff ← mkDecideProof (← mkEq (← mkAppM ``HMul.hMul #[toExpr (8 : Nat), iExpr]) offExpr)
        let prf := mkApp6 (mkConst ``sha512W_init_off_zext) block offExpr iExpr hblock hi hoff
        let rhs := mkApp2 (mkConst ``sha512W) block iExpr
        return some (prf, rhs)
    return none
  unless v.isAppOfArity ``HAdd.hAdd 6 do return none
  let lhs := v.getArg! 4
  let rhs := v.getArg! 5
  if rhs.isAppOfArity ``sha512A 3 && lhs.isAppOfArity ``sha512T1 6 then
    return ← tryApplyIdxEqThm ``sha512E_from_t1 v 5 6 4 7
  if rhs.isAppOfArity ``sha512T1 6 then
    if lhs.isAppOfArity ``sha512T2 3 then
      return ← tryApplyIdxEqThm ``sha512A_from_t1_t2 v 5 6 4 7
    if let some res ← tryApplyPureEqThm ``sha512Final0' v then return some res
    if let some res ← tryApplyPureEqThm ``sha512Final4' v then return some res
    return none
  if rhs.isAppOfArity ``HXor.hXor 6 then
    if lhs.isAppOfArity ``HXor.hXor 6 then
      return ← tryApplyPureEqThm ``sha512T2_eq v
    for thm in #[``sha512T1_eq6, ``sha512T1_eq4, ``sha512T1_eq2,
                 ``sha512T1_eq5, ``sha512T1_eq1, ``sha512T1_eq3] do
      if let some res ← tryApplyPureEqThm thm v then return some res
    if let some res ← tryApplyIdxEqThm ``sha512W_step1 v 2 5 16 6 then return some res
    if let some res ← tryApplyIdxEqThm ``sha512W_step2 v 2 5 16 6 then return some res
    if let some res ← tryApplyIdxEqThm ``sha512W_add_k v 2 6 16 7 then return some res
    return none
  if lhs.isAppOfArity ``sha512A 3 && rhs.isAppOfArity ``sha512A 3 then
    for thm in #[``sha512Final1', ``sha512Final2', ``sha512Final3'] do
      if let some res ← tryApplyPureEqThm thm v then return some res
    return none
  if lhs.isAppOfArity ``sha512E 3 && rhs.isAppOfArity ``sha512E 3 then
    for thm in #[``sha512Final5', ``sha512Final6', ``sha512Final7'] do
      if let some res ← tryApplyPureEqThm thm v then return some res
    return none
  return none

private theorem SepWP.rw_top_reg_pc {prog : Program} {target_pc : BitVec 64}
    {s : Arm64.State} {pc : BitVec 64} {r : Reg} {v v' : BitVec 64}
    {P : SepProp} {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp}
    (hv : v = v')
    (h : SepWP prog target_pc ((s.writeReg64 r v').setPC pc) P post oom) :
    SepWP prog target_pc ((s.writeReg64 r v).setPC pc) P post oom := by
  rw [hv]; exact h

private theorem SepWP.rw_top_reg_pc_mem {prog : Program} {target_pc : BitVec 64}
    {s : Arm64.State} {pc : BitVec 64} {m : Memory} {r : Reg} {v v' : BitVec 64}
    {P : SepProp} {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp}
    (hv : v = v')
    (h : SepWP prog target_pc (((s.writeReg64 r v').setPC pc).setMem m) P post oom) :
    SepWP prog target_pc (((s.writeReg64 r v).setPC pc).setMem m) P post oom := by
  rw [hv]; exact h

private theorem SepWP.rw_top_reg_ps_pc_mem {prog : Program} {target_pc : BitVec 64}
    {s : Arm64.State} {ps : PState} {pc : BitVec 64} {m : Memory} {r : Reg} {v v' : BitVec 64}
    {P : SepProp} {post : Arm64.State → SepProp → Prop} {oom : Arm64.State → SepProp}
    (hv : v = v')
    (h : SepWP prog target_pc ((((s.writeReg64 r v').setPState ps).setPC pc).setMem m) P post oom) :
    SepWP prog target_pc ((((s.writeReg64 r v).setPState ps).setPC pc).setMem m) P post oom := by
  rw [hv]; exact h

private meta def tryFoldGoalTopReg (hblock : Expr) (bs : WpSymBlockState) :
    TacticM WpSymBlockState := do
  let g ← getMainGoal
  g.withContext do
    let ty ← instantiateMVars (← g.getType)
    unless ty.isAppOfArity ``SepWP 6 do return bs
    let prog := ty.getArg! 0
    let targetPc := ty.getArg! 1
    let sExpr := ty.getArg! 2
    let P := ty.getArg! 3
    let post := ty.getArg! 4
    let oom := ty.getArg! 5
    if sExpr.isAppOfArity ``Arm64.State.setMem 2 then
      let s1 := sExpr.getArg! 0
      let m := sExpr.getArg! 1
      if s1.isAppOfArity ``Arm64.State.setPC 2 then
        let s2 := s1.getArg! 0
        let pc := s1.getArg! 1
        if s2.isAppOfArity ``Arm64.State.writeReg64 3 then
          let sInner := s2.getArg! 0
          let r := s2.getArg! 1
          let v := s2.getArg! 2
          let some (hv, v') ← tryFoldTopRegExpr v hblock | return bs
          let newS := mkApp2 (mkConst ``Arm64.State.setMem)
            (mkApp2 (mkConst ``Arm64.State.setPC)
              (mkApp3 (mkConst ``Arm64.State.writeReg64) sInner r v') pc) m
          let (newSShared, symInternalState') ←
            (Sym.withoutShareCommonChecks (Sym.shareCommon newS)) bs.symCtx |>.run bs.symInternalState
          let seeded := seedNormalizedInSymCache newSShared bs.simpState.persistentCache
          let bs' := { bs with symInternalState := symInternalState',
                               simpState := { bs.simpState with persistentCache := seeded } }
          let newGoalTy := mkApp6 (mkConst ``SepWP) prog targetPc newSShared P post oom
          let newGoalMVar ← mkFreshExprSyntheticOpaqueMVar newGoalTy (← g.getTag)
          let prf := mkAppN (mkConst ``SepWP.rw_top_reg_pc_mem)
            #[prog, targetPc, sInner, pc, m, r, v, v', P, post, oom, hv, newGoalMVar]
          g.assign prf
          replaceMainGoal [newGoalMVar.mvarId!]
          return bs'
        if s2.isAppOfArity ``Arm64.State.setPState 2 then
          let s3 := s2.getArg! 0
          let ps := s2.getArg! 1
          if s3.isAppOfArity ``Arm64.State.writeReg64 3 then
            let sInner := s3.getArg! 0
            let r := s3.getArg! 1
            let v := s3.getArg! 2
            let some (hv, v') ← tryFoldTopRegExpr v hblock | return bs
            let newS := mkApp2 (mkConst ``Arm64.State.setMem)
              (mkApp2 (mkConst ``Arm64.State.setPC)
                (mkApp2 (mkConst ``Arm64.State.setPState)
                  (mkApp3 (mkConst ``Arm64.State.writeReg64) sInner r v') ps) pc) m
            let (newSShared, symInternalState') ←
              (Sym.withoutShareCommonChecks (Sym.shareCommon newS)) bs.symCtx |>.run bs.symInternalState
            let seeded := seedNormalizedInSymCache newSShared bs.simpState.persistentCache
            let bs' := { bs with symInternalState := symInternalState',
                                 simpState := { bs.simpState with persistentCache := seeded } }
            let newGoalTy := mkApp6 (mkConst ``SepWP) prog targetPc newSShared P post oom
            let newGoalMVar ← mkFreshExprSyntheticOpaqueMVar newGoalTy (← g.getTag)
            let prf := mkAppN (mkConst ``SepWP.rw_top_reg_ps_pc_mem)
              #[prog, targetPc, sInner, ps, pc, m, r, v, v', P, post, oom, hv, newGoalMVar]
            g.assign prf
            replaceMainGoal [newGoalMVar.mvarId!]
            return bs'
      return bs
    if sExpr.isAppOfArity ``Arm64.State.setPC 2 then
      let s2 := sExpr.getArg! 0
      let pc := sExpr.getArg! 1
      if s2.isAppOfArity ``Arm64.State.writeReg64 3 then
        let sInner := s2.getArg! 0
        let r := s2.getArg! 1
        let v := s2.getArg! 2
        let some (hv, v') ← tryFoldTopRegExpr v hblock | return bs
        let newS := mkApp2 (mkConst ``Arm64.State.setPC)
          (mkApp3 (mkConst ``Arm64.State.writeReg64) sInner r v') pc
        let (newSShared, symInternalState') ←
          (Sym.withoutShareCommonChecks (Sym.shareCommon newS)) bs.symCtx |>.run bs.symInternalState
        let seeded := seedNormalizedInSymCache newSShared bs.simpState.persistentCache
        let bs' := { bs with symInternalState := symInternalState',
                             simpState := { bs.simpState with persistentCache := seeded } }
        let newGoalTy := mkApp6 (mkConst ``SepWP) prog targetPc newSShared P post oom
        let newGoalMVar ← mkFreshExprSyntheticOpaqueMVar newGoalTy (← g.getTag)
        let prf := mkAppN (mkConst ``SepWP.rw_top_reg_pc)
          #[prog, targetPc, sInner, pc, r, v, v', P, post, oom, hv, newGoalMVar]
        g.assign prf
        replaceMainGoal [newGoalMVar.mvarId!]
        return bs'
      return bs
    unless sExpr.isAppOfArity ``Arm64.State.writeReg64 3 do return bs
    let sInner := sExpr.getArg! 0
    let r := sExpr.getArg! 1
    let v := sExpr.getArg! 2
    let some (hv, v') ← tryFoldTopRegExpr v hblock | return bs
    let newS := mkApp3 (mkConst ``Arm64.State.writeReg64) sInner r v'
    let (newSShared, symInternalState') ←
      (Sym.withoutShareCommonChecks (Sym.shareCommon newS)) bs.symCtx |>.run bs.symInternalState
    let seeded := seedNormalizedInSymCache newSShared bs.simpState.persistentCache
    let bs' := { bs with symInternalState := symInternalState',
                         simpState := { bs.simpState with persistentCache := seeded } }
    let newGoalTy := mkApp6 (mkConst ``SepWP) prog targetPc newSShared P post oom
    let newGoalMVar ← mkFreshExprSyntheticOpaqueMVar newGoalTy (← g.getTag)
    let prf := mkAppN (mkConst ``SepWP.rw_top_reg)
      #[prog, targetPc, sInner, r, v, v', P, post, oom, hv, newGoalMVar]
    g.assign prf
    replaceMainGoal [newGoalMVar.mvarId!]
    return bs'

private meta def clearDeadMemFVars : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let lctx ← getLCtx
    let goalTy ← instantiateMVars (← g.getType)
    let live := collectFVars {} goalTy
    let mut toClear : Array FVarId := #[]
    for declOpt in lctx.decls.toList.reverse do
      let some decl := declOpt | continue
      if decl.isImplementationDetail || decl.isAuxDecl then continue
      if decl.type.isConstOf ``Arm64.Memory && !live.fvarSet.contains decl.fvarId then
        toClear := toClear.push decl.fvarId
    if !toClear.isEmpty then
      let g' ← g.tryClearMany toClear
      replaceMainGoal [g']

private meta def wpSha512StepsImpl (steps : Nat) (hblock : Syntax) : TacticM Unit := do
  let baseThms ← (← getMainGoal).withContext getOrBuildSymWPTheorems
  let localThms ← (← getMainGoal).withContext buildLocalSymTheorems
  let methods := mkSymWPMethods baseThms localThms
  let config : Sym.Simp.Config := { maxSteps := 100000 }
  let mut bs ← (← getMainGoal).withContext mkInitialWpSymBlockState
  let hblockExpr ← (← getMainGoal).withContext (getFVarFromUserName hblock.getId)
  for stepIdx in [0 : steps] do
    let res ← tryTacticCatchRuntimeMsg do
      let (_, bs') ← wpSymStepInBlock methods config bs (inStepLoop := true)
      let bs'' ← tryFoldGoalTopReg hblockExpr bs'
      if stepIdx % 32 == 31 then
        clearDeadMemFVars
      return bs''
    match res with
    | .ok bs' => bs := bs'
    | .error msg =>
      logWarning m!"wp_sha512_steps stopped at step {stepIdx}: {msg}"
      break
  clearDeadMemFVars

end Sha512Tactic

local elab "wp_sha512_steps" n:num hblock:ident : tactic =>
  wpSha512StepsImpl n.getNat hblock

/-- Active stack cells read or written inside the `compress512` per-block loop (`sp = s0.sp - 256#64`):
`[sp + 0x10]` (`vEnd`), `[sp + 0x18 .. 0x98]` (17 64-bit spill cells), and `[sp + 0xa8]` (1 spill cell). -/
@[expose] def sha512LoopStack (sp : BitVec 64)
    (vEnd : BitVec 64)
    (v18 v20 v28 v30 v38 v40 v48 v50 v58 v60 v68 v70 v78 v80 v88 v90 v98 va8 : BitVec 64) : SepProp :=
  ((sp + 16#64) ↦₆₄ vEnd) ∗
  ((sp + 24#64) ↦₆₄ v18) ∗ ((sp + 32#64) ↦₆₄ v20) ∗ ((sp + 40#64) ↦₆₄ v28) ∗
  ((sp + 48#64) ↦₆₄ v30) ∗ ((sp + 56#64) ↦₆₄ v38) ∗ ((sp + 64#64) ↦₆₄ v40) ∗
  ((sp + 72#64) ↦₆₄ v48) ∗ ((sp + 80#64) ↦₆₄ v50) ∗ ((sp + 88#64) ↦₆₄ v58) ∗
  ((sp + 96#64) ↦₆₄ v60) ∗ ((sp + 104#64) ↦₆₄ v68) ∗ ((sp + 112#64) ↦₆₄ v70) ∗
  ((sp + 120#64) ↦₆₄ v78) ∗ ((sp + 128#64) ↦₆₄ v80) ∗ ((sp + 136#64) ↦₆₄ v88) ∗
  ((sp + 144#64) ↦₆₄ v90) ∗ ((sp + 152#64) ↦₆₄ v98) ∗
  ((sp + 168#64) ↦₆₄ va8)

/-- All 80 read-only 64-bit round constants of `sha2`'s `K64` table. -/
@[expose] def sha2K64AllCells (k_ptr : BitVec 64) : SepProp :=
  sha2K64Cells0 k_ptr ∗ sha2K64Cells1 k_ptr ∗ sha2K64Cells2 k_ptr ∗
  sha2K64Cells3 k_ptr ∗ sha2K64Cells4 k_ptr

private theorem SepWP.of_pre_eq {prog : Program} {target_pc : BitVec 64}
    {s : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hP : P' = P) (h : SepWP prog target_pc s P' post oom) :
    SepWP prog target_pc s P post oom := by
  rw [← hP]; exact h

set_option maxHeartbeats 12000000 in
/-- One full 80-round compression iteration (`0x0038 → 0x2580` / `0x0038`, `2,385` steps). -/
theorem compress512_one_block [Compress512Placement]
    (b : BitVec 64) (hb : b = Compress512Placement.pl.base)
    (s : State) (b_ptr : BitVec 64) (st : List (BitVec 64)) (block : List (BitVec 8))
    (vEnd : BitVec 64)
    (v18 v20 v28 v30 v38 v40 v48 v50 v58 v60 v68 v70 v78 v80 v88 v90 v98 va8 : BitVec 64)
    (R : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = b + 0x38#64)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hst : st.length = 8)
    (hblock : block.length = 128)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = b_ptr)
    (hx17 : s.readReg64 (Reg.gpr 17#5) = st.getD 0 0#64)
    (hx18 : s.readReg64 (Reg.gpr 18#5) = st.getD 1 0#64)
    (hx2 : s.readReg64 (Reg.gpr 2#5) = st.getD 2 0#64)
    (hx4 : s.readReg64 (Reg.gpr 4#5) = st.getD 3 0#64)
    (hx10 : s.readReg64 (Reg.gpr 10#5) = st.getD 4 0#64)
    (hx15 : s.readReg64 (Reg.gpr 15#5) = st.getD 5 0#64)
    (hx16 : s.readReg64 (Reg.gpr 16#5) = st.getD 6 0#64)
    (hx3 : s.readReg64 (Reg.gpr 3#5) = st.getD 7 0#64)
    (hpost : ∀ (s' : State)
      (v18' v20' v28' v30' v38' v40' v48' v50' v58' v60' v68' v70' v78' v80' v88' v90' v98' va8' :
        BitVec 64),
      s'.pc = (if (b_ptr + 128#64 != vEnd) = true then b + 0x38#64 else b + 0x2580#64) →
      s'.status = .Running →
      s'.spAligned = true →
      s'.sp = s.sp →
      s'.readReg64 Reg.fp = s.readReg64 Reg.fp →
      calleeSavedVRegs s' = calleeSavedVRegs s →
      s'.readReg64 (Reg.gpr 1#5) = b_ptr + 128#64 →
      s'.readReg64 (Reg.gpr 17#5) = (sha512CompressBlock st block).getD 0 0#64 →
      s'.readReg64 (Reg.gpr 18#5) = (sha512CompressBlock st block).getD 1 0#64 →
      s'.readReg64 (Reg.gpr 2#5) = (sha512CompressBlock st block).getD 2 0#64 →
      s'.readReg64 (Reg.gpr 4#5) = (sha512CompressBlock st block).getD 3 0#64 →
      s'.readReg64 (Reg.gpr 10#5) = (sha512CompressBlock st block).getD 4 0#64 →
      s'.readReg64 (Reg.gpr 15#5) = (sha512CompressBlock st block).getD 5 0#64 →
      s'.readReg64 (Reg.gpr 16#5) = (sha512CompressBlock st block).getD 6 0#64 →
      s'.readReg64 (Reg.gpr 3#5) = (sha512CompressBlock st block).getD 7 0#64 →
      SepWP (compress512PC.rebase b) (b + 0x2580#64) s'
        (sha512LoopStack s.sp vEnd v18' v20' v28' v30' v38' v40' v48' v50' v58' v60' v68' v70'
           v78' v80' v88' v90' v98' va8' ∗
         (b_ptr ↦ᵣ block) ∗
         sha2K64AllCells
           (Compress512Placement.pl.ρ "sha2:.rodata..Lanon.ee50d778beb355e4b96e6a1be8d6f35b.0") ∗ R)
        post) :
    SepWP (compress512PC.rebase b) (b + 0x2580#64) s
      (sha512LoopStack s.sp vEnd v18 v20 v28 v30 v38 v40 v48 v50 v58 v60 v68 v70
         v78 v80 v88 v90 v98 va8 ∗
       (b_ptr ↦ᵣ block) ∗
       sha2K64AllCells
         (Compress512Placement.pl.ρ "sha2:.rodata..Lanon.ee50d778beb355e4b96e6a1be8d6f35b.0") ∗ R)
      post := by
  subst hb
  rw [sha512A_3 st block] at hx17
  rw [sha512A_2 st block] at hx18
  rw [sha512A_1 st block] at hx2
  rw [sha512A_0 st block] at hx4
  rw [sha512E_3 st block] at hx10
  rw [sha512E_2 st block] at hx15
  rw [sha512E_1 st block] at hx16
  rw [sha512E_0 st block] at hx3
  unfold sha512LoopStack sha2K64AllCells
    sha2K64Cells0 sha2K64Cells1 sha2K64Cells2 sha2K64Cells3 sha2K64Cells4
  rw [pointsToBytesRO_128_eq_cells64 b_ptr block hblock]
  wp_simp_pre only [sepConj_assoc]
  wp_sha512_steps 2385 hblock
  refine SepWP.of_pre_eq ?_
    (hpost _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · unfold sha512LoopStack sha2K64AllCells
      sha2K64Cells0 sha2K64Cells1 sha2K64Cells2 sha2K64Cells3 sha2K64Cells4
    rw [pointsToBytesRO_128_eq_cells64 b_ptr block hblock]
    simp only [sepConj_assoc]
    rfl
  · rfl
  · simp [wp_norm, hrun]
  · rw [← hsp_align]
    simp only [State.spAligned, State.sp_setPC, State.sp_setMem, State.sp_setPState, State.sp_writeReg64_gpr]
  · simp [wp_norm]
  · rfl
  · simp only [calleeSavedVRegs_setPC, calleeSavedVRegs_setMem, calleeSavedVRegs_setPState, calleeSavedVRegs_writeReg64]
  · rfl
  · rw [sha512CompressBlock_eq_sha512AE st block hst]; rfl
  · rw [sha512CompressBlock_eq_sha512AE st block hst]; rfl
  · rw [sha512CompressBlock_eq_sha512AE st block hst]; rfl
  · rw [sha512CompressBlock_eq_sha512AE st block hst]; rfl
  · rw [sha512CompressBlock_eq_sha512AE st block hst]; rfl
  · rw [sha512CompressBlock_eq_sha512AE st block hst]; rfl
  · rw [sha512CompressBlock_eq_sha512AE st block hst]; rfl
  · rw [sha512CompressBlock_eq_sha512AE st block hst]; rfl

end LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Step
