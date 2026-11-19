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
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Ref -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Cells -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256RoundDefs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Code -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Fetch
meta import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Cells
meta import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256RoundDefs

/-!
# Single-Block Symbolic Execution of `sha2::sha256::compress256` (`Compress256Step`)

Verifies one 64-round iteration (`0x0038 → 0x1da0` / `0x0038`, `1,881` symbolic steps including
the relaxable `ADRP`+`ADD` / `NOP`+`ADR` pair at `0x00d0`) of
`_RNvNtCsbvWyylYiyxg_4sha26sha25611compress256`, exporting `sha256LoopStack`, `sha2K32AllCells`,
and `compress256_one_block`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Step

open Arm64 ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Ref
  (sha256K sha256CompressBlock)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Cells
  (readLE32 pointsToBytesRO_64_eq_cells32 sha2K32Cells0 sha2K32Cells1 sha2K32Cells2 sha2K32Cells3
   SepWP.rw_top_reg)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256RoundDefs
  (sha256W sha256W_init_off sha256W_step1 sha256W_step2 sha256W_add_k
   sha256T1 sha256T2 sha256T2_eq
   sha256T1_eq1 sha256T1_eq2 sha256T1_eq3 sha256T1_eq4 sha256T1_eq5 sha256T1_eq6
   sha256A sha256E sha256A_0 sha256A_1 sha256A_2 sha256A_3
   sha256E_0 sha256E_1 sha256E_2 sha256E_3
   sha256E_from_t1 sha256A_from_t1_t2 sha256Final0 sha256Final4
   sha256CompressBlock_eq_sha256AE)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Code
  (Compress256Placement compress256PC)

arm64_proof_prelude

section Sha256Tactic
open Lean Meta Elab Tactic

@[wp_norm]
private theorem zeroExtend_32_64_eq_setWidth (x : BitVec 32) :
    BitVec.zeroExtend 64 x = BitVec.setWidth 64 x := rfl

private theorem congr_setWidth64 {x y : BitVec 32} (h : x = y) :
    BitVec.setWidth 64 x = BitVec.setWidth 64 y :=
  congrArg (BitVec.setWidth 64) h

private theorem sha256W_init_off_norm (block : List (BitVec 8)) (off i : Nat)
    (hblock : block.length = 64) (hi : i < 16) (hoff : 4 * i = off) :
    BitVec.setWidth 32 (rev32_64 (BitVec.setWidth 64 (readLE32 block off))) = sha256W block i :=
  sha256W_init_off block off i hblock hi hoff

private theorem sha256W_init_off_unnorm (block : List (BitVec 8)) (off i : Nat)
    (hblock : block.length = 64) (hi : i < 16) (hoff : 4 * i = off) :
    BitVec.setWidth 32
      (rev32_64 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.zeroExtend 64 (readLE32 block off))))) =
      sha256W block i := by
  have h : BitVec.setWidth 32 (BitVec.zeroExtend 64 (readLE32 block off)) = readLE32 block off := by
    simp
  rw [h]
  exact sha256W_init_off block off i hblock hi hoff

private theorem sha256Final0' (st : List (BitVec 32)) (block : List (BitVec 8)) :
    ((((sha256A st block 66 &&& (sha256A st block 65 ^^^ sha256A st block 64)) ^^^
        (sha256A st block 65 &&& sha256A st block 64)) + sha256A st block 3) +
      ((BitVec.setWidth 32 ((sha256A st block 66 ++ sha256A st block 66) >>> 2) ^^^
        (sha256A st block 66).rotateRight 13) ^^^ (sha256A st block 66).rotateRight 22)) +
      sha256T1 (sha256E st block 66) (sha256E st block 65) (sha256E st block 64)
        (sha256E st block 63) (sha256K.getD 63 0#32) (sha256W block 63) =
      st.getD 0 0#32 + sha256A st block 67 := by
  rw [← sha256A_3, sha256Final0]

private theorem sha256Final1' (st : List (BitVec 32)) (block : List (BitVec 8)) :
    sha256A st block 66 + sha256A st block 2 = st.getD 1 0#32 + sha256A st block 66 := by
  rw [← sha256A_2, BitVec.add_comm]

private theorem sha256Final2' (st : List (BitVec 32)) (block : List (BitVec 8)) :
    sha256A st block 65 + sha256A st block 1 = st.getD 2 0#32 + sha256A st block 65 := by
  rw [← sha256A_1, BitVec.add_comm]

private theorem sha256Final3' (st : List (BitVec 32)) (block : List (BitVec 8)) :
    sha256A st block 64 + sha256A st block 0 = st.getD 3 0#32 + sha256A st block 64 := by
  rw [← sha256A_0, BitVec.add_comm]

private theorem sha256Final4' (st : List (BitVec 32)) (block : List (BitVec 8)) :
    (sha256A st block 63 + sha256E st block 3) +
      sha256T1 (sha256E st block 66) (sha256E st block 65) (sha256E st block 64)
        (sha256E st block 63) (sha256K.getD 63 0#32) (sha256W block 63) =
      st.getD 4 0#32 + sha256E st block 67 := by
  rw [← sha256E_3, sha256Final4]

private theorem sha256Final5' (st : List (BitVec 32)) (block : List (BitVec 8)) :
    sha256E st block 66 + sha256E st block 2 = st.getD 5 0#32 + sha256E st block 66 := by
  rw [← sha256E_2, BitVec.add_comm]

private theorem sha256Final6' (st : List (BitVec 32)) (block : List (BitVec 8)) :
    sha256E st block 65 + sha256E st block 1 = st.getD 6 0#32 + sha256E st block 65 := by
  rw [← sha256E_1, BitVec.add_comm]

private theorem sha256Final7' (st : List (BitVec 32)) (block : List (BitVec 8)) :
    sha256E st block 64 + sha256E st block 0 = st.getD 7 0#32 + sha256E st block 64 := by
  rw [← sha256E_0, BitVec.add_comm]

attribute [local irreducible] sha256K

private meta def tryApplyPureEqThm (thmName : Name) (v : Expr) : MetaM (Option (Expr × Expr)) := do
  withoutModifyingState do
    let info ← getConstInfo thmName
    let (mvars, _, ty) ← forallMetaTelescope info.type
    let some (_, lhs, rhs) := ty.eq? | return none
    unless ← withReducible (isDefEq lhs v) do return none
    let prf ← instantiateMVars (mkAppN (mkConst thmName) mvars)
    let rhs' ← instantiateMVars rhs
    if prf.hasExprMVar || rhs'.hasExprMVar then return none
    if rhs'.isAppOfArity ``sha256T1 6 then
      unless (rhs'.getArg! 3).isAppOfArity ``sha256E 3 &&
             (rhs'.getArg! 4).isAppOfArity ``List.getD 4 &&
             (rhs'.getArg! 5).isAppOfArity ``sha256W 2 do
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

private meta def tryFoldTopRegExpr32 (v : Expr) (hblock : Expr) : MetaM (Option (Expr × Expr)) := do
  if v.isAppOfArity ``BitVec.setWidth 3 then
    let revCand := v.getArg! 2
    if revCand.isAppOfArity ``Arm64.rev32_64 1 then
      let arg64 := revCand.getArg! 0
      if arg64.isAppOfArity ``BitVec.setWidth 3 then
        let inner := arg64.getArg! 2
        if inner.isAppOfArity ``readLE32 2 then
          let block := inner.getArg! 0
          let offExpr := inner.getArg! 1
          let some off := offExpr.nat? | return none
          let iExpr := toExpr (off / 4)
          let hi ← mkDecideProof (← mkAppM ``LT.lt #[iExpr, toExpr (16 : Nat)])
          let hoff ← mkDecideProof (← mkEq (← mkAppM ``HMul.hMul #[toExpr (4 : Nat), iExpr]) offExpr)
          let prf := mkApp6 (mkConst ``sha256W_init_off_norm) block offExpr iExpr hblock hi hoff
          let rhs := mkApp2 (mkConst ``sha256W) block iExpr
          return some (prf, rhs)
        if inner.isAppOfArity ``BitVec.setWidth 3 then
          let zext := inner.getArg! 2
          if zext.isAppOfArity ``BitVec.zeroExtend 3 then
            let rle := zext.getArg! 2
            if rle.isAppOfArity ``readLE32 2 then
              let block := rle.getArg! 0
              let offExpr := rle.getArg! 1
              let some off := offExpr.nat? | return none
              let iExpr := toExpr (off / 4)
              let hi ← mkDecideProof (← mkAppM ``LT.lt #[iExpr, toExpr (16 : Nat)])
              let hoff ← mkDecideProof (← mkEq (← mkAppM ``HMul.hMul #[toExpr (4 : Nat), iExpr]) offExpr)
              let prf := mkApp6 (mkConst ``sha256W_init_off_unnorm) block offExpr iExpr hblock hi hoff
              let rhs := mkApp2 (mkConst ``sha256W) block iExpr
              return some (prf, rhs)
    return none
  unless v.isAppOfArity ``HAdd.hAdd 6 do return none
  let lhs := v.getArg! 4
  let rhs := v.getArg! 5
  if rhs.isAppOfArity ``sha256A 3 && lhs.isAppOfArity ``sha256T1 6 then
    return ← tryApplyIdxEqThm ``sha256E_from_t1 v 5 6 4 7
  if rhs.isAppOfArity ``sha256T1 6 then
    if lhs.isAppOfArity ``sha256T2 3 then
      return ← tryApplyIdxEqThm ``sha256A_from_t1_t2 v 5 6 4 7
    if let some res ← tryApplyPureEqThm ``sha256Final0' v then return some res
    if let some res ← tryApplyPureEqThm ``sha256Final4' v then return some res
    return none
  if rhs.isAppOfArity ``HXor.hXor 6 then
    if lhs.isAppOfArity ``HXor.hXor 6 then
      return ← tryApplyPureEqThm ``sha256T2_eq v
    for thm in #[``sha256T1_eq6, ``sha256T1_eq4, ``sha256T1_eq2,
                 ``sha256T1_eq5, ``sha256T1_eq1, ``sha256T1_eq3] do
      if let some res ← tryApplyPureEqThm thm v then return some res
    if let some res ← tryApplyIdxEqThm ``sha256W_step1 v 2 5 16 6 then return some res
    if let some res ← tryApplyIdxEqThm ``sha256W_step2 v 2 5 16 6 then return some res
    if let some res ← tryApplyIdxEqThm ``sha256W_add_k v 2 6 16 7 then return some res
    return none
  if lhs.isAppOfArity ``sha256A 3 && rhs.isAppOfArity ``sha256A 3 then
    for thm in #[``sha256Final1', ``sha256Final2', ``sha256Final3'] do
      if let some res ← tryApplyPureEqThm thm v then return some res
    return none
  if lhs.isAppOfArity ``sha256E 3 && rhs.isAppOfArity ``sha256E 3 then
    for thm in #[``sha256Final5', ``sha256Final6', ``sha256Final7'] do
      if let some res ← tryApplyPureEqThm thm v then return some res
    return none
  return none

private meta def tryFoldTopRegExpr (v64 : Expr) (hblock : Expr) : MetaM (Option (Expr × Expr)) := do
  unless v64.isAppOfArity ``BitVec.setWidth 3 do return none
  unless (v64.getArg! 0).nat? == some 32 && (v64.getArg! 1).nat? == some 64 do return none
  let v32 := v64.getArg! 2
  let some (prf32, rhs32) ← tryFoldTopRegExpr32 v32 hblock | return none
  let prf64 := mkApp3 (mkConst ``congr_setWidth64) v32 rhs32 prf32
  let rhs64 := mkApp3 (mkConst ``BitVec.setWidth) (v64.getArg! 0) (v64.getArg! 1) rhs32
  return some (prf64, rhs64)

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

private meta def wpSha256StepsImpl (steps : Nat) (hblock : Syntax) : TacticM Unit := do
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
      logWarning m!"wp_sha256_steps stopped at step {stepIdx}: {msg}"
      break
  clearDeadMemFVars

end Sha256Tactic

local elab "wp_sha256_steps" n:num hblock:ident : tactic =>
  wpSha256StepsImpl n.getNat hblock

/-- Active stack cells read or written inside the `compress256` per-block loop (`sp = s0.sp - 176#64`). -/
@[expose] def sha256LoopStack (sp : BitVec 64)
    (vEnd : BitVec 64)
    (w1c w20 w24 w28 w2c w30 w34 w38 w3c w40 w44 : BitVec 32)
    (v48 : BitVec 64)
    (w58 w5c : BitVec 32) : SepProp :=
  ((sp + 16#64) ↦₆₄ vEnd) ∗
  ((sp + 28#64) ↦₃₂ w1c) ∗ ((sp + 32#64) ↦₃₂ w20) ∗ ((sp + 36#64) ↦₃₂ w24) ∗
  ((sp + 40#64) ↦₃₂ w28) ∗ ((sp + 44#64) ↦₃₂ w2c) ∗ ((sp + 48#64) ↦₃₂ w30) ∗
  ((sp + 52#64) ↦₃₂ w34) ∗ ((sp + 56#64) ↦₃₂ w38) ∗ ((sp + 60#64) ↦₃₂ w3c) ∗
  ((sp + 64#64) ↦₃₂ w40) ∗ ((sp + 68#64) ↦₃₂ w44) ∗
  ((sp + 72#64) ↦₆₄ v48) ∗
  ((sp + 88#64) ↦₃₂ w58) ∗ ((sp + 92#64) ↦₃₂ w5c)

/-- All 64 read-only 32-bit round constants of `sha2::consts::K32`. -/
@[expose] def sha2K32AllCells (k_ptr : BitVec 64) : SepProp :=
  sha2K32Cells0 k_ptr ∗ sha2K32Cells1 k_ptr ∗ sha2K32Cells2 k_ptr ∗ sha2K32Cells3 k_ptr

private theorem SepWP.of_pre_eq {prog : Program} {target_pc : BitVec 64}
    {s : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hP : P' = P) (h : SepWP prog target_pc s P' post oom) :
    SepWP prog target_pc s P post oom := by
  rw [← hP]; exact h

set_option maxHeartbeats 8000000 in
/-- One full 64-round compression iteration (`0x0038 → 0x1da0` / `0x0038`, `1,881` steps). -/
theorem compress256_one_block [Compress256Placement]
    (b : BitVec 64) (hb : b = Compress256Placement.pl.base)
    (s : State) (b_ptr : BitVec 64) (st : List (BitVec 32)) (block : List (BitVec 8))
    (vEnd : BitVec 64)
    (w1c w20 w24 w28 w2c w30 w34 w38 w3c w40 w44 : BitVec 32)
    (v48 : BitVec 64)
    (w58 w5c : BitVec 32)
    (R : SepProp) (post : State → SepProp → Prop)
    (hpc : s.pc = b + 0x38#64)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hst : st.length = 8)
    (hblock : block.length = 64)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = b_ptr)
    (hx2 : s.readReg64 (Reg.gpr 2#5) = BitVec.setWidth 64 (st.getD 0 0#32))
    (hx5 : s.readReg64 (Reg.gpr 5#5) = BitVec.setWidth 64 (st.getD 1 0#32))
    (hx6 : s.readReg64 (Reg.gpr 6#5) = BitVec.setWidth 64 (st.getD 2 0#32))
    (hx7 : s.readReg64 (Reg.gpr 7#5) = BitVec.setWidth 64 (st.getD 3 0#32))
    (hx11 : s.readReg64 (Reg.gpr 11#5) = BitVec.setWidth 64 (st.getD 4 0#32))
    (hx17 : s.readReg64 (Reg.gpr 17#5) = BitVec.setWidth 64 (st.getD 5 0#32))
    (hx3 : s.readReg64 (Reg.gpr 3#5) = BitVec.setWidth 64 (st.getD 6 0#32))
    (hx4 : s.readReg64 (Reg.gpr 4#5) = BitVec.setWidth 64 (st.getD 7 0#32))
    (hpost : ∀ (s' : State)
      (w1c' w20' w24' w28' w2c' w30' w34' w38' w3c' w40' w44' : BitVec 32)
      (v48' : BitVec 64)
      (w58' w5c' : BitVec 32),
      s'.pc = (if (b_ptr + 64#64 != vEnd) = true then b + 0x38#64 else b + 0x1da0#64) →
      s'.status = .Running →
      s'.spAligned = true →
      s'.sp = s.sp →
      s'.readReg64 Reg.fp = s.readReg64 Reg.fp →
      calleeSavedVRegs s' = calleeSavedVRegs s →
      s'.readReg64 (Reg.gpr 1#5) = b_ptr + 64#64 →
      s'.readReg64 (Reg.gpr 2#5) = BitVec.setWidth 64 ((sha256CompressBlock st block).getD 0 0#32) →
      s'.readReg64 (Reg.gpr 5#5) = BitVec.setWidth 64 ((sha256CompressBlock st block).getD 1 0#32) →
      s'.readReg64 (Reg.gpr 6#5) = BitVec.setWidth 64 ((sha256CompressBlock st block).getD 2 0#32) →
      s'.readReg64 (Reg.gpr 7#5) = BitVec.setWidth 64 ((sha256CompressBlock st block).getD 3 0#32) →
      s'.readReg64 (Reg.gpr 11#5) = BitVec.setWidth 64 ((sha256CompressBlock st block).getD 4 0#32) →
      s'.readReg64 (Reg.gpr 17#5) = BitVec.setWidth 64 ((sha256CompressBlock st block).getD 5 0#32) →
      s'.readReg64 (Reg.gpr 3#5) = BitVec.setWidth 64 ((sha256CompressBlock st block).getD 6 0#32) →
      s'.readReg64 (Reg.gpr 4#5) = BitVec.setWidth 64 ((sha256CompressBlock st block).getD 7 0#32) →
      SepWP (compress256PC.rebase b) (b + 0x1da0#64) s'
        (sha256LoopStack s.sp vEnd w1c' w20' w24' w28' w2c' w30' w34' w38' w3c' w40' w44' v48' w58' w5c' ∗
         (b_ptr ↦ᵣ block) ∗
         sha2K32AllCells (Compress256Placement.pl.ρ "sha2:.rodata.sha2::consts::K32") ∗ R)
        post) :
    SepWP (compress256PC.rebase b) (b + 0x1da0#64) s
      (sha256LoopStack s.sp vEnd w1c w20 w24 w28 w2c w30 w34 w38 w3c w40 w44 v48 w58 w5c ∗
       (b_ptr ↦ᵣ block) ∗
       sha2K32AllCells (Compress256Placement.pl.ρ "sha2:.rodata.sha2::consts::K32") ∗ R)
      post := by
  subst hb
  rw [sha256A_3 st block] at hx2
  rw [sha256A_2 st block] at hx5
  rw [sha256A_1 st block] at hx6
  rw [sha256A_0 st block] at hx7
  rw [sha256E_3 st block] at hx11
  rw [sha256E_2 st block] at hx17
  rw [sha256E_1 st block] at hx3
  rw [sha256E_0 st block] at hx4
  unfold sha256LoopStack sha2K32AllCells sha2K32Cells0 sha2K32Cells1 sha2K32Cells2 sha2K32Cells3
  rw [pointsToBytesRO_64_eq_cells32 b_ptr block hblock]
  wp_simp_pre only [sepConj_assoc]
  wp_sha256_steps 1881 hblock
  refine SepWP.of_pre_eq ?_
    (hpost _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · unfold sha256LoopStack sha2K32AllCells sha2K32Cells0 sha2K32Cells1 sha2K32Cells2 sha2K32Cells3
    rw [pointsToBytesRO_64_eq_cells32 b_ptr block hblock]
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
  · rw [sha256CompressBlock_eq_sha256AE st block hst]; rfl
  · rw [sha256CompressBlock_eq_sha256AE st block hst]; rfl
  · rw [sha256CompressBlock_eq_sha256AE st block hst]; rfl
  · rw [sha256CompressBlock_eq_sha256AE st block hst]; rfl
  · rw [sha256CompressBlock_eq_sha256AE st block hst]; rfl
  · rw [sha256CompressBlock_eq_sha256AE st block hst]; rfl
  · rw [sha256CompressBlock_eq_sha256AE st block hst]; rfl
  · rw [sha256CompressBlock_eq_sha256AE st block hst]; rfl

end LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Step
