/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Pure -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage2
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.ModelBridge
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTraced
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Link
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytes
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import Mathlib.Tactic.Basic
import Mathlib.Tactic.ToAdditive
import Mathlib.Tactic.ToDual
import Lean.Elab.SyntheticMVars
import Lean.Meta.Reduce
import ProofLib.GenDecodes
import ProofLib.GenPlacedFetches
import ProofLib.ProgramReflection
import ProofLib.SepLogic.CodeLookup
import ProofLib.SepLogic.WP.ControlTactics
import ProofLib.VCGen
import ProofLib
import ProofLib.FsTrace
import ProofLib.Placed.Multi
import ProofLib.ProgramReflection.Variant.TrapTransfer
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Frames
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSegsExt
public meta import Lean -- shake: keep

/-!
# Stage 4 Stack/OOM Helpers and Early `Err` Exit (`+4508 → RET`)

Stack-splitting (`stackAt_fsp_split`), OOM panic discharge (`panic_oom_close`), and the early
`Err(InvalidKeyAgreement)` exit path (`stage4_err_exit`, `+4508 → RET`) freeing `kemCtPtr`
(`1569` B) and `pqspkPtr` (`1568` B) and writing `speWord 10` to `x.ret`.
-/

public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunDrop
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

macro "s4_clean_sp_attrs" : command => `(command|
  attribute [-arm64_norm]
    CryptoVerification.LibsignalTripleRatchet.Expand.sp_sub_496_eq_esp
    CryptoVerification.LibsignalTripleRatchet.Expand.sp_add_neg496_eq_esp
    CryptoVerification.LibsignalTripleRatchet.Expand.esp_add_496_sub_496
    CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
    CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
    CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
    CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
    CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
    CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
    CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
    CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp)

s4_clean_sp_attrs

@[arm64_norm, wp_norm]
theorem s4_bv_sub_sub (x : BitVec 64) (a b : Nat) (_hab : a + b < 2 ^ 64 := by decide) :
    x - BitVec.ofNat 64 a - BitVec.ofNat 64 b = x - BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

@[arm64_norm, wp_norm]
theorem s4_bv_sub_add_lt (x : BitVec 64) (a b : Nat) (_h : b < a := by decide)
    (_ha : a < 2 ^ 64 := by decide) :
    x - BitVec.ofNat 64 a + BitVec.ofNat 64 b = x - BitVec.ofNat 64 (a - b) :=
  ProofLib.bv_sub_add_lit x a b _h _ha

@[arm64_norm, wp_norm]
theorem s4_bv_sub_add_gt (x : BitVec 64) (a b : Nat) (_h : a < b := by decide)
    (_hb : b < 2 ^ 64 := by decide) :
    x - BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (b - a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

@[arm64_norm, wp_norm]
theorem s4_bv_add_neg64 (x c : BitVec 64) (_hc : c.msb = true := by decide) :
    x + c = x - (-c) := by
  rw [BitVec.sub_neg]

@[arm64_norm ↓, wp_norm ↓]
theorem s4_sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem s4_sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem s4_readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[arm64_norm ↓, wp_norm ↓]
theorem s4_readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem s4_readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem s4_readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem s4_readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem s4_readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm] cliInitiateFrame_eq BitVec.toNat_zero
run_cmd Lean.Elab.Command.liftCoreM do
  for attrName in [`arm64_norm, `wp_norm] do
    let some ext ← Lean.Meta.Simp.getSimprocExtension? attrName
      | throwError "unknown simproc extension `{attrName}`"
    for declName in [``BitVec.reduceSub, ``BitVec.reduceNeg] do
      Lean.Meta.Simp.addSimprocAttrCore ext declName .local (post := true)

/-! ## Stack Split and OOM Panic Discharge -/

theorem stackAt_fsp_split {B : RunBudgets} {stk : Nat}
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (fsp : BitVec 64) (K : Nat) (hK : K ≤ 262144) :
    stackAt fsp (stk - cliInitiateFrame) =
      stackAt fsp K ∗
        stackAt (fsp - BitVec.ofNat 64 K) (stk - cliInitiateFrame - K) := by
  have hbase_ge := stk_sub_ge_base hstk
  have h63 := stk_sub_le_63 hstk64
  dsimp only [stackAt]
  have haddr :
      (fsp - BitVec.ofNat 64 K) - BitVec.ofNat 64 (stk - cliInitiateFrame - K) =
        fsp - BitVec.ofNat 64 (stk - cliInitiateFrame) := by
    have hadd :
        BitVec.ofNat 64 K + BitVec.ofNat 64 (stk - cliInitiateFrame - K) =
          BitVec.ofNat 64 (stk - cliInitiateFrame) :=
      bv64_ofNat_add_eq_of_mod (by omega)
    bv_omega
  rw [haddr, ProofLib.memRegion_split'
    (b := fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
    (n := stk - cliInitiateFrame - K) (k := K)
    (b' := fsp - BitVec.ofNat 64 K)
    (by omega) (by rw [← haddr]; bv_omega) (by omega)]
  ac_rfl

theorem allocFailedIn_of_trace_eq' {s0 s sm : State}
    (htr : s.trace = s0.trace) (h : allocFailedIn s sm) :
    allocFailedIn s0 sm := by
  unfold allocFailedIn at h ⊢
  rwa [htr] at h

theorem sepWPp_frame_fold {prog : Program} {ret : BitVec 64} {s : State}
    {A B P Rest : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : A ⊢ B) (heq : P = A ∗ Rest)
    (hw : SepWPp prog ret s (B ∗ Rest) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  fun R hm hL =>
    hw R (Satisfies.mono (sepConj_mono_left (Entails.trans (Entails.of_eq heq) (sepConj_mono_left h))) hm) hL

theorem s4_sep_assoc_r (P Q R : SepProp) : (P ∗ Q) ∗ R = P ∗ (Q ∗ R) := by ac_rfl
theorem s4_sep_swap (A B : SepProp) : A ∗ B = B ∗ A := by ac_rfl
theorem s4_sep_pull (B A R : SepProp) : B ∗ (A ∗ R) = A ∗ (B ∗ R) := by ac_rfl
theorem s4_sep_emp_r (P : SepProp) : P ∗ emp = P := sepConj_emp P
theorem s4_sep_congr_l {P P' : SepProp} (Q : SepProp) (h : P = P') : P ∗ Q = P' ∗ Q :=
  congrArg (· ∗ Q) h
theorem s4_sep_congr_r (P : SepProp) {Q Q' : SepProp} (h : Q = Q') : P ∗ Q = P ∗ Q' :=
  congrArg (P ∗ ·) h

section S4FrameTactics
open Lean Elab Tactic Meta

private meta partial def s4SpineFnArgs (e : Expr) : Expr × Array Expr :=
  let rec go (e : Expr) (acc : List Expr) : Expr × Array Expr :=
    match e with
    | .mdata _ b => go b acc
    | .app f a   => go f (a.consumeMData :: acc)
    | _          => (e, acc.toArray)
  go e []

private meta def s4MkSepList : List Expr → Expr
  | [] => mkConst ``Arm64.emp
  | [x] => x
  | x :: xs => mkApp2 (mkConst ``Arm64.sepConj) x (s4MkSepList xs)

private meta def s4AtomsMatch (p a : Expr) : MetaM Bool := do
  let p := p.consumeMData
  let a := a.consumeMData
  if p == a then return true
  if ← withoutModifyingState (withTransparency .instances (isDefEq p a)) then
    return true
  let (pfn, pargs) := s4SpineFnArgs p
  let (afn, aargs) := s4SpineFnArgs a
  if pfn != afn || pargs.size != aargs.size then
    return false
  for i in [0 : pargs.size] do
    let pi := pargs[i]!
    let ai := aargs[i]!
    if pi != ai then
      let ty ← inferType pi
      let ok ← withoutModifyingState do
        if ← withTransparency .instances (isDefEq pi ai) then pure true
        else if ty.consumeMData.isConstOf ``Arm64.SepProp then pure false
        else if !pi.hasFVar && !ai.hasFVar then isDefEq pi ai
        else pure false
      if !ok then return false
  return true

private meta def s4AppendNorm (xs ys : List Expr) : MetaM Expr := do
  if ys.isEmpty then
    return mkApp (mkConst ``s4_sep_emp_r) (s4MkSepList xs)
  match xs with
  | [] => mkEqRefl (s4MkSepList ys)
  | [x] => mkEqRefl (mkApp2 (mkConst ``Arm64.sepConj) x (s4MkSepList ys))
  | x :: rest =>
    let restSep := s4MkSepList rest
    let ySep := s4MkSepList ys
    let rySep := s4MkSepList (rest ++ ys)
    let h_ry ← s4AppendNorm rest ys
    let h1 := mkAppN (mkConst ``s4_sep_assoc_r) #[x, restSep, ySep]
    let h2 := mkAppN (mkConst ``s4_sep_congr_r)
      #[x, mkApp2 (mkConst ``Arm64.sepConj) restSep ySep, rySep, h_ry]
    mkEqTrans h1 h2

private meta partial def s4NormSep (e : Expr) : MetaM (List Expr × Expr) := do
  let (fn, args) := s4SpineFnArgs e
  if fn.constName? == some ``Arm64.sepConj && args.size == 2 then
    let (xs, hx) ← s4NormSep args[0]!
    let (ys, hy) ← s4NormSep args[1]!
    let xSep := s4MkSepList xs
    let ySep := s4MkSepList ys
    let h_l := mkAppN (mkConst ``s4_sep_congr_l) #[args[0]!, xSep, args[1]!, hx]
    let h_r := mkAppN (mkConst ``s4_sep_congr_r) #[xSep, args[1]!, ySep, hy]
    let h_app ← s4AppendNorm xs ys
    return (xs ++ ys, ← mkEqTrans h_l (← mkEqTrans h_r h_app))
  else
    let a := e.consumeMData
    return ([a], ← mkEqRefl a)

private meta def s4ExtractOne (ps : List Expr) (a : Expr) :
    MetaM (Option (Expr × List Expr × Expr)) := do
  match ps with
  | [] => return none
  | [p] =>
    if ← s4AtomsMatch p a then return some (p, [], ← mkEqRefl p)
    else return none
  | p :: rest =>
    if ← s4AtomsMatch p a then
      return some (p, rest, ← mkEqRefl (s4MkSepList (p :: rest)))
    else
      match ← s4ExtractOne rest a with
      | none => return none
      | some (m, rem', h_sub) =>
        let restSep := s4MkSepList rest
        let mRemSep := s4MkSepList (m :: rem')
        let h1 := mkAppN (mkConst ``s4_sep_congr_r) #[p, restSep, mRemSep, h_sub]
        match rem' with
        | [] =>
          let h2 := mkAppN (mkConst ``s4_sep_swap) #[p, m]
          return some (m, [p], ← mkEqTrans h1 h2)
        | _ :: _ =>
          let remSep := s4MkSepList rem'
          let h2 := mkAppN (mkConst ``s4_sep_pull) #[p, m, remSep]
          return some (m, p :: rem', ← mkEqTrans h1 h2)

private meta def s4ExtractMany (pExpr : Expr) (ps : List Expr) :
    List Expr → MetaM (List Expr × List Expr × Expr)
  | [] => do return ([], ps, ← mkEqRefl (s4MkSepList ps))
  | a :: tailAtoms => do
    let some (m, rem1, h1) ← s4ExtractOne ps a
      | throwError "s4_frame: atom not found in precondition:\n  {a}\npre:\n  {pExpr}"
    let (ms, remFinal, h2) ← s4ExtractMany pExpr rem1 tailAtoms
    if rem1.isEmpty then
      return ([m], [], h1)
    else
      let h_step := mkAppN (mkConst ``s4_sep_congr_r)
        #[m, s4MkSepList rem1, s4MkSepList (ms ++ remFinal), h2]
      return (m :: ms, remFinal, ← mkEqTrans h1 h_step)

private meta def s4MkSplitEqProof (pExpr aExpr : Expr) : TacticM (Expr × Expr) := do
  let (ps, hpNorm) ← s4NormSep pExpr
  let (aAtoms, haNorm) ← s4NormSep aExpr
  let (matched, rem, hPerm) ← s4ExtractMany pExpr ps aAtoms
  let restExpr := s4MkSepList rem
  let aSep := s4MkSepList aAtoms
  let hApp ← s4AppendNorm matched rem
  let g1 ← mkEqTrans hpNorm (← mkEqTrans hPerm (← mkEqSymm hApp))
  let g2 := mkAppN (mkConst ``s4_sep_congr_l) #[aSep, aExpr, restExpr, ← mkEqSymm haNorm]
  let heq ← mkEqTrans g1 g2
  return (restExpr, heq)

private meta def s4SilentTac (tac : TacticM Unit) : TacticM Unit := do
  let saved ← saveState
  let logBefore ← Core.getMessageLog
  try
    tac
    if (← Core.getMessageLog).toList.length > logBefore.toList.length then
      saved.restore (restoreInfo := true)
      Core.setMessageLog logBefore
  catch _ =>
    saved.restore (restoreInfo := true)
    Core.setMessageLog logBefore

private meta def s4SimpLhs : TacticM Unit := do
  let hasFsp := (← getLCtx).findFromUserName? `fsp |>.isSome
  if hasFsp then
    let fspId : Ident := mkIdent `fsp
    s4SilentTac <| evalTactic (← `(tactic| (conv => lhs; simp only [$fspId:ident, wp_norm, arm64_norm, BitVec.sub_sub, BitVec.add_assoc, BitVec.reduceAdd])))
  else
    s4SilentTac <| evalTactic (← `(tactic| (conv => lhs; simp only [wp_norm, arm64_norm, BitVec.sub_sub, BitVec.add_assoc, BitVec.reduceAdd])))

private meta def s4SimpRhs : TacticM Unit := do
  let hasFsp := (← getLCtx).findFromUserName? `fsp |>.isSome
  if hasFsp then
    let fspId : Ident := mkIdent `fsp
    s4SilentTac <| evalTactic (← `(tactic| (conv => rhs; simp only [$fspId:ident, wp_norm, arm64_norm, BitVec.sub_sub, BitVec.add_assoc, BitVec.reduceAdd])))
  else
    s4SilentTac <| evalTactic (← `(tactic| (conv => rhs; simp only [wp_norm, arm64_norm, BitVec.sub_sub, BitVec.add_assoc, BitVec.reduceAdd])))

private meta def s4SimpRhsArg1 : TacticM Unit := do
  let hasFsp := (← getLCtx).findFromUserName? `fsp |>.isSome
  if hasFsp then
    let fspId : Ident := mkIdent `fsp
    s4SilentTac <| evalTactic (← `(tactic| (conv => rhs; arg 1; simp only [$fspId:ident, wp_norm, arm64_norm, BitVec.sub_sub, BitVec.add_assoc, BitVec.reduceAdd])))
  else
    s4SilentTac <| evalTactic (← `(tactic| (conv => rhs; arg 1; simp only [wp_norm, arm64_norm, BitVec.sub_sub, BitVec.add_assoc, BitVec.reduceAdd])))

elab "s4_ac_rfl" : tactic => do
  s4SimpLhs
  if (← getUnsolvedGoals).isEmpty then return
  s4SimpRhs
  if (← getUnsolvedGoals).isEmpty then return
  withMainContext do
    let g ← getMainGoal
    let gty ← instantiateMVars (← g.getType)
    let (efn, eargs) := s4SpineFnArgs gty
    if efn.constName? != some ``Eq || eargs.size != 3 then
      throwError "s4_ac_rfl expected equality goal, got: {gty}"
    let lhs := eargs[1]!
    let rhs := eargs[2]!
    let (rem, heq) ← s4MkSplitEqProof lhs rhs
    if !rem.isConstOf ``Arm64.emp then
      throwError "s4_ac_rfl: leftover atoms on LHS:\n  {rem}"
    let hEmp := mkApp (mkConst ``s4_sep_emp_r) rhs
    g.assign (← mkEqTrans heq hEmp)
    let gs ← getGoals
    setGoals (gs.filter (· != g))

elab "s4_split_frame" : tactic => do
  s4SimpLhs
  if (← getUnsolvedGoals).isEmpty then return
  s4SimpRhsArg1
  if (← getUnsolvedGoals).isEmpty then return
  withMainContext do
    let g ← getMainGoal
    let gty ← instantiateMVars (← g.getType)
    let (efn, eargs) := s4SpineFnArgs gty
    if efn.constName? != some ``Eq || eargs.size != 3 then
      throwError "s4_split_frame expected equality goal, got: {gty}"
    let lhs := eargs[1]!
    let rhs := eargs[2]!
    let (_, rargs) := s4SpineFnArgs rhs
    let calleePre := rargs[0]!
    let fMVar := rargs[1]!
    let (restExpr, heqExpr) ← s4MkSplitEqProof lhs calleePre
    fMVar.mvarId!.assign restExpr
    g.assign heqExpr
    let gs ← getGoals
    setGoals (gs.filter fun m => m != g && m != fMVar.mvarId!)

macro "s4_fold_pre " h:term : tactic =>
  `(tactic| refine sepWPp_frame_fold $h (by s4_split_frame) ?_)

macro "s4_rw_pre " h:term : tactic =>
  `(tactic| refine sepWPp_frame_fold (Entails.of_eq $h) (by s4_split_frame) ?_)

theorem s4_entails_fold {A B P Q Rest : SepProp}
    (h : A ⊢ B) (heq : P = A ∗ Rest) (hnext : B ∗ Rest ⊢ Q) :
    P ⊢ Q :=
  Entails.trans (Entails.of_eq heq) (Entails.trans (sepConj_mono_left h) hnext)

macro "s4_fold_ent " h:term : tactic =>
  `(tactic| refine s4_entails_fold $h (by s4_split_frame) ?_)

macro "s4_rw_ent " h:term : tactic =>
  `(tactic| refine s4_entails_fold (Entails.of_eq $h) (by s4_split_frame) ?_)

end S4FrameTactics

/-! ## Cell and Error Sret Helpers -/

@[simp, arm64_norm, wp_norm]
theorem cond_eq_adds_neg1_1 :
    ConditionHolds CondCode.EQ (addsPState64 0xffffffffffffffff#64 1#64) = true := by
  simp only [ConditionHolds, addsPState64, AddWithCarry64]
  decide

@[simp, arm64_norm, wp_norm]
theorem cond_ne_adds_speWord10_3 :
    ConditionHolds CondCode.NE (addsPState64 (speWord 10) 3#64) = true := by
  simp only [ConditionHolds, addsPState64, AddWithCarry64, speWord]
  decide

theorem cells5_eq_memRegion40 (a : BitVec 64) :
    memRegion a 40 =
      ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64,
        (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗
          ((a + 24#64) ↦₆₄ u3) ∗ ((a + 32#64) ↦₆₄ u4) := by
  rw [memRegion_split a 8 32 (by decide),
    memRegion_split (a + 8#64) 8 24 (by decide),
    memRegion_split (a + 8#64 + 8#64) 8 16 (by decide),
    memRegion_split (a + 8#64 + 8#64 + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  s4_exists_eq

theorem cells6_eq_memRegion48 (a : BitVec 64) :
    memRegion a 48 =
      ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
      ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
        (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗
          ((a + 24#64) ↦₆₄ u3) ∗ ((a + 32#64) ↦₆₄ u4) ∗ ((a + 40#64) ↦₆₄ u5) := by
  rw [memRegion_split a 8 40 (by decide), ProofLib.memRegion_eight, cells5_eq_memRegion40 (a + 8#64)]
  s4_exists_eq

theorem cells6_entails_memRegion48 (a : BitVec 64)
    (v0 v1 v2 v3 v4 v5 : BitVec 64) :
    (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗
      ((a + 24#64) ↦₆₄ v3) ∗ ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ⊢
      memRegion a 48 := by
  rw [cells6_eq_memRegion48 a]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
    (Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5
      (Entails.refl _))))))

theorem speWord10_cells5_entails_initResAt (A : RustAlloc) (a : BitVec 64)
    (v1 v2 v3 v4 v5 : BitVec 64) :
    (a ↦₆₄ speWord 10) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗
      ((a + 24#64) ↦₆₄ v3) ∗ ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ⊢
      initResAt A a (.error (.protocol .invalidKeyAgreement)) := by
  dsimp only [initResAt]
  refine Entails.trans ?_
    (Entails.sepExists_right (.plain 10 (by decide))
      (Entails.refl (speOwnedAt A a (.plain 10 (by decide)))))
  dsimp only [speOwnedAt]
  rw [cells5_eq_memRegion40 (a + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (Entails.refl _)
    (Entails.sepExists_right v1 (Entails.sepExists_right v2
      (Entails.sepExists_right v3 (Entails.sepExists_right v4
        (Entails.sepExists_right v5 (Entails.refl _))))))

/-! ## Error Cleanup Spatial Bundle and Proof (`+4508 → RET`) -/

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas
