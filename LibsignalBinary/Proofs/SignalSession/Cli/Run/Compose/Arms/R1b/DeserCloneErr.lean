/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpk -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupUpper
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpk
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpk -- shake: keep

/-!
# Stage 4a Deserialization Error Cleanup for Arm `R1b` (`0x24fc → 0x2adc`, `0x2654 → 0x2adc`)

Defines the intermediate `opk`/`spk` scratch layout `r1b_opkStage1SpkAt` and proves error cleanup
for `<PublicKey>::deserialize` (`r1b_spk_err_24fc`, `0x24fc → 0x2adc`) and
`kem::Key::deserialize` (`r1b_kem_err_2654`, `0x2654 → 0x2adc`, freeing `spkSigPtr`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton

macro (priority := 2000) "r1b_ac" : tactic =>
  `(tactic| ((try dsimp +zetaDelta only) <;> first | rfl | simp only [emp_sepConj] | with_reducible ac_rfl | ac_rfl))

private meta def r1bStripLetsT : Nat → Lean.Expr → Lean.Expr
  | 0, e => e
  | n + 1, .letE _ _ v b _ => r1bStripLetsT n (b.instantiate1 v)
  | n + 1, .mdata _ e => r1bStripLetsT n e
  | _, e => e

private meta def r1bSplitSepT : Nat → Lean.Expr → Lean.Expr → Array Lean.Expr
  | 0, _, e => #[e]
  | fuel + 1, sepSample, e =>
    let e := r1bStripLetsT 64 e
    let fn := sepSample.getAppFn.constName!
    let ar := sepSample.getAppNumArgs
    if e.isAppOfArity fn ar then
      r1bSplitSepT fuel sepSample (e.getArg! (ar - 2)) ++
        r1bSplitSepT fuel sepSample (e.getArg! (ar - 1))
    else #[e]

private meta def r1bIsDefEqPureT (x a : Lean.Expr) : Lean.Elab.TermElabM Bool := do
  let x := r1bStripLetsT 64 x; let a := r1bStripLetsT 64 a
  let xf := x.getAppFn; let af := a.getAppFn
  if xf.constName? != af.constName? then return false
  let n := x.getAppNumArgs
  if n != a.getAppNumArgs then return false
  let st ← Lean.saveState
  let mut ok ← if xf.constName?.isNone then
      if xf.isFVar != af.isFVar || xf.isProj != af.isProj then pure false
      else Lean.Meta.withReducibleAndInstances <| Lean.Meta.isDefEq xf af
    else pure true
  for i in [0:n] do
    if ok then
      ok ← Lean.Meta.withReducibleAndInstances <| Lean.Meta.isDefEq (x.getArg! i) (a.getArg! i)
  st.restore
  return ok

private meta def r1bComputeRestT (ctxName : String) (p a1 : Lean.Expr) : Lean.Elab.TermElabM Lean.Expr := do
  let sepTy := Lean.mkConst ``SepProp []
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let ps := (r1bSplitSepT 64 sepSample (← Lean.instantiateMVars p)).toList
  let a1s := (r1bSplitSepT 64 sepSample (← Lean.instantiateMVars a1)).toList
  let mut rem := ps
  for a in a1s do
    let mut removed := false
    let mut next : List Lean.Expr := []
    for x in rem do
      if !removed && (← r1bIsDefEqPureT x a) then removed := true
      else next := next.concat x
    if !removed then
      throwError "{ctxName}: unmatched atom:\n  {a}\nin:\n  {rem}"
    rem := next
  let ar := sepSample.getAppNumArgs
  let mkSep (l r : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (ar - 2) ++ #[l, r])
  match rem.reverse with
  | [] => return empExpr
  | last :: rest => return rest.foldl (fun acc x => mkSep x acc) last

elab (priority := 2000) "r1b_entails_frame " t1:term:arg h:term:arg t2:term:arg : term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let entSample ← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none
  let ear := entSample.getAppNumArgs
  let expS := r1bStripLetsT 64 exp
  let p := expS.getArg! (ear - 2)
  let q := expS.getArg! (ear - 1)
  if (← Lean.instantiateMVars p).isMVar then Lean.Elab.Term.tryPostpone
  if (← Lean.instantiateMVars q).isMVar then Lean.Elab.Term.tryPostpone
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLetsT 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2)
  let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRestT "r1b_entails_frame" p a1
  let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let rIsEmp ← r1bIsDefEqPureT r empExpr
  if rIsEmp then
    let eq1 ← Lean.Meta.mkEq p a1
    let eq2 ← Lean.Meta.mkEq a2 q
    let h1Expr ← Lean.Elab.Term.elabTerm t1 (some eq1)
    let h2Expr ← Lean.Elab.Term.elabTerm t2 (some eq2)
    Lean.Meta.mkAppM ``Entails.trans #[← Lean.Meta.mkAppM ``Entails.of_eq #[h1Expr],
      ← Lean.Meta.mkAppM ``Entails.trans #[hExpr, ← Lean.Meta.mkAppM ``Entails.of_eq #[h2Expr]]]
  else
    let eq1 ← Lean.Meta.mkEq p (mkSep a1 r)
    let eq2 ← Lean.Meta.mkEq (mkSep a2 r) q
    let h1Expr ← Lean.Elab.Term.elabTerm t1 (some eq1)
    let h2Expr ← Lean.Elab.Term.elabTerm t2 (some eq2)
    Lean.Meta.mkAppOptM ``r1b_entails_frame_core #[some a1, some a2, some r, some p, some q, h1Expr, hExpr, h2Expr]

elab (priority := 2000) "r1b_sepWPp_frame " t1:term:arg h:term:arg t2:term:arg hk:term:arg : term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let expS := r1bStripLetsT 64 exp
  let args := expS.getAppArgs
  let prog := args[0]!; let ret := args[1]!; let st := args[2]!; let p := args[3]!
  let q := args[4]!; let qp := args[5]!; let oom := args[6]!
  let entSample ← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none
  let ear := entSample.getAppNumArgs
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLetsT 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2)
  let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRestT "r1b_sepWPp_frame" p a1
  let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let rIsEmp ← r1bIsDefEqPureT r empExpr
  if rIsEmp then
    let eq1 ← Lean.Meta.mkEq p a1
    let eq2 ← Lean.Meta.mkEq a2 a2
    let h1Expr ← Lean.Elab.Term.elabTerm t1 (some eq1)
    let h2Expr ← Lean.Elab.Term.elabTerm t2 (some eq2)
    let hkTy := Lean.mkAppN expS.getAppFn #[prog, ret, st, a2, q, qp, oom]
    let hkExpr ← Lean.Elab.Term.elabTerm hk (some hkTy)
    let hent ← Lean.Meta.mkAppM ``Entails.trans #[← Lean.Meta.mkAppM ``Entails.of_eq #[h1Expr],
      ← Lean.Meta.mkAppM ``Entails.trans #[hExpr, ← Lean.Meta.mkAppM ``Entails.of_eq #[h2Expr]]]
    Lean.Meta.mkAppM ``MainHops.sepWPp_weaken_pre #[hent, hkExpr]
  else
    let a2IsEmp ← r1bIsDefEqPureT a2 empExpr
    let p' := if a2IsEmp then r else mkSep a2 r
    let eq1 ← Lean.Meta.mkEq p (mkSep a1 r)
    let eq2 ← Lean.Meta.mkEq (mkSep a2 r) p'
    let h1Expr ← Lean.Elab.Term.elabTerm t1 (some eq1)
    let h2Expr ← Lean.Elab.Term.elabTerm t2 (some eq2)
    let hkTy := Lean.mkAppN expS.getAppFn #[prog, ret, st, p', q, qp, oom]
    let hkExpr ← Lean.Elab.Term.elabTerm hk (some hkTy)
    Lean.Meta.mkAppOptM ``r1b_sepWPp_frame_core
      #[some prog, some ret, some st, some a1, some a2, some r, some p, some p',
        some q, some qp, some oom, h1Expr, hExpr, h2Expr, hkExpr]

elab:10 (priority := 2000) "r1b_call_frame" "<|" h:term:10 : term <= expectedType => do
    let exp ← Lean.instantiateMVars expectedType
    if exp.isMVar then Lean.Elab.Term.tryPostpone
    let expS := r1bStripLetsT 64 exp
    let hExpr ← Lean.Elab.Term.elabTerm h none
    let hTy0 := r1bStripLetsT 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
    for idx in [0, 1, 2, 4, 5, 6] do
      if !(← Lean.Meta.withReducibleAndInstances <| Lean.Meta.isDefEq (hTy0.getArg! idx) (expS.getArg! idx)) then
        discard <| Lean.Meta.isDefEq (hTy0.getArg! idx) (expS.getArg! idx)
    let p ← Lean.instantiateMVars (expS.getArg! 3)
    let p' ← Lean.instantiateMVars ((r1bStripLetsT 64 (← Lean.instantiateMVars hTy0)).getArg! 3)
    let sepTy := Lean.mkConst ``SepProp []
    let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
    let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
    let sar := sepSample.getAppNumArgs
    let mkSep (x y : Lean.Expr) : Lean.Expr :=
      sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
    let ps := (r1bSplitSepT 64 sepSample p).toList
    let p's := (r1bSplitSepT 64 sepSample p').toList
    let mut mvarFOpt : Option Lean.Expr := none
    let mut a1s : List Lean.Expr := []
    for a in p's do
      let ai ← Lean.instantiateMVars a
      if mvarFOpt.isNone && ai.isMVar then mvarFOpt := some ai
      else a1s := a1s.concat ai
    let mut rem := ps
    for a in a1s do
      let mut removed := false
      let mut next : List Lean.Expr := []
      for x in rem do
        if !removed && (← r1bIsDefEqPureT x a) then removed := true
        else next := next.concat x
      if !removed then
        throwError "r1b_call_frame: unmatched callee atom:\n  {a}\nin:\n  {rem}"
      rem := next
    let remProd := match rem.reverse with
      | [] => empExpr
      | last :: rest => rest.foldl (fun acc x => mkSep x acc) last
    if let some mf := mvarFOpt then
      discard <| Lean.Meta.withReducibleAndInstances <| Lean.Meta.isDefEq mf remProd
    let eqTy ← Lean.Meta.mkEq (← Lean.instantiateMVars p) (← Lean.instantiateMVars p')
    let eqProof ← Lean.Elab.Term.elabTerm (← `(by r1b_ac)) (some eqTy)
    let ent ← Lean.Meta.mkAppM ``Entails.of_eq #[eqProof]
    Lean.Meta.mkAppM ``MainHops.sepWPp_weaken_pre #[ent, hExpr]

/-- Stage-1 `opk` and spilled `spk` scratch layout across `0x2550 .. 0x25f4` (`[0x0f0..0x110)` populated with `spkW8.zeroExtend 64`, `spkW24`, `spkW16`, `spkW0`). -/
@[expose] def r1b_opkStage1SpkAt (fsp : BitVec 64)
    (spkW0 : BitVec 64) (spkW8 : BitVec 32) (spkW16 spkW24 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (w0e0 w0e4 w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64) (b31 : BitVec 8) :
    SepProp :=
  memRegion fsp 0x0e0 ∗
    ((fsp + 0x0e0#64) ↦₃₂ w0e0) ∗
    ((fsp + 0x0e4#64) ↦₃₂ w0e4) ∗
    ((fsp + 0x0e8#64) ↦₆₄ w15) ∗
    ((fsp + 0x0f0#64) ↦₆₄ spkW8.zeroExtend 64) ∗
    ((fsp + 0x0f8#64) ↦₆₄ spkW24) ∗
    ((fsp + 0x100#64) ↦₆₄ spkW16) ∗
    ((fsp + 0x108#64) ↦₆₄ spkW0) ∗
    memRegion (fsp + 0x1d0#64) 0x50 ∗
    ((fsp + 0x220#64) ↦₆₄ w23) ∗
    ((fsp + 0x228#64) ↦₈ b31) ∗
    memRegion (fsp + 0x229#64) 0x37 ∗
    memRegion (fsp + 0x2c0#64) 0xf8 ∗
    Wire.sevenBytesHeadAt (fsp + 0x3b8#64) b0 b1 b2 b3 b4 b5 b6 ∗
    memRegion (fsp + 0x3bf#64) 0x19 ∗
    ((fsp + 0x3d8#64) ↦₃₂ w9) ∗
    ((fsp + 0x3dc#64) ↦₁₆ w13) ∗
    memRegion (fsp + 0x3de#64) 0xf2

theorem r1b_opkStage1Spk_to_regions (fsp : BitVec 64)
    (spkW0 : BitVec 64) (spkW8 : BitVec 32) (spkW16 spkW24 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (w0e0 w0e4 w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64) (b31 : BitVec 8) :
    r1b_opkStage1SpkAt fsp spkW0 spkW8 spkW16 spkW24
      b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31 ⊢
      memRegion fsp 0x110 ∗
        memRegion (fsp + 0x1d0#64) 0x90 ∗
        memRegion (fsp + 0x2c0#64) 0x210 := by
  have h0f0 :
      ((fsp + 0x0f0#64) ↦₆₄ spkW8.zeroExtend 64) ∗
        ((fsp + 0x0f8#64) ↦₆₄ spkW24) ∗
        ((fsp + 0x100#64) ↦₆₄ spkW16) ∗
        ((fsp + 0x108#64) ↦₆₄ spkW0) ⊢ memRegion (fsp + 0x0f0#64) 0x20 := by
    refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (pointsTo64_entails_memRegion _ _)))) ?_
    rw [r1b_join_region fsp 0x100 8 8, r1b_join_region fsp 0x0f8 8 16,
      r1b_join_region fsp 0x0f0 8 24]
    exact Entails.refl _
  refine Entails.trans ?_
    (r1b_opkStage1_to_regions fsp b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31)
  dsimp only [r1b_opkStage1SpkAt, r1b_opkStage1At]
  exact r1b_entails_frame (by ac_rfl) h0f0 (by ac_rfl)

theorem r1b_sig64_to_ownedBytes (A : RustAlloc) (ptr : BitVec 64)
    (sig : List (BitVec 8)) (hne : ptr ≠ 0) (hlen : sig.length = 64) :
    (A.live ptr 64 1 ∗ (ptr ↦ₛ sig)) ⊢ ownedBytes A 64#64 ptr 64#64 sig := by
  have h64 : BitVec.ofNat 64 sig.length = 64#64 := by rw [hlen]
  conv => rhs; rw [show ownedBytes A 64#64 ptr 64#64 sig = ownedBytes A 64#64 ptr (BitVec.ofNat 64 sig.length) sig by rw [h64]]
  refine Entails.trans ?_
    (r1b_ownedBytes_rejoin A 64#64 ptr sig (by simp [hlen]) (by decide) hne)
  dsimp only [r1b_ownedRest]
  have hc : (64#64 : BitVec 64) ≠ 0 := by decide
  have hsub : (64#64 : BitVec 64).toNat - sig.length = 0 := by simp [hlen]
  simp only [hc, ↓reduceIte, hsub, memRegion_zero, sepConj_emp]
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SignalSession.Cli.RunCompose
