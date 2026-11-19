/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.WorkFrame -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.Common
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupSpkReg
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.RoFrame
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.SliceHelpers -- proof-setup: allow-public-import

/-!
# Stage 1 (`registration-id` and `signed-pre-key`) Helpers of Arm `R1b` (`R+0x074c → R+0x1260`)
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
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton

theorem r1b_errCommon_fold (A : RustAlloc) (g : RunCall) (d : Init1Data)
    (s0 : State) (resStack : Nat) :
    r1b_errCore A g d s0 ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool ∗ anyHeap =
      r1b_errCommon A g d s0 resStack := rfl

theorem r1b_live_bytes_to_ownedBytes (A : RustAlloc) {buf : BitVec 64} {bs : List (BitVec 8)}
    (hbuf : buf ≠ 0#64) (hpos : 0 < bs.length) (hlen : bs.length < 2 ^ 63) :
    A.live buf bs.length 1 ∗ (buf ↦ₛ bs) ⊢
      ownedBytes A (BitVec.ofNat 64 bs.length) buf (BitVec.ofNat 64 bs.length) bs := by
  rw [r1b_ownedBytes_borrow]
  have hcap_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have hne0 : BitVec.ofNat 64 bs.length ≠ 0#64 := by
    intro h0; have := congrArg BitVec.toNat h0; simp only [hcap_nat, BitVec.toNat_ofNat] at this; omega
  refine Entails.pure_right ⟨rfl, by omega, by omega, hbuf⟩ ?_
  dsimp only [r1b_ownedRest]
  simp only [show (0 : BitVec 64) = 0#64 from rfl, hne0, ↓reduceIte, hcap_nat, Nat.sub_self,
    memRegion_zero, sepConj_emp]
  exact Entails.of_eq (by ac_rfl)

theorem r1b_sepWPp_pure_left {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hk : φ → SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s (⌜φ⌝ ∗ P) Q Qp oom := SepWPp.pure_elim hk

theorem r1b_sepWPp_borrow_core (A : RustAlloc) {prog : Program} {ret : BitVec 64} {s : State}
    {cap ptr len : BitVec 64} {bs : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hk : (len = BitVec.ofNat 64 bs.length ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) →
      SepWPp prog ret s ((ptr ↦ₛ bs) ∗ r1b_ownedRest A cap ptr bs.length ∗ F) Q Qp oom) :
    SepWPp prog ret s (ownedBytes A cap ptr len bs ∗ F) Q Qp oom := by
  rw [r1b_ownedBytes_borrow A cap ptr len bs]
  simp only [sepConj_assoc]
  exact SepWPp.pure_elim hk

macro "r1b_prove_spe_str" : tactic =>
  `(tactic| (refine r1b_SpePayload_str _ ?_; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_bits))

macro "r1b_ac" : tactic =>
  `(tactic| first | rfl | simp only [emp_sepConj] | ac_rfl | ((try dsimp +zetaDelta only); first | rfl | simp only [emp_sepConj] | ac_rfl))

private meta def r1bStripLets2 : Nat → Lean.Expr → Lean.Expr
  | 0, e => e
  | n + 1, .letE _ _ v b _ => r1bStripLets2 n (b.instantiate1 v)
  | n + 1, .mdata _ e => r1bStripLets2 n e
  | _, e => e

private meta def r1bSplitSep2 : Nat → Lean.Expr → Lean.Expr → Array Lean.Expr
  | 0, _, e => #[e]
  | fuel + 1, sepSample, e =>
    let e := r1bStripLets2 64 e
    let fn := sepSample.getAppFn.constName!
    let ar := sepSample.getAppNumArgs
    if e.isAppOfArity fn ar then
      r1bSplitSep2 fuel sepSample (e.getArg! (ar - 2)) ++
        r1bSplitSep2 fuel sepSample (e.getArg! (ar - 1))
    else #[e]

private meta def r1bIsDefEqPure2 (x a : Lean.Expr) : Lean.Elab.TermElabM Bool := do
  let x := r1bStripLets2 64 x; let a := r1bStripLets2 64 a
  if x.getAppFn.constName? != a.getAppFn.constName? then return false
  let n := x.getAppNumArgs
  if n != a.getAppNumArgs then return false
  let st ← Lean.saveState
  let mut ok := true
  for i in [0:n] do
    if ok then ok ← Lean.Meta.isDefEq (x.getArg! i) (a.getArg! i)
  st.restore
  return ok

elab:10 "r1b_call_frame" "<|" h:term:10 : term <= expectedType => do
    let exp ← Lean.instantiateMVars expectedType
    if exp.isMVar then Lean.Elab.Term.tryPostpone
    let expS := r1bStripLets2 64 exp
    let hExpr ← Lean.Elab.Term.elabTerm h none
    let hTy0 := r1bStripLets2 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
    for idx in [0, 1, 2, 4, 5, 6] do
      discard <| Lean.Meta.isDefEq (hTy0.getArg! idx) (expS.getArg! idx)
    let p ← Lean.instantiateMVars (expS.getArg! 3)
    let p' ← Lean.instantiateMVars ((r1bStripLets2 64 (← Lean.instantiateMVars hTy0)).getArg! 3)
    let sepTy := Lean.mkConst ``SepProp []
    let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
    let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
    let sar := sepSample.getAppNumArgs
    let mkSep (x y : Lean.Expr) : Lean.Expr :=
      sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
    let ps := (r1bSplitSep2 64 sepSample p).toList
    let p's := (r1bSplitSep2 64 sepSample p').toList
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
        if !removed && (← r1bIsDefEqPure2 x a) then removed := true
        else next := next.concat x
      rem := next
    let remProd := match rem.reverse with
      | [] => empExpr
      | last :: rest => rest.foldl (fun acc x => mkSep x acc) last
    if let some mf := mvarFOpt then
      discard <| Lean.Meta.isDefEq mf remProd
    let eqTy ← Lean.Meta.mkEq (← Lean.instantiateMVars p) (← Lean.instantiateMVars p')
    let eqProof ← Lean.Elab.Term.elabTerm (← `(by r1b_ac)) (some eqTy)
    let ent ← Lean.Meta.mkAppM ``Entails.of_eq #[eqProof]
    Lean.Meta.mkAppM ``MainHops.sepWPp_weaken_pre #[ent, hExpr]

end CryptoVerification.SignalSession.Cli.RunCompose
