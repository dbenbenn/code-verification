/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDeser -- proof-setup: allow-public-import
import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanup -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.SliceHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpers
import LibsignalBinary.Specifications.AsmConstants

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

/-! ## Universal Framing and `.rodata` Cross-Reference Helpers -/

theorem r1b_entails_frame_core {A1 A2 R P Q : SepProp}
    (h1 : P = A1 ∗ R) (h : A1 ⊢ A2) (h2 : A2 ∗ R = Q) :
    P ⊢ Q := by
  rw [h1, ← h2]
  exact sepConj_mono_left h

theorem r1b_sepWPp_frame_core {prog : Program} {ret : BitVec 64} {s : State}
    {A1 A2 R P P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h1 : P = A1 ∗ R) (h : A1 ⊢ A2) (h2 : A2 ∗ R = P')
    (hk : SepWPp prog ret s P' Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  MainHops.sepWPp_weaken_pre (r1b_entails_frame_core h1 h h2) hk

private meta def r1bStripLets : Nat → Lean.Expr → Lean.Expr
  | 0, e => e
  | n + 1, .letE _ _ v b _ => r1bStripLets n (b.instantiate1 v)
  | n + 1, .mdata _ e => r1bStripLets n e
  | _, e => e

private meta def r1bSplitSep : Nat → Lean.Expr → Lean.Expr → Array Lean.Expr
  | 0, _, e => #[e]
  | fuel + 1, sepSample, e =>
    let e := r1bStripLets 64 e
    let fn := sepSample.getAppFn.constName!
    let ar := sepSample.getAppNumArgs
    if e.isAppOfArity fn ar then
      r1bSplitSep fuel sepSample (e.getArg! (ar - 2)) ++
        r1bSplitSep fuel sepSample (e.getArg! (ar - 1))
    else
      #[e]

private meta def r1bIsDefEqPure (x a : Lean.Expr) : Lean.Elab.TermElabM Bool := do
  let x := r1bStripLets 64 x
  let a := r1bStripLets 64 a
  if x.getAppFn.constName? != a.getAppFn.constName? then
    return false
  let n := x.getAppNumArgs
  if n != a.getAppNumArgs then
    return false
  let st ← Lean.saveState
  let mut ok := true
  for i in [0:n] do
    if ok then
      ok ← Lean.Meta.isDefEq (x.getArg! i) (a.getArg! i)
  st.restore
  return ok

private meta def r1bComputeRest (p a1 : Lean.Expr) : Lean.Elab.TermElabM Lean.Expr := do
  let sepTy := Lean.mkConst ``SepProp []
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let ps := (r1bSplitSep 64 sepSample (← Lean.instantiateMVars p)).toList
  let a1s := (r1bSplitSep 64 sepSample (← Lean.instantiateMVars a1)).toList
  let mut rem := ps
  for a in a1s do
    let mut removed := false
    let mut next : List Lean.Expr := []
    for x in rem do
      if !removed && (← r1bIsDefEqPure x a) then
        removed := true
      else
        next := next.concat x
    rem := next
  let ar := sepSample.getAppNumArgs
  let mkSep (l r : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (ar - 2) ++ #[l, r])
  match rem.reverse with
  | [] => return empExpr
  | last :: rest => return rest.foldl (fun acc x => mkSep x acc) last

elab "r1b_entails_frame " t1:term:arg h:term:arg t2:term:arg : term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let entSample ← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none
  let ear := entSample.getAppNumArgs
  let expS := r1bStripLets 64 exp
  let p := expS.getArg! (ear - 2)
  let q := expS.getArg! (ear - 1)
  if (← Lean.instantiateMVars p).isMVar then Lean.Elab.Term.tryPostpone
  if (← Lean.instantiateMVars q).isMVar then Lean.Elab.Term.tryPostpone
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLets 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2)
  let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRest p a1
  let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let rIsEmp ← r1bIsDefEqPure r empExpr
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

elab "r1b_sepWPp_frame " t1:term:arg h:term:arg t2:term:arg hk:term:arg : term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let expS := r1bStripLets 64 exp
  let args := expS.getAppArgs
  let prog := args[0]!; let ret := args[1]!; let st := args[2]!; let p := args[3]!
  let q := args[4]!; let qp := args[5]!; let oom := args[6]!
  let entSample ← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none
  let ear := entSample.getAppNumArgs
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLets 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2)
  let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRest p a1
  let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let rIsEmp ← r1bIsDefEqPure r empExpr
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
    let a2IsEmp ← r1bIsDefEqPure a2 empExpr
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

theorem r1b_ownedBytes_facts (A : RustAlloc) (cap ptr len : BitVec 64) (bs : List (BitVec 8)) :
    ownedBytes A cap ptr len bs ⊢
      ⌜len = BitVec.ofNat 64 bs.length ∧ cap.toNat < 2 ^ 63 ∧ bs.length < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ownedBytes A cap ptr len bs := by
  conv_lhs => rw [r1b_ownedBytes_borrow A cap ptr len bs]
  apply Entails.pure_left
  rintro ⟨rfl, hle, hlt, hne⟩
  have hbs63 : bs.length < 2 ^ 63 := Nat.lt_of_le_of_lt hle hlt
  refine Entails.pure_right ⟨rfl, hlt, hbs63, hne⟩ ?_
  exact r1b_ownedBytes_rejoin A cap ptr bs hle hlt hne

theorem r1b_cmn1_false_of_lt63 {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    cap + 1#64 ≠ 0#64 := by
  intro heq
  have hmax : cap = 0xffffffffffffffff#64 := by bv_omega
  subst hmax
  simp at h

theorem r1b_exists_4bytes {bs : List (BitVec 8)} (h : bs.length = 4) :
    ∃ b0 b1 b2 b3, bs = [b0, b1, b2, b3] := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | _⟩⟩⟩⟩ <;> simp at h
  exact ⟨b0, b1, b2, b3, rfl⟩

theorem r1b_owned_of_live_region (A : RustAlloc) (n : Nat) (buf : BitVec 64)
    (hn0 : BitVec.ofNat 64 n ≠ 0#64)
    (hn_toNat : (BitVec.ofNat 64 n).toNat = n)
    (hn63 : n < 2 ^ 63)
    (hbuf : buf ≠ 0#64) :
    (A.live buf n 1 ∗ memRegion buf n) ⊢
      ∃∗ eBs : List (BitVec 8),
        ⌜eBs.length = n⌝ ∗
          ownedBytes A (BitVec.ofNat 64 n) buf (BitVec.ofNat 64 n) eBs := by
  rw [memRegion_eq_exists_bytes buf n (by omega), sepExists_sepConj_right]
  apply Entails.sepExists_elim
  intro bs
  rw [show (A.live buf n 1 ∗ (⌜bs.length = n⌝ ∗ (buf ↦ₛ bs))) =
    (⌜bs.length = n⌝ ∗ ((buf ↦ₛ bs) ∗ A.live buf n 1)) by ac_rfl]
  apply Entails.pure_left
  intro hlen
  refine Entails.sepExists_right bs (Entails.pure_right hlen ?_)
  have hn0' : BitVec.ofNat 64 n ≠ 0 := hn0
  have hrest : A.live buf n 1 = r1b_ownedRest A (BitVec.ofNat 64 n) buf bs.length := by
    simp only [r1b_ownedRest, hn0', ↓reduceIte, hn_toNat, hlen, Nat.sub_self,
      memRegion_zero, sepConj_emp]
  rw [hrest, ← hlen]
  exact r1b_ownedBytes_rejoin A (BitVec.ofNat 64 bs.length) buf bs
    (by rw [hlen, hn_toNat]) (by rwa [hlen, hn_toNat]) hbuf

theorem r1b_buf22_split1 (buf : BitVec 64) :
    memRegion buf 22 =
      (∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64,
        (buf ↦₆₄ d0) ∗ ((buf + 8#64) ↦₆₄ d1) ∗ memRegion (buf + 16#64) 6) := by
  rw [show (22 : Nat) = 8 + 14 from rfl,
    ProofLib.memRegion_split buf 8 14 (by decide),
    show (14 : Nat) = 8 + 6 from rfl,
    ProofLib.memRegion_split (buf + 8#64) 8 6 (by decide),
    show buf + 8#64 + 8#64 = buf + 16#64 from by bv_omega,
    ProofLib.memRegion_eight buf, sepExists_sepConj_left]
  simp only [ProofLib.memRegion_eight, sepExists_sepConj_left, sepExists_sepConj_right]

theorem r1b_buf22_realign (buf d0 d1 : BitVec 64) :
    ((buf ↦₆₄ d0) ∗ ((buf + 8#64) ↦₆₄ d1) ∗ memRegion (buf + 16#64) 6) ⊢
      ∃∗ d2 : BitVec 64, memRegion buf 14 ∗ ((buf + 14#64) ↦₆₄ d2) := by
  have h1 : ((buf + 8#64) ↦₆₄ d1) ∗ memRegion (buf + 16#64) 6 ⊢ memRegion (buf + 8#64) 14 := by
    rw [show buf + 16#64 = (buf + 8#64) + 8#64 from by bv_omega]
    exact r1b_cell64_cons _ (by decide)
  have h2 : (buf ↦₆₄ d0) ∗ memRegion (buf + 8#64) 14 ⊢ memRegion buf 22 :=
    r1b_cell64_cons _ (by decide)
  refine Entails.trans (Entails.of_eq (by ac_rfl))
    (Entails.trans (Entails.trans (sepConj_mono_right h1) h2) ?_)
  rw [show (22 : Nat) = 14 + 8 from rfl,
    ProofLib.memRegion_split buf 14 8 (by decide),
    ProofLib.memRegion_eight (buf + 14#64), sepExists_sepConj_right]
  exact Entails.refl _

theorem r1b_buf22_owned (A : RustAlloc) (buf d2 : BitVec 64) (hbuf : buf ≠ 0#64) :
    (A.live buf 22 1 ∗ memRegion buf 14 ∗ ((buf + 14#64) ↦₆₄ d2)) ⊢
      ∃∗ eBs : List (BitVec 8), ⌜eBs.length = 22⌝ ∗ ownedBytes A 22#64 buf 22#64 eBs := by
  have hm : memRegion buf 14 ∗ ((buf + 14#64) ↦₆₄ d2) ⊢ memRegion buf 22 := by
    refine Entails.trans (sepConj_mono_right (pointsTo64_entails_memRegion (buf + 14#64) d2)) ?_
    exact Entails.of_eq (ProofLib.memRegion_split buf 14 8 (by decide)).symm
  exact Entails.trans (sepConj_mono_right hm)
    (r1b_owned_of_live_region A 22 buf (by decide) rfl (by decide) hbuf)

theorem r1b_buf14_split1 (buf : BitVec 64) :
    memRegion buf 14 =
      (∃∗ d0 : BitVec 64, (buf ↦₆₄ d0) ∗ memRegion (buf + 8#64) 6) := by
  rw [show (14 : Nat) = 8 + 6 from rfl,
    ProofLib.memRegion_split buf 8 6 (by decide),
    ProofLib.memRegion_eight buf, sepExists_sepConj_left]

theorem r1b_buf14_realign (buf d0 : BitVec 64) :
    ((buf ↦₆₄ d0) ∗ memRegion (buf + 8#64) 6) ⊢
      ∃∗ d1 : BitVec 64, memRegion buf 6 ∗ ((buf + 6#64) ↦₆₄ d1) := by
  have h1 : (buf ↦₆₄ d0) ∗ memRegion (buf + 8#64) 6 ⊢ memRegion buf 14 :=
    r1b_cell64_cons _ (by decide)
  refine Entails.trans h1 ?_
  rw [show (14 : Nat) = 6 + 8 from rfl,
    ProofLib.memRegion_split buf 6 8 (by decide),
    ProofLib.memRegion_eight (buf + 6#64), sepExists_sepConj_right]
  exact Entails.refl _

theorem r1b_buf14_owned (A : RustAlloc) (buf d1 : BitVec 64) (hbuf : buf ≠ 0#64) :
    (A.live buf 14 1 ∗ memRegion buf 6 ∗ ((buf + 6#64) ↦₆₄ d1)) ⊢
      ∃∗ eBs : List (BitVec 8), ⌜eBs.length = 14⌝ ∗ ownedBytes A 14#64 buf 14#64 eBs := by
  have hm : memRegion buf 6 ∗ ((buf + 6#64) ↦₆₄ d1) ⊢ memRegion buf 14 := by
    refine Entails.trans (sepConj_mono_right (pointsTo64_entails_memRegion (buf + 6#64) d1)) ?_
    exact Entails.of_eq (ProofLib.memRegion_split buf 6 8 (by decide)).symm
  exact Entails.trans (sepConj_mono_right hm)
    (r1b_owned_of_live_region A 14 buf (by decide) rfl (by decide) hbuf)

/-! ## `PublicKey` (`spk` and `opk`), `addrUpperAt`, and `boxU8At` Helpers -/

theorem r1b_head7_init (d : BitVec 64) :
    memRegion d 7 =
      ∃∗ v0 : BitVec 32, ∃∗ d4 : BitVec 8, ∃∗ d5 : BitVec 8, ∃∗ d6 : BitVec 8,
        (d ↦₃₂ v0) ∗ ((d + 4#64) ↦₈ d4) ∗ ((d + 5#64) ↦₈ d5) ∗ ((d + 6#64) ↦₈ d6) := by
  rw [show (7 : Nat) = 4 + 3 from rfl, ProofLib.memRegion_split d 4 3 (by decide),
    show (3 : Nat) = 1 + 2 from rfl, ProofLib.memRegion_split (d + 4#64) 1 2 (by decide),
    show (2 : Nat) = 1 + 1 from rfl, ProofLib.memRegion_split ((d + 4#64) + 1#64) 1 1 (by decide),
    show (d + 4#64) + 1#64 + 1#64 = d + 6#64 from by bv_omega,
    show (d + 4#64) + 1#64 = d + 5#64 from by bv_omega,
    ProofLib.memRegion_four d, sepExists_sepConj_left]
  conv_lhs =>
    arg 1; ext v0
    rw [ProofLib.memRegion_one (d + 4#64), sepExists_sepConj_left, sepExists_sepConj_right]
    arg 1; ext d4
    rw [ProofLib.memRegion_one (d + 5#64), sepExists_sepConj_left,
      sepExists_sepConj_right, sepExists_sepConj_right]
    arg 1; ext d5
    rw [ProofLib.memRegion_one (d + 6#64), sepExists_sepConj_right, sepExists_sepConj_right,
      sepExists_sepConj_right]

theorem r1b_tail7_init (d : BitVec 64) :
    memRegion d 7 =
      ∃∗ d0 : BitVec 8, ∃∗ d1 : BitVec 8, ∃∗ d2 : BitVec 8, ∃∗ v3 : BitVec 32,
        (d ↦₈ d0) ∗ ((d + 1#64) ↦₈ d1) ∗ ((d + 2#64) ↦₈ d2) ∗ ((d + 3#64) ↦₃₂ v3) := by
  rw [show (7 : Nat) = 1 + 6 from rfl, ProofLib.memRegion_split d 1 6 (by decide),
    show (6 : Nat) = 1 + 5 from rfl, ProofLib.memRegion_split (d + 1#64) 1 5 (by decide),
    show (5 : Nat) = 1 + 4 from rfl, ProofLib.memRegion_split ((d + 1#64) + 1#64) 1 4 (by decide),
    show (d + 1#64) + 1#64 + 1#64 = d + 3#64 from by bv_omega,
    show (d + 1#64) + 1#64 = d + 2#64 from by bv_omega,
    ProofLib.memRegion_one d, sepExists_sepConj_left]
  conv_lhs =>
    arg 1; ext d0
    rw [ProofLib.memRegion_one (d + 1#64), sepExists_sepConj_left, sepExists_sepConj_right]
    arg 1; ext d1
    rw [ProofLib.memRegion_one (d + 2#64), sepExists_sepConj_left,
      sepExists_sepConj_right, sepExists_sepConj_right]
    arg 1; ext d2
    rw [ProofLib.memRegion_four (d + 3#64), sepExists_sepConj_right, sepExists_sepConj_right,
      sepExists_sepConj_right]

theorem r1b_head7_to_region (d : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) :
    Wire.sevenBytesHeadAt d b0 b1 b2 b3 b4 b5 b6 ⊢ memRegion d 7 := by
  dsimp only [Wire.sevenBytesHeadAt]
  rw [r1b_head7_init d]
  exact Entails.sepExists_right _ (Entails.sepExists_right _
    (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.refl _))))

@[expose] def r1b_spkLayoutAt (a : BitVec 64)
    (w0 : BitVec 64) (w8 w12 : BitVec 32) (w16 w24 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₃₂ w8) ∗ ((a + 12#64) ↦₃₂ w12) ∗
    ((a + 16#64) ↦₆₄ w16) ∗ ((a + 24#64) ↦₆₄ w24)

@[expose] def r1b_spkBytesOf (w0 : BitVec 64) (w8 w12 : BitVec 32) (w16 w24 : BitVec 64) :
    List (BitVec 8) :=
  unpack64 w0 ++ unpack32 w8 ++ unpack32 w12 ++ unpack64 w16 ++ unpack64 w24

theorem r1b_spkLayoutAt_eq (a : BitVec 64)
    (w0 : BitVec 64) (w8 w12 : BitVec 32) (w16 w24 : BitVec 64) :
    r1b_spkLayoutAt a w0 w8 w12 w16 w24 = (a ↦ₛ r1b_spkBytesOf w0 w8 w12 w16 w24) := by
  dsimp only [r1b_spkLayoutAt, r1b_spkBytesOf]
  rw [pointsTo64_eq_pointsToBytes, pointsTo32_eq_pointsToBytes, pointsTo32_eq_pointsToBytes,
    pointsTo64_eq_pointsToBytes, pointsTo64_eq_pointsToBytes]
  simp only [unpack64, unpack32, List.cons_append, List.nil_append,
    pointsToBytes_cons, pointsToBytes_nil, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
  ac_rfl

theorem r1b_exists_spkBytesOf (bs : List (BitVec 8)) (h : bs.length = 32) :
    ∃ w0 w8 w12 w16 w24, bs = r1b_spkBytesOf w0 w8 w12 w16 w24 := by
  have h0 : (bs.take 8).length = 8 := by simp [h]
  have h8 : ((bs.drop 8).take 4).length = 4 := by simp [h]
  have h12 : ((bs.drop 12).take 4).length = 4 := by simp [h]
  have h16 : ((bs.drop 16).take 8).length = 8 := by simp [h]
  have h24 : (bs.drop 24).length = 8 := by simp [h]
  rcases Wire.exists_eight_bytes _ h0 with ⟨b0, b1, b2, b3, b4, b5, b6, b7, hb0⟩
  rcases r1b_exists_4bytes h8 with ⟨b8, b9, b10, b11, hb8⟩
  rcases r1b_exists_4bytes h12 with ⟨b12, b13, b14, b15, hb12⟩
  rcases Wire.exists_eight_bytes _ h16 with ⟨b16, b17, b18, b19, b20, b21, b22, b23, hb16⟩
  rcases Wire.exists_eight_bytes _ h24 with ⟨b24, b25, b26, b27, b28, b29, b30, b31, hb24⟩
  refine ⟨b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0,
    b11 ++ b10 ++ b9 ++ b8,
    b15 ++ b14 ++ b13 ++ b12,
    b23 ++ b22 ++ b21 ++ b20 ++ b19 ++ b18 ++ b17 ++ b16,
    b31 ++ b30 ++ b29 ++ b28 ++ b27 ++ b26 ++ b25 ++ b24, ?_⟩
  have hcat : bs = bs.take 8 ++ ((bs.drop 8).take 4 ++
      ((bs.drop 12).take 4 ++ ((bs.drop 16).take 8 ++ bs.drop 24))) := by
    have s16 : bs.drop 16 = (bs.drop 16).take 8 ++ bs.drop 24 := by
      simpa [Nat.add_comm] using (List.take_append_drop 8 (bs.drop 16)).symm
    have s12 : bs.drop 12 = (bs.drop 12).take 4 ++ bs.drop 16 := by
      simpa [Nat.add_comm] using (List.take_append_drop 4 (bs.drop 12)).symm
    have s8 : bs.drop 8 = (bs.drop 8).take 4 ++ bs.drop 12 := by
      simpa [Nat.add_comm] using (List.take_append_drop 4 (bs.drop 8)).symm
    have s0 : bs = bs.take 8 ++ bs.drop 8 := (List.take_append_drop 8 bs).symm
    exact s0.trans (congrArg (bs.take 8 ++ ·)
      (s8.trans (congrArg ((bs.drop 8).take 4 ++ ·)
        (s12.trans (congrArg ((bs.drop 12).take 4 ++ ·) s16)))))
  rw [hcat, hb0, hb8, hb12, hb16, hb24]
  dsimp only [r1b_spkBytesOf]
  rw [Wire.unpack64_append8, Wire.unpack32_append4, Wire.unpack32_append4,
    Wire.unpack64_append8, Wire.unpack64_append8]
  simp only [List.append_assoc]

theorem r1b_zext32_pack64 (a : BitVec 64) (wlo whi : BitVec 64) :
    let w64 := (whi <<< 32) ||| (wlo &&& 0xffffffff#64)
    ((a ↦₃₂ wlo.truncate 32) ∗ ((a + 4#64) ↦₃₂ whi.truncate 32)) =
      (a ↦₆₄ w64) := by
  intro w64
  rw [pointsTo32_eq_pointsToBytes, pointsTo32_eq_pointsToBytes, pointsTo64_eq_pointsToBytes]
  have hlen : (unpack32 (wlo.truncate 32)).length = 4 := rfl
  rw [← hlen, ← pointsToBytes_append]
  congr 1
  unfold unpack32 unpack64
  have h0 : w64.extractLsb' 0 8 = (wlo.truncate 32).extractLsb' 0 8 := by dsimp [w64]; bv_bits
  have h1 : w64.extractLsb' 8 8 = (wlo.truncate 32).extractLsb' 8 8 := by dsimp [w64]; bv_bits
  have h2 : w64.extractLsb' 16 8 = (wlo.truncate 32).extractLsb' 16 8 := by dsimp [w64]; bv_bits
  have h3 : w64.extractLsb' 24 8 = (wlo.truncate 32).extractLsb' 24 8 := by dsimp [w64]; bv_bits
  have h4 : w64.extractLsb' 32 8 = (whi.truncate 32).extractLsb' 0 8 := by dsimp [w64]; bv_bits
  have h5 : w64.extractLsb' 40 8 = (whi.truncate 32).extractLsb' 8 8 := by dsimp [w64]; bv_bits
  have h6 : w64.extractLsb' 48 8 = (whi.truncate 32).extractLsb' 16 8 := by dsimp [w64]; bv_bits
  have h7 : w64.extractLsb' 56 8 = (whi.truncate 32).extractLsb' 24 8 := by dsimp [w64]; bv_bits
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  rfl

theorem r1b_spk_pack_words (a : BitVec 64)
    (w0 : BitVec 64) (w8 w12 : BitVec 32) (w16 w24 : BitVec 64) :
    ((a ↦₆₄ w0) ∗
      ((a + 8#64) ↦₆₄ (((w12.zeroExtend 64) <<< 32) ||| (w8.zeroExtend 64))) ∗
      ((a + 16#64) ↦₆₄ w16) ∗
      ((a + 24#64) ↦₆₄ w24)) =
      (a ↦ₛ r1b_spkBytesOf w0 w8 w12 w16 w24) := by
  have hz : (((w12.zeroExtend 64) <<< 32) ||| ((w8.zeroExtend 64) &&& 0xffffffff#64)) =
      (((w12.zeroExtend 64) <<< 32) ||| (w8.zeroExtend 64)) := by bv_bits
  have htr8 : (w8.zeroExtend 64).truncate 32 = w8 := by bv_bits
  have htr12 : (w12.zeroExtend 64).truncate 32 = w12 := by bv_bits
  have hp := (r1b_zext32_pack64 (a + 8#64) (w8.zeroExtend 64) (w12.zeroExtend 64)).symm
  rw [hz, htr8, htr12, show a + 8#64 + 4#64 = a + 12#64 from by bv_omega] at hp
  rw [hp, ← r1b_spkLayoutAt_eq]
  dsimp only [r1b_spkLayoutAt]
  ac_rfl

theorem r1b_addrUpperAt_to_words (a : BitVec 64) (g : AddrGhost) :
    addrUpperAt a g ⊢
      ∃∗ w1 : BitVec 64,
        ⌜w1.extractLsb' 0 8 = g.device⌝ ∗
        (a ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
        ((a + 8#64) ↦₆₄ w1) := by
  dsimp only [addrUpperAt]
  rw [memRegion_eq_exists_bytes (a + 9#64) 7 (by decide),
    sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs
  rw [show (a ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
      (((a + 8#64) ↦₈ g.device) ∗ (⌜bs.length = 7⌝ ∗ ((a + 9#64) ↦ₛ bs))) =
    ⌜bs.length = 7⌝ ∗ ((a ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
      (((a + 8#64) ↦₈ g.device) ∗ ((a + 9#64) ↦ₛ bs))) by ac_rfl]
  apply Entails.pure_left; intro hlen
  rcases bs with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩ <;>
    simp at hlen
  let w1 : BitVec 64 := b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ g.device
  have hw0 : w1.extractLsb' 0 8 = g.device := by dsimp [w1]; bv_bits
  have hw_eq : ((a + 8#64) ↦₆₄ w1) =
      ((a + 8#64) ↦₈ g.device) ∗ ((a + 9#64) ↦ₛ [b1, b2, b3, b4, b5, b6, b7]) := by
    rw [pointsTo64_eq_pointsToBytes, Wire.unpack64_append8, pointsToBytes_cons,
      show a + 8#64 + 1#64 = a + 9#64 from by bv_omega]
  refine Entails.sepExists_right w1 (Entails.pure_right hw0 ?_)
  rw [hw_eq]
  exact Entails.of_eq (by ac_rfl)

theorem r1b_words_to_addrUpperAt (a : BitVec 64) (g : AddrGhost) (w1 : BitVec 64)
    (hw : w1.extractLsb' 0 8 = g.device) :
    ((a ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗ ((a + 8#64) ↦₆₄ w1)) ⊢
      addrUpperAt a g := by
  dsimp only [addrUpperAt]
  refine sepConj_mono_right ?_
  rw [pointsTo64_eq_pointsToBytes]
  simp only [unpack64]
  rw [pointsToBytes_cons, hw, show a + 8#64 + 1#64 = a + 9#64 from by bv_omega]
  exact sepConj_mono_right (pointsToBytes_entails_memRegion (a + 9#64) _)

theorem r1b_box1568_unpack (A : RustAlloc) (a ptr : BitVec 64) (key : List (BitVec 8))
    (h1568 : key.length = 1568) :
    boxU8At A a ptr key ⊢
      ⌜ptr ≠ 0⌝ ∗ (a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ 1568#64) ∗
        A.live ptr 1568 1 ∗ (ptr ↦ₛ key) := by
  dsimp only [boxU8At]
  have hne_nil : key ≠ [] := by intro h; simp [h] at h1568
  simp only [hne_nil, ↓reduceIte, h1568]
  have hoff : (asm64% boxSliceLenOff : BitVec 64) = 8#64 := by decide
  rw [hoff]
  rw [show (a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 1568) ∗
      ⌜ptr ≠ 0 ∧ 1568 < 2 ^ 63⌝ ∗ (A.live ptr 1568 1 ∗ (ptr ↦ₛ key)) =
    ⌜ptr ≠ 0 ∧ 1568 < 2 ^ 63⌝ ∗ ((a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ 1568#64) ∗
      A.live ptr 1568 1 ∗ (ptr ↦ₛ key)) by ac_rfl]
  apply Entails.pure_left
  rintro ⟨hp, -⟩
  exact Entails.pure_right hp (Entails.refl _)

/-! ## `r1b_SpeRegs` Bit-Slice Unpack Lemmas -/

theorem r1b_speRegs_22 (buf : BitVec 64) :
    r1b_SpeRegs 22#64 buf 22#64
      22#64 0#64 buf (((buf >>> 56).truncate 32).zeroExtend 64) 0#64 0#64 0#64 22#64 := by
  refine ⟨by bv_bits, by bv_bits, by bv_bits, ?_, by bv_bits, by bv_bits, by bv_bits, by bv_bits⟩
  bv_bits

theorem r1b_u64_split32 (a v : BitVec 64) :
    (a ↦₆₄ v) = (a ↦₃₂ v.truncate 32) ∗ ((a + 4#64) ↦₃₂ (v >>> 32).truncate 32) := by
  have hz := r1b_zext32_pack64 a v (v >>> 32)
  dsimp only at hz
  have hw : (((v >>> 32) <<< 32) ||| (v &&& 0xffffffff#64)) = v := by bv_bits
  rw [hw] at hz
  exact hz.symm

theorem r1b_cells6_to_region48 (a v0 v1 v2 v3 v4 v5 : BitVec 64) :
    ((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗
      ((a + 24#64) ↦₆₄ v3) ∗ ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5)) ⊢
      memRegion a 48 := by
  rw [r1b_region48_to_cells a]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
    (Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5
      (Entails.refl _))))))

theorem r1b_speRegs_14 (buf : BitVec 64) :
    r1b_SpeRegs 14#64 buf 14#64
      14#64 0#64 buf (((buf >>> 56).truncate 32).zeroExtend 64) 0#64 0#64 0#64 14#64 := by
  refine ⟨by bv_bits, by bv_bits, by bv_bits, ?_, by bv_bits, by bv_bits, by bv_bits, by bv_bits⟩
  bv_bits

theorem r1b_speRegs_from_u64 (cap ptr len : BitVec 64) :
    r1b_SpeRegs cap ptr len
      cap (cap >>> 32) ptr (((ptr >>> 56).truncate 32).zeroExtend 64)
      (((len >>> 32).truncate 32).zeroExtend 64)
      (((len.truncate 32) >>> 8).zeroExtend 64)
      (len >>> 56) len := by
  refine ⟨by bv_bits, by bv_bits, by bv_bits, ?_, ?_, ?_, by bv_bits, by bv_bits⟩ <;> bv_bits

theorem r1b_speRegs_from_u32_pair (cap ptr len : BitVec 64) :
    r1b_SpeRegs cap ptr len
      cap (cap >>> 32) ptr (((ptr >>> 56).truncate 32).zeroExtend 64)
      (((len >>> 32).truncate 32).zeroExtend 64)
      (((len.truncate 32) >>> 8).zeroExtend 64)
      ((((len >>> 32).truncate 32) >>> 24).zeroExtend 64)
      ((len.truncate 32).zeroExtend 64) := by
  refine ⟨by bv_bits, by bv_bits, by bv_bits, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_bits

/-! ## Region Split/Merge and Spine Frame (`r1b_invCore`) -/

theorem r1b_split_region (fsp : BitVec 64) (o n1 n2 : Nat)
    (ho : BitVec.ofNat 64 o + BitVec.ofNat 64 n1 = BitVec.ofNat 64 (o + n1) := by decide)
    (hb : n1 + n2 ≤ 2 ^ 64 := by decide) :
    memRegion (fsp + BitVec.ofNat 64 o) (n1 + n2) =
      memRegion (fsp + BitVec.ofNat 64 o) n1 ∗
        memRegion (fsp + BitVec.ofNat 64 (o + n1)) n2 := by
  have heq : fsp + BitVec.ofNat 64 (o + n1) = (fsp + BitVec.ofNat 64 o) + BitVec.ofNat 64 n1 := by
    rw [BitVec.add_assoc, ho]
  rw [heq]
  exact ProofLib.memRegion_split (fsp + BitVec.ofNat 64 o) n1 n2 hb

theorem r1b_join_region (fsp : BitVec 64) (o n1 n2 : Nat)
    (ho : BitVec.ofNat 64 o + BitVec.ofNat 64 n1 = BitVec.ofNat 64 (o + n1) := by decide)
    (hb : n1 + n2 ≤ 2 ^ 64 := by decide) :
    memRegion (fsp + BitVec.ofNat 64 o) n1 ∗
      memRegion (fsp + BitVec.ofNat 64 (o + n1)) n2 =
      memRegion (fsp + BitVec.ofNat 64 o) (n1 + n2) :=
  (r1b_split_region fsp o n1 n2 ho hb).symm

theorem r1b_allocFailed_of_null {s0 st_bl sf : State}
    (htr0 : s0.trace <+: st_bl.trace)
    (htr_f : sf.trace = st_bl.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf := by
  refine r1b_allocFailedIn_sub htr0 ?_
  dsimp only [allocFailedIn]
  rw [htr_f]
  simp

/-! ## `readBundleV` Failure and Success Semantic Lemmas -/

theorem r1b_ownedBytes_zero (A : RustAlloc) (ptr len : BitVec 64) (bs : List (BitVec 8)) :
    ownedBytes A 0#64 ptr len bs ⊢ emp := by
  rw [r1b_ownedBytes_borrow A 0#64 ptr len bs]
  apply Entails.pure_left
  rintro ⟨_, hle, _, _⟩
  have hnil : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
  subst hnil
  simp only [List.length_nil, pointsToBytes_nil, r1b_ownedRest, emp_sepConj]
  exact Entails.refl _

theorem r1b_pointsToBytes4_eq_u32 (a : BitVec 64) (b0 b1 b2 b3 : BitVec 8) :
    (a ↦ₛ [b0, b1, b2, b3]) = (a ↦₃₂ ofLe32 b0 b1 b2 b3) := by
  dsimp only [ofLe32]
  rw [Wire.pointsTo32_append4 a b0 b1 b2 b3]
  simp only [pointsToBytes_cons, pointsToBytes_nil, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]

private theorem opt_bind_none_right {α β : Type} (x : Option α) (f : α → Option β)
    (hf : ∀ a, x = some a → f a = none) : (x >>= f) = none := by
  cases x with
  | none => rfl
  | some a => exact hf a rfl

theorem r1b_none_reg_rd {F : FsFiles} {dir : Bytes} {dev : BitVec 8}
    (h : cliIo.rd F (dir ++ [0x2f#8] ++ utf8 "registration-id") = .error ()) :
    readBundleV F dir dev = none := by
  have hb : bundleFile F dir "registration-id" = none := by
    dsimp only [bundleFile, bundlePath]; rw [h]; rfl
  unfold readBundleV
  refine opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun _ _ => ?_
  rw [hb]; rfl

theorem r1b_none_reg_len {F : FsFiles} {dir regBs : Bytes} {dev : BitVec 8}
    (hrd : cliIo.rd F (dir ++ [0x2f#8] ++ utf8 "registration-id") = .ok regBs)
    (hlen : regBs.length ≠ 4) :
    readBundleV F dir dev = none := by
  have hb : bundleFile F dir "registration-id" = some regBs := by
    dsimp only [bundleFile, bundlePath]; rw [hrd]; rfl
  have hu : readU32LE regBs = none := by
    rcases regBs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩⟩ <;> simp [readU32LE] at hlen ⊢
  unfold readBundleV
  refine opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun _ _ => ?_
  rw [hb]; dsimp only [Bind.bind, Option.bind]; rw [hu]

theorem r1b_none_spk_rd {F : FsFiles} {dir : Bytes} {dev : BitVec 8}
    (h : cliIo.rd F (dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .error ()) :
    readBundleV F dir dev = none := by
  have hb : bundleFile F dir "signed-pre-key" = none := by
    dsimp only [bundleFile, bundlePath]; rw [h]; rfl
  unfold readBundleV
  refine opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun _ _ =>
    opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun _ _ => ?_
  rw [hb]; rfl

theorem r1b_none_spk_split {F : FsFiles} {dir spkBs : Bytes} {dev : BitVec 8}
    (hrd : cliIo.rd F (dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .ok spkBs)
    (hsp : splitSigned spkBs = none) :
    readBundleV F dir dev = none := by
  have hb : bundleFile F dir "signed-pre-key" = some spkBs := by
    dsimp only [bundleFile, bundlePath]; rw [hrd]; rfl
  unfold readBundleV
  refine opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun _ _ =>
    opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun _ _ => ?_
  rw [hb]; dsimp only [Bind.bind, Option.bind]; rw [hsp]

theorem r1b_none_kpk_rd {F : FsFiles} {dir : Bytes} {dev : BitVec 8}
    (h : cliIo.rd F (dir ++ [0x2f#8] ++ utf8 "kyber-pre-key") = .error ()) :
    readBundleV F dir dev = none := by
  have hb : bundleFile F dir "kyber-pre-key" = none := by
    dsimp only [bundleFile, bundlePath]; rw [h]; rfl
  unfold readBundleV
  refine opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun _ _ =>
    opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun _ _ =>
    opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun ⟨_, _, _⟩ _ => ?_
  rw [hb]; rfl

theorem r1b_none_kpk_split {F : FsFiles} {dir kpkBs : Bytes} {dev : BitVec 8}
    (hrd : cliIo.rd F (dir ++ [0x2f#8] ++ utf8 "kyber-pre-key") = .ok kpkBs)
    (hsp : splitSigned kpkBs = none) :
    readBundleV F dir dev = none := by
  have hb : bundleFile F dir "kyber-pre-key" = some kpkBs := by
    dsimp only [bundleFile, bundlePath]; rw [hrd]; rfl
  unfold readBundleV
  refine opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun _ _ =>
    opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun _ _ =>
    opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun ⟨_, _, _⟩ _ => ?_
  rw [hb]; dsimp only [Bind.bind, Option.bind]; rw [hsp]

theorem r1b_none_opk_rd {F : FsFiles} {dir : Bytes} {dev : BitVec 8}
    (h : cliIo.rd F (dir ++ [0x2f#8] ++ utf8 "one-time-pre-key") = .error ()) :
    readBundleV F dir dev = none := by
  have hb : bundleFile F dir "one-time-pre-key" = none := by
    dsimp only [bundleFile, bundlePath]; rw [h]; rfl
  unfold readBundleV
  refine opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun _ _ =>
    opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun _ _ =>
    opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun ⟨_, _, _⟩ _ =>
    opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun ⟨_, _, _⟩ _ => ?_
  rw [hb]; rfl

theorem r1b_none_opk_split {F : FsFiles} {dir opkBs : Bytes} {dev : BitVec 8}
    (hrd : cliIo.rd F (dir ++ [0x2f#8] ++ utf8 "one-time-pre-key") = .ok opkBs)
    (hne : opkBs ≠ []) (hsp : splitId opkBs = none) :
    readBundleV F dir dev = none := by
  have hb : bundleFile F dir "one-time-pre-key" = some opkBs := by
    dsimp only [bundleFile, bundlePath]; rw [hrd]; rfl
  have hemp : opkBs.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  unfold readBundleV
  refine opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun _ _ =>
    opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun _ _ =>
    opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun ⟨_, _, _⟩ _ =>
    opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun ⟨_, _, _⟩ _ => ?_
  rw [hb]; dsimp only [Bind.bind, Option.bind]
  simp only [hemp, Bool.false_eq_true, ↓reduceIte, hsp]

theorem r1b_none_opk_deser {F : FsFiles} {dir opkBs opkKey : Bytes} {dev : BitVec 8}
    {opkId : BitVec 32} {e : SignalProtocolError}
    (hrd : cliIo.rd F (dir ++ [0x2f#8] ++ utf8 "one-time-pre-key") = .ok opkBs)
    (hne : opkBs ≠ []) (hsp : splitId opkBs = some (opkId, opkKey))
    (hd : PublicKey.deserialize opkKey = .error e) :
    readBundleV F dir dev = none := by
  have hb : bundleFile F dir "one-time-pre-key" = some opkBs := by
    dsimp only [bundleFile, bundlePath]; rw [hrd]; rfl
  have hemp : opkBs.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  have he : exceptOpt (PublicKey.deserialize opkKey) = none := by rw [hd]; rfl
  unfold readBundleV
  refine opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun _ _ =>
    opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun _ _ =>
    opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun ⟨_, _, _⟩ _ =>
    opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun ⟨_, _, _⟩ _ => ?_
  rw [hb]; dsimp only [Bind.bind, Option.bind]
  simp only [hemp, Bool.false_eq_true, ↓reduceIte, hsp]; rw [he]

theorem r1b_none_spk_deser {F : FsFiles} {dir spkBs spkKey spkSig : Bytes} {dev : BitVec 8}
    {spkId : BitVec 32} {e : SignalProtocolError}
    (hrd : cliIo.rd F (dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .ok spkBs)
    (hsp : splitSigned spkBs = some (spkId, spkKey, spkSig))
    (hd : PublicKey.deserialize spkKey = .error e) :
    readBundleV F dir dev = none := by
  have hb : bundleFile F dir "signed-pre-key" = some spkBs := by
    dsimp only [bundleFile, bundlePath]; rw [hrd]; rfl
  have he : exceptOpt (PublicKey.deserialize spkKey) = none := by rw [hd]; rfl
  unfold readBundleV
  refine opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun _ _ =>
    opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun _ _ => ?_
  rw [hb]; dsimp only [Bind.bind, Option.bind]; rw [hsp]; dsimp only [Bind.bind, Option.bind]
  refine opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun ⟨_, _, _⟩ _ =>
    opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun _ _ => ?_
  rw [he]

theorem r1b_none_kpk_deser {F : FsFiles} {dir kpkBs kpkKey kpkSig : Bytes} {dev : BitVec 8}
    {kpkId : BitVec 32}
    (hrd : cliIo.rd F (dir ++ [0x2f#8] ++ utf8 "kyber-pre-key") = .ok kpkBs)
    (hsp : splitSigned kpkBs = some (kpkId, kpkKey, kpkSig))
    (hd : ∀ key, RunProofs.kemPkDeserialize kpkKey ≠ .ok key) :
    readBundleV F dir dev = none := by
  have hb : bundleFile F dir "kyber-pre-key" = some kpkBs := by
    dsimp only [bundleFile, bundlePath]; rw [hrd]; rfl
  unfold readBundleV
  refine opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun _ _ =>
    opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun _ _ =>
    opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun ⟨_, _, _⟩ _ => ?_
  rw [hb]; dsimp only [Bind.bind, Option.bind]; rw [hsp]; dsimp only [Bind.bind, Option.bind]
  refine opt_bind_none_right _ _ fun _ _ => opt_bind_none_right _ _ fun _ _ =>
    opt_bind_none_right _ _ fun _ _ => ?_
  cases hk : RunProofs.kemPkDeserialize kpkKey with
  | ok key => exact False.elim (hd key hk)
  | _ => rfl

theorem r1b_readBundleV_some {F : FsFiles} {dir spkBs spkKey spkSig kpkBs kpkKey kpkSig kpk opkBs : Bytes}
    {dev r0 r1 r2 r3 : BitVec 8} {idKey : IdentityKey}
    {spkId kpkId : BitVec 32} {spk : PublicKey} {opk : Option (BitVec 32 × PublicKey)}
    (hik : ∃ ikB : Bytes,
      bundleFile F dir "identity-key" = some ikB ∧ exceptOpt (decodeIdentityKey ikB) = some idKey)
    (hreg : cliIo.rd F (dir ++ [0x2f#8] ++ utf8 "registration-id") = .ok [r0, r1, r2, r3])
    (hspk_rd : cliIo.rd F (dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .ok spkBs)
    (hspk_sp : splitSigned spkBs = some (spkId, spkKey, spkSig))
    (hkpk_rd : cliIo.rd F (dir ++ [0x2f#8] ++ utf8 "kyber-pre-key") = .ok kpkBs)
    (hkpk_sp : splitSigned kpkBs = some (kpkId, kpkKey, kpkSig))
    (hopk_rd : cliIo.rd F (dir ++ [0x2f#8] ++ utf8 "one-time-pre-key") = .ok opkBs)
    (hopk_sem : (opkBs = [] ∧ opk = none) ∨
      (∃ opkId opkKey opkPk, opkBs ≠ [] ∧ splitId opkBs = some (opkId, opkKey) ∧
        PublicKey.deserialize opkKey = .ok opkPk ∧ opk = some (opkId, opkPk)))
    (hspk_d : PublicKey.deserialize spkKey = .ok spk)
    (hkpk_d : RunProofs.kemPkDeserialize kpkKey = .ok kpk) :
    readBundleV F dir dev = some {
      idKey := idKey, regId := ofLe32 r0 r1 r2 r3, device := dev,
      spkId := spkId, spk := spk, spkSig := spkSig,
      kpkId := kpkId, kpk := kpk, kpkSig := kpkSig, opk := opk
    } := by
  rcases hik with ⟨ikB, hik1, hik2⟩
  have hb_reg : bundleFile F dir "registration-id" = some [r0, r1, r2, r3] := by
    dsimp only [bundleFile, bundlePath]; rw [hreg]; rfl
  have hb_spk : bundleFile F dir "signed-pre-key" = some spkBs := by
    dsimp only [bundleFile, bundlePath]; rw [hspk_rd]; rfl
  have hb_kpk : bundleFile F dir "kyber-pre-key" = some kpkBs := by
    dsimp only [bundleFile, bundlePath]; rw [hkpk_rd]; rfl
  have hb_opk : bundleFile F dir "one-time-pre-key" = some opkBs := by
    dsimp only [bundleFile, bundlePath]; rw [hopk_rd]; rfl
  have he_spk : exceptOpt (PublicKey.deserialize spkKey) = some spk := by rw [hspk_d]; rfl
  unfold readBundleV
  rw [hik1]; dsimp only [Bind.bind, Option.bind]
  rw [hik2]; dsimp only [Bind.bind, Option.bind]
  rw [hb_reg]; dsimp only [Bind.bind, Option.bind, readU32LE]
  rw [hb_spk]; dsimp only [Bind.bind, Option.bind]
  rw [hspk_sp]; dsimp only [Bind.bind, Option.bind]
  rw [hb_kpk]; dsimp only [Bind.bind, Option.bind]
  rw [hkpk_sp]; dsimp only [Bind.bind, Option.bind]
  rw [hb_opk]; dsimp only [Bind.bind, Option.bind]
  rcases hopk_sem with ⟨rfl, rfl⟩ | ⟨opkId, opkKey, opkPk, hne, hsp_o, hd_o, rfl⟩
  · dsimp only [List.isEmpty, Bind.bind, Option.bind, Pure.pure]
    rw [he_spk]; dsimp only [Bind.bind, Option.bind]
    rw [hkpk_d]; rfl
  · have hemp : opkBs.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
    have he_opk : exceptOpt (PublicKey.deserialize opkKey) = some opkPk := by rw [hd_o]; rfl
    simp only [hemp, Bool.false_eq_true, ↓reduceIte, hsp_o]
    rw [he_opk]; dsimp only [Bind.bind, Option.bind, Pure.pure]
    rw [he_spk]; dsimp only [Bind.bind, Option.bind]
    rw [hkpk_d]

end CryptoVerification.SignalSession.Cli.RunCompose
