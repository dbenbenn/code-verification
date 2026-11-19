/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public meta import Lean

/-!
# Shared 64-Bit Linear Address Canonicalization and Spatial Bundle Unfolding

Provides the shared address canonicalization and spatial normalization primitives for `ProofLib.Sep`:
- `LinAddr64` & `canonAddr64`: memoized bottom-up 64-bit linear address canonicalizer (`root ± k#64`)
  that unfolds non-recursive local `let` bindings, substitutes acyclic local pointer equalities,
  normalizes `BitVec.ofNat 64 u.toNat` to `u.zeroExtend 64`, and folds signed/unsigned 64-bit
  constant chains using closed-form kernel lemmas.
- `peelAddrRoot`: syntactic `(root, byteOff)` peeler that avoids invoking `isDefEq` across unequal
  symbolic-base offsets.
- `autoUnfoldBundles` & `pushPrenexSepExists`: zero-attribute `@[expose]` spatial bundle unfolder
  and prenex `∃∗` scope pusher.
-/

namespace ProofLib.Sep

open Arm64 ProofLib

public section

/-- Kernel-evaluated `n ≤ 2 ^ 64` bridge via `Nat.ble`. -/
theorem le_two_pow_64_of_ble {n : Nat} (h : Nat.ble n 0x10000000000000000 = true) :
    n ≤ 2 ^ 64 := by
  have h1 : n ≤ 0x10000000000000000 := Nat.le_of_ble_eq_true h
  omega

/-- Canonicalize `BitVec.ofNat 64 b.toNat` for any `b : BitVec w` to `b.zeroExtend 64`. -/
theorem bitvec64_ofNat_toNat_eq_zeroExtend {w : Nat} (b : BitVec w) :
    BitVec.ofNat 64 b.toNat = b.zeroExtend 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]

/-- Transport `P ⊢ Q` across endpoint equalities `P₀ = P` and `Q = Q₀`. -/
theorem entails_of_eq_both {P₀ P Q Q₀ : SepProp}
    (hP : P₀ = P) (hPQ : P ⊢ Q) (hQ : Q = Q₀) : P₀ ⊢ Q₀ :=
  hP ▸ hQ ▸ hPQ

/-- A 128-bit cell weakens to a 16-byte `memRegion`. -/
theorem pointsTo128_entails_memRegion (a : BitVec 64) (v : BitVec 128) :
    (a ↦₁₂₈ v) ⊢ memRegion a 16 :=
  IsBlock.entails_memRegion (IsBlock.pointsTo128 a v)

end

public meta section

open Lean Meta Elab Tactic

/-- Kernel `Eq.refl true` certificate. -/
def rflTrueExpr : Expr :=
  mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)

/-- Kernel `Eq.refl n` for a `Nat` expression `n`. -/
def mkEqReflNat (nExpr : Expr) : Expr :=
  mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Nat) nExpr

/-- Canonical `k#64` (`BitVec.ofNat 64 k`) matching user literal syntax. -/
@[inline] def mkBV64Lit (v : Nat) : Expr :=
  mkApp2 (mkConst ``BitVec.ofNat) (toExpr (64 : Nat)) (toExpr (v % (1 <<< 64)))

/-- Convert an unsigned 64-bit integer to signed `Int` in `[-2^63, 2^63)`. -/
def toSigned64 (u : Int) : Int :=
  let m : Int := ((1 : Nat) <<< 64 : Nat)
  let half : Int := ((1 : Nat) <<< 63 : Nat)
  let r := u % m
  let r := if r < 0 then r + m else r
  if r >= half then r - m else r

/-- Canonicalized 64-bit linear address `root ± |byteOff|#64`. -/
structure LinAddr64 where
  root : Expr
  byteOff : Int
  canonExpr : Expr
  /-- Proof of `origExpr = canonExpr` (`none` when `origExpr == canonExpr`). -/
  eqProof? : Option Expr
  deriving Inhabited

/-- Local context facts extracted once per goal. -/
structure CtxFacts where
  letVals : Std.HashMap FVarId Expr := {}
  bvEqs : Array (Expr × Expr × Expr) := #[]
  lenEqs : Array (Expr × Nat × Expr) := #[]

/-- Evaluate a closed `Nat` expression if possible. -/
def evalClosedNat? (e : Expr) : MetaM (Option Nat) := do
  let e := e.consumeMData
  if let some n := e.rawNatLit? then return some n
  if let some n ← getNatValue? e then return some n
  if e.hasFVar || e.hasMVar then return none
  let e' ← withTransparency .default (whnf e)
  if let some n := e'.rawNatLit? then return some n
  getNatValue? e'

/-- Evaluate a closed `BitVec 64` expression to `[0, 2^64)`. -/
partial def evalClosedBV64? (e : Expr) : MetaM (Option Nat) := do
  let e := e.consumeMData
  if let some n ← ProofLib.SepSolver.evalBV64Lit? e then return some n
  if e.hasFVar || e.hasMVar then return none
  let e' ← withTransparency .default (whnf e)
  ProofLib.SepSolver.evalBV64Lit? e'

/-- Purely syntactic `(root, signedByteOff)` peeler for 64-bit addresses.
    Never calls `whnf` or `isDefEq` on symbolic `BitVec 64` expressions. -/
partial def peelAddrRoot (letVals : Std.HashMap FVarId Expr := {}) (e : Expr) (fuel : Nat := 12) :
    Expr × Int :=
  let e := e.consumeMData
  if fuel == 0 then (e, 0)
  else
    match e with
    | .fvar fv =>
      match letVals[fv]? with
      | some v => peelAddrRoot letVals v (fuel - 1)
      | none => (e, 0)
    | _ =>
      if e.isAppOfArity ``HAdd.hAdd 6 then
        let a := (e.getArg! 4).consumeMData
        let b := (e.getArg! 5).consumeMData
        if b.isAppOfArity ``BitVec.ofNat 2 then
          if (b.getArg! 0).rawNatLit? == some 64 then
            if let some k := (b.getArg! 1).rawNatLit? then
              let (r, o) := peelAddrRoot letVals a (fuel - 1)
              (r, toSigned64 (o + (k : Int)))
            else (e, 0)
          else (e, 0)
        else (e, 0)
      else if e.isAppOfArity ``HSub.hSub 6 then
        let a := (e.getArg! 4).consumeMData
        let b := (e.getArg! 5).consumeMData
        if b.isAppOfArity ``BitVec.ofNat 2 then
          if (b.getArg! 0).rawNatLit? == some 64 then
            if let some k := (b.getArg! 1).rawNatLit? then
              let (r, o) := peelAddrRoot letVals a (fuel - 1)
              (r, toSigned64 (o - (k : Int)))
            else (e, 0)
          else (e, 0)
        else (e, 0)
      else
        (e, 0)

/-- Collect non-recursive local `let` bindings (`BitVec 64` / `Nat`), pointer equalities, and list lengths. -/
def collectCtxFacts : MetaM CtxFacts := do
  let bv64Ty := mkApp (mkConst ``BitVec) (toExpr (64 : Nat))
  let natTy := mkConst ``Nat
  let mut letVals : Std.HashMap FVarId Expr := {}
  let mut bvEqs : Array (Expr × Expr × Expr) := #[]
  let mut lenEqs : Array (Expr × Nat × Expr) := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    if let some val := decl.value? then
      let val ← instantiateMVars val
      if !val.containsFVar decl.fvarId then
        if (← withReducibleAndInstances (isDefEq ty bv64Ty)) ||
           (← withReducibleAndInstances (isDefEq ty natTy)) then
          letVals := letVals.insert decl.fvarId val
    else
      if ty.isAppOfArity ``Eq 3 then
        let eqTy := ty.getArg! 0
        let lhs := (ty.getArg! 1).consumeMData
        let rhs := (ty.getArg! 2).consumeMData
        let hPrf := mkFVar decl.fvarId
        if ← withReducibleAndInstances (isDefEq eqTy bv64Ty) then
          let isGoodLhs (x y : Expr) : Bool :=
            (x.isFVar || x.isAppOfArity ``Arm64.State.sp 1) &&
            !(y.find? (· == x)).isSome &&
            !bvEqs.any (fun (l, r, _) => l == x || (r.find? (· == x)).isSome || l == y)
          if isGoodLhs lhs rhs then
            bvEqs := bvEqs.push (lhs, rhs, hPrf)
          else if isGoodLhs rhs lhs then
            bvEqs := bvEqs.push (rhs, lhs, ← mkEqSymm hPrf)
        else if ← withReducibleAndInstances (isDefEq eqTy natTy) then
          if lhs.isAppOfArity ``List.length 2 then
            if let some k ← evalClosedNat? rhs then
              lenEqs := lenEqs.push (lhs.getArg! 1, k, hPrf)
          else if rhs.isAppOfArity ``List.length 2 then
            if let some k ← evalClosedNat? lhs then
              lenEqs := lenEqs.push (rhs.getArg! 1, k, ← mkEqSymm hPrf)
  return { letVals, bvEqs, lenEqs }

/-- Combine optional equality proofs `a = b` and `b = c`. -/
def chainEq? (p1? p2? : Option Expr) : MetaM (Option Expr) := do
  match p1?, p2? with
  | none, none => return none
  | some p1, none => return some p1
  | none, some p2 => return some p2
  | some p1, some p2 => return some (← mkEqTrans p1 p2)

/-- Normalize `BitVec.ofNat 64 b.toNat` (after unfolding `let`-bound `Nat`s in `b.toNat`)
    into `b.zeroExtend 64` for `b : BitVec w` (`w < 64`). -/
private def tryNormOfNatToNat? (ctx : CtxFacts) (e : Expr) : MetaM (Option (Expr × Option Expr)) := do
  unless e.isAppOfArity ``BitVec.ofNat 2 do return none
  let wArg := (e.getArg! 0).consumeMData
  let some 64 ← evalClosedNat? wArg | return none
  let mut nArg := (e.getArg! 1).consumeMData
  if let .fvar fv := nArg then
    if let some v := ctx.letVals[fv]? then
      nArg := v.consumeMData
  unless nArg.isAppOfArity ``BitVec.toNat 2 do return none
  let srcW := (nArg.getArg! 0).consumeMData
  let b := nArg.getArg! 1
  let some w ← evalClosedNat? srcW | return none
  unless w < 64 do return none
  let dst ← mkAppM ``BitVec.zeroExtend #[toExpr (64 : Nat), b]
  let prf := mkApp2 (mkConst ``bitvec64_ofNat_toNat_eq_zeroExtend) srcW b
  let prf ← mkExpectedTypeHint prf (← mkEq e dst)
  return some (dst, some prf)

/-- Unfold local `let`-bound `BitVec 64` / `Nat` `FVar`s (depth ≤ 8, zero proof cost when pure `zeta`),
    normalize `BitVec.ofNat 64 b.toNat` to `b.zeroExtend 64`, and substitute acyclic local `BitVec 64`
    equalities `s.sp = ...` / `b = ...`. -/
partial def expandAddrExpr (ctx : CtxFacts) (e : Expr) (fuel : Nat := 8) :
    MetaM (Expr × Option Expr) := do
  let e := e.consumeMData
  if fuel == 0 then return (e, none)
  for (lhs, rhs, hEq) in ctx.bvEqs do
    if e == lhs then
      let (rhs', h2?) ← expandAddrExpr ctx rhs (fuel - 1)
      return (rhs', ← chainEq? (some hEq) h2?)
  if let .fvar fv := e then
    if let some val := ctx.letVals[fv]? then
      let (val', h?) ← expandAddrExpr ctx val (fuel - 1)
      match h? with
      | none => return (val', none)
      | some p => return (val', some (← mkExpectedTypeHint p (← mkEq e val')))
    return (e, none)
  if let some (dst, hp?) ← tryNormOfNatToNat? ctx e then
    return (dst, hp?)
  if e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HSub.hSub 6 || e.isAppOfArity ``HMul.hMul 6 then
    let a := e.getArg! 4
    let b := e.getArg! 5
    let (a', ha?) ← expandAddrExpr ctx a fuel
    let (b', hb?) ← expandAddrExpr ctx b fuel
    if a' == a && b' == b && ha?.isNone && hb?.isNone then
      return (e, none)
    let fn := e.getAppFn
    let args := e.getAppArgs
    let eNew := mkAppN fn ((args.set! 4 a').set! 5 b')
    if ha?.isNone && hb?.isNone then
      return (eNew, none)
    let f2 := mkAppN fn (args.extract 0 4)
    let pa ← match ha? with
      | some pa => pure pa
      | none => mkExpectedTypeHint (← mkEqRefl a') (← mkEq a a')
    let pb ← match hb? with
      | some pb => pure pb
      | none => mkExpectedTypeHint (← mkEqRefl b') (← mkEq b b')
    let prf ← mkCongr (← mkCongrArg f2 pa) pb
    return (eNew, some prf)
  if e.isAppOfArity ``Neg.neg 3 then
    let a := e.getArg! 2
    let (a', ha?) ← expandAddrExpr ctx a fuel
    if a' == a && ha?.isNone then return (e, none)
    let eNew := mkAppN e.getAppFn (e.getAppArgs.set! 2 a')
    if ha?.isNone then return (eNew, none)
    let f1 := mkAppN e.getAppFn (e.getAppArgs.extract 0 2)
    let pa := ha?.getD (← mkEqRefl a')
    return (eNew, some (← mkCongrArg f1 pa))
  return (e, none)

/-- Fast single-pass bottom-up constant-offset chain folder using `bitvec64_*` kernel lemmas. -/
partial def foldBV64LitChain (e : Expr) : MetaM (Expr × Option Expr) := do
  let e := e.consumeMData
  if let some v ← evalClosedBV64? e then
    let c := mkBV64Lit v
    if e == c then return (e, none)
    return (c, some (← mkExpectedTypeHint (← mkEqRefl c) (← mkEq e c)))
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let a0 := e.getArg! 4
    let b0 := e.getArg! 5
    let (a, pa?) ← foldBV64LitChain a0
    let (b, pb?) ← foldBV64LitChain b0
    let cur := if a == a0 && b == b0 then e else mkAppN e.getAppFn ((e.getAppArgs.set! 4 a).set! 5 b)
    let pCur? ←
      if pa?.isNone && pb?.isNone then pure none
      else do
        let f2 := mkAppN e.getAppFn (e.getAppArgs.extract 0 4)
        let pa ← match pa? with | some p => pure p | none => mkEqRefl a
        let pb ← match pb? with | some p => pure p | none => mkEqRefl b
        pure (some (← mkCongr (← mkCongrArg f2 pa) pb))
    if let some vb ← evalClosedBV64? b then
      if vb == 0 then
        let pStep ← mkAppM ``BitVec.add_zero #[a]
        let pStep ← mkExpectedTypeHint pStep (← mkEq cur a)
        return (a, ← chainEq? pCur? (some pStep))
      if a.isAppOfArity ``HAdd.hAdd 6 then
        let x := a.getArg! 4
        let aLit := a.getArg! 5
        if let some va ← evalClosedBV64? aLit then
          let sum := (va + vb) % (1 <<< 64)
          if sum == 0 then
            let pStep ← mkAppM ``bitvec64_add_add_zero #[x, aLit, b, ← mkEqRefl (mkBV64Lit 0)]
            return (x, ← chainEq? pCur? (some pStep))
          else if sum >= (1 <<< 63) then
            let mag := (1 <<< 64) - sum
            let cSum := mkBV64Lit sum
            let cMag := mkBV64Lit mag
            let mid ← mkAppM ``HAdd.hAdd #[x, cSum]
            let p1 ← mkAppM ``bitvec64_add_add_fold #[x, aLit, b, cSum, ← mkEqRefl cSum]
            let dst ← mkAppM ``HSub.hSub #[x, cMag]
            let p2 ← mkAppM ``bitvec64_add_neg_lit_eq_sub #[x, cSum, cMag, ← mkEqRefl (mkBV64Lit 0)]
            let pStep ← mkEqTrans (← mkExpectedTypeHint p1 (← mkEq cur mid)) p2
            return (dst, ← chainEq? pCur? (some pStep))
          else
            let cSum := mkBV64Lit sum
            let dst ← mkAppM ``HAdd.hAdd #[x, cSum]
            let pStep ← mkAppM ``bitvec64_add_add_fold #[x, aLit, b, cSum, ← mkEqRefl cSum]
            return (dst, ← chainEq? pCur? (some pStep))
      if a.isAppOfArity ``HSub.hSub 6 then
        let x := a.getArg! 4
        let aLit := a.getArg! 5
        if let some va ← evalClosedBV64? aLit then
          let diff := (vb + (1 <<< 64) - va) % (1 <<< 64)
          if diff == 0 then
            let pStep ← mkAppM ``bitvec64_sub_add_zero #[x, aLit, b, ← mkEqRefl aLit]
            return (x, ← chainEq? pCur? (some pStep))
          else if diff >= (1 <<< 63) then
            let cExpr := mkBV64Lit ((1 <<< 64) - diff)
            let dst ← mkAppM ``HSub.hSub #[x, cExpr]
            let pStep ← mkAppM ``bitvec64_sub_add_fold_sub #[x, aLit, b, cExpr, ← mkEqRefl cExpr]
            return (dst, ← chainEq? pCur? (some pStep))
          else
            let cExpr := mkBV64Lit diff
            let dst ← mkAppM ``HAdd.hAdd #[x, cExpr]
            let pStep ← mkAppM ``bitvec64_sub_add_fold_add #[x, aLit, b, cExpr, ← mkEqRefl cExpr]
            return (dst, ← chainEq? pCur? (some pStep))
      if vb >= (1 <<< 63) then
        let cMag := mkBV64Lit ((1 <<< 64) - vb)
        let dst ← mkAppM ``HSub.hSub #[a, cMag]
        let pStep ← mkAppM ``bitvec64_add_neg_lit_eq_sub #[a, b, cMag, ← mkEqRefl (mkBV64Lit 0)]
        return (dst, ← chainEq? pCur? (some pStep))
    return (cur, pCur?)
  if e.isAppOfArity ``HSub.hSub 6 then
    let a0 := e.getArg! 4
    let b0 := e.getArg! 5
    let (a, pa?) ← foldBV64LitChain a0
    let (b, pb?) ← foldBV64LitChain b0
    let cur := if a == a0 && b == b0 then e else mkAppN e.getAppFn ((e.getAppArgs.set! 4 a).set! 5 b)
    let pCur? ←
      if pa?.isNone && pb?.isNone then pure none
      else do
        let f2 := mkAppN e.getAppFn (e.getAppArgs.extract 0 4)
        let pa ← match pa? with | some p => pure p | none => mkEqRefl a
        let pb ← match pb? with | some p => pure p | none => mkEqRefl b
        pure (some (← mkCongr (← mkCongrArg f2 pa) pb))
    if let some vb ← evalClosedBV64? b then
      if vb == 0 then
        let pStep ← mkAppM ``BitVec.sub_zero #[a]
        let pStep ← mkExpectedTypeHint pStep (← mkEq cur a)
        return (a, ← chainEq? pCur? (some pStep))
      if a.isAppOfArity ``HSub.hSub 6 then
        let x := a.getArg! 4
        let aLit := a.getArg! 5
        if let some va ← evalClosedBV64? aLit then
          let sum := (va + vb) % (1 <<< 64)
          if sum == 0 then
            let pStep ← mkAppM ``bitvec64_sub_sub_zero #[x, aLit, b, ← mkEqRefl (mkBV64Lit 0)]
            return (x, ← chainEq? pCur? (some pStep))
          else if sum >= (1 <<< 63) then
            let cAdd := mkBV64Lit ((1 <<< 64) - sum)
            let cSub := mkBV64Lit sum
            let mid ← mkAppM ``HSub.hSub #[x, cSub]
            let p1 ← mkAppM ``bitvec64_sub_sub_fold #[x, aLit, b, cSub, ← mkEqRefl cSub]
            let dst ← mkAppM ``HAdd.hAdd #[x, cAdd]
            let p2 ← ProofLib.BV.Lin.proveEq? mid dst
            if let some p2 := p2 then
              let pStep ← mkEqTrans p1 p2
              return (dst, ← chainEq? pCur? (some pStep))
          else
            let cExpr := mkBV64Lit sum
            let dst ← mkAppM ``HSub.hSub #[x, cExpr]
            let pStep ← mkAppM ``bitvec64_sub_sub_fold #[x, aLit, b, cExpr, ← mkEqRefl cExpr]
            return (dst, ← chainEq? pCur? (some pStep))
      if a.isAppOfArity ``HAdd.hAdd 6 then
        let x := a.getArg! 4
        let aLit := a.getArg! 5
        if let some va ← evalClosedBV64? aLit then
          let diff := (va + (1 <<< 64) - vb) % (1 <<< 64)
          if diff == 0 then
            let pStep ← mkAppM ``bitvec64_add_sub_zero #[x, aLit, b, ← mkEqRefl aLit]
            return (x, ← chainEq? pCur? (some pStep))
          else if diff >= (1 <<< 63) then
            let cExpr := mkBV64Lit ((1 <<< 64) - diff)
            let dst ← mkAppM ``HSub.hSub #[x, cExpr]
            let pStep ← mkAppM ``bitvec64_add_sub_fold_sub #[x, aLit, b, cExpr, ← mkEqRefl cExpr]
            return (dst, ← chainEq? pCur? (some pStep))
          else
            let cExpr := mkBV64Lit diff
            let dst ← mkAppM ``HAdd.hAdd #[x, cExpr]
            let pStep ← mkAppM ``bitvec64_add_sub_fold_add #[x, aLit, b, cExpr, ← mkEqRefl cExpr]
            return (dst, ← chainEq? pCur? (some pStep))
    return (cur, pCur?)
  return (e, none)

/-- Build canonical `root ± |off|#64` expression. -/
def mkCanonAddrExpr (root : Expr) (byteOff : Int) : MetaM Expr := do
  if byteOff == 0 then return root
  else if byteOff > 0 then mkAppM ``HAdd.hAdd #[root, mkBV64Lit byteOff.toNat]
  else mkAppM ``HSub.hSub #[root, mkBV64Lit ((-byteOff).toNat)]

/-- Canonicalize `e0 : BitVec 64` into `LinAddr64` with memoization per distinct `Expr`. -/
def canonAddr64 (ctx : CtxFacts) (cacheRef : IO.Ref (Std.HashMap Expr LinAddr64)) (e0 : Expr) :
    MetaM LinAddr64 := do
  let e ← instantiateMVars e0
  if let some hit := (← cacheRef.get)[e]? then
    return hit
  let (eExp, hExp?) ← expandAddrExpr ctx e 8
  let (root, byteOff) ← do
    let some lf ← ProofLib.BV.Lin.LinM.run' (ProofLib.BV.Lin.linearize eExp)
      | pure (eExp, (0 : Int))
    let off := toSigned64 lf.const
    if lf.terms.isEmpty then
      pure (mkBV64Lit 0, off)
    else if lf.terms.size == 1 && toSigned64 lf.terms[0]!.2 == 1 then
      pure (lf.terms[0]!.1, off)
    else
      let sorted := lf.terms.qsort fun (a1, c1) (a2, c2) =>
        let s1 := toSigned64 c1
        let s2 := toSigned64 c2
        if s1 == 1 && s2 != 1 then true
        else if s1 != 1 && s2 == 1 then false
        else a1.lt a2
      let mut acc? : Option Expr := none
      for (atom, cRaw) in sorted do
        let sc := toSigned64 cRaw
        if sc == 0 then continue
        let mag := sc.natAbs
        let term ← if mag == 1 then pure atom else mkAppM ``HMul.hMul #[atom, mkBV64Lit mag]
        acc? ← match acc? with
          | none => if sc < 0 then some <$> mkAppM ``Neg.neg #[term] else pure (some term)
          | some prev =>
            if sc < 0 then some <$> mkAppM ``HSub.hSub #[prev, term]
            else some <$> mkAppM ``HAdd.hAdd #[prev, term]
      pure (acc?.getD (mkBV64Lit 0), off)
  let canonExpr ← mkCanonAddrExpr root byteOff
  let eqProof? ← do
    if e == canonExpr then
      pure none
    else if eExp == canonExpr then
      match hExp? with
      | some p => pure (some p)
      | none => pure (some (← mkExpectedTypeHint (← mkEqRefl canonExpr) (← mkEq e canonExpr)))
    else
      let (eFold, hFold?) ← foldBV64LitChain eExp
      if eFold == canonExpr then
        let h12? ← chainEq? hExp? hFold?
        match h12? with
        | some p => pure (some (← mkExpectedTypeHint p (← mkEq e canonExpr)))
        | none => pure (some (← mkExpectedTypeHint (← mkEqRefl canonExpr) (← mkEq e canonExpr)))
      else if let some pLin ← ProofLib.BV.Lin.proveEq? eExp canonExpr then
        let pTot ← match hExp? with | some h1 => mkEqTrans h1 pLin | none => pure pLin
        pure (some (← mkExpectedTypeHint pTot (← mkEq e canonExpr)))
      else
        throwError "ProofLib.Sep.Addr: failed to prove address canonicalization {e} = {canonExpr}"
  let res : LinAddr64 := { root, byteOff, canonExpr, eqProof? }
  cacheRef.modify (·.insert e res)
  return res

/-- Prove `lhs = rhs` between two 64-bit address expressions via `canonAddr64` + `BV.Lin.proveEq?`
    without calling `whnf` `isDefEq` across unequal symbolic offsets. -/
def proveAddrEqFast? (ctx : CtxFacts) (cacheRef : IO.Ref (Std.HashMap Expr LinAddr64))
    (lhs rhs : Expr) : MetaM (Option Expr) := do
  let lhs ← instantiateMVars lhs
  let rhs ← instantiateMVars rhs
  if lhs == rhs then
    return some (← mkEqRefl lhs)
  let la? ← try some <$> canonAddr64 ctx cacheRef lhs catch _ => pure none
  let ra? ← try some <$> canonAddr64 ctx cacheRef rhs catch _ => pure none
  if let (some la, some ra) := (la?, ra?) then
    if la.canonExpr == ra.canonExpr then
      let pL ← match la.eqProof? with
        | some p => pure p
        | none => mkExpectedTypeHint (← mkEqRefl la.canonExpr) (← mkEq lhs la.canonExpr)
      let pR ← match ra.eqProof? with
        | some p => mkEqSymm p
        | none => mkExpectedTypeHint (← mkEqRefl ra.canonExpr) (← mkEq ra.canonExpr rhs)
      return some (← mkEqTrans pL pR)
    if let some pMid ← ProofLib.BV.Lin.proveEq? la.canonExpr ra.canonExpr then
      let pL ← match la.eqProof? with
        | some p => pure p
        | none => mkExpectedTypeHint (← mkEqRefl la.canonExpr) (← mkEq lhs la.canonExpr)
      let pR ← match ra.eqProof? with
        | some p => mkEqSymm p
        | none => mkExpectedTypeHint (← mkEqRefl ra.canonExpr) (← mkEq ra.canonExpr rhs)
      return some (← mkEqTrans (← mkEqTrans pL pMid) pR)
  ProofLib.BV.Lin.proveEq? lhs rhs

/-- Prove `aCanon + BitVec.ofNat 64 n = bCanon` in $O(1)$ for adjacent canonical addresses `(root, off)`
    and `(root, off + n)` (`0 ≤ n < 2^63`). -/
def proveCanonAddrStep (root : Expr) (off : Int) (n : Nat) (aCanon bCanon : Expr) : MetaM Expr := do
  let nLit := mkBV64Lit n
  let goalTy ← mkEq (← mkAppM ``HAdd.hAdd #[aCanon, nLit]) bCanon
  if n == 0 then
    let p ← mkAppM ``BitVec.add_zero #[aCanon]
    return ← mkExpectedTypeHint p goalTy
  if off == 0 then
    return ← mkExpectedTypeHint (← mkEqRefl bCanon) goalTy
  if off > 0 then
    let cSum := mkBV64Lit (off.toNat + n)
    let p ← mkAppM ``bitvec64_add_add_fold #[root, mkBV64Lit off.toNat, nLit, cSum, ← mkEqRefl cSum]
    return ← mkExpectedTypeHint p goalTy
  let aMag := (-off).toNat
  let aLit := mkBV64Lit aMag
  let nextOff := off + (n : Int)
  if nextOff == 0 then
    let p ← mkAppM ``bitvec64_sub_add_zero #[root, aLit, nLit, ← mkEqRefl aLit]
    return ← mkExpectedTypeHint p goalTy
  else if nextOff < 0 then
    let cRem := mkBV64Lit ((-nextOff).toNat)
    let p ← mkAppM ``bitvec64_sub_add_fold_sub #[root, aLit, nLit, cRem, ← mkEqRefl cRem]
    return ← mkExpectedTypeHint p goalTy
  else
    let cPos := mkBV64Lit nextOff.toNat
    let p ← mkAppM ``bitvec64_sub_add_fold_add #[root, aLit, nLit, cPos, ← mkEqRefl cPos]
    return ← mkExpectedTypeHint p goalTy

/-- Recognized primitive spatial heads (never unfolded as user bundles). -/
def isKnownSpatialHead (fn : Name) : Bool :=
  fn == ``Arm64.pointsTo8 || fn == ``Arm64.pointsTo16 || fn == ``Arm64.pointsTo32 ||
  fn == ``Arm64.pointsTo64 || fn == ``Arm64.pointsTo128 ||
  fn == ``Arm64.pointsTo8RO || fn == ``Arm64.pointsTo16RO || fn == ``Arm64.pointsTo32RO ||
  fn == ``Arm64.pointsTo64RO || fn == ``Arm64.pointsTo128RO ||
  fn == ``Arm64.pointsToBytes || fn == ``Arm64.pointsToBytesRO ||
  fn == ``Arm64.pointsToWords64 || fn == ``Arm64.pointsToWords64RO ||
  fn == ``ProofLib.cells || fn == ``ProofLib.stackAt ||
  fn == ``Arm64.stackFrameAt || fn == ``Arm64.stackFrame ||
  fn == ``Arm64.stackFrame16At || fn == ``Arm64.stackFrame32At ||
  fn == ``Arm64.stackFrame16 || fn == ``Arm64.stackFrame32 ||
  fn == ``Arm64.memRegion || fn == ``Arm64.memRegionProtNone || fn == ``Arm64.memRegionLazy ||
  fn == ``SepProp.emp || fn == ``SepProp.pure || fn == ``SepProp.sepConj ||
  fn == ``SepProp.sepExists || fn == ``SepProp.sepImp ||
  fn == ``Arm64.Allocator.live || fn == ``Arm64.AllocatorOom.live ||
  fn == ``Arm64.Allocator.pool || fn == ``Arm64.AllocatorOom.pool

/-- Check whether `e` is a pure spatial bundle (`∗`, `∃∗`, `⌜·⌝`, `emp`, or spatial primitives, depth ≤ 4). -/
partial def isSpatialBundleBody (e : Expr) (depth : Nat) : MetaM Bool := do
  let e := e.consumeMData.headBeta
  if e.isAppOfArity ``SepProp.sepConj 2 then
    return (← isSpatialBundleBody (e.getArg! 0) depth) && (← isSpatialBundleBody (e.getArg! 1) depth)
  if e.isAppOfArity ``SepProp.sepExists 2 then
    match (e.getArg! 1).consumeMData with
    | .lam n ty body bi =>
      return ← withLocalDecl n bi ty fun fv => isSpatialBundleBody (body.instantiate1 fv) depth
    | _ => return false
  let some fn := e.getAppFn.constName? | return false
  if isKnownSpatialHead fn then return true
  if depth >= 4 then return false
  let some eUnf ← unfoldDefinition? e | return false
  isSpatialBundleBody eUnf (depth + 1)

/-- Auto-unfold reducible / `@[expose]` spatial bundle definitions (depth ≤ 4) without `@[sep_unfold]`. -/
partial def autoUnfoldBundles (e : Expr) (depth : Nat := 0) : MetaM Expr := do
  let e := e.consumeMData.headBeta
  if e.isAppOfArity ``SepProp.sepConj 2 then
    let l ← autoUnfoldBundles (e.getArg! 0) depth
    let r ← autoUnfoldBundles (e.getArg! 1) depth
    return ProofLib.SepSolver.mkSep l r
  let some fn := e.getAppFn.constName? | return e
  if isKnownSpatialHead fn || depth >= 4 then return e
  let some eUnf ← unfoldDefinition? e | return e
  if ← isSpatialBundleBody eUnf (depth + 1) then
    autoUnfoldBundles eUnf (depth + 1)
  else
    return e

/-- Push prenex `∃∗ x, A ∗ B` down to single-conjunct `(∃∗ x, addr ↦_w x)` when `x` occurs in one side. -/
partial def pushPrenexSepExists (e : Expr) : MetaM (Expr × Option Expr) := do
  let e := e.consumeMData.headBeta
  if e.isAppOfArity ``SepProp.sepConj 2 then
    let a := e.getArg! 0
    let b := e.getArg! 1
    let (a', pa?) ← pushPrenexSepExists a
    let (b', pb?) ← pushPrenexSepExists b
    if pa?.isNone && pb?.isNone then return (e, none)
    let e' := ProofLib.SepSolver.mkSep a' b'
    let pa ← match pa? with | some p => pure p | none => mkEqRefl a'
    let pb ← match pb? with | some p => pure p | none => mkEqRefl b'
    let prf ← mkCongr (← mkCongrArg (mkConst ``SepProp.sepConj) pa) pb
    return (e', some prf)
  if e.isAppOfArity ``SepProp.sepExists 2 then
    let α := e.getArg! 0
    let lam := (e.getArg! 1).consumeMData
    if let .lam n ty body bi := lam then
      let u ← getLevel α
      let (innerExpr, pInner?) ← withLocalDecl n bi ty fun fv => do
        let inst := body.instantiate1 fv
        let (inst', pInst?) ← pushPrenexSepExists inst
        let lam' ← mkLambdaFVars #[fv] inst'
        let ex' := mkApp2 (mkConst ``SepProp.sepExists [u]) α lam'
        let pCongr? ← match pInst? with
          | none => pure none
          | some pI =>
            let hFun ← mkLambdaFVars #[fv] pI
            pure (some (mkApp4 (mkConst ``ProofLib.sepExists_congr [u]) α lam lam' hFun))
        return (ex', pCongr?)
      let rec peelOne (curEx : Expr) : MetaM (Expr × Option Expr) := do
        if !curEx.isAppOfArity ``SepProp.sepExists 2 then return (curEx, none)
        let α1 := curEx.getArg! 0
        let u1 ← getLevel α1
        let .lam n1 ty1 b1 bi1 := (curEx.getArg! 1).consumeMData | return (curEx, none)
        let b1 := b1.consumeMData.headBeta
        if !b1.isAppOfArity ``SepProp.sepConj 2 then return (curEx, none)
        let lBody := b1.getArg! 0
        let rBody := b1.getArg! 1
        let inL := lBody.hasLooseBVar 0
        let inR := rBody.hasLooseBVar 0
        if inL && !inR then
          let rClosed := rBody.lowerLooseBVars 1 1
          let pLam := Expr.lam n1 ty1 lBody bi1
          let stepPrf ← mkEqSymm (mkApp3 (mkConst ``sepExists_sepConj_left [u1]) α1 pLam rClosed)
          let lhsEx := mkApp2 (mkConst ``SepProp.sepExists [u1]) α1 pLam
          let (lhsEx', pSub?) ← peelOne lhsEx
          let resExpr := ProofLib.SepSolver.mkSep lhsEx' rClosed
          let pTot ← match pSub? with
            | none => pure stepPrf
            | some ps =>
              let fL := Expr.lam `x (mkConst ``SepProp) (ProofLib.SepSolver.mkSep (.bvar 0) rClosed) .default
              mkEqTrans stepPrf (← mkCongrArg fL ps)
          return (resExpr, some pTot)
        else if !inL && inR then
          let lClosed := lBody.lowerLooseBVars 1 1
          let qLam := Expr.lam n1 ty1 rBody bi1
          let stepPrf ← mkEqSymm (mkApp3 (mkConst ``sepExists_sepConj_right [u1]) α1 lClosed qLam)
          let rhsEx := mkApp2 (mkConst ``SepProp.sepExists [u1]) α1 qLam
          let (rhsEx', pSub?) ← peelOne rhsEx
          let resExpr := ProofLib.SepSolver.mkSep lClosed rhsEx'
          let pTot ← match pSub? with
            | none => pure stepPrf
            | some ps =>
              let fR := Expr.lam `x (mkConst ``SepProp) (ProofLib.SepSolver.mkSep lClosed (.bvar 0)) .default
              mkEqTrans stepPrf (← mkCongrArg fR ps)
          return (resExpr, some pTot)
        else
          return (curEx, none)
      let (peeled, pPeel?) ← peelOne innerExpr
      return (peeled, ← chainEq? pInner? pPeel?)
  return (e, none)

end

end ProofLib.Sep
