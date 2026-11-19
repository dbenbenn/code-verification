/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.CodeLookup
public import ProofLib.ProgramReflection
public import ProofLib.GenDecodes
public import ProofLib.VCGen
public meta import Lean
public meta import ProofLib.SepLogic.CodeLookup
public meta import ProofLib.ProgramReflection
public meta import ProofLib.GenDecodes
public meta import ProofLib.VCGen

/-!
# Closed Numeral, Page, and `WordTree` Lookup Utilities

Provides elaboration-time closed `Nat`/`BitVec` numerals (`num%`, `bv%`, `pageOf`, `page%`),
`WordTree` cross-reference lookups (`code_xref%`), and `gen_decodes` / identifier helpers.
-/

public section

namespace CryptoVerification.CodeLayout

open Lean Meta Elab Term Command Arm64 ProofLib.ProgramReflection

public meta section

/-! ## Numerals -/

partial def natLit? : Expr → Option Nat
  | .lit (.natVal n) => some n
  | .mdata _ e => natLit? e
  | e => if e.isAppOfArity ``OfNat.ofNat 3 then natLit? (e.getArg! 1) else none

/-- Evaluate a closed `Nat` term to a numeral.

`withSynthesize` scopes the synthesis to the mvars created while elaborating `t`. -/
def evalNat (t : Term) (what : String) : TermElabM Nat := do
  let e ← withSynthesize <| elabTermEnsuringType t (mkConst ``Nat)
  let e ← instantiateMVars e
  if e.hasMVar || e.hasFVar then
    throwError "{what}: {e} is not a closed `Nat` term"
  let r ← withTransparency .all <| reduce e
  let some n := natLit? r
    | throwError "{what}: {e} does not reduce to a numeral (got {r})"
  return n

/-- `num% t`: the closed `Nat` term `t` evaluated and elaborated as a bare numeral at the expected
    type (the same term the numeral itself elaborates to, also at `BitVec w`). -/
syntax:max (name := numStx) "num% " term:max : term

@[term_elab numStx] def elabNum : TermElab := fun stx expectedType? => do
  match stx with
  | `(num% $t) =>
    let n ← evalNat t "num%"
    elabTerm (Syntax.mkNumLit (toString n)) expectedType?
  | _ => throwUnsupportedSyntax

/-- `bv% t`: `BitVec.ofNat 64 (num% t)`, the term `n#64` elaborates to. -/
macro:max "bv% " t:term:max : term => `(BitVec.ofNat 64 (num% $t))

end

/-- Start of the 4 KiB page of `a` (what `adrp` computes, relative to a page-aligned base). -/
@[expose, reducible] def pageOf (a : Nat) : Nat := a / 4096 * 4096

public meta section

/-- `page% t`: `pageOf t` without opening the namespace (for use inside `num%` / `bv%`). -/
macro:max "page% " t:term:max : term => `(($t) / 4096 * 4096)

/-! ## `WordTree` cross-references and decode generators -/

def whnfAll (e : Expr) : MetaM Expr := withTransparency .all (whnf e)

partial def strOf (e : Expr) : MetaM String := do
  match e with
  | .lit (.strVal s) => return s
  | .mdata _ e => strOf e
  | _ =>
    match ← whnfAll e with
    | .lit (.strVal s) => return s
    | e' => throwError "code layout: expected a string literal, got {e'}"

/-- The 4 bytes of the instruction at code offset `off` of the tree constant `tree`. -/
def quadOf (tree : Name) (off : Nat) : MetaM (Nat × Nat × Nat × Nat) := do
  ProofLib.GenDecodes.quadOfTreeVal (← ProofLib.GenDecodes.treeValueOf tree) off

/-- The 32-bit instruction word at code offset `off` of the tree constant `tree`. -/
def wordAt (tree : Name) (off : Nat) : MetaM Nat := do
  let (b0, b1, b2, b3) ← quadOf tree off
  return b0 + 0x100 * b1 + 0x00010000 * b2 + 0x1000000 * b3

def sext (v bits : Nat) : Int :=
  if v ≥ 2 ^ (bits - 1) then (v : Int) - 2 ^ bits else v

/-- The target of the PC-relative instruction at `pc`: the address of a `b` / `bl` / `adr`, the
    page of an `adrp`. -/
def pcRelTarget (tree : Name) (pc : Nat) : MetaM Int := do
  let w ← wordAt tree pc
  let imm21 := (((w >>> 5) &&& 0x0007FFFF) <<< 2) ||| ((w >>> 29) &&& 3)
  if w &&& 0x7C000000 == 0x14000000 then
    return pc + 4 * sext (w &&& 0x3FFFFFF) 26
  else if w &&& 0x9F000000 == 0x90000000 then
    return (pc / 4096 * 4096 : Nat) + 4096 * sext imm21 21
  else if w &&& 0x9F000000 == 0x10000000 then
    return pc + sext imm21 21
  else
    throwError "code_xref%: the instruction at {pc} is not `adrp`, `adr`, `b` or `bl`"

/-- `(base register, low-12 byte offset)` of the `add` (immediate, unshifted) or `ldr` / `str`
    (unsigned offset) at `pc`. -/
def lo12At (tree : Name) (pc : Nat) : MetaM (Nat × Nat) := do
  let w ← wordAt tree pc
  let rn := (w >>> 5) &&& 31
  let imm12 := (w >>> 10) &&& 0xFFF
  if w &&& 0x7F800000 == 0x11000000 && (w >>> 22) &&& 1 == 0 then
    return (rn, imm12)
  else if w &&& 0x3B000000 == 0x39000000 then
    let (size, v, opc) := (w >>> 30, (w >>> 26) &&& 1, (w >>> 22) &&& 3)
    return (rn, imm12 * (if v == 1 && size == 0 && opc &&& 2 != 0 then 16 else 2 ^ size))
  else
    throwError "code_xref%: the instruction at {pc} is not an unshifted `add` (immediate) or an \
      unsigned-offset `ldr` / `str`"

/-- The address the code at `pc` refers to. -/
def xrefTarget (tree : Name) (pc : Nat) (pc₂? : Option Nat) : MetaM Nat := do
  let t ← pcRelTarget tree pc
  let t ← match pc₂? with
    | none => pure t
    | some pc₂ =>
      let w ← wordAt tree pc
      unless w &&& 0x9F000000 == 0x90000000 do
        throwError "code_xref%: the instruction at {pc} is not `adrp`"
      let (rn, lo) ← lo12At tree pc₂
      unless rn == w &&& 31 do
        throwError "code_xref%: the instruction at {pc₂} does not use the register the `adrp` \
          at {pc} writes"
      pure (t + lo)
  unless t ≥ 0 do throwError "code_xref%: negative target {t}"
  return t.toNat

/-- `code_xref% tree pc` / `code_xref% tree pc pc₂`: the address the code of the `WordTree`
    constant `tree` refers to at `pc`. -/
syntax:max (name := codeXrefStx) "code_xref% " ident term:max (ppSpace term:max)? : term

@[term_elab codeXrefStx] def elabCodeXref : TermElab := fun stx expectedType? => do
  match stx with
  | `(code_xref% $t:ident $a:term $[$b?:term]?) =>
    let tree ← realizeGlobalConstNoOverloadWithInfo t
    let aVal ← evalNat a "code_xref%"
    let bVal? ← b?.mapM (evalNat · "code_xref%")
    let v ← xrefTarget tree aVal bVal?
    elabTerm (Syntax.mkNumLit (toString v)) expectedType?
  | _ => throwUnsupportedSyntax

def decodeStmtOfTreeVal (tree : Name) (treeVal : Expr) (off : Nat) (raw : Bool := false) :
    MetaM Expr := do
  let (w, rhs?) ← ProofLib.GenDecodes.instrRhs? treeVal off raw
  let some rhs := rhs?
    | throwError "gen_decodes: the word {w} at offset {off} does not decode"
  return ProofLib.GenDecodes.decodeStmtOf tree off rhs

def decodeStmt (tree : Name) (off : Nat) (raw : Bool := false) : MetaM Expr := do
  decodeStmtOfTreeVal tree (← ProofLib.GenDecodes.treeValueOf tree) off raw

syntax "(" term ")" : decodeRange
syntax "(" term ")" " → " "(" term ")" : decodeRange
syntax num " → " "(" term ")" : decodeRange
syntax "(" term ")" " → " num : decodeRange
syntax &"raw " "(" term ")" : decodeRange
syntax &"raw " num " → " num : decodeRange
syntax &"raw " "(" term ")" " → " "(" term ")" : decodeRange
syntax &"raw " num " → " "(" term ")" : decodeRange
syntax &"raw " "(" term ")" " → " num : decodeRange

def rangeBounds (a b : Nat) (r : Syntax) (raw : Bool := false) :
    CommandElabM (Array (Nat × Bool)) := do
  unless a ≤ b && (b - a) % 4 == 0 do
    throwErrorAt r "gen_decodes: bad range {a} → {b}"
  return (List.range ((b - a) / 4 + 1)).toArray.map (a + 4 * ·, raw)

def rangeOffsets (r : TSyntax `decodeRange) : CommandElabM (Array (Nat × Bool)) := do
  match r with
  | `(decodeRange| $a:num) => return #[(a.getNat, false)]
  | `(decodeRange| raw $a:num) => return #[(a.getNat, true)]
  | `(decodeRange| $a:num → $b:num) => rangeBounds a.getNat b.getNat r
  | `(decodeRange| raw $a:num → $b:num) => rangeBounds a.getNat b.getNat r true
  | `(decodeRange| ($a:term)) =>
    return #[(← liftTermElabM <| evalNat a "gen_decodes", false)]
  | `(decodeRange| raw ($a:term)) =>
    return #[(← liftTermElabM <| evalNat a "gen_decodes", true)]
  | `(decodeRange| ($a:term) → ($b:term)) =>
    let na ← liftTermElabM <| evalNat a "gen_decodes"
    let nb ← liftTermElabM <| evalNat b "gen_decodes"
    rangeBounds na nb r
  | `(decodeRange| raw ($a:term) → ($b:term)) =>
    let na ← liftTermElabM <| evalNat a "gen_decodes"
    let nb ← liftTermElabM <| evalNat b "gen_decodes"
    rangeBounds na nb r true
  | `(decodeRange| $a:num → ($b:term)) =>
    let nb ← liftTermElabM <| evalNat b "gen_decodes"
    rangeBounds a.getNat nb r
  | `(decodeRange| raw $a:num → ($b:term)) =>
    let nb ← liftTermElabM <| evalNat b "gen_decodes"
    rangeBounds a.getNat nb r true
  | `(decodeRange| ($a:term) → $b:num) =>
    let na ← liftTermElabM <| evalNat a "gen_decodes"
    rangeBounds na b.getNat r
  | `(decodeRange| raw ($a:term) → $b:num) =>
    let na ← liftTermElabM <| evalNat a "gen_decodes"
    rangeBounds na b.getNat r true
  | _ => throwUnsupportedSyntax

@[command_elab ProofLib.GenDecodes.genDecodesStx] def elabGenDecodes : CommandElab := fun stx => do
  match stx with
  | `($mods:declModifiers gen_decodes $tree:ident $pfx:ident [$rs:decodeRange,*]) =>
    let mut offs := #[]
    for r in rs.getElems do offs := offs ++ (← rangeOffsets r)
    let modifiers ← elabModifiers mods
    let isPublic := (← getScope).isPublic
    let pfxStr := pfx.getId.eraseMacroScopes.toString
    liftTermElabM do
      let treeName ← realizeGlobalConstNoOverloadWithInfo tree
      let treeVal ← ProofLib.GenDecodes.treeValueOf treeName
      for (off, raw) in offs do
        let hex := String.ofList (Nat.toDigits 16 off)
        let short := Name.mkSimple s!"{pfxStr}_decode_0x{hex}"
        let declName ← withExporting (isExporting := isPublic) <|
          mkDeclName (← getCurrNamespace) modifiers short
        let ty ← decodeStmtOfTreeVal treeName treeVal off raw
        let lhs := ty.appFn!.appArg!
        ProofLib.GenDecodes.addThm declName.1 ty
          (mkApp2 (mkConst ``Eq.refl [.succ .zero]) ProofLib.GenDecodes.optInstr lhs)
        applyAttributesAt declName.1 modifiers.attrs .afterTypeChecking
        applyAttributesAt declName.1 modifiers.attrs .afterCompilation
  | _ => throwUnsupportedSyntax

end

end CryptoVerification.CodeLayout
