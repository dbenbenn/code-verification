/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean.Elab.Term
public meta import Lean.Elab.Term.TermElabM

/-!
# Compile-Time Binary Slice Elaborator

Defines the `include_bytes% "path" off len` term elaborator, which splices bytes `[off, off + len)`
of a companion binary file into a computable `List (BitVec 8)` literal at elaboration time, along
with `IncludeBytes.cons16` and shared `BitVec` and `List` `Expr` builders (`IncludeBytes.bv8Exprs`,
`IncludeBytes.toListExpr`). Slices exceeding 4096 bytes are split into 4 KiB auxiliary chunk
definitions built with `IncludeBytes.cons16` so LCNF/IR compilation scales linearly in binary size.
Kept separate from `Arm64.lean` so core specifications do not import `Lean.Elab.Term`.
-/

@[expose] public section

namespace Arm64

/-- Prepend 16 bytes onto `rest`, keeping LCNF/IR block sizes compact in chunked `include_bytes%`
    definitions while unfolding in one step to `List.cons`. -/
def IncludeBytes.cons16
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8)
    (rest : List (BitVec 8)) : List (BitVec 8) :=
  b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
  b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: rest

meta section

open Lean Elab Term

/-- Single-entry `(path, bytes)` cache avoiding repeated full-file reads across multiple
    `include_bytes%` slices in the same file. -/
initialize includeBytesCache : IO.Ref (Option (System.FilePath × ByteArray)) ← IO.mkRef none

/-- Read bytes `[off, off + len)` of `path`, resolved relative to the current Lean file's directory. -/
def IncludeBytes.read (path : String) (off len : Nat) : TermElabM ByteArray := do
  let p : System.FilePath := path
  let dir := (System.FilePath.mk (← getFileName)).parent.getD "."
  let resolved := if p.isAbsolute then p else dir / p
  let bytes ← match ← includeBytesCache.get with
    | some (cachedPath, cachedBytes) =>
      if cachedPath == resolved then
        pure cachedBytes
      else
        let b ← IO.FS.readBinFile resolved
        includeBytesCache.set (some (resolved, b))
        pure b
    | none =>
      let b ← IO.FS.readBinFile resolved
      includeBytesCache.set (some (resolved, b))
      pure b
  if off + len > bytes.size then
    throwError "include_bytes%: {resolved} has {bytes.size} bytes, but bytes \
      [{off}, {off + len}) were requested"
  return bytes.extract off (off + len)

/-- Shared `BitVec 8` `Expr` constants for byte values `0..255` so slices share DAG nodes. -/
def IncludeBytes.bv8Exprs : Array Expr :=
  let ofNat := mkApp (mkConst ``BitVec.ofNat) (mkNatLit 8)
  (Array.range 256).map fun b => mkApp ofNat (mkNatLit b)

/-- `List (BitVec 8)` literal of `bs`, built from `IncludeBytes.bv8Exprs`. -/
def IncludeBytes.toListExpr (bs : ByteArray) : Expr := Id.run do
  let bv8 := mkApp (mkConst ``BitVec) (mkNatLit 8)
  let cons := mkApp (mkConst ``List.cons [Level.zero]) bv8
  let mut acc := mkApp (mkConst ``List.nil [Level.zero]) bv8
  for i in [0:bs.size] do
    acc := mkApp2 cons IncludeBytes.bv8Exprs[(bs.get! (bs.size - 1 - i)).toNat]! acc
  return acc

def IncludeBytes.bv64Expr (n : Nat) : Expr :=
  mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit n)

def IncludeBytes.listExpr (ty : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [Level.zero]) ty x acc)
    (mkApp (mkConst ``List.nil [Level.zero]) ty)

/-- Maximum byte length elaborated inline before splitting into auxiliary 4 KiB chunk definitions. -/
def IncludeBytes.chunkSize : Nat := 4096

/-- Prepend `bs` onto `tail` (`: List (BitVec 8)`) using `IncludeBytes.cons16` for 16-byte groups
    and `List.cons` for any `< 16`-byte remainder. -/
def IncludeBytes.toCons16TailExpr (bs : ByteArray) (tail : Expr) : Expr := Id.run do
  let bv8 := mkApp (Lean.mkConst ``BitVec) (mkNatLit 8)
  let cons := mkApp (Lean.mkConst ``List.cons [Level.zero]) bv8
  let c16 := Lean.mkConst ``IncludeBytes.cons16
  let rem := bs.size % 16
  let mut acc := tail
  for k in [0:rem] do
    let b := (bs.get! (bs.size - 1 - k)).toNat
    acc := mkApp2 cons IncludeBytes.bv8Exprs[b]! acc
  let mut pos := bs.size - rem
  for _ in [0 : bs.size / 16] do
    pos := pos - 16
    let mut f := c16
    for j in [0:16] do
      let b := (bs.get! (pos + j)).toNat
      f := mkApp f IncludeBytes.bv8Exprs[b]!
    acc := mkApp f acc
  return acc

/-- Elaborate `bs` as `IncludeBytes.toListExpr bs` when `bs.size ≤ 4096`, or as a right-to-left
    chain of 4 KiB auxiliary `List (BitVec 8)` definitions built with `IncludeBytes.cons16`. -/
def IncludeBytes.elabBytes (bs : ByteArray) : TermElabM Expr := do
  let chunk := IncludeBytes.chunkSize
  if bs.size ≤ chunk then
    return IncludeBytes.toListExpr bs
  let bv8 := mkApp (Lean.mkConst ``BitVec) (mkNatLit 8)
  let ty := mkApp (Lean.mkConst ``List [Level.zero]) bv8
  let mut tail := mkApp (Lean.mkConst ``List.nil [Level.zero]) bv8
  let n := (bs.size + chunk - 1) / chunk
  for i in [0 : n - 1] do
    let k := n - 1 - i
    let slice := bs.extract (k * chunk) (Nat.min bs.size ((k + 1) * chunk))
    let val := IncludeBytes.toCons16TailExpr slice tail
    let nm ← Lean.mkAuxDeclName (kind := `_includeBytes)
    let env ← getEnv
    addAndCompile (.defnDecl {
      name := nm
      levelParams := []
      type := ty
      value := val
      hints := .regular (getMaxHeight env val + 1)
      safety := .safe
    })
    tail := Lean.mkConst nm
  return IncludeBytes.toCons16TailExpr (bs.extract 0 chunk) tail

/-- `include_bytes% "path" off len`: bytes `[off, off + len)` of `path` as a
    `List (BitVec 8)` literal. -/
syntax (name := includeBytes) "include_bytes% " str ppSpace num ppSpace num : term

@[term_elab includeBytes]
def elabIncludeBytes : TermElab := fun stx _ => do
  match stx with
  | `(include_bytes% $path:str $off:num $len:num) =>
    let bs ← IncludeBytes.read path.getString off.getNat len.getNat
    IncludeBytes.elabBytes bs
  | _ => throwUnsupportedSyntax

end

end Arm64
end
