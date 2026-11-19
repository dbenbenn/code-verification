/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.Placed
public meta import ProofLib.Testing.Perf.Budget

/-!
# Placed Symbol Index Performance Tests

Heartbeat-budget tests for `Obj.MultiPlacedLib.SymIndex` (`gen_multi_sym_index`) on the 600-block
`alphaMulti600` synthetic fixture.
-/

set_option autoImplicit false

@[expose] public section

namespace Examples.Testing.ProofLib.Perf.RelocAndPlacedScale

open Arm64 Arm64.Obj _root_.ProofLib _root_.ProofLib.ProgramReflection

/-- Realistic 76-character mangled symbol name sharing a long common prefix across all 600 entries. -/
meta def mkAlphaSymName (i : Nat) : String :=
  s!"_ZN12alpha_widget14module_section18dispatch_entry_{1000 + i}17h0123456789abcdefE"

def alphaSym0 : String :=
  "_ZN12alpha_widget14module_section18dispatch_entry_100017h0123456789abcdefE"

def alphaSym599 : String :=
  "_ZN12alpha_widget14module_section18dispatch_entry_159917h0123456789abcdefE"

section BuildFixtures
open Lean Elab Command Meta

private meta def mkPrebuiltDef (declName : Name) (ty val : Expr) : CommandElabM Unit :=
  liftTermElabM do
    let env ← getEnv
    addDecl (.defnDecl {
      name := declName
      levelParams := []
      type := ty
      value := val
      hints := .regular (getMaxHeight env val + 1)
      safety := .safe
    })

private meta def mkBitVecLit (w v : Nat) : Expr :=
  mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit w) (mkNatLit v)

private meta def mkChunkedBytesExpr (bytes : Array Nat) : MetaM Expr := do
  let u8Ty := mkApp (Lean.mkConst ``BitVec) (mkNatLit 8)
  let listU8Ty := mkApp (Lean.mkConst ``List [0]) u8Ty
  let chunkSz := 256
  if bytes.size ≤ chunkSz then
    mkListLit u8Ty (bytes.toList.map (mkBitVecLit 8))
  else
    let mut chunks : Array Expr := #[]
    let mut i := 0
    while i < bytes.size do
      let stop := Nat.min (i + chunkSz) bytes.size
      let slice := (bytes.extract i stop).toList.map (mkBitVecLit 8)
      chunks := chunks.push (← mkListLit u8Ty slice)
      i := stop
    let chunkList ← mkListLit listU8Ty chunks.toList
    return mkApp2 (Lean.mkConst ``List.flatten [0]) u8Ty chunkList

private meta def pushWordLE (acc : Array Nat) (w : UInt32) : Array Nat :=
  let n := w.toNat
  acc.push (n &&& 0xff)
    |>.push ((n >>> 8) &&& 0xff)
    |>.push ((n >>> 16) &&& 0xff)
    |>.push ((n >>> 24) &&& 0xff)

private meta def mkCall26RelocExpr (off : Nat) (sym : String) : Expr :=
  mkApp5 (Lean.mkConst ``RelocEntry.mk)
    (mkNatLit off) (Lean.mkConst ``RelocKind.call26) (mkStrLit sym)
    (toExpr (0 : Int)) (toExpr false)

run_cmd do
  let ns ← getCurrNamespace
  let sym0 := mkAlphaSymName 0
  -- Build 2,000-instruction (`8,000`-byte) body with 80 sorted `.call26` relocations for #599:
  let mut bigBytes : Array Nat := Array.mkEmpty 8000
  let mut bigRelocExprs : Array Expr := Array.mkEmpty 80
  for j in [:2000] do
    if j == 1999 then
      bigBytes := pushWordLE bigBytes 0xd65f03c0
    else if j % 25 == 0 then
      bigBytes := pushWordLE bigBytes 0x94000007
      bigRelocExprs := bigRelocExprs.push (mkCall26RelocExpr (4 * j) sym0)
    else
      bigBytes := pushWordLE bigBytes 0x91000400

  let u8Ty := mkApp (Lean.mkConst ``BitVec) (mkNatLit 8)
  let strTy := Lean.mkConst ``String
  let relocTy := Lean.mkConst ``RelocEntry
  let codeBlockTy := Lean.mkConst ``CodeBlock
  let symDataTy := Lean.mkConst ``SymDataInfo
  let symPairTy := mkApp2 (Lean.mkConst ``Prod [0, 0]) strTy (Lean.mkConst ``Nat)

  let (blockListExpr, dataListExpr, exportsExpr) ← liftTermElabM do
    let smallBytes := pushWordLE (pushWordLE #[] 0xd2800000) 0xd65f03c0
    let smallCodeExpr ← mkChunkedBytesExpr smallBytes
    let emptyRelocsExpr ← mkListLit relocTy []
    let emptyExternsExpr ← mkListLit strTy []
    let emptyDataRelocsExpr ← mkListLit relocTy []
    let bigCodeExpr ← mkChunkedBytesExpr bigBytes
    let bigRelocsExpr ← mkListLit relocTy bigRelocExprs.toList

    let mut blocks : Array Expr := Array.mkEmpty 600
    for i in [:600] do
      let s := mkAlphaSymName i
      let sExpr := mkStrLit s
      let (cE, rE) := if i == 599 then (bigCodeExpr, bigRelocsExpr) else (smallCodeExpr, emptyRelocsExpr)
      let sp := mkApp4 (Lean.mkConst ``Prod.mk [0, 0]) strTy (Lean.mkConst ``Nat) sExpr (mkNatLit 0)
      let symsE ← mkListLit symPairTy [sp]
      blocks := blocks.push (mkApp6 (Lean.mkConst ``CodeBlock.mk)
        cE (mkNatLit 4) symsE rE emptyExternsExpr emptyExternsExpr)

    let mut datas : Array Expr := Array.mkEmpty 32
    for k in [:32] do
      let ds := mkStrLit s!"alpha_ro_{k}"
      let bs ← mkListLit u8Ty [mkBitVecLit 8 k]
      datas := datas.push (mkApp6 (Lean.mkConst ``SymDataInfo.mk)
        ds (mkNatLit 8) (toExpr true) bs (mkNatLit 0) emptyDataRelocsExpr)

    let listBlockTy := mkApp (Lean.mkConst ``List [0]) codeBlockTy
    let mut blkChunks : Array Expr := #[]
    let mut bi := 0
    while bi < 600 do
      let stop := Nat.min (bi + 200) 600
      blkChunks := blkChunks.push (← mkListLit codeBlockTy (blocks.extract bi stop).toList)
      bi := stop
    let blockListExpr := mkApp2 (Lean.mkConst ``List.flatten [0]) codeBlockTy
      (← mkListLit listBlockTy blkChunks.toList)
    let dataListExpr ← mkListLit symDataTy datas.toList
    let exportsExpr ← mkListLit strTy [mkStrLit sym0, mkStrLit (mkAlphaSymName 599)]
    return (blockListExpr, dataListExpr, exportsExpr)

  let exportSymsNil ← liftTermElabM <| mkListLit
    (mkApp2 (Lean.mkConst ``Prod [0, 0]) strTy strTy) []
  let multiExpr := mkApp5 (Lean.mkConst ``MultiPlacedLib.mk)
    (mkStrLit "alpha_multi_600") blockListExpr dataListExpr exportsExpr exportSymsNil
  mkPrebuiltDef (ns ++ `alphaMulti600) (Lean.mkConst ``MultiPlacedLib) multiExpr

end BuildFixtures

/-! ## Symbol and Read-Only Data Resolution on `alphaMulti600` -/

#perf_budget 65000 in
gen_multi_sym_index alphaMulti600Idx alphaMulti600

#perf_budget 10000 in
theorem alphaMulti600_fnAddr_599 (mpl : MultiPlacement) :
    alphaMulti600.fnAddr mpl alphaSym599 = mpl.base 599 + 0#64 :=
  alphaMulti600Idx.fnAddr_eq_base mpl (by decide +kernel)

#perf_budget 2000 in
theorem alphaMulti600_fnAddr_599_chars (mpl : MultiPlacement) :
    alphaMulti600.fnAddr mpl alphaSym599 = mpl.base 599 + 0#64 :=
  alphaMulti600Idx.fnAddr_eq_base_of_chars mpl (cs := char_lit% alphaSym599) (by decide +kernel)

#perf_budget 1000 in
theorem alphaMulti600_resolve_ro31 (mpl : MultiPlacement) :
    alphaMulti600.resolve mpl "alpha_ro_31" = mpl.ρ "alpha_ro_31" :=
  alphaMulti600Idx.resolve_eq_rho mpl (by decide +kernel)

#perf_budget 1000 in
theorem alphaMulti600_resolve_ro31_chars (mpl : MultiPlacement) :
    alphaMulti600.resolve mpl "alpha_ro_31" = mpl.ρ "alpha_ro_31" :=
  alphaMulti600Idx.resolve_eq_rho_of_chars mpl (cs := char_lit% "alpha_ro_31") (by decide +kernel)

#perf_budget 1000 in
theorem alphaMulti600_findData_31 :
    (alphaMulti600Idx.findDataSym "alpha_ro_31").map (·.1) = some 31 := by
  decide +kernel

#perf_budget 1000 in
theorem alphaMulti600_findData_31_chars :
    (alphaMulti600Idx.findDataSymChars (char_lit% "alpha_ro_31")).map (·.1) = some 31 := by
  decide +kernel

end Examples.Testing.ProofLib.Perf.RelocAndPlacedScale
