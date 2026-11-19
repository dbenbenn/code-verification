/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.CliLabels -- proof-setup: allow-public-import
public import ProofLib.Placed.LabelsCoverage
public import ProofLib.Placed.LabelsInterned
public import ProofLib.ProgramReflection
public meta import Lean
public meta import Arm64
public meta import ProofLib.ProgramReflection
public meta import ProofLib.Placed.LabelsCoverage
public meta import ProofLib.Placed.LabelsInterned
public meta import GeneratedLean.LibsignalSessionExtractedObj -- proof-setup: allow-public-import
public meta import GeneratedLean.LibsignalSessionPlacedObj -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.Placed.CliLabels -- proof-setup: allow-public-import

public section

set_option autoImplicit false

/-!
# Panic Label Soundness and Completeness (`CliPanicLabelsSound`)

**Checked by Lean.** Proves `cliPanicLabelsSound : CliPanicLabelsSound` and
`cliPanicLabelsComplete` directly over interned `IdxTree` symbol and character tables without
kernel `String.toList` scans, and certifies that `Vec::remove::assert_failed`
(`cliPanicExtraRawSym`) is the unique extern in `cliCratePanicSyms` outside
`Rust.isPanicSymbol`.
-/

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliPanicLabels

open Arm64
open ProofLib.ProgramReflection (IdxTree)
open CryptoVerification.SignalSession (
  CliPanicLabelsSound
  cliLinkObjs
  cliPanicExtraDemangled
  cliCratePanicSyms
  isCliPanicSymbolPlaced
  libsignalSessionLib
)

/-- Mangled `.strtab` name of the unique extern in `cliCratePanicSyms` outside
`Rust.isPanicSymbol`. -/
def cliPanicExtraRawSym : String :=
  "_RNvNvMs_NtCs69KKACWg7bl_5alloc3vecINtB6_3VecppE6remove13assert_failed"

/-- Demangled `.o` symbol name corresponding to `cliPanicExtraRawSym`. -/
def cliPanicExtraDemangledSym : String :=
  "<alloc::vec::Vec<_, _>>::remove::assert_failed"

section MetaGenP2b

open Lean Elab Command Meta

private meta def p2bWhnfCtor (ctor : Name) (arity : Nat) (e : Expr) : MetaM Expr := do
  let c := e.consumeMData
  if c.isAppOfArity ctor arity then return c
  let e' ← whnf c
  if e'.isAppOfArity ctor arity then return e'
  let eAll ← withTransparency .all (whnf c)
  if eAll.isAppOfArity ctor arity then return eAll
  throwError "p2bWhnfCtor: expected {ctor}/{arity}, got {eAll}"

private meta partial def p2bListElems (e : Expr) : MetaM (Array Expr) := do
  let mut cur := e
  let mut out : Array Expr := #[]
  while true do
    let raw := cur.consumeMData
    if raw.isAppOfArity ``List.nil 1 then return out
    if raw.isAppOfArity ``List.cons 3 then
      out := out.push (raw.getArg! 1)
      cur := raw.getArg! 2
    else
      let c ← whnf raw
      if c.isAppOfArity ``List.nil 1 then return out
      if c.isAppOfArity ``List.cons 3 then
        out := out.push (c.getArg! 1)
        cur := c.getArg! 2
      else
        let cAll ← withTransparency .all (whnf raw)
        if cAll.isAppOfArity ``List.nil 1 then return out
        if cAll.isAppOfArity ``List.cons 3 then
          out := out.push (cAll.getArg! 1)
          cur := cAll.getArg! 2
        else
          throwError "p2bListElems: expected List, got {cAll}"
  return out

private meta def p2bStrVal (e : Expr) : MetaM String := do
  let c := e.consumeMData
  if let .lit (.strVal s) := c then return s
  let e' ← withTransparency .all (whnf c)
  if let .lit (.strVal s) := e' then return s
  throwError "p2bStrVal: expected string literal, got {e'}"

private meta def p2bCharCodeLt : List Char → List Char → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
    if a.toNat < b.toNat then true
    else if b.toNat < a.toNat then false
    else p2bCharCodeLt as bs

private meta def p2bMkList (ty : Expr) (xs : Array Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (Lean.mkConst ``List.cons [Level.zero]) ty x acc)
    (mkApp (Lean.mkConst ``List.nil [Level.zero]) ty)

private meta def p2bDecodeSymBindKey (e : Expr) : MetaM String := do
  let raw := e.consumeMData
  if raw.isConstOf ``Obj.SymBind.local then return "local"
  if raw.isConstOf ``Obj.SymBind.global then return "global"
  if raw.isConstOf ``Obj.SymBind.weak then return "weak"
  if raw.isConstOf ``Obj.SymBind.other then return "other"
  let c ← withTransparency .all (whnf raw)
  if c.isConstOf ``Obj.SymBind.local then return "local"
  if c.isConstOf ``Obj.SymBind.global then return "global"
  if c.isConstOf ``Obj.SymBind.weak then return "weak"
  return "other"

private meta def p2bDecodeSymSecKey (e : Expr) : MetaM String := do
  let raw := e.consumeMData
  if raw.isConstOf ``Obj.SymSec.undef then return "undef"
  if raw.isConstOf ``Obj.SymSec.other then return "other"
  if raw.isAppOfArity ``Obj.SymSec.sec 1 then
    if let some n := (raw.getArg! 0).rawNatLit? then return s!"sec:{n}"
  let c ← withTransparency .all (whnf raw)
  if c.isConstOf ``Obj.SymSec.undef then return "undef"
  if c.isAppOfArity ``Obj.SymSec.sec 1 then
    let n ← withTransparency .all (whnf (c.getArg! 0))
    return s!"sec:{n}"
  return "other"

elab "gen_p2b_interned" : command => do
  let currNs ← getCurrNamespace
  let _ ← liftTermElabM do
    let objEs ← p2bListElems (Lean.mkConst ``CryptoVerification.libsignalSessionExtractedObjs)
    let libC ← p2bWhnfCtor ``Obj.MultiPlacedLib.mk 5
      (Lean.mkConst ``CryptoVerification.libsignalSessionMultiLib)
    let blkEs ← p2bListElems (libC.getArg! 1)
    let b0C ← p2bWhnfCtor ``Obj.CodeBlock.mk 6 blkEs[0]!
    let extEs ← p2bListElems (b0C.getArg! 4)
    let extStrs ← (extEs.mapM p2bStrVal : MetaM (Array String))
    let panicEs ← p2bListElems (Lean.mkConst ``CryptoVerification.SignalSession.cliCratePanicSyms)
    let panicStrs ← (panicEs.mapM p2bStrVal : MetaM (Array String))

    let exactPanicEs ← p2bListElems (Lean.mkConst ``Obj.rustPanicExactNames)
    let exactPanicStrs ← (exactPanicEs.mapM p2bStrVal : MetaM (Array String))

    let extraRawStr := "_RNvNvMs_NtCs69KKACWg7bl_5alloc3vecINtB6_3VecppE6remove13assert_failed"
    let extraDemStr := "<alloc::vec::Vec<_, _>>::remove::assert_failed"

    let mut panicRawSet : Std.HashSet String := Std.HashSet.emptyWithCapacity 64
    for s in panicStrs do panicRawSet := panicRawSet.insert s

    let mut targetRawSet : Std.HashSet String := Std.HashSet.emptyWithCapacity 256
    for s in extStrs do targetRawSet := targetRawSet.insert s
    for s in panicStrs do targetRawSet := targetRawSet.insert s

    let mut nameSet : Std.HashSet String := Std.HashSet.emptyWithCapacity 8192
    nameSet := ((nameSet.insert "").insert extraRawStr).insert extraDemStr
    for s in extStrs do nameSet := nameSet.insert s
    for s in panicStrs do nameSet := nameSet.insert s

    let mut rawObjSymEs : Array (Array (String × String × Expr)) := #[]
    for oE in objEs do
      let oC ← p2bWhnfCtor ``Obj.ExtractedObj.mk 4 oE
      let symEs ← p2bListElems (oC.getArg! 2)
      let mut arr : Array (String × String × Expr) := Array.mkEmpty symEs.size
      for syE in symEs do
        let syC ← p2bWhnfCtor ``Obj.RawSym.mk 7 syE
        let rn ← p2bStrVal (syC.getArg! 0)
        let dn ← p2bStrVal (syC.getArg! 1)
        nameSet := nameSet.insert rn
        nameSet := nameSet.insert dn
        arr := arr.push (rn, dn, syC)
      rawObjSymEs := rawObjSymEs.push arr

    let sortedNames := nameSet.toArray.qsort (fun a b => p2bCharCodeLt a.toList b.toList)
    let N := sortedNames.size
    let mut idMap : Std.HashMap String Nat := Std.HashMap.emptyWithCapacity (N * 2)
    for idx in [:N] do
      idMap := idMap.insert sortedNames[idx]! idx
    let idOf (s : String) : Nat := idMap.getD s 0

    let mut targetIdSet : Std.HashSet Nat := Std.HashSet.emptyWithCapacity 256
    for s in extStrs do targetIdSet := targetIdSet.insert (idOf s)
    for s in panicStrs do targetIdSet := targetIdSet.insert (idOf s)

    let strTy := Lean.mkConst ``String
    let charListTy := mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Char)
    let natTy := Lean.mkConst ``Nat
    let natListTy := mkApp (Lean.mkConst ``List [Level.zero]) natTy
    let boolTy := Lean.mkConst ``Bool
    let trueE := Lean.mkConst ``Bool.true
    let falseE := Lean.mkConst ``Bool.false
    let iSymTy := Lean.mkConst ``Obj.LabelsInterned.ISym
    let mkTreeTy (t : Expr) := mkApp (Lean.mkConst ``IdxTree [Level.zero]) t
    let iSymTreeTy := mkTreeTy iSymTy
    let natPairTy := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) natTy natTy
    let summaryWitTy := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) iSymTy natPairTy

    let namesTreeVal := ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero strTy
      (sortedNames.map mkStrLit)
    let charsTreeVal := ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero charListTy
      (sortedNames.map ProofLib.ProgramReflection.mkStrCharsExpr)

    let mut isTargetArr : Array Expr := Array.mkEmpty N
    for idx in [:N] do
      isTargetArr := isTargetArr.push (if targetIdSet.contains idx then trueE else falseE)
    let isTargetTreeVal := ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero boolTy isTargetArr

    let zeroLit := mkRawNatLit 0
    let mut objSymTrees : Array Expr := Array.mkEmpty rawObjSymEs.size
    let mut seenSummary : Std.HashSet String := Std.HashSet.emptyWithCapacity 256
    let mut panicItems : Array (String × Nat × String × Expr × Nat × Nat) := #[]
    let mut otherItems : Array (String × Nat × String × Expr × Nat × Nat) := #[]

    for oi in [:rawObjSymEs.size] do
      let syms := rawObjSymEs[oi]!
      let mut isyms : Array Expr := Array.mkEmpty syms.size
      for si in [:syms.size] do
        let (rn, dn, syC) := syms[si]!
        let rid := idOf rn
        let nid := idOf dn
        let isyE := mkAppN (Lean.mkConst ``Obj.LabelsInterned.ISym.mk) #[
          mkRawNatLit rid,
          mkRawNatLit nid,
          zeroLit,
          syC.getArg! 6,
          syC.getArg! 5,
          syC.getArg! 2,
          syC.getArg! 3,
          syC.getArg! 4
        ]
        isyms := isyms.push isyE
        if targetRawSet.contains rn then
          let bk ← p2bDecodeSymBindKey (syC.getArg! 6)
          if bk != "local" then
            let sk ← p2bDecodeSymSecKey (syC.getArg! 2)
            let key := s!"{rid}:{nid}:{sk}:{bk}"
            if !seenSummary.contains key then
              seenSummary := seenSummary.insert key
              if panicRawSet.contains rn then
                panicItems := panicItems.push (rn, rid, sk, isyE, oi, si)
              else
                otherItems := otherItems.push (rn, rid, sk, isyE, oi, si)
      objSymTrees := objSymTrees.push
        (ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero iSymTy isyms)

    let allItems := panicItems ++ otherItems
    let numPanicSummary := panicItems.size
    let mut summaryISyms : Array Expr := Array.mkEmpty allItems.size
    let mut panicSummaryISyms : Array Expr := Array.mkEmpty numPanicSummary
    let mut panicSummaryWits : Array Expr := Array.mkEmpty numPanicSummary
    let mut bucketsByRaw : Std.HashMap Nat (Array Nat) := Std.HashMap.emptyWithCapacity 256
    let mut undefIdxByRaw : Std.HashMap String Nat := Std.HashMap.emptyWithCapacity 256

    for sIdx in [:allItems.size] do
      let (rn, rid, sk, isyE, oi, si) := allItems[sIdx]!
      summaryISyms := summaryISyms.push isyE
      if sIdx < numPanicSummary then
        panicSummaryISyms := panicSummaryISyms.push isyE
        let pair2 := mkApp4 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero])
          natTy natTy (mkRawNatLit oi) (mkRawNatLit si)
        let witE := mkApp4 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero])
          iSymTy natPairTy isyE pair2
        panicSummaryWits := panicSummaryWits.push witE
      let prev := bucketsByRaw.getD rid #[]
      bucketsByRaw := bucketsByRaw.insert rid (prev.push sIdx)
      if sk == "undef" && !undefIdxByRaw.contains rn then
        undefIdxByRaw := undefIdxByRaw.insert rn sIdx

    let some extraUndefWitIdx := undefIdxByRaw[extraRawStr]?
      | throwError "gen_p2b_interned: missing .undef symbol for {extraRawStr}"
    if extraUndefWitIdx >= numPanicSummary then
      throwError "gen_p2b_interned: extra panic .undef index {extraUndefWitIdx} >= {numPanicSummary}"

    let objSymsTreeVal :=
      ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero iSymTreeTy objSymTrees
    let summaryTreeVal :=
      ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero iSymTy summaryISyms
    let panicSummaryTreeVal :=
      ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero iSymTy panicSummaryISyms

    let emptyNatList := mkApp (Lean.mkConst ``List.nil [Level.zero]) natTy
    let mut bucketArr : Array Expr := Array.mkEmpty N
    for idx in [:N] do
      match bucketsByRaw[idx]? with
      | none => bucketArr := bucketArr.push emptyNatList
      | some ks => bucketArr := bucketArr.push (p2bMkList natTy (ks.map mkRawNatLit))
    let targetBucketTreeVal :=
      ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero natListTy bucketArr

    let addD (nm : Name) (ty val : Expr) : MetaM Unit := do
      let env ← getEnv
      addDecl (.defnDecl {
        name := currNs ++ nm
        levelParams := []
        type := ty
        value := val
        hints := .regular (getMaxHeight env val + 1)
        safety := .safe
      })
      modifyEnv (addNoncomputable · (currNs ++ nm))

    addD `p2bNumNames natTy (mkRawNatLit N)
    addD `p2bNumBlocks natTy (mkRawNatLit blkEs.size)
    addD `p2bExtraRawId natTy (mkRawNatLit (idOf extraRawStr))
    addD `p2bExtraDemangledId natTy (mkRawNatLit (idOf extraDemStr))
    addD `p2bExtraUndefWitIdx natTy (mkRawNatLit extraUndefWitIdx)
    addD `p2bNamesTree (mkTreeTy strTy) namesTreeVal
    addD `p2bCharsTree (mkTreeTy charListTy) charsTreeVal
    addD `p2bIsTargetTree (mkTreeTy boolTy) isTargetTreeVal
    addD `p2bTargetBucketTree (mkTreeTy natListTy) targetBucketTreeVal
    addD `p2bObjSymsTree (mkTreeTy iSymTreeTy) objSymsTreeVal
    addD `p2bSummaryTree iSymTreeTy summaryTreeVal
    addD `p2bPanicSummaryTree iSymTreeTy panicSummaryTreeVal
    addD `p2bPanicSummaryWits (mkApp (Lean.mkConst ``List [Level.zero]) summaryWitTy)
      (p2bMkList summaryWitTy panicSummaryWits)
    addD `p2bExternIds natListTy
      (p2bMkList natTy (extStrs.map (mkRawNatLit ∘ idOf)))
    addD `p2bPanicIds natListTy
      (p2bMkList natTy (panicStrs.map (mkRawNatLit ∘ idOf)))
    let charListListTy := mkApp (Lean.mkConst ``List [Level.zero]) charListTy
    addD `p2bRustExactPanicChars charListListTy
      (p2bMkList charListTy (exactPanicStrs.map ProofLib.ProgramReflection.mkStrCharsExpr))
    addD `cliAllExterns (mkApp (Lean.mkConst ``List [Level.zero]) strTy)
      (p2bMkList strTy (extStrs.map mkStrLit))
    return ()

gen_p2b_interned

end MetaGenP2b

private theorem p2b_names_sz : p2bNamesTree.size? = some p2bNumNames := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem p2b_chars_sz : p2bCharsTree.size? = some p2bNumNames := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem p2b_names_eq :
    p2bNamesTree.toList = p2bCharsTree.toList.map String.ofList := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem p2b_names_nodup :
    Obj.Interned.namesNodup p2bCharsTree.toList = true := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem p2b_objs_syms_eq :
    cliLinkObjs.map Obj.ExtractedObj.symbols =
      p2bObjSymsTree.toList.map
        (fun t => t.toList.map (Obj.LabelsInterned.ISym.toRawSym p2bNamesTree)) := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem p2b_panic_summary_wits_eq :
    p2bPanicSummaryTree.toList = p2bPanicSummaryWits.map Prod.fst := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem p2b_externs_eq :
    cliAllExterns = p2bExternIds.map (Obj.LabelsInterned.symAt p2bNamesTree) := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem p2b_panics_eq :
    cliCratePanicSyms = p2bPanicIds.map (Obj.LabelsInterned.symAt p2bNamesTree) := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem p2b_blocks_externs_eq :
    libsignalSessionLib.blocks.map Obj.CodeBlock.externs =
      List.replicate p2bNumBlocks cliAllExterns := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem p2b_exact_panic_toList_eq :
    Obj.rustPanicExactNames.map String.toList = p2bRustExactPanicChars := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem p2b_extra_raw_eq :
    Obj.LabelsInterned.symAt p2bNamesTree p2bExtraRawId = cliPanicExtraRawSym := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem p2b_extra_demangled_eq :
    Obj.LabelsInterned.symAt p2bNamesTree p2bExtraDemangledId = cliPanicExtraDemangledSym := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem cliBlock_externs_eq {b : Obj.CodeBlock} (hb : b ∈ libsignalSessionLib.blocks) :
    b.externs = cliAllExterns := by
  have hmem : b.externs ∈ libsignalSessionLib.blocks.map Obj.CodeBlock.externs :=
    List.mem_map_of_mem hb
  rw [p2b_blocks_externs_eq] at hmem
  exact List.eq_of_mem_replicate hmem

private def isymMatches (a b : Obj.LabelsInterned.ISym) : Bool :=
  Nat.beq a.rawId b.rawId && Nat.beq a.nameId b.nameId && (a.sec == b.sec) && (a.bind == b.bind)

private noncomputable def p2bTargetIdOk (extId : Nat) : Bool :=
  Nat.blt extId p2bNumNames && (p2bIsTargetTree.get? extId == some true)

private noncomputable def p2bSummaryWitOk
    (w : Obj.LabelsInterned.ISym × Nat × Nat) : Bool :=
  match p2bObjSymsTree.get? w.2.1 with
  | none => false
  | some t =>
    match t.get? w.2.2 with
    | none => false
    | some isy => isymMatches isy w.1

private noncomputable def p2bPanicBucketEntryOk (k : Nat) : Bool :=
  match p2bSummaryTree.get? k with
  | none => false
  | some s1 =>
    match p2bPanicSummaryTree.get? k with
    | none => false
    | some s2 => isymMatches s1 s2

private noncomputable def p2bPanicBucketsOk : Bool :=
  p2bPanicIds.all fun extId =>
    match p2bTargetBucketTree.get? extId with
    | none => false
    | some ks => ks.all p2bPanicBucketEntryOk

private noncomputable def p2bSymOk (isy : Obj.LabelsInterned.ISym) : Bool :=
  Nat.blt isy.rawId p2bNumNames &&
  match p2bIsTargetTree.get? isy.rawId with
  | some true =>
    if isy.bind != .local then
      match p2bTargetBucketTree.get? isy.rawId with
      | none => false
      | some ks =>
        ks.any fun k =>
          match p2bSummaryTree.get? k with
          | none => false
          | some s => isymMatches isy s
    else true
  | _ => true

private noncomputable def p2bSubsumesB : Bool :=
  (p2bExternIds ++ p2bPanicIds).all p2bTargetIdOk &&
  p2bPanicSummaryWits.all p2bSummaryWitOk &&
  p2bPanicBucketsOk &&
  p2bObjSymsTree.all (fun t => t.all p2bSymOk)

private theorem p2bSubsumesB_ok : p2bSubsumesB = true := by
  open ProofLib.ProgramReflection in rfl_kernel

private noncomputable def isRustPanicChars (cs : List Char) : Bool :=
  List.isPrefixOf
    ['c', 'o', 'r', 'e', ':', ':', 'p', 'a', 'n', 'i', 'c', 'k', 'i', 'n', 'g', ':', ':'] cs ||
    p2bRustExactPanicChars.any (fun p => cs == p)

private theorem rust_isPanicSymbol_eq_chars (s : String) :
    Rust.isPanicSymbol s = isRustPanicChars s.toList := by
  rw [Obj.rust_isPanicSymbol_eq_fast]
  unfold Obj.isPanicSymbolFast Obj.isPanicSymbolChars isRustPanicChars
  rw [p2b_exact_panic_toList_eq]

private theorem rust_isPanicSymbol_symAt {id : Nat} (hid : id < p2bNumNames) :
    Rust.isPanicSymbol (Obj.LabelsInterned.symAt p2bNamesTree id) =
      isRustPanicChars (Obj.LabelsInterned.charsAt p2bCharsTree id) := by
  rw [Obj.LabelsInterned.symAt_eq_ofList_charsAt p2b_names_sz p2b_chars_sz p2b_names_eq hid,
    rust_isPanicSymbol_eq_chars, String.toList_ofList]

private noncomputable def p2bPanicSummaryISymOk (isy : Obj.LabelsInterned.ISym) : Bool :=
  Nat.blt isy.rawId p2bNumNames && Nat.blt isy.nameId p2bNumNames &&
  (!(isy.bind != .local) ||
    ((isRustPanicChars (Obj.LabelsInterned.charsAt p2bCharsTree isy.nameId) ||
      Nat.beq isy.nameId p2bExtraDemangledId) &&
     (Nat.beq isy.rawId p2bExtraRawId ||
      isRustPanicChars (Obj.LabelsInterned.charsAt p2bCharsTree isy.nameId)) &&
     (!(Nat.beq isy.rawId p2bExtraRawId) ||
      ((isy.sec == .undef) && Nat.beq isy.nameId p2bExtraDemangledId))))

private noncomputable def p2bSummaryISymCompleteOk (isy : Obj.LabelsInterned.ISym) : Bool :=
  Nat.blt isy.rawId p2bNumNames && Nat.blt isy.nameId p2bNumNames &&
  (!(isy.sec == .undef) ||
    !(isRustPanicChars (Obj.LabelsInterned.charsAt p2bCharsTree isy.nameId) ||
      Nat.beq isy.nameId p2bExtraDemangledId) ||
    p2bPanicIds.any (Nat.beq isy.rawId))

private noncomputable def p2bExtraChecksOk : Bool :=
  Nat.blt p2bExtraRawId p2bNumNames &&
  Nat.blt p2bExtraDemangledId p2bNumNames &&
  !isRustPanicChars (Obj.LabelsInterned.charsAt p2bCharsTree p2bExtraDemangledId) &&
  p2bPanicIds.any (Nat.beq p2bExtraRawId) &&
  match p2bPanicSummaryTree.get? p2bExtraUndefWitIdx with
  | none => false
  | some isy =>
    Nat.beq isy.rawId p2bExtraRawId && (isy.bind != .local) &&
    (isy.sec == .undef) && Nat.beq isy.nameId p2bExtraDemangledId

private noncomputable def p2bFastChecksB : Bool :=
  (p2bExternIds.all fun id =>
    Nat.blt id p2bNumNames && !isRustPanicChars (Obj.LabelsInterned.charsAt p2bCharsTree id)) &&
  p2bPanicSummaryTree.all p2bPanicSummaryISymOk &&
  p2bSummaryTree.all p2bSummaryISymCompleteOk &&
  p2bExtraChecksOk

private theorem p2bFastChecks_ok : p2bFastChecksB = true := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem isymMatches_props {a b : Obj.LabelsInterned.ISym} (h : isymMatches a b = true) :
    a.rawId = b.rawId ∧ a.nameId = b.nameId ∧ a.sec = b.sec ∧ a.bind = b.bind := by
  unfold isymMatches at h
  rcases Eq.mp (Bool.and_eq_true _ _) h with ⟨h123, hbd⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h123 with ⟨h12, hsec⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h12 with ⟨hr, hn⟩
  exact ⟨Nat.eq_of_beq_eq_true hr, Nat.eq_of_beq_eq_true hn,
    beq_iff_eq.mp hsec, beq_iff_eq.mp hbd⟩

private theorem summary_has_matching_isym {x : String}
    (hx : x ∈ cliAllExterns ∨ x ∈ cliCratePanicSyms)
    {o : Obj.ExtractedObj} (ho : o ∈ cliLinkObjs)
    {sy : Obj.RawSym} (hsy : sy ∈ o.symbols)
    (hraw : sy.rawName = x) (hbind : sy.bind ≠ .local) :
    ∃ s ∈ p2bSummaryTree.toList,
      Obj.LabelsInterned.symAt p2bNamesTree s.rawId = sy.rawName ∧
      Obj.LabelsInterned.symAt p2bNamesTree s.nameId = sy.name ∧
      s.sec = sy.sec ∧ s.bind = sy.bind := by
  have hnd : p2bNamesTree.toList.Nodup :=
    Obj.Interned.nodup_of_namesNodup p2b_names_eq p2b_names_nodup
  rcases Eq.mp (Bool.and_eq_true _ _) p2bSubsumesB_ok with ⟨h123, htree_b⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h123 with ⟨h12, _⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h12 with ⟨htids_b, _⟩
  have htids : ∀ extId ∈ p2bExternIds ++ p2bPanicIds, p2bTargetIdOk extId = true :=
    List.all_eq_true.mp htids_b
  rw [IdxTree.all_eq_toList_all] at htree_b
  have hall_objs : ∀ t ∈ p2bObjSymsTree.toList, t.all p2bSymOk = true :=
    List.all_eq_true.mp htree_b
  have hid_ex : ∃ extId ∈ p2bExternIds ++ p2bPanicIds,
      x = Obj.LabelsInterned.symAt p2bNamesTree extId := by
    rcases hx with hext | hpan
    · rw [p2b_externs_eq, List.mem_map] at hext
      obtain ⟨extId, hid, rfl⟩ := hext
      exact ⟨extId, List.mem_append_left _ hid, rfl⟩
    · rw [p2b_panics_eq, List.mem_map] at hpan
      obtain ⟨extId, hid, rfl⟩ := hpan
      exact ⟨extId, List.mem_append_right _ hid, rfl⟩
  obtain ⟨extId, hid_mem, rfl⟩ := hid_ex
  have htid_ok := htids extId hid_mem
  unfold p2bTargetIdOk at htid_ok
  rcases Eq.mp (Bool.and_eq_true _ _) htid_ok with ⟨hext_lt_b, hext_tree_b⟩
  have hext_lt : extId < p2bNumNames := Obj.Interned.blt_iff.mp hext_lt_b
  have hext_tree : p2bIsTargetTree.get? extId = some true := beq_iff_eq.mp hext_tree_b
  have ho_map :
      o.symbols ∈
        p2bObjSymsTree.toList.map
          (fun t => t.toList.map (Obj.LabelsInterned.ISym.toRawSym p2bNamesTree)) := by
    rw [← p2b_objs_syms_eq]
    exact List.mem_map_of_mem ho
  obtain ⟨t, ht_mem, ht_eq⟩ := List.mem_map.mp ho_map
  rw [← ht_eq] at hsy
  obtain ⟨isy, hisy_mem, rfl⟩ := List.mem_map.mp hsy
  have ht_ok := hall_objs t ht_mem
  rw [IdxTree.all_eq_toList_all] at ht_ok
  have hisy_ok : p2bSymOk isy = true := List.all_eq_true.mp ht_ok isy hisy_mem
  unfold p2bSymOk at hisy_ok
  rcases Eq.mp (Bool.and_eq_true _ _) hisy_ok with ⟨hisy_lt_b, hisy_tgt⟩
  have hisy_lt : isy.rawId < p2bNumNames := Obj.Interned.blt_iff.mp hisy_lt_b
  have hid_eq : isy.rawId = extId :=
    Obj.LabelsInterned.symAt_inj p2b_names_sz hnd hisy_lt hext_lt hraw
  rw [hid_eq, hext_tree] at hisy_tgt
  dsimp only at hisy_tgt
  have hbn : (isy.bind != .local) = true := bne_iff_ne.mpr hbind
  rw [hbn] at hisy_tgt
  simp only [↓reduceIte] at hisy_tgt
  cases hbucket : p2bTargetBucketTree.get? extId with
  | none => rw [hbucket] at hisy_tgt; cases hisy_tgt
  | some ks =>
    rw [hbucket] at hisy_tgt
    dsimp only at hisy_tgt
    obtain ⟨k, _, hk_ok⟩ := List.any_eq_true.mp hisy_tgt
    cases hget_s : p2bSummaryTree.get? k with
    | none => rw [hget_s] at hk_ok; cases hk_ok
    | some s =>
      rw [hget_s] at hk_ok
      dsimp only at hk_ok
      obtain ⟨hr, hn, hsec, hbd⟩ := isymMatches_props hk_ok
      refine ⟨s, IdxTree.mem_toList_of_get? hget_s, ?_⟩
      dsimp only [Obj.LabelsInterned.ISym.toRawSym]
      exact ⟨congrArg _ hr.symm, congrArg _ hn.symm, hsec.symm, hbd.symm⟩

private theorem panic_summary_has_matching_isym {x : String}
    (hx : x ∈ cliCratePanicSyms)
    {o : Obj.ExtractedObj} (ho : o ∈ cliLinkObjs)
    {sy : Obj.RawSym} (hsy : sy ∈ o.symbols)
    (hraw : sy.rawName = x) (hbind : sy.bind ≠ .local) :
    ∃ s2 ∈ p2bPanicSummaryTree.toList,
      Obj.LabelsInterned.symAt p2bNamesTree s2.rawId = sy.rawName ∧
      Obj.LabelsInterned.symAt p2bNamesTree s2.nameId = sy.name ∧
      s2.sec = sy.sec ∧ s2.bind = sy.bind := by
  have hnd : p2bNamesTree.toList.Nodup :=
    Obj.Interned.nodup_of_namesNodup p2b_names_eq p2b_names_nodup
  rcases Eq.mp (Bool.and_eq_true _ _) p2bSubsumesB_ok with ⟨h123, htree_b⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h123 with ⟨h12, hpbuckets_b⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h12 with ⟨htids_b, _⟩
  have htids : ∀ extId ∈ p2bExternIds ++ p2bPanicIds, p2bTargetIdOk extId = true :=
    List.all_eq_true.mp htids_b
  have hpbuckets := List.all_eq_true.mp hpbuckets_b
  rw [IdxTree.all_eq_toList_all] at htree_b
  have hall_objs : ∀ t ∈ p2bObjSymsTree.toList, t.all p2bSymOk = true :=
    List.all_eq_true.mp htree_b
  rw [p2b_panics_eq, List.mem_map] at hx
  obtain ⟨extId, hid_pan, rfl⟩ := hx
  have htid_ok := htids extId (List.mem_append_right _ hid_pan)
  unfold p2bTargetIdOk at htid_ok
  rcases Eq.mp (Bool.and_eq_true _ _) htid_ok with ⟨hext_lt_b, hext_tree_b⟩
  have hext_lt : extId < p2bNumNames := Obj.Interned.blt_iff.mp hext_lt_b
  have hext_tree : p2bIsTargetTree.get? extId = some true := beq_iff_eq.mp hext_tree_b
  have ho_map :
      o.symbols ∈
        p2bObjSymsTree.toList.map
          (fun t => t.toList.map (Obj.LabelsInterned.ISym.toRawSym p2bNamesTree)) := by
    rw [← p2b_objs_syms_eq]
    exact List.mem_map_of_mem ho
  obtain ⟨t, ht_mem, ht_eq⟩ := List.mem_map.mp ho_map
  rw [← ht_eq] at hsy
  obtain ⟨isy, hisy_mem, rfl⟩ := List.mem_map.mp hsy
  have ht_ok := hall_objs t ht_mem
  rw [IdxTree.all_eq_toList_all] at ht_ok
  have hisy_ok : p2bSymOk isy = true := List.all_eq_true.mp ht_ok isy hisy_mem
  unfold p2bSymOk at hisy_ok
  rcases Eq.mp (Bool.and_eq_true _ _) hisy_ok with ⟨hisy_lt_b, hisy_tgt⟩
  have hisy_lt : isy.rawId < p2bNumNames := Obj.Interned.blt_iff.mp hisy_lt_b
  have hid_eq : isy.rawId = extId :=
    Obj.LabelsInterned.symAt_inj p2b_names_sz hnd hisy_lt hext_lt hraw
  rw [hid_eq, hext_tree] at hisy_tgt
  dsimp only at hisy_tgt
  have hbn : (isy.bind != .local) = true := bne_iff_ne.mpr hbind
  rw [hbn] at hisy_tgt
  simp only [↓reduceIte] at hisy_tgt
  have hpb := hpbuckets extId hid_pan
  cases hbucket : p2bTargetBucketTree.get? extId with
  | none => rw [hbucket] at hisy_tgt; cases hisy_tgt
  | some ks =>
    rw [hbucket] at hisy_tgt hpb
    dsimp only at hisy_tgt hpb
    obtain ⟨k, hk_mem, hk_ok⟩ := List.any_eq_true.mp hisy_tgt
    have hk_ent : p2bPanicBucketEntryOk k = true := List.all_eq_true.mp hpb k hk_mem
    unfold p2bPanicBucketEntryOk at hk_ent
    cases hget_s : p2bSummaryTree.get? k with
    | none => rw [hget_s] at hk_ok; cases hk_ok
    | some s =>
      rw [hget_s] at hk_ok hk_ent
      dsimp only at hk_ok hk_ent
      cases hget_p : p2bPanicSummaryTree.get? k with
      | none => rw [hget_p] at hk_ent; cases hk_ent
      | some s2 =>
        rw [hget_p] at hk_ent
        dsimp only at hk_ent
        obtain ⟨hr1, hn1, hsec1, hbd1⟩ := isymMatches_props hk_ok
        obtain ⟨hr2, hn2, hsec2, hbd2⟩ := isymMatches_props hk_ent
        refine ⟨s2, IdxTree.mem_toList_of_get? hget_p, ?_⟩
        dsimp only [Obj.LabelsInterned.ISym.toRawSym]
        exact ⟨congrArg _ (hr1.trans hr2).symm, congrArg _ (hn1.trans hn2).symm,
          (hsec1.trans hsec2).symm, (hbd1.trans hbd2).symm⟩

private theorem panic_objs_has_matching_isym {s2 : Obj.LabelsInterned.ISym}
    (hs2 : s2 ∈ p2bPanicSummaryTree.toList) :
    ∃ o ∈ cliLinkObjs, ∃ sy ∈ o.symbols,
      sy.rawName = Obj.LabelsInterned.symAt p2bNamesTree s2.rawId ∧
      sy.name = Obj.LabelsInterned.symAt p2bNamesTree s2.nameId ∧
      sy.sec = s2.sec ∧ sy.bind = s2.bind := by
  rcases Eq.mp (Bool.and_eq_true _ _) p2bSubsumesB_ok with ⟨h123, _⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h123 with ⟨h12, _⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h12 with ⟨_, hwits_b⟩
  have hwits : ∀ w ∈ p2bPanicSummaryWits, p2bSummaryWitOk w = true := List.all_eq_true.mp hwits_b
  rw [p2b_panic_summary_wits_eq] at hs2
  obtain ⟨w, hw_mem, rfl⟩ := List.mem_map.mp hs2
  have hw_ok := hwits w hw_mem
  unfold p2bSummaryWitOk at hw_ok
  cases hget_o : p2bObjSymsTree.get? w.2.1 with
  | none => rw [hget_o] at hw_ok; cases hw_ok
  | some t =>
    rw [hget_o] at hw_ok
    dsimp only at hw_ok
    cases hget_s : t.get? w.2.2 with
    | none => rw [hget_s] at hw_ok; cases hw_ok
    | some isy =>
      rw [hget_s] at hw_ok
      dsimp only at hw_ok
      obtain ⟨hr, hn, hsec, hbd⟩ := isymMatches_props hw_ok
      have ht_mem : t ∈ p2bObjSymsTree.toList := IdxTree.mem_toList_of_get? hget_o
      have hisy_mem : isy ∈ t.toList := IdxTree.mem_toList_of_get? hget_s
      have hmap :
          t.toList.map (Obj.LabelsInterned.ISym.toRawSym p2bNamesTree) ∈
            cliLinkObjs.map Obj.ExtractedObj.symbols := by
        rw [p2b_objs_syms_eq]
        exact List.mem_map_of_mem ht_mem
      obtain ⟨o, ho, ho_syms⟩ := List.mem_map.mp hmap
      refine ⟨o, ho, isy.toRawSym p2bNamesTree, ?_, ?_⟩
      · rw [ho_syms]
        exact List.mem_map_of_mem hisy_mem
      · dsimp only [Obj.LabelsInterned.ISym.toRawSym]
        exact ⟨congrArg _ hr, congrArg _ hn, hsec, hbd⟩

/-- Every non-local `.o` symbol matching an extern in `libsignalSessionLib` with
`isCliPanicSymbolPlaced x = true` demangles to a Rust panic entry point (`Rust.isPanicSymbol` or
`cliPanicExtraDemangled`). -/
theorem cliPanicLabelsSound : CliPanicLabelsSound := by
  rcases Eq.mp (Bool.and_eq_true _ _) p2bFastChecks_ok with ⟨h123, _⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h123 with ⟨h12, _⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h12 with ⟨hext_b, hpans_b⟩
  have hext_ok := List.all_eq_true.mp hext_b
  rw [IdxTree.all_eq_toList_all] at hpans_b
  have hpans_ok := List.all_eq_true.mp hpans_b
  intro b hb x hx hpanic o ho sy hsy hraw hbind
  rw [cliBlock_externs_eq hb] at hx
  unfold isCliPanicSymbolPlaced at hpanic
  have hx_mem : x ∈ cliCratePanicSyms := by
    rcases Eq.mp (Bool.or_eq_true _ _) hpanic with hin | hstd
    · exact List.contains_iff_mem.mp hin
    · rw [p2b_externs_eq, List.mem_map] at hx
      obtain ⟨extId, hid, rfl⟩ := hx
      rcases Eq.mp (Bool.and_eq_true _ _) (hext_ok extId hid) with ⟨hid_lt_b, hnot⟩
      have hid_lt : extId < p2bNumNames := Obj.Interned.blt_iff.mp hid_lt_b
      rw [rust_isPanicSymbol_symAt hid_lt] at hstd
      rw [hstd] at hnot
      cases hnot
  obtain ⟨s2, hs2_mem, _, hname', _, hbind'⟩ :=
    panic_summary_has_matching_isym hx_mem ho hsy hraw hbind
  have hs2_ok : p2bPanicSummaryISymOk s2 = true := hpans_ok s2 hs2_mem
  unfold p2bPanicSummaryISymOk at hs2_ok
  rcases Eq.mp (Bool.and_eq_true _ _) hs2_ok with ⟨hbounds, hbody⟩
  rcases Eq.mp (Bool.and_eq_true _ _) hbounds with ⟨_, hname_lt_b⟩
  have hname_lt : s2.nameId < p2bNumNames := Obj.Interned.blt_iff.mp hname_lt_b
  have hbn : (s2.bind != .local) = true := bne_iff_ne.mpr (hbind' ▸ hbind)
  rw [hbn] at hbody
  simp only [Bool.not_true, Bool.false_or] at hbody
  rcases Eq.mp (Bool.and_eq_true _ _) hbody with ⟨h12_s2, _⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h12_s2 with ⟨hdem_ok, _⟩
  rcases Eq.mp (Bool.or_eq_true _ _) hdem_ok with hstd | hextra
  · left
    rw [← hname', rust_isPanicSymbol_symAt hname_lt]
    exact hstd
  · right
    have hnid : s2.nameId = p2bExtraDemangledId := Nat.eq_of_beq_eq_true hextra
    have hextra_list : cliPanicExtraDemangled = [cliPanicExtraDemangledSym] := rfl
    rw [← hname', hnid, p2b_extra_demangled_eq, hextra_list]
    exact List.mem_singleton.mpr rfl

/-- Completeness converse of `cliPanicLabelsSound`: every extern of `libsignalSessionLib` whose
non-local `.undef` symbol in `cliLinkObjs` demangles to `Rust.isPanicSymbol` or
`cliPanicExtraDemangled` satisfies `isCliPanicSymbolPlaced x = true`. -/
theorem cliPanicLabelsComplete :
    ∀ b ∈ libsignalSessionLib.blocks, ∀ x ∈ b.externs,
      ∀ o ∈ cliLinkObjs, ∀ sy ∈ o.symbols,
        sy.rawName = x → sy.bind ≠ .local → sy.sec = .undef →
        (Rust.isPanicSymbol sy.name = true ∨ sy.name ∈ cliPanicExtraDemangled) →
        isCliPanicSymbolPlaced x = true := by
  have hnd : p2bNamesTree.toList.Nodup :=
    Obj.Interned.nodup_of_namesNodup p2b_names_eq p2b_names_nodup
  rcases Eq.mp (Bool.and_eq_true _ _) p2bFastChecks_ok with ⟨h123, hextra_ok⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h123 with ⟨_, hcomp_b⟩
  rw [IdxTree.all_eq_toList_all] at hcomp_b
  have hcomp_ok := List.all_eq_true.mp hcomp_b
  unfold p2bExtraChecksOk at hextra_ok
  rcases Eq.mp (Bool.and_eq_true _ _) hextra_ok with ⟨h1234_ex, _⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h1234_ex with ⟨h123_ex, _⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h123_ex with ⟨h12_ex, _⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h12_ex with ⟨_, hextra_dem_lt_b⟩
  have hextra_dem_lt : p2bExtraDemangledId < p2bNumNames :=
    Obj.Interned.blt_iff.mp hextra_dem_lt_b
  intro b hb x hx o ho sy hsy hraw hbind hsec hdem
  rw [cliBlock_externs_eq hb] at hx
  obtain ⟨s, hs_mem, hraw', hname', hsec', _⟩ :=
    summary_has_matching_isym (Or.inl hx) ho hsy hraw hbind
  have hok : p2bSummaryISymCompleteOk s = true := hcomp_ok s hs_mem
  unfold p2bSummaryISymCompleteOk at hok
  rcases Eq.mp (Bool.and_eq_true _ _) hok with ⟨hbounds, hbody⟩
  rcases Eq.mp (Bool.and_eq_true _ _) hbounds with ⟨_, hname_lt_b⟩
  have hname_lt : s.nameId < p2bNumNames := Obj.Interned.blt_iff.mp hname_lt_b
  rcases Eq.mp (Bool.or_eq_true _ _) hbody with h12 | hany
  · rcases Eq.mp (Bool.or_eq_true _ _) h12 with hnot_sec | hnot_dem
    · have hsec_b : (s.sec == .undef) = true := beq_iff_eq.mpr (hsec'.trans hsec)
      rw [hsec_b] at hnot_sec
      cases hnot_sec
    · have hdem_b : (isRustPanicChars (Obj.LabelsInterned.charsAt p2bCharsTree s.nameId) ||
          Nat.beq s.nameId p2bExtraDemangledId) = true := by
        apply Eq.mpr (Bool.or_eq_true _ _)
        rcases hdem with hstd | hextra
        · rw [← hname', rust_isPanicSymbol_symAt hname_lt] at hstd
          exact Or.inl hstd
        · have hextra_eq : cliPanicExtraDemangled = [cliPanicExtraDemangledSym] := rfl
          rw [hextra_eq, List.mem_singleton] at hextra
          have hsym_eq : Obj.LabelsInterned.symAt p2bNamesTree s.nameId =
              Obj.LabelsInterned.symAt p2bNamesTree p2bExtraDemangledId := by
            rw [hname', hextra, p2b_extra_demangled_eq]
          have hnid := Obj.LabelsInterned.symAt_inj p2b_names_sz hnd hname_lt hextra_dem_lt hsym_eq
          exact Or.inr (Nat.beq_eq.mpr hnid)
      rw [hdem_b] at hnot_dem
      cases hnot_dem
  · obtain ⟨pid, hpid_mem, hpid_eq_b⟩ := List.any_eq_true.mp hany
    have hpid_eq : s.rawId = pid := Nat.eq_of_beq_eq_true hpid_eq_b
    have hx_mem : x ∈ cliCratePanicSyms := by
      rw [← hraw, ← hraw', hpid_eq, p2b_panics_eq]
      exact List.mem_map_of_mem hpid_mem
    unfold isCliPanicSymbolPlaced
    exact Eq.mpr (Bool.or_eq_true _ _) (Or.inl (List.contains_iff_mem.mpr hx_mem))

/-- Pinning certificate for `cliPanicExtraRawSym`: it belongs to `cliCratePanicSyms`, occurs as
a non-local `.undef` symbol in `cliLinkObjs` with demangled name `cliPanicExtraDemangledSym` outside
`Rust.isPanicSymbol`, while every other symbol in `cliCratePanicSyms` satisfies
`Rust.isPanicSymbol`. -/
theorem cliPanicExtraSym_is_extraDemangled :
    [cliPanicExtraDemangledSym] = cliPanicExtraDemangled ∧
    Rust.isPanicSymbol cliPanicExtraDemangledSym = false ∧
    cliPanicExtraRawSym ∈ cliCratePanicSyms ∧
    Obj.NonVacuousUndefSymDemangled cliLinkObjs cliPanicExtraRawSym cliPanicExtraDemangledSym ∧
    (∀ p ∈ cliCratePanicSyms, p ≠ cliPanicExtraRawSym →
      ∀ o ∈ cliLinkObjs, ∀ sy ∈ o.symbols,
        sy.rawName = p → sy.bind ≠ .local → Rust.isPanicSymbol sy.name = true) := by
  have hnd : p2bNamesTree.toList.Nodup :=
    Obj.Interned.nodup_of_namesNodup p2b_names_eq p2b_names_nodup
  rcases Eq.mp (Bool.and_eq_true _ _) p2bFastChecks_ok with ⟨h123, hextra_ok⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h123 with ⟨h12, _⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h12 with ⟨_, hpans_b⟩
  rw [IdxTree.all_eq_toList_all] at hpans_b
  have hpans_ok := List.all_eq_true.mp hpans_b
  unfold p2bExtraChecksOk at hextra_ok
  rcases Eq.mp (Bool.and_eq_true _ _) hextra_ok with ⟨h1234, hwit_ok⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h1234 with ⟨h123_ex, hpan_any⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h123_ex with ⟨h12_ex, hnot_std⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h12_ex with ⟨hextra_raw_lt_b, hextra_dem_lt_b⟩
  have hextra_raw_lt : p2bExtraRawId < p2bNumNames :=
    Obj.Interned.blt_iff.mp hextra_raw_lt_b
  have hextra_dem_lt : p2bExtraDemangledId < p2bNumNames :=
    Obj.Interned.blt_iff.mp hextra_dem_lt_b
  obtain ⟨pid, hpid_mem, hpid_eq_b⟩ := List.any_eq_true.mp hpan_any
  have hpid_eq : p2bExtraRawId = pid := Nat.eq_of_beq_eq_true hpid_eq_b
  have hpan_mem : cliPanicExtraRawSym ∈ cliCratePanicSyms := by
    rw [← p2b_extra_raw_eq, hpid_eq, p2b_panics_eq]
    exact List.mem_map_of_mem hpid_mem
  refine ⟨rfl, ?_, hpan_mem, ?_, ?_⟩
  · rw [← p2b_extra_demangled_eq, rust_isPanicSymbol_symAt hextra_dem_lt]
    exact Bool.eq_false_iff.mpr fun h => by rw [h] at hnot_std; cases hnot_std
  · cases hget_w : p2bPanicSummaryTree.get? p2bExtraUndefWitIdx with
    | none => rw [hget_w] at hwit_ok; cases hwit_ok
    | some isy0 =>
      rw [hget_w] at hwit_ok
      dsimp only at hwit_ok
      rcases Eq.mp (Bool.and_eq_true _ _) hwit_ok with ⟨hw123, hwnid_b⟩
      rcases Eq.mp (Bool.and_eq_true _ _) hw123 with ⟨hw12, hwsec_b⟩
      rcases Eq.mp (Bool.and_eq_true _ _) hw12 with ⟨hwrid_b, hwbind_b⟩
      have hwrid : isy0.rawId = p2bExtraRawId := Nat.eq_of_beq_eq_true hwrid_b
      have hwnid : isy0.nameId = p2bExtraDemangledId := Nat.eq_of_beq_eq_true hwnid_b
      have hwbind : isy0.bind ≠ .local := bne_iff_ne.mp hwbind_b
      have hwsec : isy0.sec = .undef := beq_iff_eq.mp hwsec_b
      obtain ⟨o0, ho0, sy0, hsy0, hr0, hn0, hsc0, hbd0⟩ :=
        panic_objs_has_matching_isym (IdxTree.mem_toList_of_get? hget_w)
      refine ⟨⟨o0, ho0, sy0, hsy0,
        by rw [hr0, hwrid, p2b_extra_raw_eq],
        hbd0.symm ▸ hwbind,
        hsc0.trans hwsec,
        by rw [hn0, hwnid, p2b_extra_demangled_eq]⟩, ?_⟩
      intro o ho sy hsy hraw hbind
      obtain ⟨s2, hs2_mem, hr', hn', hsc', hbd'⟩ :=
        panic_summary_has_matching_isym hpan_mem ho hsy hraw hbind
      have hs2_ok : p2bPanicSummaryISymOk s2 = true := hpans_ok s2 hs2_mem
      unfold p2bPanicSummaryISymOk at hs2_ok
      rcases Eq.mp (Bool.and_eq_true _ _) hs2_ok with ⟨hbounds, hbody⟩
      rcases Eq.mp (Bool.and_eq_true _ _) hbounds with ⟨hraw_lt_b, _⟩
      have hraw_lt : s2.rawId < p2bNumNames := Obj.Interned.blt_iff.mp hraw_lt_b
      have hbn : (s2.bind != .local) = true := bne_iff_ne.mpr (hbd' ▸ hbind)
      rw [hbn] at hbody
      simp only [Bool.not_true, Bool.false_or] at hbody
      rcases Eq.mp (Bool.and_eq_true _ _) hbody with ⟨_, himp⟩
      have hs2_raw_eq : s2.rawId = p2bExtraRawId := by
        apply Obj.LabelsInterned.symAt_inj p2b_names_sz hnd hraw_lt hextra_raw_lt
        rw [hr', hraw, p2b_extra_raw_eq]
      have hbeq_true : Nat.beq s2.rawId p2bExtraRawId = true := Nat.beq_eq.mpr hs2_raw_eq
      rw [hbeq_true] at himp
      simp only [Bool.not_true, Bool.false_or] at himp
      rcases Eq.mp (Bool.and_eq_true _ _) himp with ⟨hs2_sec_b, hs2_nid_b⟩
      have hs2_sec : s2.sec = .undef := beq_iff_eq.mp hs2_sec_b
      have hs2_nid : s2.nameId = p2bExtraDemangledId := Nat.eq_of_beq_eq_true hs2_nid_b
      exact ⟨hsc'.symm.trans hs2_sec, by rw [← hn', hs2_nid, p2b_extra_demangled_eq]⟩
  · intro p hp hp_ne o ho sy hsy hraw hbind
    obtain ⟨s2, hs2_mem, hr', hn', _, hbd'⟩ :=
      panic_summary_has_matching_isym hp ho hsy hraw hbind
    have hs2_ok : p2bPanicSummaryISymOk s2 = true := hpans_ok s2 hs2_mem
    unfold p2bPanicSummaryISymOk at hs2_ok
    rcases Eq.mp (Bool.and_eq_true _ _) hs2_ok with ⟨hbounds, hbody⟩
    rcases Eq.mp (Bool.and_eq_true _ _) hbounds with ⟨_, hname_lt_b⟩
    have hname_lt : s2.nameId < p2bNumNames := Obj.Interned.blt_iff.mp hname_lt_b
    have hbn : (s2.bind != .local) = true := bne_iff_ne.mpr (hbd' ▸ hbind)
    rw [hbn] at hbody
    simp only [Bool.not_true, Bool.false_or] at hbody
    rcases Eq.mp (Bool.and_eq_true _ _) hbody with ⟨h12_s2, _⟩
    rcases Eq.mp (Bool.and_eq_true _ _) h12_s2 with ⟨_, hother⟩
    rcases Eq.mp (Bool.or_eq_true _ _) hother with hextra | hstd
    · have hs2_raw : s2.rawId = p2bExtraRawId := Nat.eq_of_beq_eq_true hextra
      have hp_eq : p = cliPanicExtraRawSym := by
        rw [← hraw, ← hr', hs2_raw, p2b_extra_raw_eq]
      exact absurd hp_eq hp_ne
    · rw [← hn', rust_isPanicSymbol_symAt hname_lt]
      exact hstd

/-- `cliPanicExtraRawSym` occurs as a non-local `.undef` symbol in `cliLinkObjs`, and every
non-local occurrence has `[sy.name] = cliPanicExtraDemangled`. -/
theorem cliPanicExtraRawSym_demangled_eq :
    (∃ o ∈ cliLinkObjs, ∃ sy ∈ o.symbols,
      sy.rawName = cliPanicExtraRawSym ∧ sy.bind ≠ .local ∧ sy.sec = .undef ∧
      [sy.name] = cliPanicExtraDemangled) ∧
    (∀ o ∈ cliLinkObjs, ∀ sy ∈ o.symbols,
      sy.rawName = cliPanicExtraRawSym → sy.bind ≠ .local →
      [sy.name] = cliPanicExtraDemangled) := by
  obtain ⟨hlist_eq, _, _, ⟨⟨o0, ho0, sy0, hsy0, hr0, hb0, hs0, hd0⟩, hall⟩, _⟩ :=
    cliPanicExtraSym_is_extraDemangled
  refine ⟨⟨o0, ho0, sy0, hsy0, hr0, hb0, hs0, hd0 ▸ hlist_eq⟩, ?_⟩
  intro o ho sy hsy hraw hbind
  have hd := (hall o ho sy hsy hraw hbind).2
  exact hd ▸ hlist_eq

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliPanicLabels
