/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.Placed
public import ProofLib.Placed.Split
public meta import ProofLib.Placed.Split
public meta import ProofLib.ProgramReflection
public meta import ProofLib.Testing.Perf.Budget
public import ProofLib.Testing.Perf.IncludeBytesFixture
meta import ProofLib.Testing.Perf.IncludeBytesFixture

/-!
# Chunked `include_bytes%` Scale and Reflection Regression Tests

Verifies that cross-module multi-chunk `include_bytes%` constants (including a 320 KiB computable
binary slice) support:
- fast runtime evaluation (`#guard`),
- linear-time `word_tree_of%` (`listElemsWhnf`) within a tight `#perf_budget`,
- kernel `rfl_kernel` equivalence against `WordTree.toBytes`,
- `gen_labels_from_objects` (`LabelsInterned.decodeBytes`) and `seg_lens%` (`Split.listLitLen`),
- exact stuck-spine handling in `listElemsWhnf` and negative `#guard_msgs` rejection in `seg_lens%`.
-/

set_option autoImplicit false

@[expose] public section

namespace Examples.Testing.ProofLib.Perf.IncludeBytesScale

open Arm64 Arm64.Process Arm64.Obj _root_.ProofLib _root_.ProofLib.ProgramReflection
  _root_.ProofLib.Placed.Split Examples.Testing.ProofLib.Perf.IncludeBytesFixture

/-! ## 1. 320 KiB Cross-Module Computable Evaluation, `word_tree_of%`, and `rfl_kernel` -/

#guard alphaCode320k.length == 327680

#perf_budget 30000 in
noncomputable def alphaTree320k : WordTree := word_tree_of% alphaProg320k

set_option maxRecDepth 4000000 in
theorem alphaCode320k_eq : alphaProg320k.code = alphaTree320k.toBytes := by
  rfl_kernel

set_option maxRecDepth 4000000 in
theorem alphaTree320k_size : alphaTree320k.checkSize? = some 81920 := by
  rfl_kernel

/-! ## 2. `gen_labels_from_objects` (`LabelsInterned.decodeBytes`) on Chunked `include_bytes%` -/

def alphaChunkedObjs : List ExtractedObj :=
  [ { name := "alpha_chunked.o"
      sections :=
        [ { name := ".text.alpha_chunked"
            bytes := alphaCode5000
            size := 5000
            align := 4
            isExec := true
            readOnly := true
            isNobits := false
            isTls := false
            relocs := [] } ]
      symbols :=
        [ { rawName := "", name := "", sec := .undef, value := 0, size := 0,
            kind := .other, bind := .local }
        , { rawName := "alpha_chunked_fn", name := "alpha_chunked_fn", sec := .sec 0,
            value := 0, size := 5000, kind := .func, bind := .global } ] } ]

def alphaChunkedLib : MultiPlacedLib :=
  { name := "alpha_chunked_lib"
    blocks :=
      [ { code := alphaCode5000
          align := 4
          symbols := [("alpha_chunked_fn", 0)]
          relocs := []
          externs := []
          weakRefs := [] } ]
    data := []
    exports := ["alpha_chunked_fn"]
    exportSyms := [("alpha_chunked_fn", "alpha_chunked_fn")] }

#perf_budget 25000 in
gen_labels_from_objects alpha_chunked_lbl alphaChunkedObjs alphaChunkedLib

/-! ## 3. `seg_lens%` (`Split.listLitLen`) Positive and Negative Tests -/

def alphaChunkedElf : ElfImage :=
  ElfImage.mk 0x400000#64 0x40#64 56 1
    [{ start := 0x400000#64, perm := { r := true, w := false, x := true }, bytes := alphaCode5000 }]
    0x402000#64 []

def alphaChunkedSegLens : List Nat := seg_lens% alphaChunkedElf

#guard alphaChunkedSegLens == [5000]

theorem alphaChunkedSegLens_eq :
    alphaChunkedElf.segments.map (fun r => rLen r.bytes) = alphaChunkedSegLens := by
  rfl_kernel

opaque opaqueElf : ElfImage

/-- error: seg_lens%: -/
#guard_msgs (substring := true) in
def badSegLens : List Nat := seg_lens% opaqueElf

/-! ## 4. `listElemsWhnf` Concrete vs Stuck-Spine Semantics -/

open Lean Meta in
#guard_msgs in
run_cmd Lean.Elab.Command.liftTermElabM do
  let listBv8 := mkApp (Lean.mkConst ``List [.zero]) (mkApp (Lean.mkConst ``BitVec) (mkNatLit 8))
  withLocalDeclD `xs listBv8 fun xs => do
    let twoBytes ← mkListLit (mkApp (Lean.mkConst ``BitVec) (mkNatLit 8))
      [mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 8) (mkNatLit 1),
       mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 8) (mkNatLit 2)]
    -- Stuck head (`xs ++ [1#8, 2#8]`) must stop immediately (`#[]`), never skip `xs`.
    let stuckHead ← mkAppM ``HAppend.hAppend #[xs, twoBytes]
    let elemsHead ← listElemsWhnf stuckHead
    unless elemsHead.size == 0 do
      throwError "expected 0 elements for stuck head, got {elemsHead.size}"
    -- Concrete prefix + stuck tail (`[1#8, 2#8] ++ xs`) returns the 2-element concrete prefix.
    let stuckTail ← mkAppM ``HAppend.hAppend #[twoBytes, xs]
    let elemsTail ← listElemsWhnf stuckTail
    unless elemsTail.size == 2 do
      throwError "expected 2 elements for concrete prefix + stuck tail, got {elemsTail.size}"
    -- `List.flatten` of two concrete lists returns all 4 elements.
    let flatExpr ← mkAppM ``List.flatten #[← mkListLit listBv8 [twoBytes, twoBytes]]
    let elemsFlat ← listElemsWhnf flatExpr
    unless elemsFlat.size == 4 do
      throwError "expected 4 elements for List.flatten, got {elemsFlat.size}"

end Examples.Testing.ProofLib.Perf.IncludeBytesScale
end
