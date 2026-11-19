/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.Bridge -- proof-setup: allow-public-import
public import ProofLib.Placed.Multi
meta import LibsignalBinary.Proofs.Placed.Bridge
meta import ProofLib.ProgramReflection
meta import Lean

/-!
# Compatibility Balanced `IdxTree` of `libsignalSessionBlocks`

Provides `lsBlocksTree` and `blockLib_eq_of_lsBlocksTree` in a standalone opt-in module so
`GenLsBlock.lean` and its 114 `gen_ls_blk*` consumers do not pay the 4.9 MiB `.olean` cost of
serializing all 624 `CodeBlock` descriptors in `GenLsBlock.olean`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.Placed.BlocksTreeDefs

open Arm64
open Arm64.Obj
open ProofLib
open Lean Meta Elab Term
open CryptoVerification (
  IdxTree
  libsignalSessionBlocks
  libsignalSessionData
  libsignalSessionLib
  libsignalSessionMultiLib
)

private meta partial def mkIdxTreeExprBtd (ty : Expr) (elems : Array Expr) (lo hi : Nat) : Expr :=
  if _h : lo < hi then
    if hi - lo == 1 then
      mkApp2 (Lean.mkConst ``IdxTree.leaf) ty elems[lo]!
    else
      let mid := (lo + hi) / 2
      let l := mkIdxTreeExprBtd ty elems lo mid
      let r := mkIdxTreeExprBtd ty elems mid hi
      mkApp4 (Lean.mkConst ``IdxTree.node) ty (mkNatLit (mid - lo)) l r
  else
    mkApp (Lean.mkConst ``IdxTree.empty) ty

local elab "blocks_idx_tree_of% " listStx:term:max : term => do
  let listE ← elabTerm listStx none
  let elems ← ProofLib.ProgramReflection.listElemsWhnf listE
  return mkIdxTreeExprBtd (Lean.mkConst ``CodeBlock) elems 0 elems.size

set_option maxHeartbeats 0 in
/-- Balanced binary tree of the 624 `CodeBlock` entries of `libsignalSessionBlocks`. -/
-- noncomputable: compiling this 624-CodeBlock reflected IdxTree literal roughly quadruples this module's build time
@[expose] noncomputable def _root_.CryptoVerification.lsBlocksTree : IdxTree CodeBlock :=
  blocks_idx_tree_of% libsignalSessionBlocks

private theorem lsBlocksTree_toList :
    _root_.CryptoVerification.lsBlocksTree.toList = libsignalSessionLib.blocks :=
  rfl

private theorem lsBlocksTree_size :
    _root_.CryptoVerification.lsBlocksTree.size? = some 624 := by
  decide +kernel

theorem _root_.CryptoVerification.blockLib_eq_of_lsBlocksTree
    {lib : PlacedLib} {i : Nat} {blk : CodeBlock}
    (hget : _root_.CryptoVerification.lsBlocksTree.getFast? i = some blk)
    (hlib : lib = { name := "libsignalSession", text := blk, data := libsignalSessionData,
                    exports := libsignalSessionMultiLib.exports }) :
    lib = libsignalSessionLib.blockLib i := by
  subst hlib
  have hg0 : _root_.CryptoVerification.lsBlocksTree.get? i = some blk :=
    (IdxTree.getFast?_eq_get? _root_.CryptoVerification.lsBlocksTree i).symm.trans hget
  have h1 : libsignalSessionLib.blocks[i]? = some blk :=
    (congrArg (·[i]?) lsBlocksTree_toList.symm).trans
      ((IdxTree.get?_eq_toList_getElem? lsBlocksTree_size i).symm.trans hg0)
  unfold MultiPlacedLib.blockLib
  change PlacedLib.mk "libsignalSession" blk _ _ =
    PlacedLib.mk libsignalSessionLib.name (libsignalSessionLib.blocks.getD i { code := [] })
      libsignalSessionLib.data libsignalSessionLib.exports
  have hgetD : libsignalSessionLib.blocks.getD i { code := [] } = blk := by
    rw [List.getD_eq_getElem?_getD, h1]; rfl
  rw [hgetD]
  rfl

end LibsignalBinary.Proofs.Placed.BlocksTreeDefs
