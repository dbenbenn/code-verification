/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.GenLsBlockFast -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.Placed.GenLsBlockFast -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.Placed.GenLsBlock -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.Placed.PlacedCallSym -- proof-setup: allow-public-import
meta import LibsignalBinary.Proofs.Placed.Bridge
public meta import ProofLib.ProgramReflection
public meta import ProofLib.GenPlacedFetches
public meta import ProofLib.GenDecodes
public meta import Lean
import ProofLib.Hoare.Hooks
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Proofs.Placed.GenLsBlock -- proof-setup: allow-public-import

/-!
# Tree-Accelerated Per-Block Fetch and Relocation Elaborator

Defines `gen_ls_blk_ultra <idx>`, emitting the same per-block declarations and theorem signatures as
`gen_ls_blk <idx>` (with `rel_<idx>` relocation symbol tags) via `elabGenLsBlkImpl` and
`FastDecode.elabFastPlacedFetchesForBlock`, plus 64-bucket `IdxTree` symbol lookup lemmas.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches

theorem ls_hook_ok_ultra_of_mem [LibsignalPlacement] {α : Type} {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {sym : String} {spec : Spec α} (hsat : HookSat H sym spec)
    (hmem : sym ∈ libsignalHookedExterns := by ls_extern_mem_tac)
    {bi : Nat} [LsBlockBound bi]
    (hi : i < bi := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ sym) spec := by
  obtain ⟨f, hf, hok⟩ := hsat
  exact subroutine_ok_of_hookOk ((ls_externAt?_of_mem hmem hi hunmut).trans hf) hok

syntax (name := genLsBlkUltraStx) "gen_ls_blk_ultra " num : command

section MetaGenLsBlkUltra

open Lean Meta Elab Term Command

private meta def whnfAllU (e : Expr) : MetaM Expr := withTransparency .all (whnf e)

private meta def evalStrLitU (e : Expr) : MetaM String := do
  let r ← whnfAllU e
  match r with
  | .lit (.strVal s) => return s
  | _ =>
    let r2 ← withTransparency .all (reduce e)
    match r2 with
    | .lit (.strVal s) => return s
    | _ => throwError "gen_ls_blk_ultra: expected string literal, got {r2}"

private meta def evalNatExprU? (e : Expr) : MetaM (Option Nat) := do
  if let .lit (.natVal n) := e then return some n
  let r ← whnfAllU e
  if let some n := r.rawNatLit? then return some n
  if let some n := r.nat? then return some n
  let r2 ← withTransparency .all (reduce e)
  if let some n := r2.rawNatLit? then return some n
  if let some n := r2.nat? then return some n
  return none

private meta partial def collectSymIdxTreeU (treeE : Expr)
    (acc : Array (String × Nat × Nat))
    (seen : Std.HashSet String)
    (counts : Std.HashMap Nat Nat) :
    MetaM (Array (String × Nat × Nat) × Std.HashSet String × Std.HashMap Nat Nat) := do
  let r ← whnfAllU treeE
  if r.isAppOfArity ``IdxTree.empty 1 then
    return (acc, seen, counts)
  else if r.isAppOfArity ``IdxTree.leaf 2 then
    let pE ← whnfAllU (r.getArg! 1)
    let s ← evalStrLitU (pE.getArg! 2)
    let some j ← evalNatExprU? (pE.getArg! 3)
      | throwError "gen_ls_blk_ultra: invalid block index in lsBlockSymIdxTree"
    if seen.contains s then
      return (acc, seen, counts)
    else
      let k := counts.getD j 0
      return (acc.push (s, j, k), seen.insert s, counts.insert j (k + 1))
  else if r.isAppOfArity ``IdxTree.node 4 then
    let (acc, seen, counts) ← collectSymIdxTreeU (r.getArg! 2) acc seen counts
    collectSymIdxTreeU (r.getArg! 3) acc seen counts
  else
    throwError "gen_ls_blk_ultra: unexpected lsBlockSymIdxTree expression {r}"

private meta partial def mkBktTreeU (elemTy : Expr) (elems : Array Expr) (lo hi : Nat) : Expr :=
  if hi - lo == 1 then
    mkApp2 (Lean.mkConst ``IdxTree.leaf) elemTy elems[lo]!
  else
    let mid := (lo + hi) / 2
    mkApp4 (Lean.mkConst ``IdxTree.node) elemTy (mkNatLit (mid - lo))
      (mkBktTreeU elemTy elems lo mid) (mkBktTreeU elemTy elems mid hi)

local elab "#init_ls_sym_buckets64" : command => liftTermElabM do
  let currNs ← getCurrNamespace
  let (entries, _, _) ← collectSymIdxTreeU (Lean.mkConst ``lsBlockSymIdxTree) #[] {} {}
  let strTy := Lean.mkConst ``String
  let natTy := Lean.mkConst ``Nat
  let strNatTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) strTy natTy
  let mut bkts : Array (Array Expr) := Array.replicate 64 #[]
  for (s, j, _) in entries do
    let sjE := mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) strTy natTy (mkStrLit s) (mkNatLit j)
    let bi := s.utf8ByteSize % 64
    bkts := bkts.modify bi (·.push sjE)
  let listPairTy := mkApp (Lean.mkConst ``List [.zero]) strNatTy
  let mut bktListExprs : Array Expr := #[]
  for b in bkts do
    bktListExprs := bktListExprs.push (← mkListLit strNatTy b.toList)
  withExporting <| addDecl (.defnDecl {
    name := currNs ++ `lsSymBuckets64, levelParams := [],
    type := mkApp (Lean.mkConst ``IdxTree) listPairTy,
    value := mkBktTreeU listPairTy bktListExprs 0 64, hints := .regular 0, safety := .safe
  })

set_option maxHeartbeats 0 in
#init_ls_sym_buckets64

@[expose] noncomputable def lsBucketLookup (name : String) : Option Nat :=
  match lsSymBuckets64.get? (name.utf8ByteSize % 64) with
  | some bkt => lookup name bkt
  | none => none

private def checkTreeIdxU {α : Type} (f : Nat → α → Bool) : Nat → IdxTree α → Bool
  | _, .empty => true
  | base, .leaf v => f base v
  | base, .node leftSz l r => checkTreeIdxU f base l && checkTreeIdxU f (base + leftSz) r

private def checkListIdxU {α : Type} (f : Nat → α → Bool) : Nat → List α → Bool
  | _, [] => true
  | base, x :: xs => f base x && checkListIdxU f (base + 1) xs

private theorem checkListIdxU_append {α : Type} (f : Nat → α → Bool) :
    ∀ (base : Nat) (l1 l2 : List α),
      checkListIdxU f base (l1 ++ l2) =
        (checkListIdxU f base l1 && checkListIdxU f (base + l1.length) l2)
  | base, [], l2 => by simp [checkListIdxU]
  | base, x :: xs, l2 => by
    simp [checkListIdxU, checkListIdxU_append f (base + 1) xs l2, Bool.and_assoc,
      Nat.add_right_comm, Nat.add_assoc]

private theorem checkTreeIdxU_eq_checkListIdxU {α : Type} (f : Nat → α → Bool) :
    ∀ {t : IdxTree α} {n : Nat}, t.size? = some n →
      ∀ (base : Nat), checkTreeIdxU f base t = checkListIdxU f base t.toList
  | .empty, _, _, _ => rfl
  | .leaf v, _, _, base => by simp [checkTreeIdxU, checkListIdxU, IdxTree.toList]
  | .node leftSz l r, _, h, base => by
    simp only [IdxTree.size?] at h
    cases hl : l.size? with
    | none => simp [hl] at h
    | some ls =>
      cases hr : r.size? with
      | some rs =>
        simp only [hl, hr] at h
        split at h
        · rename_i heq
          rw [beq_iff_eq] at heq
          subst heq
          have hllen := IdxTree.length_toList_of_size? hl
          simp [checkTreeIdxU, IdxTree.toList, checkListIdxU_append,
            checkTreeIdxU_eq_checkListIdxU f hl base,
            checkTreeIdxU_eq_checkListIdxU f hr (base + leftSz), hllen]
        · cases h
      | none => simp [hl, hr] at h

private theorem lsBlockSyms_bucket_sound :
    checkTreeIdxU (fun i syms => syms.all (fun p => lsBucketLookup p.1 == some i))
      0 lsBlockSymsTree = true := by
  decide +kernel

private theorem lookupSymInLists_none_of_bucketNone {tgt : String} (hb : lsBucketLookup tgt = none) :
    ∀ (base : Nat) (lists : List (List (String × Nat))),
      checkListIdxU (fun i syms => syms.all (fun p => lsBucketLookup p.1 == some i)) base lists = true →
      lookupSymInLists tgt base lists = none
  | _, [], _ => rfl
  | base, syms :: rest, hc => by
    simp only [checkListIdxU, Bool.and_eq_true] at hc
    have hnone : lookup tgt syms = none := by
      apply lookup_none_of_not_mem_fst
      intro hmem
      obtain ⟨⟨s, off⟩, hp, rfl⟩ := List.mem_map.1 hmem
      have hall := List.all_eq_true.1 hc.1 (s, off) hp
      rw [beq_iff_eq] at hall
      rw [hb] at hall
      cases hall
    simp only [lookupSymInLists, hnone]
    exact lookupSymInLists_none_of_bucketNone hb (base + 1) rest hc.2

theorem ls_resolve_data_ultra {pl : MultiPlacement} {tgt : String}
    (h : (lsBucketLookup tgt).isNone = true) :
    libsignalSessionLib.resolve pl tgt = pl.ρ tgt := by
  have hb : lsBucketLookup tgt = none := Option.isNone_iff_eq_none.mp h
  have hc : checkListIdxU (fun i syms => syms.all (fun p => lsBucketLookup p.1 == some i))
      0 lsBlockSymsTree.toList = true := by
    rw [← checkTreeIdxU_eq_checkListIdxU _ lsBlockSymsTree_size 0]
    exact lsBlockSyms_bucket_sound
  have hlk : lookupBlockSym tgt libsignalSessionLib.blocks = none := by
    rw [lookupBlockSym_eq_lookupSymInLists, ← lsBlockSymsTree_toList]
    exact lookupSymInLists_none_of_bucketNone hb 0 _ hc
  simp [MultiPlacedLib.resolve, hlk]

@[expose] noncomputable def checkBlockSymAtU (i : Nat) (tgt : String) : Bool :=
  (lsBucketLookup tgt == some i) &&
  match lsBlockSymsTree.get? i with
  | some syms => lookup tgt syms == some 0
  | none => false

private theorem lookupSymInLists_at_of_bucket {tgt : String} {i : Nat}
    {syms : List (String × Nat)}
    (hb : lsBucketLookup tgt = some i) :
    ∀ (base : Nat) (lists : List (List (String × Nat))),
      base ≤ i →
      lists[i - base]? = some syms →
      lookup tgt syms = some 0 →
      checkListIdxU (fun k s => s.all (fun p => lsBucketLookup p.1 == some k)) base lists = true →
      lookupSymInLists tgt base lists = some (i, 0)
  | _, [], _, hget, _, _ => by simp at hget
  | base, s0 :: rest, hle, hget, hlk, hc => by
    simp only [checkListIdxU, Bool.and_eq_true] at hc
    by_cases heq : i = base
    · subst heq
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      simp [lookupSymInLists, hlk]
    · have hlt : base < i := by omega
      have hsub : i - base = (i - (base + 1)) + 1 := by omega
      rw [hsub, List.getElem?_cons_succ] at hget
      have hnone : lookup tgt s0 = none := by
        apply lookup_none_of_not_mem_fst
        intro hmem
        obtain ⟨⟨s, off⟩, hp, rfl⟩ := List.mem_map.1 hmem
        have hall := List.all_eq_true.1 hc.1 (s, off) hp
        rw [beq_iff_eq, hb, Option.some.injEq] at hall
        omega
      simp only [lookupSymInLists, hnone]
      exact lookupSymInLists_at_of_bucket hb (base + 1) rest (by omega) hget hlk hc.2

theorem lookupBlockSym_of_checkBlockSymAtU {i : Nat} {tgt : String}
    (h : checkBlockSymAtU i tgt = true) :
    lookupBlockSym tgt libsignalSessionLib.blocks = some (i, 0) := by
  unfold checkBlockSymAtU at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  cases hg : lsBlockSymsTree.get? i with
  | none => simp [hg] at h
  | some syms =>
    simp only [hg, beq_iff_eq] at h
    have hget : lsBlockSymsTree.toList[i]? = some syms := by
      rw [← IdxTree.get?_eq_toList_getElem? lsBlockSymsTree_size i]
      exact hg
    have hc : checkListIdxU (fun k s => s.all (fun p => lsBucketLookup p.1 == some k))
        0 lsBlockSymsTree.toList = true := by
      rw [← checkTreeIdxU_eq_checkListIdxU _ lsBlockSymsTree_size 0]
      exact lsBlockSyms_bucket_sound
    rw [lookupBlockSym_eq_lookupSymInLists, ← lsBlockSymsTree_toList]
    exact lookupSymInLists_at_of_bucket (syms := syms) h.1 0 _ (Nat.zero_le i)
      (by simpa using hget) h.2 hc

theorem ls_resolve_block_ultra {pl : MultiPlacement} {tgt : String} {i : Nat}
    (h : checkBlockSymAtU i tgt = true) :
    libsignalSessionLib.resolve pl tgt = pl.base i := by
  simp [MultiPlacedLib.resolve, lookupBlockSym_of_checkBlockSymAtU h]

theorem ls_fnAddr_block_ultra {pl : MultiPlacement} {tgt : String} {i : Nat}
    (h : checkBlockSymAtU i tgt = true) :
    libsignalSessionLib.fnAddr pl tgt = pl.base i := by
  simp [MultiPlacedLib.fnAddr, lookupBlockSym_of_checkBlockSymAtU h]

theorem lsProg_fnAddr_of_blockProg_ultra [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H] {tgt : String}
    (h : checkBlockSymAtU i tgt = true) :
    prog.fnAddr tgt = lsmpl.base i := by
  rw [hprog.eq_blockProgram]
  have h' := libsignalSessionLib_blockProgram_fnAddr (pl := lsmpl) (H := H)
    (lookupBlockSym_of_checkBlockSymAtU h)
  exact h'.1.trans h'.2

@[command_elab genLsBlkUltraStx]
meta def elabGenLsBlkUltra : CommandElab := fun stx => do
  match stx with
  | `(command| gen_ls_blk_ultra $idxStx:num) =>
    elabGenLsBlkImpl idxStx true s!"rel_{idxStx.getNat}" true
  | _ => throwUnsupportedSyntax

end MetaGenLsBlkUltra

end CryptoVerification
