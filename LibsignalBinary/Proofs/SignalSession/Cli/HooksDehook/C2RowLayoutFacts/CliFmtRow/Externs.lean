/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.MuslMemOpsRunsTo
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.Code -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.TimeAddPanic
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesDataRefl3
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesDataRefl4
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# Exact `externAt?` Agreement Between `c2FmtProg`, `c2FmtProgTrap lr`, and Block `617` (`CliFmtRow.Externs`)
-/

set_option autoImplicit false
set_option maxRecDepth 4000000

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.Externs

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoVerification (libsignalSessionExterns)
open CryptoVerification.SignalSession
  (CliHooks cliCratePanicSyms cliElfBytes cliExternsPlaced isCliPanicSymbolPlaced
   libsignalSessionLib)
open LibsignalBinary.Heap.Fine (f3RxWordCount)
open LibsignalBinary.Heap.MuslMemOpsRunsTo (BlockExternFree)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.AesCbc
  (keepRxSeg keepRxSeg_eq_lt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.Defs
  (c2FmtExterns c2FmtProg c2FmtProgTrap c2FmtProgTrap_base c2FmtProgTrap_externs
   c2FmtProgTrap_stubs c2FmtProgTrap_symbols c2FmtProg_base c2FmtProg_externs c2FmtProg_stubs
   c2FmtProg_symbols c2FmtStubs c2HaltHook c2LrTrapSym c2Seg1Start)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon
  (libsignalSessionExterns_resolve_eq_rho)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.TimeAddPanic
  (externAt?_cliProgExtPlacedAt_617 ls_block617_externs_eq_libsignalSessionExterns)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
  (lsPlacedStubPairs lsPlacedStubPairs_eq ls_block617_externs_eq ls_sharedExterns_lt)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (isLinkedPanicAddr isLinkedPanicAddr_false_of_lt keepLib2Text keepLib2Text_sub_rxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (f3RxSegBase)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced
  (cliElfMultiPlacement cliElfSymAddrs cliElf_linkedAt_unique lsInternedMultiLib ls_names_nodup)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2FirstExternStubAddr wp4HandleErrorAddr)

private theorem string_startsWith_eq_isPrefixOf (s pat : String) :
    s.startsWith pat = List.isPrefixOf pat.toList s.toList := by
  rw [Bool.eq_iff_iff, String.startsWith_string_iff, List.isPrefixOf_iff_prefix]

private def panicPrefixChars : List Char :=
  ['c', 'o', 'r', 'e', ':', ':', 'p', 'a', 'n', 'i', 'c', 'k', 'i', 'n', 'g', ':', ':']

private theorem core_panicking_toList_eq : "core::panicking::".toList = panicPrefixChars := by
  decide

private def isPanicSymbolFast (name : String) : Bool :=
  List.isPrefixOf panicPrefixChars name.toList ||
  [ "core::result::unwrap_failed",
    "core::option::unwrap_failed",
    "core::option::expect_failed",
    "core::slice::index::slice_start_index_len_fail",
    "core::slice::index::slice_end_index_len_fail",
    "core::slice::index::slice_index_order_fail",
    "core::slice::index::slice_index_fail",
    "alloc::raw_vec::handle_error",
    "alloc::raw_vec::capacity_overflow",
    "alloc::alloc::handle_alloc_error" ].contains name

private def isCliPanicSymbolPlacedFast (s : String) : Bool :=
  cliCratePanicSyms.contains s || isPanicSymbolFast s

private theorem isCliPanicSymbolPlaced_eq_fast (s : String) :
    isCliPanicSymbolPlaced s = isCliPanicSymbolPlacedFast s := by
  unfold isCliPanicSymbolPlaced isCliPanicSymbolPlacedFast Rust.isPanicSymbol isPanicSymbolFast
  rw [string_startsWith_eq_isPrefixOf, core_panicking_toList_eq]

private theorem ls_externs_eq_stubPairs_fst :
    libsignalSessionExterns = lsPlacedStubPairs.map Prod.fst := by
  rw [← ls_block617_externs_eq_libsignalSessionExterns, ls_block617_externs_eq,
    lsPlacedStubPairs_eq, List.map_map]
  rfl

theorem list_getD_eq_getElem {α : Type} (l : List α) (d : α) {i : Nat}
    (hi : i < l.length) : l.getD i d = l[i] := by
  simp [List.getD, hi]

private theorem cliElfMultiPlacement_rho_of_getD {idx : Nat} {s : String}
    (hlt : idx < lsInternedMultiLib.names.length)
    (hn : lsInternedMultiLib.names.getD idx "" = s) :
    cliElfMultiPlacement.ρ s = cliElfSymAddrs.getD idx 0#64 := by
  subst hn
  change cliElfSymAddrs.getD
    (lsInternedMultiLib.names.idxOf (lsInternedMultiLib.names.getD idx "")) 0#64 =
    cliElfSymAddrs.getD idx 0#64
  rw [Obj.Interned.idxOf_getD ls_names_nodup hlt]

private theorem lsPlacedStubPairs_mem_and_rho :
    ∀ p ∈ lsPlacedStubPairs,
      p.1 ∈ lsInternedMultiLib.names ∧ cliElfMultiPlacement.ρ p.1 = p.2 := by
  rw [lsPlacedStubPairs_eq]
  intro p hp
  obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp hp
  have hlt : idx < lsInternedMultiLib.names.length :=
    Nat.blt_eq.mp (List.all_eq_true.mp ls_sharedExterns_lt idx hidx)
  have hmem : lsInternedMultiLib.names.getD idx "" ∈ lsInternedMultiLib.names := by
    rw [list_getD_eq_getElem _ _ hlt]
    exact List.getElem_mem hlt
  exact ⟨hmem, cliElfMultiPlacement_rho_of_getD hlt rfl⟩

private theorem sub_toNat_beq_eq (a b base : BitVec 64) :
    ((a - base).toNat == (b - base).toNat) = (a == b) := by
  cases h : a == b with
  | true =>
    rw [beq_iff_eq.mp h, beq_self_eq_true]
  | false =>
    rw [beq_eq_false_iff_ne] at h ⊢
    intro hnat
    apply h
    have hbv := BitVec.eq_of_toNat_eq hnat
    have hadd : (a - base) + base = (b - base) + base := congrArg (· + base) hbv
    simpa [BitVec.sub_add_cancel] using hadd

set_option maxHeartbeats 2000000 in
private theorem c2FmtExterns_stub_bounds_pairs_chk :
    (lsPlacedStubPairs.all fun (e, a) =>
      !isCliPanicSymbolPlacedFast e ||
        (Nat.ble c2FirstExternStubAddr.toNat a.toNat &&
         isLinkedPanicAddr a)) = true := by
  rfl_kernel

set_option maxHeartbeats 2000000 in
private theorem c2FmtProg_externAt_handleError_pairs_chk :
    (lsPlacedStubPairs.findSome? fun (e, a) =>
      if a == wp4HandleErrorAddr then
        if isCliPanicSymbolPlacedFast e then some true else none
      else none) = some true := by
  rfl_kernel

private theorem c2FmtStubs_no_trapSym_pairs :
    (lsPlacedStubPairs.all fun p => !(p.1 == c2LrTrapSym)) = true := by
  rfl_kernel

private theorem program_externAt?_of_symbols_nil (prog : Program) (hSym : prog.symbols = [])
    (pc : BitVec 64) :
    prog.externAt? pc =
      prog.stubs.findSome? fun s =>
        if s.2 == (pc - prog.base).toNat then prog.externs s.1 else none := by
  unfold Program.externAt? Program.hookAtOff?
  rw [hSym]
  simp only [List.findSome?_nil, Option.or_none]

private theorem c2FmtStubs_eq :
    c2FmtStubs = libsignalSessionExterns.map fun e =>
      (e, (cliElfMultiPlacement.ρ e - c2Seg1Start).toNat) := by
  unfold c2FmtStubs
  rw [ls_block617_externs_eq_libsignalSessionExterns]

attribute [local irreducible] c2Seg1Start c2FmtStubs c2FmtProg c2FmtProgTrap
attribute [local irreducible]
  LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData.f3LsMpl
  lsPlacedStubPairs libsignalSessionExterns

private theorem c2FmtProg_externAt_unfold (pc : BitVec 64) :
    c2FmtProg.externAt? pc =
      c2FmtStubs.findSome? fun s =>
        if s.2 == (pc - c2Seg1Start).toNat then c2FmtExterns s.1 else none := by
  rw [program_externAt?_of_symbols_nil c2FmtProg c2FmtProg_symbols,
    c2FmtProg_stubs, c2FmtProg_base, c2FmtProg_externs]

private theorem c2FmtProgTrap_externAt_unfold (lr pc : BitVec 64) :
    (c2FmtProgTrap lr).externAt? pc =
      ((c2LrTrapSym, (lr - c2Seg1Start).toNat) :: c2FmtStubs).findSome? fun s =>
        if s.2 == (pc - c2Seg1Start).toNat then
          if s.1 == c2LrTrapSym then some c2HaltHook else c2FmtExterns s.1
        else none := by
  rw [program_externAt?_of_symbols_nil (c2FmtProgTrap lr) (c2FmtProgTrap_symbols lr),
    c2FmtProgTrap_stubs, c2FmtProgTrap_base, c2FmtProgTrap_externs]

private theorem c2FmtExterns_stub_bounds_chk :
    (libsignalSessionExterns.all fun e =>
      let a := cliElfMultiPlacement.ρ e
      !isCliPanicSymbolPlaced e ||
        (Nat.ble c2FirstExternStubAddr.toNat a.toNat &&
         isLinkedPanicAddr a)) = true := by
  rw [ls_externs_eq_stubPairs_fst, List.all_map]
  refine List.all_eq_true.mpr fun p hp => ?_
  have hp0 := List.all_eq_true.mp c2FmtExterns_stub_bounds_pairs_chk p hp
  have hrho := (lsPlacedStubPairs_mem_and_rho p hp).2
  dsimp only [Function.comp_apply]
  rw [hrho, isCliPanicSymbolPlaced_eq_fast]
  exact hp0

private theorem resolve_extern_eq_rho {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {e : String} (he : e ∈ libsignalSessionExterns) :
    libsignalSessionLib.resolve mpl e = cliElfMultiPlacement.ρ e := by
  have he' : e ∈ lsPlacedStubPairs.map Prod.fst := ls_externs_eq_stubPairs_fst ▸ he
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he'
  have hname : p.1 ∈ lsInternedMultiLib.names := (lsPlacedStubPairs_mem_and_rho p hp).1
  exact ((cliElf_linkedAt_unique hLs).2.1 p.1 hname).trans
    (libsignalSessionExterns_resolve_eq_rho cliElfMultiPlacement p.1 he)

private theorem c2FmtExterns_eq_cliExternsPlaced (mmpl : MultiPlacement) (W : CliHooks)
    (e : String) :
    c2FmtExterns e = cliExternsPlaced mmpl W e := by
  unfold c2FmtExterns cliExternsPlaced
  rfl

/-- Pointwise `externAt?` identity: `c2FmtProg` has the exact same extern hooks at every `pc` as
    the 0-hook real Block-`617` program `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W`. -/
theorem c2FmtProg_externAt_eq_real {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (mmpl : MultiPlacement) (W : CliHooks) (pc : BitVec 64) :
    c2FmtProg.externAt? pc =
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc := by
  rw [externAt?_cliProgExtPlacedAt_617, c2FmtProg_externAt_unfold, c2FmtStubs_eq,
    List.findSome?_map, ls_block617_externs_eq_libsignalSessionExterns]
  have hpoint : ∀ e ∈ libsignalSessionExterns,
      (if ((cliElfMultiPlacement.ρ e - c2Seg1Start).toNat == (pc - c2Seg1Start).toNat) = true
       then c2FmtExterns e else none) =
      (if libsignalSessionLib.resolve mpl e == pc then cliExternsPlaced mmpl W e else none) := by
    intro e he
    rw [resolve_extern_eq_rho hLs he, ← c2FmtExterns_eq_cliExternsPlaced mmpl W e,
      sub_toNat_beq_eq]
  revert hpoint
  generalize libsignalSessionExterns = es
  intro hpoint
  induction es with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.findSome?_cons, Function.comp_apply]
    rw [hpoint e (.head _)]
    cases (if libsignalSessionLib.resolve mpl e == pc then cliExternsPlaced mmpl W e else none) with
    | none => exact ih fun x hx => hpoint x (.tail _ hx)
    | some f => rfl

/-- Every active extern stub of `c2FmtProg` is one of the `18` `cliLinkedPanicAddrs`
    (`≥ c2FirstExternStubAddr`) and runs `Rust.panicked`. -/
theorem c2FmtProg_externAt_some_bounds {pc : BitVec 64} {f : State → State}
    (he : c2FmtProg.externAt? pc = some f) :
    f = Rust.panicked ∧
      c2FirstExternStubAddr.toNat ≤ pc.toNat ∧ isLinkedPanicAddr pc = true := by
  rw [c2FmtProg_externAt_unfold, c2FmtStubs_eq, List.findSome?_map] at he
  obtain ⟨e, heMem, heHit⟩ := List.exists_of_findSome?_eq_some he
  dsimp only [Function.comp_apply] at heHit
  rw [sub_toNat_beq_eq] at heHit
  cases hoff : (cliElfMultiPlacement.ρ e == pc) with
  | false => simp only [hoff, Bool.false_eq_true, ↓reduceIte] at heHit; cases heHit
  | true =>
    simp only [hoff, ↓reduceIte] at heHit
    unfold c2FmtExterns at heHit
    cases hpan : isCliPanicSymbolPlaced e with
    | false => simp only [hpan, Bool.false_eq_true, ↓reduceIte] at heHit; cases heHit
    | true =>
      simp only [hpan, ↓reduceIte] at heHit
      injection heHit with hf
      have hbnd := List.all_eq_true.mp c2FmtExterns_stub_bounds_chk e heMem
      dsimp only at hbnd
      simp only [hpan, Bool.not_true, Bool.false_or, Bool.and_eq_true,
        Nat.ble_eq] at hbnd
      rw [← beq_iff_eq.mp hoff]
      exact ⟨hf.symm, hbnd.1, hbnd.2⟩

theorem c2FmtProg_externAt_none_of_lt_stub {pc : BitVec 64}
    (hlt : pc.toNat < c2FirstExternStubAddr.toNat) :
    c2FmtProg.externAt? pc = none := by
  cases he : c2FmtProg.externAt? pc with
  | none => rfl
  | some f =>
    have ⟨_, hge, _⟩ := c2FmtProg_externAt_some_bounds he
    omega

theorem c2FmtProg_externAt_none_of_not_panic {pc : BitVec 64}
    (hnp : isLinkedPanicAddr pc = false) :
    c2FmtProg.externAt? pc = none := by
  cases he : c2FmtProg.externAt? pc with
  | none => rfl
  | some f =>
    have ⟨_, _, hp⟩ := c2FmtProg_externAt_some_bounds he
    cases hp.symm.trans hnp

theorem c2FmtProg_externAt_handleError :
    c2FmtProg.externAt? wp4HandleErrorAddr = some Rust.panicked := by
  rw [c2FmtProg_externAt_unfold, c2FmtStubs_eq, List.findSome?_map,
    ls_externs_eq_stubPairs_fst, List.findSome?_map]
  have hcongr : ∀ p ∈ lsPlacedStubPairs,
      (if ((cliElfMultiPlacement.ρ p.1 - c2Seg1Start).toNat ==
          (wp4HandleErrorAddr - c2Seg1Start).toNat) = true
       then c2FmtExterns p.1 else none) =
      ((if (p.2 == wp4HandleErrorAddr) = true then
        if isCliPanicSymbolPlacedFast p.1 then some true else none
      else none)).map (fun _ => Rust.panicked) := by
    intro p hp
    rw [(lsPlacedStubPairs_mem_and_rho p hp).2, sub_toNat_beq_eq]
    unfold c2FmtExterns
    rw [isCliPanicSymbolPlaced_eq_fast]
    cases (p.2 == wp4HandleErrorAddr) with
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; rfl
    | true =>
      simp only [↓reduceIte]
      cases isCliPanicSymbolPlacedFast p.1 <;> rfl
  trans ((lsPlacedStubPairs.findSome? fun (e, a) =>
      if a == wp4HandleErrorAddr then
        if isCliPanicSymbolPlacedFast e then some true else none
      else none).map (fun _ => Rust.panicked))
  · revert hcongr
    generalize lsPlacedStubPairs = ps
    intro hcongr
    induction ps with
    | nil => rfl
    | cons p rest ih =>
      simp only [List.findSome?_cons, Function.comp_apply]
      rw [hcongr p (.head _)]
      cases (if (p.2 == wp4HandleErrorAddr) = true then
        if isCliPanicSymbolPlacedFast p.1 then some true else none
      else none) with
      | none => exact ih fun q hq => hcongr q (.tail _ hq)
      | some _ => rfl
  · rw [c2FmtProg_externAt_handleError_pairs_chk]
    rfl

/-- Behavior of `(c2FmtProgTrap lr).externAt? pc`: returns `some c2HaltHook` at `pc = lr`, and
    agrees identically with `c2FmtProg.externAt? pc` at every `pc ≠ lr`. -/
theorem c2FmtProgTrap_externAt_self (lr : BitVec 64) :
    (c2FmtProgTrap lr).externAt? lr = some c2HaltHook := by
  rw [c2FmtProgTrap_externAt_unfold]
  simp only [List.findSome?_cons, beq_self_eq_true, ↓reduceIte]

private theorem c2FmtStubs_no_trapSym :
    (libsignalSessionExterns.all fun x => !(x == c2LrTrapSym)) = true := by
  rw [ls_externs_eq_stubPairs_fst, List.all_map]
  exact c2FmtStubs_no_trapSym_pairs

theorem c2FmtProgTrap_externAt_of_ne {lr pc : BitVec 64} (hne : pc ≠ lr) :
    (c2FmtProgTrap lr).externAt? pc = c2FmtProg.externAt? pc := by
  rw [c2FmtProgTrap_externAt_unfold, c2FmtProg_externAt_unfold]
  simp only [List.findSome?_cons]
  have hneOff : (((lr - c2Seg1Start).toNat == (pc - c2Seg1Start).toNat) = false) := by
    rw [sub_toNat_beq_eq, beq_eq_false_iff_ne]
    exact hne.symm
  rw [hneOff]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have htail : ∀ s ∈ c2FmtStubs,
      (if s.2 == (pc - c2Seg1Start).toNat then
        if s.1 == c2LrTrapSym then some c2HaltHook else c2FmtExterns s.1
       else none) =
      (if s.2 == (pc - c2Seg1Start).toNat then c2FmtExterns s.1 else none) := by
    rw [c2FmtStubs_eq]
    intro s hs
    obtain ⟨e, heMem, rfl⟩ := List.mem_map.mp hs
    have hnotTrap : (e == c2LrTrapSym) = false :=
      Bool.not_eq_true' _ |>.mp (List.all_eq_true.mp c2FmtStubs_no_trapSym e heMem)
    rw [hnotTrap]
    rfl
  revert htail
  generalize c2FmtStubs = ss
  intro htail
  induction ss with
  | nil => rfl
  | cons s rest ih =>
    simp only [List.findSome?_cons]
    rw [htail s (.head _)]
    cases (if s.2 == (pc - c2Seg1Start).toNat then c2FmtExterns s.1 else none) with
    | none => exact ih fun x hx => htail x (.tail _ hx)
    | some f => rfl

theorem c2FmtProgTrap_externAt_handleError {lr : BitVec 64}
    (hlr : lr.toNat < c2FirstExternStubAddr.toNat) :
    (c2FmtProgTrap lr).externAt? wp4HandleErrorAddr = some Rust.panicked := by
  have hge : c2FirstExternStubAddr.toNat ≤ wp4HandleErrorAddr.toNat := by decide
  have hne : wp4HandleErrorAddr ≠ lr := by intro h; rw [h] at hge; omega
  rw [c2FmtProgTrap_externAt_of_ne hne]
  exact c2FmtProg_externAt_handleError

theorem c2FmtProgTrap_externAt_none_of_ge_stub_not_panic {lr pc : BitVec 64}
    (hlr : lr.toNat < c2FirstExternStubAddr.toNat)
    (hge : c2FirstExternStubAddr.toNat ≤ pc.toNat)
    (hnp : isLinkedPanicAddr pc = false) :
    (c2FmtProgTrap lr).externAt? pc = none := by
  have hne : pc ≠ lr := by intro h; rw [h] at hge; omega
  rw [c2FmtProgTrap_externAt_of_ne hne]
  exact c2FmtProg_externAt_none_of_not_panic hnp

private theorem le_of_sub_toNat_lt {a b : BitVec 64} {n : Nat}
    (hbnd : a.toNat + n ≤ 2 ^ 64)
    (hlt : (b - a).toNat < n) :
    a.toNat ≤ b.toNat := by
  by_contra h
  have hsub : (b - a).toNat = 2 ^ 64 - a.toNat + b.toNat := by
    rw [BitVec.toNat_sub, Nat.mod_eq_of_lt (by have := a.isLt; omega)]
  omega

theorem c2FmtProgTrap_externAt_none_of_keepRxSeg_not_panic {lr pc : BitVec 64}
    (hlr : lr.toNat < c2FirstExternStubAddr.toNat)
    (hk : keepRxSeg pc = true)
    (hnp : isLinkedPanicAddr pc = false) :
    (c2FmtProgTrap lr).externAt? pc = none := by
  rw [keepRxSeg_eq_lt] at hk
  have hlt := of_decide_eq_true hk
  have hrxbnd : f3RxSegBase.toNat + 4 * f3RxWordCount ≤ 2 ^ 64 := by decide
  have hstub_le_rx : c2FirstExternStubAddr.toNat ≤ f3RxSegBase.toNat := by decide
  exact c2FmtProgTrap_externAt_none_of_ge_stub_not_panic hlr
    (Nat.le_trans hstub_le_rx (le_of_sub_toNat_lt hrxbnd hlt)) hnp

theorem c2FmtProgTrap_blockExternFree_of_pre_lib2 {lr addr : BitVec 64} {len : Nat}
    (hlr : lr.toNat < c2FirstExternStubAddr.toNat)
    (hge : f3RxSegBase.toNat ≤ addr.toNat)
    (hbnd : addr.toNat + len ≤ 0x479798) :
    BlockExternFree (c2FmtProgTrap lr) addr len := by
  intro pc hpc
  have hpc_ge_addr : addr.toNat ≤ pc.toNat := le_of_sub_toNat_lt (by omega) hpc
  have hpc_lt : pc.toNat < 0x479798 := by
    have hsub := BitVec.toNat_sub_of_le (BitVec.le_def.mpr hpc_ge_addr)
    unfold InRegion at hpc
    rw [hsub] at hpc
    omega
  have hstub_le_rx : c2FirstExternStubAddr.toNat ≤ f3RxSegBase.toNat := by decide
  exact c2FmtProgTrap_externAt_none_of_ge_stub_not_panic hlr (by omega)
    (isLinkedPanicAddr_false_of_lt hpc_lt)

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.Externs
