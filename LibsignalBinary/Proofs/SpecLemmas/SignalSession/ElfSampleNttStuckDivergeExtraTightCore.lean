/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.TimeAddPanic

/-!
# Core Engines for Tight-Keep & Sentinel `SampleNTT` Non-Visitation (`ElfSampleNttStuckDivergeExtraTightCore`)

Provides the two program-lifting engines shared by the 23 tight-keep and sentinel rows of
`ElfSampleNttStuckDivergeExtraTight`:
1. `stepsStrictAvoid_of_visitedIn_noExtern` / `stepsStrictAvoid_s5_of_visitedIn_all_false`:
   lifts `h2fsgen_StepsVisitedIn D P1 s sf` directly to `StepsStrictAvoid` against the 5
   `mlkemSampleNttSyms` entry addresses (`c2S5Addrs`) whenever `D` is disjoint from `c2S5Addrs`
   and `externAt? = none` on `D`.
2. `s5TrapExt` + `stepsStrictAvoid_of_s5Trap`: replaces the 5 `mlkemSampleNttSyms` extern slots
   with an immediate `.Exception "sntt_trap"` hook and lifts any `Steps` trace ending in a
   non-`.Exception` state directly to `StepsStrictAvoid` on `P_real`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTightCore

open Arm64
open Arm64.Obj (MultiPlacement)
open CryptoVerification (libsignalHookedExterns)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable
  (c2Kyber1024DecapsAddr c2Kyber1024EncapsAddr c2Mlkem768DecapsAddr c2Mlkem768Encaps1Addr
   c2Mlkem768FromSeedAddr c2_resolve_kyber1024Decaps_eq c2_resolve_kyber1024Encaps_eq
   c2_resolve_mlkem768Decaps_eq c2_resolve_mlkem768Encaps1_eq c2_resolve_mlkem768FromSeed_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.TimeAddPanic
  (externAt?_cliProgExtPlacedAt_617)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer
  (mlkemSampleNttSyms)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (C2ExternTableFacts f3RxSeg_ghostProg617_externAt_entry keepTextBPre)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeCore
  (StepsStrictAvoid)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
  (h2fsgen_StepsVisitedIn h2fsgen_fetchMem_eq_of_externAt_eq)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2RxDehookedSyms c2TextBPreHi c2TextBPreLo)

/-! ## 1. Concrete `c2S5Addrs` Resolution & Disjointness Helpers -/

/-- The 5 concrete entry addresses of `mlkemSampleNttSyms`
    (`[lsKemEncapsSym, lsKemDecapsSym, lsMlkemFromSeedSym, lsMlkemEncaps1Sym, lsMlkemDecapsSym]`). -/
@[expose] def c2S5Addrs : List (BitVec 64) :=
  [c2Kyber1024EncapsAddr, c2Kyber1024DecapsAddr, c2Mlkem768FromSeedAddr,
   c2Mlkem768Encaps1Addr, c2Mlkem768DecapsAddr]

theorem mlkemSampleNttSyms_map_resolve_eq {mpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl) = c2S5Addrs := by
  simp only [mlkemSampleNttSyms, c2S5Addrs, List.map_cons, List.map_nil,
    c2_resolve_kyber1024Encaps_eq hLs, c2_resolve_kyber1024Decaps_eq hLs,
    c2_resolve_mlkem768FromSeed_eq hLs, c2_resolve_mlkem768Encaps1_eq hLs,
    c2_resolve_mlkem768Decaps_eq hLs]
  decide +kernel

theorem not_mem_s5_of_not_mem_c2S5Addrs {mpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) {pc : BitVec 64}
    (hnot : pc ∉ c2S5Addrs) :
    pc ∉ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl) := by
  rwa [mlkemSampleNttSyms_map_resolve_eq hLs]

theorem not_mem_s5_of_keep_all_false {mpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {keep : BitVec 64 → Bool}
    (hall : (c2S5Addrs.all fun p => !(keep p)) = true)
    {pc : BitVec 64} (hk : keep pc = true) :
    pc ∉ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl) := by
  rw [mlkemSampleNttSyms_map_resolve_eq hLs]
  intro hmem
  have hp := List.all_eq_true.mp hall pc hmem
  rw [hk] at hp
  cases hp

theorem not_mem_s5_of_lt_textBPreHi {mpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {pc : BitVec 64} (hlt : pc.toNat < c2TextBPreHi.toNat) :
    pc ∉ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl) := by
  rw [mlkemSampleNttSyms_map_resolve_eq hLs]
  have hge : (c2S5Addrs.all fun p => decide (c2TextBPreHi.toNat ≤ p.toNat)) = true := by decide
  intro hmem
  have hp := decide_eq_true_eq.mp (List.all_eq_true.mp hge pc hmem)
  omega

theorem not_mem_s5_of_keepTextBPre {mpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    {pc : BitVec 64} (hk : keepTextBPre pc = true) :
    pc ∉ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl) := by
  apply not_mem_s5_of_lt_textBPreHi hLs
  unfold keepTextBPre at hk
  rw [decide_eq_true_eq] at hk
  omega

theorem setPC_eq_self_of_pc_eq {u : State} {pc : BitVec 64} (h : u.pc = pc) :
    u.setPC pc = u := by
  cases u; subst h; rfl

theorem realProg617_svc_eq (mpl mmpl : MultiPlacement) (W : CliHooks) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).svc = Syscall.standard :=
  rfl

/-! ## 2. Engine A: `h2fsgen_StepsVisitedIn` → `StepsStrictAvoid` -/

private theorem step_of_externAt?_and_svc_eq {P1 P2 : Program} {s1 s2 : State}
    (hsvc : P2.svc = P1.svc)
    (hext : P2.externAt? s1.pc = P1.externAt? s1.pc)
    (h : Step P1 s1 s2) :
    Step P2 s1 s2 := by
  have hfm : P2.fetchMem s1.mem s1.pc = P1.fetchMem s1.mem s1.pc :=
    h2fsgen_fetchMem_eq_of_externAt_eq s1.mem s1.pc hext
  cases h with
  | @exec inst hrun hfetch =>
    have hev : P2.evalInst inst s1 = P1.evalInst inst s1 := by
      unfold Program.evalInst execInstWithSvc
      rw [hsvc]
    rw [← hev]
    exact Step.exec hrun (hfm.trans hfetch)
  | halt_unmapped hrun hfetch hnone =>
    exact Step.halt_unmapped hrun (hfm.trans hfetch) (hext.trans hnone)
  | @extern f hrun hext1 hkf hsym =>
    exact Step.extern hrun (hext.trans hext1) hkf hsym
  | @extern_fault f hrun hext1 hnkf =>
    exact Step.extern_fault hrun (hext.trans hext1) hnkf

/-- Lifts `h2fsgen_StepsVisitedIn D P1 s sf` to `StepsStrictAvoid` on `P2` whenever `D` has no
    extern hooks on `P1`/`P2`, `P1.svc = P2.svc`, and `D` avoids `bad`. -/
theorem stepsStrictAvoid_of_visitedIn_noExtern
    {D : BitVec 64 → Bool} {bad : BitVec 64 → Prop} {P1 P2 : Program} {s sf : State}
    (hsvc : P1.svc = P2.svc)
    (hext1 : ∀ pc : BitVec 64, D pc = true → P1.externAt? pc = none)
    (hext2 : ∀ pc : BitVec 64, D pc = true → P2.externAt? pc = none)
    (hnot : ∀ pc : BitVec 64, D pc = true → ¬ bad pc)
    (hvis : h2fsgen_StepsVisitedIn D P1 s sf) :
    StepsStrictAvoid (fun z => bad z.pc) P2 s sf := by
  induction hvis with
  | refl u => exact .refl u
  | @step s1 s2 s3 hd h1 _ ih =>
    have hext : P2.externAt? s1.pc = P1.externAt? s1.pc :=
      (hext2 s1.pc hd).trans (hext1 s1.pc hd).symm
    exact .step (hnot s1.pc hd) (step_of_externAt?_and_svc_eq hsvc.symm hext h1) ih

/-- Direct `S5` specialization of `stepsStrictAvoid_of_visitedIn_noExtern` when `D` evaluates to
    `false` on all 5 `c2S5Addrs`. -/
theorem stepsStrictAvoid_s5_of_visitedIn_all_false
    {mpl mmpl : MultiPlacement} {D : BitVec 64 → Bool} {P1 : Program}
    {W : CliHooks} {s sf : State}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hsvc : P1.svc = Syscall.standard)
    (hext1 : ∀ pc : BitVec 64, D pc = true → P1.externAt? pc = none)
    (hext2 : ∀ pc : BitVec 64, D pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hall : (c2S5Addrs.all fun p => !(D p)) = true)
    (hvis : h2fsgen_StepsVisitedIn D P1 s sf) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl))
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) s sf :=
  stepsStrictAvoid_of_visitedIn_noExtern
    hsvc hext1 hext2
    (fun _ hk => not_mem_s5_of_keep_all_false hLs hall hk)
    hvis

/-! ## 3. Engine B: `s5TrapExt` & `stepsStrictAvoid_of_s5Trap` -/

/-- Extern table agreeing with `cliExternsPlaced mmpl` everywhere outside `mlkemSampleNttSyms`
    and trapping immediately into `.Exception "sntt_trap"` on `mlkemSampleNttSyms`. -/
@[expose] noncomputable def s5TrapExt (mmpl : MultiPlacement) (W : CliHooks) (sym : String) :
    Option (State → State) :=
  if mlkemSampleNttSyms.contains sym then
    some (fun u => { u with status := .Exception "sntt_trap" })
  else
    cliExternsPlaced mmpl W sym

theorem s5TrapProg_svc (mpl mmpl : MultiPlacement) (W : CliHooks) :
    (cliProgExtPlacedAt mpl (s5TrapExt mmpl) 617 W).svc = Syscall.standard :=
  rfl

private theorem findSome?_congr_s5 {α β : Type} (xs : List α) (f g : α → Option β)
    (h : ∀ x ∈ xs, f x = g x) :
    xs.findSome? f = xs.findSome? g := by
  induction xs with
  | nil => rfl
  | cons a tl ih =>
    simp only [List.findSome?_cons, h a (.head _)]
    rw [ih (fun x hx => h x (.tail _ hx))]

set_option maxRecDepth 400000 in
private theorem mlkemSampleNttSyms_sub_c2Rx_all :
    (mlkemSampleNttSyms.all fun s => c2RxDehookedSyms.contains s) = true := by
  decide +kernel

private theorem mlkemSampleNttSyms_sub_c2Rx {sym : String} (h : sym ∈ mlkemSampleNttSyms) :
    sym ∈ c2RxDehookedSyms :=
  List.contains_iff_mem.mp (List.all_eq_true.mp mlkemSampleNttSyms_sub_c2Rx_all sym h)

set_option maxRecDepth 400000 in
private theorem mlkemSampleNttSyms_sub_hooked_all :
    (mlkemSampleNttSyms.all fun s => libsignalHookedExterns.contains s) = true := by
  decide +kernel

private theorem mlkemSampleNttSyms_sub_hooked {sym : String} (h : sym ∈ mlkemSampleNttSyms) :
    sym ∈ libsignalHookedExterns :=
  List.contains_iff_mem.mp (List.all_eq_true.mp mlkemSampleNttSyms_sub_hooked_all sym h)

theorem externAt?_s5TrapExt_eq_of_not_mem {mpl mmpl : MultiPlacement}
    (W : CliHooks) {pc : BitVec 64}
    (hnot : pc ∉ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl)) :
    (cliProgExtPlacedAt mpl (s5TrapExt mmpl) 617 W).externAt? pc =
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc := by
  rw [externAt?_cliProgExtPlacedAt_617, externAt?_cliProgExtPlacedAt_617]
  refine findSome?_congr_s5 _ _ _ fun e _ => ?_
  cases heq : libsignalSessionLib.resolve mpl e == pc with
  | false => rfl
  | true =>
    have hres : libsignalSessionLib.resolve mpl e = pc := beq_iff_eq.mp heq
    have hnc : mlkemSampleNttSyms.contains e = false := by
      cases hc : mlkemSampleNttSyms.contains e with
      | false => rfl
      | true =>
        exfalso
        exact hnot (hres ▸ List.mem_map_of_mem (List.contains_iff_mem.mp hc))
    simp only [↓reduceIte, s5TrapExt, hnc, Bool.false_eq_true]

theorem externAt?_s5TrapExt_eq_of_keep_all_false {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (W : CliHooks) {keep : BitVec 64 → Bool}
    (hall : (c2S5Addrs.all fun p => !(keep p)) = true)
    {pc : BitVec 64} (hk : keep pc = true) :
    (cliProgExtPlacedAt mpl (s5TrapExt mmpl) 617 W).externAt? pc =
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc :=
  externAt?_s5TrapExt_eq_of_not_mem W (not_mem_s5_of_keep_all_false hLs hall hk)

theorem externAt?_s5TrapExt_entry {mpl mmpl : MultiPlacement}
    (hExt : C2ExternTableFacts mpl) (W : CliHooks) {sym : String}
    (hsym : sym ∈ mlkemSampleNttSyms) :
    (cliProgExtPlacedAt mpl (s5TrapExt mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl sym) =
      some (fun u => { u with status := .Exception "sntt_trap" }) := by
  rw [f3RxSeg_ghostProg617_externAt_entry hExt
    (s5TrapExt mmpl) W (mlkemSampleNttSyms_sub_c2Rx hsym)
    (mlkemSampleNttSyms_sub_hooked hsym)]
  have hc : mlkemSampleNttSyms.contains sym = true := List.contains_iff_mem.mpr hsym
  simp only [s5TrapExt, hc, ↓reduceIte]

private theorem steps_eq_of_not_running {P : Program} {s1 s2 : State}
    (hnr : s1.status ≠ .Running) (h : Steps P s1 s2) : s1 = s2 := by
  cases h with
  | refl => rfl
  | step h1 _ =>
    have hrun : s1.status = .Running := by cases h1 <;> assumption
    exact absurd hrun hnr

/-- Any `Steps` trace on `cliProgExtPlacedAt mpl (s5TrapExt mmpl) 617 W` ending in a non-`.Exception`
    state strictly avoids `mlkemSampleNttSyms` and is therefore a `StepsStrictAvoid` trace on
    `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W`. -/
theorem stepsStrictAvoid_of_s5Trap {mpl mmpl : MultiPlacement}
    (hExt : C2ExternTableFacts mpl) (W : CliHooks) {u v : State}
    (hSteps : Steps (cliProgExtPlacedAt mpl (s5TrapExt mmpl) 617 W) u v)
    (hnoex : ∀ msg, v.status ≠ .Exception msg) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl))
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u v := by
  induction hSteps with
  | refl s => exact .refl s
  | @step s1 s2 s3 h1 hrest ih =>
    have hnot : s1.pc ∉ mlkemSampleNttSyms.map (libsignalSessionLib.resolve mpl) := by
      intro hmem
      obtain ⟨sym, hsym, hpc⟩ := List.mem_map.mp hmem
      have hext :
          (cliProgExtPlacedAt mpl (s5TrapExt mmpl) 617 W).externAt? s1.pc =
            some (fun z => { z with status := .Exception "sntt_trap" }) := by
        rw [← hpc]
        exact externAt?_s5TrapExt_entry hExt W hsym
      cases h1 with
      | exec _ hfetch =>
        unfold Program.fetchMem at hfetch
        simp [hext] at hfetch
      | halt_unmapped _ _ hnone =>
        rw [hext] at hnone
        cases hnone
      | extern _ hext1 _ _ =>
        rw [hext] at hext1
        injection hext1 with hf
        subst hf
        have hs2 : ({ s1 with status := ExecStatus.Exception "sntt_trap" } : State).status ≠
            ExecStatus.Running := by simp
        have heq := steps_eq_of_not_running hs2 hrest
        rw [← heq] at hnoex
        exact hnoex "sntt_trap" rfl
      | extern_fault _ _ _ =>
        have heq := steps_eq_of_not_running (by simp) hrest
        rw [← heq] at hnoex
        exact hnoex _ rfl
    have hext_eq :
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? s1.pc =
          (cliProgExtPlacedAt mpl (s5TrapExt mmpl) 617 W).externAt? s1.pc :=
      (externAt?_s5TrapExt_eq_of_not_mem (mmpl := mmpl) W hnot).symm
    have hsvc_eq :
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).svc =
          (cliProgExtPlacedAt mpl (s5TrapExt mmpl) 617 W).svc :=
      (realProg617_svc_eq mpl mmpl W).trans (s5TrapProg_svc mpl mmpl W).symm
    exact .step hnot (step_of_externAt?_and_svc_eq hsvc_eq hext_eq h1) (ih hnoex)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTightCore
