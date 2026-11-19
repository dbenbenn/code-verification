/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import LibsignalBinary.Heap.SpecBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtWriteProof -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FormatInnerProof -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Bottom-of-DAG Formatting Envelopes, `withLsRet624` Contracts, and `cliExternsPlaced` Stub Bridges (`HooksDehook.CliFmtLsPlacedSpecs`)

Untrusted (`Role::Proof`) foundational bridge module sitting below `SpqrV1`, `TripleRatchet`,
`PeakBudget`, and `SignalSession/Cli`:

1. **Body-Private Formatting Envelopes (`CliFmtWriteEnv`, `CliFormatInnerEnv`, `MsgDeserErrEnv`):**
   Defined without `@[expose]` so Lean 4.34 `module` encapsulation keeps their bodies opaque
   downstream (preventing kernel unfolding blowup in heavy `PeakBudget` / `Hole3` modules), while
   exposing explicit `_iff`, `_nil`, and per-shape introduction/projection theorems.
2. **Lightweight `withLsRet624` Formatting Specs (`fmtWriteLsEnvSpec`, `formatInnerLsEnvSpec`,
   `fmtWriteCliLsSpec`, `formatInnerCliLsSpec`):**
   Definitionally (`rfl`) identical to `WithLsRet.withLsRet (fmtWriteBudgetEnvSpec ...)` and
   `WithLsRet.withLsRet (formatInnerBudgetEnvSpec ...)`, usable in `SpqrV1/` and `TripleRatchet/`
   without importing `SignalSession/Cli/Main/Callees`.
3. **One-Line `HookOk` & `HookSat (cliExternsPlaced mmpl W)` Stub Witnesses:**
   Any `Env` satisfying `Env []` (in particular `CliFmtWriteEnv` and `CliFormatInnerEnv`) is
   satisfied by `main`'s stub hooks (`fmtWriteHook0`, `formatInnerHook0`) and `cliExternsPlaced`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtLsPlacedSpecs

open Arm64 ProofLib ProofLib.SepLogic SepProp
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.E2E (fmtWriteHook0 formatInnerHook0)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.RustHeap (vecU8)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget
   rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.Fine
  (fmtWriteHook0_budget_ok formatInnerHook0_budget_ok)
open LibsignalBinary.Heap.SpecBudget
  (FmtWriteEnv FormatInnerEnv fmtWriteBudgetEnvSpec fmtWriteBudgetSpec
   formatInnerBudgetEnvSpec formatInnerBudgetSpec)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtPlacedObj (formatInnerKnownEvents)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FmtWriteProof (FmtWriteAddrEnv)
open LibsignalBinary.Proofs.HookDischarge.CliIoFmt.FormatInnerProof
  (FormatInnerAddrEnv FormatInnerAnyU32Env FormatInnerAnyU8Env FormatInnerFromStrEnv
   FormatInnerShortLitEnv FormatInnerSingleEnv FormatInnerU32Env FormatInnerU8Env
   formatInnerAnyU32Env_of_u32 formatInnerAnyU8Env_of_u8 formatInnerKnownEvents_zero_singleton)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr
  (LsRetAddr624 lsLen lsRetAddr624_base_add lsRetAddr624_blockPlacement_base_add)

/-! ## 1. `ExactOrNilEnv` & Body-Private Unified Consumer Envelopes -/

/-- Minimal 2-point envelope containing `[]` (fallback hook) and `exactEvs` (real `mallocng` trace). -/
@[expose] def ExactOrNilEnv (exactEvs : List AllocEvent) (evs : List AllocEvent) : Prop :=
  evs = [] ∨ evs = exactEvs

theorem exactOrNilEnv_nil (exactEvs : List AllocEvent) : ExactOrNilEnv exactEvs [] :=
  Or.inl rfl

theorem exactOrNilEnv_exact (exactEvs : List AllocEvent) : ExactOrNilEnv exactEvs exactEvs :=
  Or.inr rfl

theorem exactOrNilEnv_imp {Env : List AllocEvent → Prop} {exactEvs : List AllocEvent}
    (hNil : Env []) (hEx : Env exactEvs) :
    ∀ evs, ExactOrNilEnv exactEvs evs → Env evs := by
  rintro _ (rfl | rfl)
  · exact hNil
  · exact hEx

/-- `FitsEnv M lim st Env` plus `Env exactEvs` immediately discharges
    `FitsEnv M lim st (ExactOrNilEnv exactEvs)` (`FitsEvents` on `[]` is `True`). -/
theorem fitsEnv_exactOrNil {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {Env : List AllocEvent → Prop} {exactEvs : List AllocEvent}
    (hFit : FitsEnv M lim st Env) (hEx : Env exactEvs) :
    FitsEnv M lim st (ExactOrNilEnv exactEvs) := by
  intro evs h
  rcases h with rfl | rfl
  · trivial
  · exact hFit _ hEx

/-- Unified allocation-event envelope covering all CLI `core::fmt::write` call sites
    (`FmtWriteEnv` `[]` plus `<ProtocolAddress as Display>::fmt` `"{}.{}"` on an empty buffer with
    `nameLen ≤ 40` and `1 ≤ devDigits ≤ 10`). Kept body-private (`module` encapsulation, no
    `@[expose]`) so downstream proofs treat `CliFmtWriteEnv` as an atomic predicate. -/
def CliFmtWriteEnv (evs : List AllocEvent) : Prop :=
  evs = [] ∨
    ∃ nameLen devDigits : Nat,
      nameLen ≤ 40 ∧ 1 ≤ devDigits ∧ devDigits ≤ 10 ∧
      FmtWriteAddrEnv 0 0 nameLen devDigits evs

theorem cliFmtWriteEnv_iff {evs : List AllocEvent} :
    CliFmtWriteEnv evs ↔
      (evs = [] ∨
        ∃ nameLen devDigits : Nat,
          nameLen ≤ 40 ∧ 1 ≤ devDigits ∧ devDigits ≤ 10 ∧
          FmtWriteAddrEnv 0 0 nameLen devDigits evs) :=
  Iff.rfl

theorem cliFmtWriteEnv_nil : CliFmtWriteEnv [] :=
  Or.inl rfl

theorem cliFmtWriteEnv_of_fmtWriteEnv {evs : List AllocEvent} (h : FmtWriteEnv evs) :
    CliFmtWriteEnv evs :=
  Or.inl h

theorem cliFmtWriteEnv_of_addr0 {nameLen devDigits : Nat} {evs : List AllocEvent}
    (hn : nameLen ≤ 40) (hd1 : 1 ≤ devDigits) (hd2 : devDigits ≤ 10)
    (h : FmtWriteAddrEnv 0 0 nameLen devDigits evs) :
    CliFmtWriteEnv evs :=
  Or.inr ⟨nameLen, devDigits, hn, hd1, hd2, h⟩

/-- Allocation-event envelope for `alloc::fmt::format::format_inner` on a literal-prefixed
    template (`cap0 ≤ 80`, leading literal piece `n0 ≤ cap0` fitting inside `cap0` with `0`
    growth, followed by up to `2` formatted pieces `rest` with `n0 + rest.sum ≤ 120`, covering
    all binary prefixed error strings: `"Expected a number between 0 and 6, got {}"`,
    `"decryption failed: {}"`, and `"post-quantum ratchet error: {}"`). -/
@[expose] def FormatInnerPrefixedEnv (evs : List AllocEvent) : Prop :=
  ∃ cap0 n0 : Nat, cap0 ≤ 80 ∧ n0 ≤ cap0 ∧
    ∃ rest : List Nat, rest.length ≤ 2 ∧ n0 + rest.sum ≤ 120 ∧
      evs = formatInnerKnownEvents cap0 (n0 :: rest)

/-- Unified allocation-event envelope covering all CLI / TripleRatchet / PublicApi
    `alloc::fmt::format::format_inner` call shapes (`[]`, `u8`, `u32`, `from_str ≤ 127`,
    short literal `1..127`, single `&str ≤ 127`, `"{}.{}"` address `nameLen ≤ 40, devDigits ≤ 10`,
    and literal-prefixed error templates `FormatInnerPrefixedEnv`). Kept body-private (`module`
    encapsulation, no `@[expose]`) so downstream proofs treat `CliFormatInnerEnv` as atomic. -/
def CliFormatInnerEnv (evs : List AllocEvent) : Prop :=
  evs = [] ∨
    FormatInnerAnyU8Env evs ∨
    FormatInnerAnyU32Env evs ∨
    (∃ n : Nat, n ≤ 127 ∧ FormatInnerFromStrEnv n evs) ∨
    (∃ n : Nat, 1 ≤ n ∧ n ≤ 127 ∧ FormatInnerShortLitEnv n evs) ∨
    (∃ n : Nat, n ≤ 127 ∧ FormatInnerSingleEnv n evs) ∨
    (∃ nameLen devDigits : Nat,
      nameLen ≤ 40 ∧ 1 ≤ devDigits ∧ devDigits ≤ 10 ∧
      FormatInnerAddrEnv nameLen devDigits evs) ∨
    FormatInnerPrefixedEnv evs

theorem cliFormatInnerEnv_iff {evs : List AllocEvent} :
    CliFormatInnerEnv evs ↔
      (evs = [] ∨
        FormatInnerAnyU8Env evs ∨
        FormatInnerAnyU32Env evs ∨
        (∃ n : Nat, n ≤ 127 ∧ FormatInnerFromStrEnv n evs) ∨
        (∃ n : Nat, 1 ≤ n ∧ n ≤ 127 ∧ FormatInnerShortLitEnv n evs) ∨
        (∃ n : Nat, n ≤ 127 ∧ FormatInnerSingleEnv n evs) ∨
        (∃ nameLen devDigits : Nat,
          nameLen ≤ 40 ∧ 1 ≤ devDigits ∧ devDigits ≤ 10 ∧
          FormatInnerAddrEnv nameLen devDigits evs) ∨
        FormatInnerPrefixedEnv evs) :=
  Iff.rfl

theorem cliFormatInnerEnv_nil : CliFormatInnerEnv [] :=
  Or.inl rfl

theorem cliFormatInnerEnv_of_formatInnerEnv {evs : List AllocEvent} (h : FormatInnerEnv evs) :
    CliFormatInnerEnv evs :=
  Or.inl h

theorem cliFormatInnerEnv_of_anyU8 {evs : List AllocEvent} (h : FormatInnerAnyU8Env evs) :
    CliFormatInnerEnv evs :=
  Or.inr (Or.inl h)

theorem cliFormatInnerEnv_of_u8 (v : BitVec 8) {evs : List AllocEvent}
    (h : FormatInnerU8Env v evs) : CliFormatInnerEnv evs :=
  cliFormatInnerEnv_of_anyU8 (formatInnerAnyU8Env_of_u8 v h)

theorem cliFormatInnerEnv_of_anyU32 {evs : List AllocEvent} (h : FormatInnerAnyU32Env evs) :
    CliFormatInnerEnv evs :=
  Or.inr (Or.inr (Or.inl h))

theorem cliFormatInnerEnv_of_u32 (v : BitVec 32) {evs : List AllocEvent}
    (h : FormatInnerU32Env v evs) : CliFormatInnerEnv evs :=
  cliFormatInnerEnv_of_anyU32 (formatInnerAnyU32Env_of_u32 v h)

theorem cliFormatInnerEnv_of_fromStr {n : Nat} {evs : List AllocEvent}
    (hn : n ≤ 127) (h : FormatInnerFromStrEnv n evs) : CliFormatInnerEnv evs :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, h⟩)))

theorem cliFormatInnerEnv_of_shortLit {n : Nat} {evs : List AllocEvent}
    (h1 : 1 ≤ n) (h2 : n ≤ 127) (h : FormatInnerShortLitEnv n evs) : CliFormatInnerEnv evs :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, h1, h2, h⟩))))

theorem cliFormatInnerEnv_of_single {n : Nat} {evs : List AllocEvent}
    (hn : n ≤ 127) (h : FormatInnerSingleEnv n evs) : CliFormatInnerEnv evs :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, h⟩)))))

theorem cliFormatInnerEnv_of_addr {nameLen devDigits : Nat} {evs : List AllocEvent}
    (hn : nameLen ≤ 40) (hd1 : 1 ≤ devDigits) (hd2 : devDigits ≤ 10)
    (h : FormatInnerAddrEnv nameLen devDigits evs) : CliFormatInnerEnv evs :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨nameLen, devDigits, hn, hd1, hd2, h⟩))))))

theorem cliFormatInnerEnv_of_prefixed {evs : List AllocEvent} (h : FormatInnerPrefixedEnv evs) :
    CliFormatInnerEnv evs :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

/-- Envelope for `Message::deserialize` (`TryFrom<&[u8]>`) error paths: `CliFormatInnerEnv`
    followed by `FreeOnlyEvs`. Kept body-private (`module` encapsulation, no `@[expose]`) so
    downstream proofs treat `MsgDeserErrEnv` as atomic. -/
def MsgDeserErrEnv (evs : List AllocEvent) : Prop :=
  ∃ evs₁ evs₂ : List AllocEvent,
    evs = evs₁ ++ evs₂ ∧ CliFormatInnerEnv evs₁ ∧ FreeOnlyEvs evs₂

theorem msgDeserErrEnv_iff {evs : List AllocEvent} :
    MsgDeserErrEnv evs ↔
      (∃ evs₁ evs₂ : List AllocEvent,
        evs = evs₁ ++ evs₂ ∧ CliFormatInnerEnv evs₁ ∧ FreeOnlyEvs evs₂) :=
  Iff.rfl

private theorem freeOnlyEvs_nil_local : FreeOnlyEvs [] := by
  intro _ h; nomatch h

private theorem freeOnlyEvs_append_local {e₁ e₂ : List AllocEvent}
    (h1 : FreeOnlyEvs e₁) (h2 : FreeOnlyEvs e₂) : FreeOnlyEvs (e₁ ++ e₂) := by
  intro ev hev
  rcases List.mem_append.mp hev with he1 | he2
  · exact h1 ev he1
  · exact h2 ev he2

theorem msgDeserErrEnv_nil : MsgDeserErrEnv [] :=
  ⟨[], [], rfl, cliFormatInnerEnv_nil, freeOnlyEvs_nil_local⟩

theorem msgDeserErrEnv_of_freeOnly {evs : List AllocEvent} (h : FreeOnlyEvs evs) :
    MsgDeserErrEnv evs :=
  ⟨[], evs, rfl, cliFormatInnerEnv_nil, h⟩

theorem msgDeserErrEnv_of_cliFormatInnerEnv {evs : List AllocEvent} (h : CliFormatInnerEnv evs) :
    MsgDeserErrEnv evs :=
  ⟨evs, [], (List.append_nil evs).symm, h, freeOnlyEvs_nil_local⟩

theorem msgDeserErrEnv_of_anyU8 {evs : List AllocEvent} (h : FormatInnerAnyU8Env evs) :
    MsgDeserErrEnv evs :=
  msgDeserErrEnv_of_cliFormatInnerEnv (cliFormatInnerEnv_of_anyU8 h)

theorem msgDeserErrEnv_of_u8 (v : BitVec 8) {evs : List AllocEvent}
    (h : FormatInnerU8Env v evs) : MsgDeserErrEnv evs :=
  msgDeserErrEnv_of_anyU8 (formatInnerAnyU8Env_of_u8 v h)

theorem msgDeserErrEnv_append_freeOnly {evs₁ evs₂ : List AllocEvent}
    (h1 : MsgDeserErrEnv evs₁) (h2 : FreeOnlyEvs evs₂) :
    MsgDeserErrEnv (evs₁ ++ evs₂) := by
  rcases h1 with ⟨a, b, rfl, ha, hb⟩
  exact ⟨a, b ++ evs₂, List.append_assoc a b evs₂, ha, freeOnlyEvs_append_local hb h2⟩

theorem msgDeserErrEnv_of_fmt_and_dealloc {evs₁ : List AllocEvent} (cap al : Nat)
    (h1 : CliFormatInnerEnv evs₁) :
    MsgDeserErrEnv (evs₁ ++ rustDeallocEvents cap al) := by
  refine ⟨evs₁, rustDeallocEvents cap al, rfl, h1, ?_⟩
  intro ev hev
  unfold rustDeallocEvents at hev
  rw [List.mem_singleton] at hev
  exact ⟨al, cap, hev⟩

theorem fitsEnv_cliFormatInnerEnv_of_msgDeserErrEnv {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} (h : FitsEnv M lim st MsgDeserErrEnv) :
    FitsEnv M lim st CliFormatInnerEnv :=
  fun evs hE => h evs (msgDeserErrEnv_of_cliFormatInnerEnv hE)

/-- Every `FormatInnerAnyU8Env` trace is `[.alloc 8]` (`1 ≤ dLen ≤ 3` → `max dLen 8 = 8`). -/
theorem formatInnerAnyU8Env_eq_alloc8 {evs : List AllocEvent}
    (h : FormatInnerAnyU8Env evs) : evs = [.alloc 8] := by
  rcases h with ⟨dLen, hlo, hhi, hSingle⟩
  unfold FormatInnerSingleEnv at hSingle
  rw [hSingle, formatInnerKnownEvents_zero_singleton]
  have hne : dLen ≠ 0 := by omega
  have hmax : max dLen 8 = 8 := by omega
  simp [hne, hmax, rustAllocEvents]

/-! ## 2. Lightweight `withLsRet624` Wrapper & Placed Formatting Contracts -/

/-- Narrow `spec.pre` with `⌜LsRetAddr624 (s.readReg64 .lr)⌝` (definitionally `rfl`-equal to
    `WithLsRet.withLsRet spec`). -/
@[expose] def withLsRet624 [LibsignalPlacement] {α : Type} (spec : Spec α) : Spec α :=
  { spec with pre := fun x s => ⌜LsRetAddr624 (s.readReg64 .lr)⌝ ∗ spec.pre x s }

theorem extract_withLsRet624 [LibsignalPlacement] {α : Type} {spec : Spec α}
    {x : α} {s0 : State} {R : SepProp}
    (hpre : s0.mem ⊨ (withLsRet624 spec).pre x s0 ∗ R) :
    LsRetAddr624 (s0.readReg64 .lr) ∧ (s0.mem ⊨ spec.pre x s0 ∗ R) := by
  dsimp only [withLsRet624] at hpre
  rwa [sepConj_assoc, satisfies_pure_sepConj] at hpre

theorem intro_withLsRet624 [LibsignalPlacement] {α : Type} {spec : Spec α}
    {x : α} {s0 : State} {R : SepProp}
    (hlr : LsRetAddr624 (s0.readReg64 .lr))
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ R) :
    s0.mem ⊨ (withLsRet624 spec).pre x s0 ∗ R := by
  dsimp only [withLsRet624]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hlr, hpre⟩

theorem hookOk_withLsRet624 [LibsignalPlacement] {α : Type} {f : State → State} {spec : Spec α}
    (h : HookOk f spec) :
    HookOk f (withLsRet624 spec) := by
  intro x R s0 hrun hpre hsp
  exact h x R s0 hrun (extract_withLsRet624 hpre).2 hsp

theorem hookSat_withLsRet624 [LibsignalPlacement] {α : Type}
    {H : String → Option (State → State)} {n : String} {spec : Spec α}
    (h : HookSat H n spec) :
    HookSat H n (withLsRet624 spec) := by
  rcases h with ⟨f, hfn, hok⟩
  exact ⟨f, hfn, hookOk_withLsRet624 hok⟩

/-- Placed `withLsRet624`-guarded `core::fmt::write` budget contract at arbitrary `Env`. -/
@[expose] def fmtWriteLsEnvSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (Env : List AllocEvent → Prop) :
    Spec (BitVec 64 × List (BitVec 8) × M.σ) :=
  withLsRet624 (fmtWriteBudgetEnvSpec M A lim Env)

/-- Placed `withLsRet624`-guarded `alloc::fmt::format::format_inner` budget contract at `Env`. -/
@[expose] def formatInnerLsEnvSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (Env : List AllocEvent → Prop) :
    Spec (BitVec 64 × M.σ) :=
  withLsRet624 (formatInnerBudgetEnvSpec M A lim Env)

/-- Canonical CLI placed `core::fmt::write` budget contract (`Env := CliFmtWriteEnv`). -/
@[expose] def fmtWriteCliLsSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (BitVec 64 × List (BitVec 8) × M.σ) :=
  fmtWriteLsEnvSpec M A lim CliFmtWriteEnv

/-- Canonical CLI placed `alloc::fmt::format::format_inner` budget contract (`Env := CliFormatInnerEnv`). -/
@[expose] def formatInnerCliLsSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (BitVec 64 × M.σ) :=
  formatInnerLsEnvSpec M A lim CliFormatInnerEnv

/-! ## 3. Generic Stub-Hook `HookOk` & `cliExternsPlaced` `HookSat` Bridges -/

/-- `fmtWriteHook0` satisfies `fmtWriteBudgetEnvSpec M A lim Env` whenever `Env []` holds. -/
theorem fmtWriteHook0_budgetEnv_ok (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {Env : List AllocEvent → Prop} (hNil : Env []) :
    HookOk fmtWriteHook0 (fmtWriteBudgetEnvSpec M A lim Env) := by
  rintro ⟨v, bs, st⟩ R s0 hrun hpre hsp
  dsimp only [fmtWriteBudgetEnvSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, _hFit⟩, hmem⟩
  have hpre0 : s0.mem ⊨ (fmtWriteBudgetSpec M A lim).pre (v, bs, st) s0 ∗ R := by
    dsimp only [fmtWriteBudgetSpec, fmtWriteBudgetEnvSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, fun _ h => by subst h; trivial⟩, hmem⟩
  obtain ⟨hkf, hsym, hout⟩ := fmtWriteHook0_budget_ok M A lim (v, bs, st) R s0 hrun hpre0 hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨ec, he, hex⟩ | ⟨ho, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [fmtWriteBudgetSpec, fmtWriteBudgetEnvSpec] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hp⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    rcases hp with ⟨⟨hw0, htr, rfl⟩, hm⟩
    exact ⟨⟨hw0, htr, hNil⟩, hm⟩
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨ec, he, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

/-- `formatInnerHook0` satisfies `formatInnerBudgetEnvSpec M A lim Env` whenever `Env []` holds. -/
theorem formatInnerHook0_budgetEnv_ok (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {Env : List AllocEvent → Prop} (hNil : Env []) :
    HookOk formatInnerHook0 (formatInnerBudgetEnvSpec M A lim Env) := by
  rintro ⟨ret, st⟩ R s0 hrun hpre hsp
  dsimp only [formatInnerBudgetEnvSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, _hFit⟩, hmem⟩
  have hpre0 : s0.mem ⊨ (formatInnerBudgetSpec M A lim).pre (ret, st) s0 ∗ R := by
    dsimp only [formatInnerBudgetSpec, formatInnerBudgetEnvSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, fun _ h => by subst h; trivial⟩, hmem⟩
  obtain ⟨hkf, hsym, hout⟩ := formatInnerHook0_budget_ok M A lim (ret, st) R s0 hrun hpre0 hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨ec, he, hex⟩ | ⟨ho, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [formatInnerBudgetSpec, formatInnerBudgetEnvSpec] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hp⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    rcases hp with ⟨⟨htr, rfl⟩, hm⟩
    exact ⟨⟨htr, hNil⟩, hm⟩
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨ec, he, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

theorem fmtWriteHook0_lsEnv_ok [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {Env : List AllocEvent → Prop}
    (hNil : Env []) :
    HookOk fmtWriteHook0 (fmtWriteLsEnvSpec M A lim Env) :=
  hookOk_withLsRet624 (fmtWriteHook0_budgetEnv_ok M A lim hNil)

theorem formatInnerHook0_lsEnv_ok [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {Env : List AllocEvent → Prop}
    (hNil : Env []) :
    HookOk formatInnerHook0 (formatInnerLsEnvSpec M A lim Env) :=
  hookOk_withLsRet624 (formatInnerHook0_budgetEnv_ok M A lim hNil)

theorem fmtWriteHook0_cliLs_ok [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk fmtWriteHook0 (fmtWriteCliLsSpec M A lim) :=
  fmtWriteHook0_lsEnv_ok M A lim cliFmtWriteEnv_nil

theorem formatInnerHook0_cliLs_ok [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk formatInnerHook0 (formatInnerCliLsSpec M A lim) :=
  formatInnerHook0_lsEnv_ok M A lim cliFormatInnerEnv_nil

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtLsPlacedSpecs
