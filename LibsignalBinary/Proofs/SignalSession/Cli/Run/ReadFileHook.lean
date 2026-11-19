/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Skeleton -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Defs
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

public section

set_option autoImplicit false

/-!
# `signal_session_io::read_file`: Hook and Callee Contracts

Establishes `readFileSpec` for `signal_session_io::read_file` both from the concrete `readFileHook`
at `E2E.HooksE.A0` and `cliExterns W` (`cliReadFile_ok`, splitting on out-of-memory allocation
panic `CliReadFileOom` versus normal return) and from the contract-backed `CliExternsOk.readFile`
interface (`runCallees_readFile_of_externsOk`).
-/

namespace CryptoVerification.SignalSession.Cli.RunSkeleton

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.E2E.HooksE.HooksOkAux

/-- Out-of-memory condition for `read_file`: `readView` returns non-empty bytes that do not fit in
bump memory (`vecOk` panics via `allocPanicHook`). -/
@[expose] def CliReadFileOom (x : ReadFileGhost) (s0 : State) : Prop :=
  ∃ bs, readView s0.fs (pathStr x.path) = some bs ∧ bs ≠ [] ∧
    E2E.bumpAddr? s0.mem bs.length 1 = none

private theorem stackAt_le_two_pow_64_of_sep {m : Memory} {p sp : BitVec 64} {n stk : Nat}
    {R : SepProp} (hn : 0 < n) (hstk : 0 < stk)
    (h : m ⊨ memRegion p n ∗ (stackAt sp stk ∗ R)) : stk ≤ 2 ^ 64 := by
  have hdisj := (IsBlock.memRegion p n).disjoint
    (IsBlock.memRegion (sp - BitVec.ofNat 64 stk) stk) hn hstk h
  have hlt := (p - (sp - BitVec.ofNat 64 stk)).isLt
  exact Nat.le_of_lt (Nat.lt_of_le_of_lt hdisj.2 hlt)

private theorem hookOk_map_frame {α β : Type} {f : State → State} {s₁ : Spec α} {s₂ : Spec β}
    (hh : HookOk f s₁)
    (hmap : ∀ y R s0, s0.mem ⊨ s₂.pre y s0 ∗ R →
      ∃ x F, s0.mem ⊨ s₁.pre x s0 ∗ (F ∗ R) ∧
        (∀ sf, sf.mem ⊨ s₁.post x s0 sf ∗ (F ∗ R) → sf.mem ⊨ s₂.post y s0 sf ∗ R) ∧
        (∀ sf, sf.mem ⊨ s₁.onPanic x s0 sf ∗ (F ∗ R) → sf.mem ⊨ s₂.onPanic y s0 sf ∗ R) ∧
        (∀ c sf, sf.mem ⊨ s₁.onExit x c s0 sf ∗ (F ∗ R) → sf.mem ⊨ s₂.onExit y c s0 sf ∗ R) ∧
        (∀ sf, sf.mem ⊨ s₁.onOom x s0 sf ∗ (F ∗ R) → sf.mem ⊨ s₂.onOom y s0 sf ∗ R)) :
    HookOk f s₂ := by
  intro y R s0 hrun hp hsp
  obtain ⟨x, F, hp₁, hpost, hpanic, hexit, hoom⟩ := hmap y R s0 hp
  obtain ⟨hkf, hsym, hout⟩ := hh x (F ∗ R) s0 hrun hp₁ hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hr, hc, hq⟩ | ⟨hs, hq⟩ | ⟨c, hs, hq⟩ | ⟨hs, hq⟩
  · exact Or.inl ⟨hr, hc, hpost (f s0) hq⟩
  · exact Or.inr (Or.inl ⟨hs, hpanic (f s0) hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hs, hexit c (f s0) hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hs, hoom (f s0) hq⟩))

private theorem ioVecAt_eq_cli (A : RustAlloc) (r : BitVec 64)
    (res : Except Unit (List (BitVec 8))) :
    CliExt.ioVecAt A r res = Cli.ioVecAt A r res := by
  cases res <;> rfl

end CryptoVerification.SignalSession.Cli.RunSkeleton
