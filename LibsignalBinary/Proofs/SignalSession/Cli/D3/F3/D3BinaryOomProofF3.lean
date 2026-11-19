/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomSpecF3 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ValidMatchElfF3 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ValidOverElfF3 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3ExternNoAllocFail
public import LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SpecLemmas.RoLiterals

/-!
# Two-Placement Whole-Process Assembly of `CliPqBinaryV2OomF3Placed`

Assembles `CliPqBinaryV2OomF3Placed mpl mmpl elf`, `LibsignalCliPqBinaryV2OomF3PlacedAt`,
and `LibsignalCliPqBinaryV2OomF3Placed` from `CliElfF3B2NeedLocksAssumptions` and the six
`NeedLocks` + `cliBudgetLimits` `main`-level hypotheses (`MainOkCliF3PqB2NeedLocksPlacedAt`,
`MainOkOverD3F3`, `MainOkUntypedD3F3`, `MainOkPathBD3F3`, `MainOkValidMatchD3F3`, and
`MainInitRunSemOkF3`).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3

open Arm64 (Memory)
open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage)
open CryptoVerification (libsignalSessionLib)
open CryptoVerification.SignalSession (CliRun Inputs Outcome OutcomeOrExcusedAbort)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomSpecF3 (
  CliPqBinaryV2OomF3Placed LibsignalCliPqBinaryV2OomF3Placed LibsignalCliPqBinaryV2OomF3PlacedAt
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3 (
  MainOkPathBD3F3 d3_matchingPathB_f3
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3 (
  MainOkOverD3F3 MainOkValidMatchD3F3 mainOkCliF3Over_of_mainOkOverD3F3
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3 (
  d3_pksmParseNone_f3 d3_recvOverStdinCap_f3
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3 (
  MainOkUntypedD3F3 d3_untypedReject_f3 mainOkParseNoneD3F3_of_untyped
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ValidMatchElfF3 (
  d3_valid_match_outcomeUpTo_of_f3
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ValidOverElfF3 (
  d3_canonical_noMatch_outcomeUpTo_of_f3 d3_valid_over_outcomeUpTo_of_f3
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2 (
  CliElfF3B2NeedLocksAssumptions MainOkCliF3PqB2NeedLocksPlacedAt
  cliPqxdhElfCorrectStrictPlaced2_of_f3B2NeedLocks
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3ExternNoAllocFail (
  externPreservesNoAllocFailed_cliExternsPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2 (
  cliPqxdhElfCorrectPlacedWith_of_strict2With
)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3 (
  MainInitRunSemOkF3 outcomeUpTo_pqInitFiles_exact_or_none_of_f3
  outcomeUpTo_pqInitOverCap_or_none_of_f3 outcomeUpTo_pqInitReject_or_none_of_f3
)

private theorem outcomeOrExcusedAbort_inl_exc {exc₁ exc₂ : Inputs → Prop} {run : CliRun}
    {i : Inputs} {P : Outcome → Prop}
    (h : OutcomeOrExcusedAbort exc₁ run i P) :
    OutcomeOrExcusedAbort (fun k => exc₁ k ∨ exc₂ k) run i P :=
  h.imp id fun ⟨hn, he⟩ => ⟨hn, Or.inl he⟩

/-- Assembles `CliPqBinaryV2OomF3Placed mpl mmpl elf` across all 16 whole-process clauses
from `CliElfF3B2NeedLocksAssumptions` and the six `main`-level hypotheses. -/
theorem cliPqBinaryV2OomF3Placed_of_f3B2NeedLocks
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAt mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hoverD3 : MainOkOverD3F3 mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (huntyped : MainOkUntypedD3F3 mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hpathB : MainOkPathBD3F3 mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hvalidMatch : MainOkValidMatchD3F3 mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hinitSem : MainInitRunSemOkF3 mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    CliPqBinaryV2OomF3Placed mpl mmpl elf where
  base :=
    let hstrict := cliPqxdhElfCorrectStrictPlaced2_of_f3B2NeedLocks
      (externPreservesNoAllocFailed_cliExternsPlaced mmpl) H hmain
      (mainOkCliF3Over_of_mainOkOverD3F3 hoverD3)
    cliPqxdhElfCorrectPlacedWith_of_strict2With ⟨hstrict.1, fun W _ _ _ _ _ _ _ _ _ => hstrict.2 W⟩
  recvOverStdinCap := fun W _ _ _ _ _ _ _ _ _ st hst body rc hover =>
    outcomeOrExcusedAbort_inl_exc (d3_recvOverStdinCap_f3 H hmain W st hst body rc hover)
  canonicalNoMatch := fun W _ _ _ _ _ _ _ _ _ X st hst x g hsess m rc hinner hnomatch =>
    outcomeOrExcusedAbort_inl_exc
      (d3_canonical_noMatch_outcomeUpTo_of_f3 H hoverD3 W X st hst x g hsess m rc hinner hnomatch)
  pksmParseNone := fun W _ _ _ _ _ _ _ _ _ st hst body rc hbody hnone =>
    outcomeOrExcusedAbort_inl_exc
      (d3_pksmParseNone_f3 H (mainOkParseNoneD3F3_of_untyped huntyped) W st hst body rc hbody hnone)
  untypedReject := fun W _ _ _ _ _ _ _ _ _ st hst body pm rc hbody hparse hpk hnomatch =>
    outcomeOrExcusedAbort_inl_exc
      (d3_untypedReject_f3 H huntyped W st hst body pm rc hbody hparse hpk hnomatch)
  matchingPathB := fun W _ _ _ _ _ _ _ _ _ st x g body pm rc hwf hsess hlen hparse hmatch =>
    outcomeOrExcusedAbort_inl_exc
      (d3_matchingPathB_f3 H hpathB W st x g body pm rc hwf hsess hlen hparse hmatch)
  validMatch := fun W _ _ _ _ _ _ _ _ _ X st hst body pm m rc hbody hpm hm hinner hmatch =>
    outcomeOrExcusedAbort_inl_exc
      (d3_valid_match_outcomeUpTo_of_f3 H hvalidMatch W X st hst body pm m rc hbody hpm hm hinner hmatch)
  validOver := fun W _ _ _ _ _ _ _ _ _ X st hst x g hsess body pm m rc hbody hpm hm hinner hnomatch =>
    outcomeOrExcusedAbort_inl_exc
      (d3_valid_over_outcomeUpTo_of_f3 H hoverD3 W X st hst x g hsess body pm m rc hbody hpm hm hinner hnomatch)
  initFiles := fun W _ _ _ _ _ _ _ _ _ X _st _files _b _t _i heq hwf hs hb hcap hparse =>
    (outcomeUpTo_pqInitFiles_exact_or_none_of_f3 H hinitSem W X heq hwf hs hb hcap hparse).imp_right
      outcomeOrExcusedAbort_inl_exc
  initReject := fun W _ _ _ _ _ _ _ _ _ _st _files _t _i heq hwf hs hb hparse =>
    (outcomeUpTo_pqInitReject_or_none_of_f3 H hinitSem W heq hwf hs hb hparse).imp_right
      outcomeOrExcusedAbort_inl_exc
  initOverFileCap := fun W _ _ _ _ _ _ _ _ _ _st _files _t _i heq hwf hs hb hover =>
    (outcomeUpTo_pqInitOverCap_or_none_of_f3 H hinitSem W heq hwf hs hb hover).imp_right
      outcomeOrExcusedAbort_inl_exc

/-- Lifts `cliPqBinaryV2OomF3Placed_of_f3B2NeedLocks` to raw ELF bytes at fixed placements
`(mpl, mmpl)`. -/
theorem libsignalCliPqBinaryV2OomF3PlacedAt_of_f3B2NeedLocks
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {bytes : List (BitVec 8)} {elf : ElfImage}
    (hparse : ElfImage.parse bytes = .ok elf)
    (H : CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAt mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hoverD3 : MainOkOverD3F3 mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (huntyped : MainOkUntypedD3F3 mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hpathB : MainOkPathBD3F3 mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hvalidMatch : MainOkValidMatchD3F3 mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hinitSem : MainInitRunSemOkF3 mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    LibsignalCliPqBinaryV2OomF3PlacedAt mpl mmpl bytes :=
  ⟨elf, hparse, cliPqBinaryV2OomF3Placed_of_f3B2NeedLocks H hmain hoverD3 huntyped hpathB
    hvalidMatch hinitSem⟩

/-- Universally quantified two-placement ELF-byte constructor for
`LibsignalCliPqBinaryV2OomF3Placed bytes` across all `LinkedAt` placements `(mpl, mmpl)`. -/
theorem libsignalCliPqBinaryV2OomF3Placed_of_f3B2NeedLocks
    {bytes : List (BitVec 8)}
    (hat : ∀ mpl mmpl : MultiPlacement,
      libsignalSessionLib.LinkedAt bytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl →
      LibsignalCliPqBinaryV2OomF3PlacedAt mpl mmpl bytes) :
    LibsignalCliPqBinaryV2OomF3Placed bytes :=
  hat

end LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3
