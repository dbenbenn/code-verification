/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridges -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Pqxdh.SpqrHooksPCommon
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
import ProofLib.Hoare.Model
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# Untrusted `SampleNTT` State/Input Equivalence & Real-Run Divergence Helpers (`C2RowLayoutFacts.MlKemSampleNttHelpers`)

Reusable untrusted helper lemmas for the 5 `libcrux_ml_kem` `SampleNTT` (`sample_from_xof`) entry
points in the 0-hook stock ELF (`0d6227d21a4550baedafa8c9caf9a975266592662e339a92eaa774ec54cd7020`):
- `B24` `lsKyber1024EncapsSym` (`libcrux_ml_kem::mlkem1024::kyber::encapsulate`)
- `B23` `lsKyber1024DecapsSym` (`libcrux_ml_kem::mlkem1024::kyber::decapsulate`)
- `B10` `lsMlkem768FromSeedSym` (`<KeyPairCompressedBytes>::from_seed`)
- `B19` `lsMlkem768Encaps1Sym` (`libcrux_ml_kem::mlkem768::incremental::encapsulate1`)
- `B22` `lsMlkem768DecapsSym` (`libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key`)

Provides:
1. **State-level `SampleNTT` predicates & `mpl.ρ` / `resolve` bridges**:
   `*StateTerminates u` (`rfl`-identical to `MlKemHooksDehook.*StateTerminates`), `setPC` and
   `stripS` invariance, `MlKemSampleNttStuckAtU mpl u`, and `libsignalSessionLib.resolve mpl sym =
   mpl.ρ sym` for all 5 mangled symbols.
2. **State-level `↔` Input-level `*Terminates` equivalences (via AAPCS64 register & memory reads)**:
   `iff` and negated `iff` bridges between `*StateTerminates u` and `Kyber1024EncapsTerminates` /
   `Kyber1024DecapsTerminates` / `Mlkem768FromSeedTerminates` / `Mlkem768Encaps1Terminates` /
   `Mlkem768DecapsTerminates` (and `*CallTerminates`), both from raw `(ptr ↦ₛ bytes) ∗ R` and
   directly from `(*AtSpec stk …).pre x u ∗ R`.
3. **Real-run return & contrapositive non-return bridges on `0d6227d2…`**:
   For each of the 5 rows, `*StateTerminates u` at entry `u` yields a returning run on both
   `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W` and `cliProgPlacedSig mpl mmpl W` (as well
   as `mlkemMultiLib.blockProgram c2MlkemMpl j`), giving the contrapositive
   `(real run from u never returns) → ¬ *StateTerminates u` on all three programs.
4. **Generic `SampleNTT` loop divergence combinators**:
   `¬ Shake128SeedTerminates` → `∀ extra, allLanesDone N seeds extra = false` →
   `SafeSepWP prog s P (fun _ _ => False)` → infinite `.Running` execution that never returns when
   `CallerLrUnmapped prog s0` holds.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemSampleNttHelpers

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement libsignalSessionExterns lsmpl)
open CryptoVerification.E2E (PqxdhPrims readVecN)
open CryptoVerification.E2E.Pqxdh (readVecN_eq_of_pointsToBytes)
open CryptoVerification.LibsignalSpqrV1 (
  MlKem MlkemDecapsCall MlkemEncaps1Call MlkemFromSeedCall
  mlkemDecapsName mlkemEncaps1Name mlkemFromSeedName
)
open CryptoVerification.SignalSession (CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib)
open LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced.Placed (cliProgPlacedSig)
open LibsignalBinary.Heap (FdsHiFrame PoolPreserved VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridges (
  KemDecapsCall KemDecapsCallTerminates KemEncapsCall KemEncapsCallTerminates
  MlkemDecapsCallTerminates MlkemEncaps1CallTerminates MlkemFromSeedCallTerminates
  kemDecaps_at_keepsFs_vm_premise_subroutineOk
  kemEncapsPreserved_at_keepsFs_vm_premise_subroutineOk
  kemEncaps_at_keepsFs_vm_premise_subroutineOk
  mlkemDecaps_at_keepsFs_vm_premise_subroutineOk
  mlkemEncaps1_at_keepsFs_vm_premise_subroutineOk
  mlkemFromSeed_at_keepsFs_vm_premise_subroutineOk
  withPremise
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridgesBase (
  kemDecapsAtSpec kemDecapsName kemEncapsAtSpec kemEncapsName kemEncapsPreservedAtSpec
  mlkemDecapsAtSpec mlkemEncaps1AtSpec mlkemFromSeedAtSpec withMlKemRoOk
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase (
  mlkemKeep mlkemRoOk_stripExecOutside stripS_mem stripS_pc stripS_readReg64 stripS_sp
  stripS_spAligned stripS_status strip_codeLoaded_mlkem strip_readBytes
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.MlKemCorrectProofs (
  kyber1024DecapsVec_toList kyber1024EncapsVec_fst_toList kyber1024EncapsVec_snd_toList
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (
  mlkem768Incremental_fromSeed_dk_toList
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.LoopFramework (
  allLanesDone allLanesDone_eq_true_iff sampleNttWhile_safeSepWP1
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Kyber1024DecapsTerminates Kyber1024EncapsTerminates Mlkem768DecapsTerminates
  Mlkem768Encaps1Terminates Mlkem768FromSeedTerminates Shake128MatrixTerminates
  Shake128SeedTerminates kyber1024Decaps kyber1024Encaps mlkem768DecapsWith mlkem768Incremental
  mlkem768KeyPairWith parseRej12Candidates sampleNtt shake128FirstBlocks toByteVec
)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs withStack)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ExecFrozen satisfies_of_stripExecOutside satisfies_stripExecOutside
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (CallerLrUnmapped)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (
  cliProgExtPlacedAt cliProgExtPlacedSigAt_cliExternsPlaced_eq
  externAt?_cliProgExtPlacedSigAt_eq_none
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKem (
  c2_mlkem_invMem_of_f3CodeInv
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemPlaceable (
  c2MlkemKeep c2MlkemMpl c2_mlkemKeep_lr_false c2_mlkemKeep_noPanic c2_mlkemKeep_sub_rxProg
  c2_mlkem_placeable c2_resolve_kyber1024Decaps_eq c2_resolve_kyber1024Encaps_eq
  c2_resolve_mlkem768Decaps_eq c2_resolve_mlkem768Encaps1_eq c2_resolve_mlkem768FromSeed_eq
  lsKyber1024DecapsSym lsKyber1024EncapsSym lsMlkem768DecapsSym lsMlkem768Encaps1Sym
  lsMlkem768FromSeedSym
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon (
  libsignalSessionExterns_resolve_eq_rho
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs (
  kemDecapsTightStack kemEncapsTightStack kyber1024Prims₀ mlkemDecapsTightStack
  mlkemEncaps1TightStack mlkemFromSeedTightStack
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts (
  C2ExternTableFacts f3RxSeg_realProg617_externAt_none
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric (
  h2fsgen_StepsVisitedIn h2fsgen_stepsVisitedIn_of_stripS_standard
  h2fsgen_steps_lift_of_visitedIn_noExtern
)

/-! ## 1. State-Level `SampleNTT` Predicates, Invariance, & `resolve = mpl.ρ` Bridges -/

/-- State-level `SampleNTT` termination predicate for `kyber1024::encapsulate` (`B24`),
    `rfl`-identical to `MlKemHooksDehook.KemEncapsStateTerminates`. -/
@[expose] def KemEncapsStateTerminates (u : State) : Prop :=
  Kyber1024EncapsTerminates (u.mem.readBytes (u.readReg64 .x0) 1568)

/-- State-level `SampleNTT` termination predicate for `kyber1024::decapsulate` (`B23`),
    `rfl`-identical to `MlKemHooksDehook.KemDecapsStateTerminates`. -/
@[expose] def KemDecapsStateTerminates (u : State) : Prop :=
  Kyber1024DecapsTerminates (u.mem.readBytes (u.readReg64 .x0) 3168)

/-- State-level `SampleNTT` termination predicate for `<KeyPairCompressedBytes>::from_seed` (`B10`),
    `rfl`-identical to `MlKemHooksDehook.MlkemFromSeedStateTerminates`. -/
@[expose] def MlkemFromSeedStateTerminates (u : State) : Prop :=
  Mlkem768FromSeedTerminates (readVecN u.mem (u.readReg64 .x0) 64)

/-- State-level `SampleNTT` termination predicate for `mlkem768::incremental::encapsulate1` (`B19`),
    `rfl`-identical to `MlKemHooksDehook.MlkemEncaps1StateTerminates`. -/
@[expose] def MlkemEncaps1StateTerminates (u : State) : Prop :=
  Mlkem768Encaps1Terminates (u.mem.readBytes (u.readReg64 .x0) (u.readReg64 .x1).toNat)

/-- State-level `SampleNTT` termination predicate for
    `mlkem768::incremental::decapsulate_compressed_key` (`B22`),
    `rfl`-identical to `MlKemHooksDehook.MlkemDecapsStateTerminates`. -/
@[expose] def MlkemDecapsStateTerminates (u : State) : Prop :=
  Mlkem768DecapsTerminates (readVecN u.mem (u.readReg64 .x0) 2400)

/-- Untrusted mirror of the 5-way per-call stuck-entry predicate (`B2-DESIGN` `MlKemSampleNttStuckAt`),
    keyed by `mpl.ρ` on the 5 mangled `SampleNTT` symbols. -/
@[expose] def MlKemSampleNttStuckAtU (mpl : Obj.MultiPlacement) (u : State) : Prop :=
  (u.pc = mpl.ρ lsKyber1024EncapsSym ∧ ¬ KemEncapsStateTerminates u) ∨
  (u.pc = mpl.ρ lsKyber1024DecapsSym ∧ ¬ KemDecapsStateTerminates u) ∨
  (u.pc = mpl.ρ lsMlkem768FromSeedSym ∧ ¬ MlkemFromSeedStateTerminates u) ∨
  (u.pc = mpl.ρ lsMlkem768Encaps1Sym ∧ ¬ MlkemEncaps1StateTerminates u) ∨
  (u.pc = mpl.ρ lsMlkem768DecapsSym ∧ ¬ MlkemDecapsStateTerminates u)

private theorem stripS_readBytes_eq (keep : BitVec 64 → Bool) (s : State) (a : BitVec 64) (n : Nat) :
    (stripS keep s).mem.readBytes a n = s.mem.readBytes a n := by
  rw [stripS_mem]
  exact strip_readBytes keep s.mem a n

private theorem stripS_readVecN_eq (keep : BitVec 64 → Bool) (s : State) (a : BitVec 64) (n : Nat) :
    readVecN (stripS keep s).mem a n = readVecN s.mem a n :=
  Subtype.ext (stripS_readBytes_eq keep s a n)

@[simp] theorem kemEncapsStateTerminates_setPC (s : State) (pc : BitVec 64) :
    KemEncapsStateTerminates (s.setPC pc) ↔ KemEncapsStateTerminates s := by
  cases s; rfl

@[simp] theorem kemDecapsStateTerminates_setPC (s : State) (pc : BitVec 64) :
    KemDecapsStateTerminates (s.setPC pc) ↔ KemDecapsStateTerminates s := by
  cases s; rfl

@[simp] theorem mlkemFromSeedStateTerminates_setPC (s : State) (pc : BitVec 64) :
    MlkemFromSeedStateTerminates (s.setPC pc) ↔ MlkemFromSeedStateTerminates s := by
  cases s; rfl

@[simp] theorem mlkemEncaps1StateTerminates_setPC (s : State) (pc : BitVec 64) :
    MlkemEncaps1StateTerminates (s.setPC pc) ↔ MlkemEncaps1StateTerminates s := by
  cases s; rfl

@[simp] theorem mlkemDecapsStateTerminates_setPC (s : State) (pc : BitVec 64) :
    MlkemDecapsStateTerminates (s.setPC pc) ↔ MlkemDecapsStateTerminates s := by
  cases s; rfl

@[simp] theorem kemEncapsStateTerminates_stripS (keep : BitVec 64 → Bool) (s : State) :
    KemEncapsStateTerminates (stripS keep s) ↔ KemEncapsStateTerminates s := by
  unfold KemEncapsStateTerminates
  rw [stripS_readReg64, stripS_readBytes_eq]

@[simp] theorem kemDecapsStateTerminates_stripS (keep : BitVec 64 → Bool) (s : State) :
    KemDecapsStateTerminates (stripS keep s) ↔ KemDecapsStateTerminates s := by
  unfold KemDecapsStateTerminates
  rw [stripS_readReg64, stripS_readBytes_eq]

@[simp] theorem mlkemFromSeedStateTerminates_stripS (keep : BitVec 64 → Bool) (s : State) :
    MlkemFromSeedStateTerminates (stripS keep s) ↔ MlkemFromSeedStateTerminates s := by
  unfold MlkemFromSeedStateTerminates
  rw [stripS_readReg64, stripS_readVecN_eq]

@[simp] theorem mlkemEncaps1StateTerminates_stripS (keep : BitVec 64 → Bool) (s : State) :
    MlkemEncaps1StateTerminates (stripS keep s) ↔ MlkemEncaps1StateTerminates s := by
  unfold MlkemEncaps1StateTerminates
  rw [stripS_readReg64, stripS_readReg64, stripS_readBytes_eq]

@[simp] theorem mlkemDecapsStateTerminates_stripS (keep : BitVec 64 → Bool) (s : State) :
    MlkemDecapsStateTerminates (stripS keep s) ↔ MlkemDecapsStateTerminates s := by
  unfold MlkemDecapsStateTerminates
  rw [stripS_readReg64, stripS_readVecN_eq]

theorem lsKyber1024EncapsSym_resolve_eq_rho (mpl : Obj.MultiPlacement) :
    libsignalSessionLib.resolve mpl lsKyber1024EncapsSym = mpl.ρ lsKyber1024EncapsSym :=
  libsignalSessionExterns_resolve_eq_rho mpl lsKyber1024EncapsSym
    (List.contains_iff_mem.mp (by rfl_kernel))

theorem lsKyber1024DecapsSym_resolve_eq_rho (mpl : Obj.MultiPlacement) :
    libsignalSessionLib.resolve mpl lsKyber1024DecapsSym = mpl.ρ lsKyber1024DecapsSym :=
  libsignalSessionExterns_resolve_eq_rho mpl lsKyber1024DecapsSym
    (List.contains_iff_mem.mp (by rfl_kernel))

theorem lsMlkem768FromSeedSym_resolve_eq_rho (mpl : Obj.MultiPlacement) :
    libsignalSessionLib.resolve mpl lsMlkem768FromSeedSym = mpl.ρ lsMlkem768FromSeedSym :=
  libsignalSessionExterns_resolve_eq_rho mpl lsMlkem768FromSeedSym
    (List.contains_iff_mem.mp (by rfl_kernel))

theorem lsMlkem768Encaps1Sym_resolve_eq_rho (mpl : Obj.MultiPlacement) :
    libsignalSessionLib.resolve mpl lsMlkem768Encaps1Sym = mpl.ρ lsMlkem768Encaps1Sym :=
  libsignalSessionExterns_resolve_eq_rho mpl lsMlkem768Encaps1Sym
    (List.contains_iff_mem.mp (by rfl_kernel))

theorem lsMlkem768DecapsSym_resolve_eq_rho (mpl : Obj.MultiPlacement) :
    libsignalSessionLib.resolve mpl lsMlkem768DecapsSym = mpl.ρ lsMlkem768DecapsSym :=
  libsignalSessionExterns_resolve_eq_rho mpl lsMlkem768DecapsSym
    (List.contains_iff_mem.mp (by rfl_kernel))

theorem mlKemSampleNttStuckAtU_iff_resolve (mpl : Obj.MultiPlacement) (u : State) :
    MlKemSampleNttStuckAtU mpl u ↔
      (u.pc = libsignalSessionLib.resolve mpl lsKyber1024EncapsSym ∧ ¬ KemEncapsStateTerminates u) ∨
      (u.pc = libsignalSessionLib.resolve mpl lsKyber1024DecapsSym ∧ ¬ KemDecapsStateTerminates u) ∨
      (u.pc = libsignalSessionLib.resolve mpl lsMlkem768FromSeedSym ∧ ¬ MlkemFromSeedStateTerminates u) ∨
      (u.pc = libsignalSessionLib.resolve mpl lsMlkem768Encaps1Sym ∧ ¬ MlkemEncaps1StateTerminates u) ∨
      (u.pc = libsignalSessionLib.resolve mpl lsMlkem768DecapsSym ∧ ¬ MlkemDecapsStateTerminates u) := by
  simp only [MlKemSampleNttStuckAtU, lsKyber1024EncapsSym_resolve_eq_rho,
    lsKyber1024DecapsSym_resolve_eq_rho, lsMlkem768FromSeedSym_resolve_eq_rho,
    lsMlkem768Encaps1Sym_resolve_eq_rho, lsMlkem768DecapsSym_resolve_eq_rho]

/-! ## 2. State-Level `*StateTerminates` `↔` Input-Level `*Terminates` via ABI Register/Memory Reads -/

/-- Row 1 (`B24` `kyber1024::encapsulate`): `KemEncapsStateTerminates u ↔ Kyber1024EncapsTerminates pk`
    given `x0 = pkA`, `pk.length = 1568`, and `(pkA ↦ₛ pk) ∗ R`. -/
theorem kemEncapsStateTerminates_iff_of_pointsTo {u : State} {pkA : BitVec 64}
    {pk : List (BitVec 8)} {R : SepProp}
    (hx0 : u.readReg64 .x0 = pkA) (hlen : pk.length = 1568)
    (hmem : u.mem ⊨ (pkA ↦ₛ pk) ∗ R) :
    KemEncapsStateTerminates u ↔ Kyber1024EncapsTerminates pk := by
  obtain ⟨_, hread⟩ := (IsBlock.pointsToBytes pkA pk).read hmem
  rw [hlen] at hread
  unfold KemEncapsStateTerminates
  rw [hx0, hread]

theorem not_kemEncapsStateTerminates_iff_of_pointsTo {u : State} {pkA : BitVec 64}
    {pk : List (BitVec 8)} {R : SepProp}
    (hx0 : u.readReg64 .x0 = pkA) (hlen : pk.length = 1568)
    (hmem : u.mem ⊨ (pkA ↦ₛ pk) ∗ R) :
    ¬ KemEncapsStateTerminates u ↔ ¬ Kyber1024EncapsTerminates pk :=
  not_congr (kemEncapsStateTerminates_iff_of_pointsTo hx0 hlen hmem)

theorem kemEncapsStateTerminates_iff_vec_of_pointsTo {u : State} {pkA : BitVec 64}
    {pk : List.Vector (BitVec 8) 1568} {R : SepProp}
    (hx0 : u.readReg64 .x0 = pkA) (hmem : u.mem ⊨ (pkA ↦ₛ pk.toList) ∗ R) :
    KemEncapsStateTerminates u ↔ Kyber1024EncapsTerminates pk.toList :=
  kemEncapsStateTerminates_iff_of_pointsTo hx0 pk.toList_length hmem

/-- Row 2 (`B23` `kyber1024::decapsulate`): `KemDecapsStateTerminates u ↔ Kyber1024DecapsTerminates sk`
    given `x0 = skA`, `sk.length = 3168`, and `(skA ↦ₛ sk) ∗ R`. -/
theorem kemDecapsStateTerminates_iff_of_pointsTo {u : State} {skA : BitVec 64}
    {sk : List (BitVec 8)} {R : SepProp}
    (hx0 : u.readReg64 .x0 = skA) (hlen : sk.length = 3168)
    (hmem : u.mem ⊨ (skA ↦ₛ sk) ∗ R) :
    KemDecapsStateTerminates u ↔ Kyber1024DecapsTerminates sk := by
  obtain ⟨_, hread⟩ := (IsBlock.pointsToBytes skA sk).read hmem
  rw [hlen] at hread
  unfold KemDecapsStateTerminates
  rw [hx0, hread]

theorem not_kemDecapsStateTerminates_iff_of_pointsTo {u : State} {skA : BitVec 64}
    {sk : List (BitVec 8)} {R : SepProp}
    (hx0 : u.readReg64 .x0 = skA) (hlen : sk.length = 3168)
    (hmem : u.mem ⊨ (skA ↦ₛ sk) ∗ R) :
    ¬ KemDecapsStateTerminates u ↔ ¬ Kyber1024DecapsTerminates sk :=
  not_congr (kemDecapsStateTerminates_iff_of_pointsTo hx0 hlen hmem)

theorem kemDecapsStateTerminates_iff_vec_of_pointsTo {u : State} {skA : BitVec 64}
    {sk : List.Vector (BitVec 8) 3168} {R : SepProp}
    (hx0 : u.readReg64 .x0 = skA) (hmem : u.mem ⊨ (skA ↦ₛ sk.toList) ∗ R) :
    KemDecapsStateTerminates u ↔ Kyber1024DecapsTerminates sk.toList :=
  kemDecapsStateTerminates_iff_of_pointsTo hx0 sk.toList_length hmem

/-- Row 3 (`B10` `mlkem768::from_seed`): `MlkemFromSeedStateTerminates u ↔ Mlkem768FromSeedTerminates seed`
    given `x0 = seedA` and `(seedA ↦ₛ seed.toList) ∗ R`. -/
theorem mlkemFromSeedStateTerminates_iff_of_pointsTo {u : State} {seedA : BitVec 64}
    {seed : List.Vector (BitVec 8) 64} {R : SepProp}
    (hx0 : u.readReg64 .x0 = seedA) (hmem : u.mem ⊨ (seedA ↦ₛ seed.toList) ∗ R) :
    MlkemFromSeedStateTerminates u ↔ Mlkem768FromSeedTerminates seed := by
  unfold MlkemFromSeedStateTerminates
  rw [hx0, readVecN_eq_of_pointsToBytes hmem]

theorem not_mlkemFromSeedStateTerminates_iff_of_pointsTo {u : State} {seedA : BitVec 64}
    {seed : List.Vector (BitVec 8) 64} {R : SepProp}
    (hx0 : u.readReg64 .x0 = seedA) (hmem : u.mem ⊨ (seedA ↦ₛ seed.toList) ∗ R) :
    ¬ MlkemFromSeedStateTerminates u ↔ ¬ Mlkem768FromSeedTerminates seed :=
  not_congr (mlkemFromSeedStateTerminates_iff_of_pointsTo hx0 hmem)

/-- Row 4 (`B19` `mlkem768::encapsulate1`): `MlkemEncaps1StateTerminates u ↔ Mlkem768Encaps1Terminates hdr`
    given `x0 = hdrA`, `(x1).toNat = hdr.length`, and `(hdrA ↦ₛ hdr) ∗ R`. -/
theorem mlkemEncaps1StateTerminates_iff_of_pointsTo {u : State} {hdrA : BitVec 64}
    {hdr : List (BitVec 8)} {R : SepProp}
    (hx0 : u.readReg64 .x0 = hdrA) (hx1 : (u.readReg64 .x1).toNat = hdr.length)
    (hmem : u.mem ⊨ (hdrA ↦ₛ hdr) ∗ R) :
    MlkemEncaps1StateTerminates u ↔ Mlkem768Encaps1Terminates hdr := by
  obtain ⟨_, hread⟩ := (IsBlock.pointsToBytes hdrA hdr).read hmem
  unfold MlkemEncaps1StateTerminates
  rw [hx0, hx1, hread]

theorem not_mlkemEncaps1StateTerminates_iff_of_pointsTo {u : State} {hdrA : BitVec 64}
    {hdr : List (BitVec 8)} {R : SepProp}
    (hx0 : u.readReg64 .x0 = hdrA) (hx1 : (u.readReg64 .x1).toNat = hdr.length)
    (hmem : u.mem ⊨ (hdrA ↦ₛ hdr) ∗ R) :
    ¬ MlkemEncaps1StateTerminates u ↔ ¬ Mlkem768Encaps1Terminates hdr :=
  not_congr (mlkemEncaps1StateTerminates_iff_of_pointsTo hx0 hx1 hmem)

/-- Row 5 (`B22` `mlkem768::decapsulate_compressed_key`):
    `MlkemDecapsStateTerminates u ↔ Mlkem768DecapsTerminates dk`
    given `x0 = dkA` and `(dkA ↦ₛ dk.toList) ∗ R`. -/
theorem mlkemDecapsStateTerminates_iff_of_pointsTo {u : State} {dkA : BitVec 64}
    {dk : List.Vector (BitVec 8) 2400} {R : SepProp}
    (hx0 : u.readReg64 .x0 = dkA) (hmem : u.mem ⊨ (dkA ↦ₛ dk.toList) ∗ R) :
    MlkemDecapsStateTerminates u ↔ Mlkem768DecapsTerminates dk := by
  unfold MlkemDecapsStateTerminates
  rw [hx0, readVecN_eq_of_pointsToBytes hmem]

theorem not_mlkemDecapsStateTerminates_iff_of_pointsTo {u : State} {dkA : BitVec 64}
    {dk : List.Vector (BitVec 8) 2400} {R : SepProp}
    (hx0 : u.readReg64 .x0 = dkA) (hmem : u.mem ⊨ (dkA ↦ₛ dk.toList) ∗ R) :
    ¬ MlkemDecapsStateTerminates u ↔ ¬ Mlkem768DecapsTerminates dk :=
  not_congr (mlkemDecapsStateTerminates_iff_of_pointsTo hx0 hmem)

/-! ### Consumer-Spec `.pre` Specializations (`*StateTerminates u ↔ *CallTerminates x`) -/

theorem kemEncapsStateTerminates_iff_of_atSpec_pre {stk : Nat} {Q : PqxdhPrims}
    {x : KemEncapsCall} {R : SepProp} {u : State}
    (hpre : u.mem ⊨ (kemEncapsAtSpec stk Q).pre x u ∗ R) :
    KemEncapsStateTerminates u ↔ KemEncapsCallTerminates x := by
  rcases x with ⟨pkA, pk, rA, rnd, ret⟩
  dsimp only [kemEncapsAtSpec, withStack] at hpre
  simp only [sepConj_assoc] at hpre
  rw [satisfies_pure_sepConj] at hpre
  exact kemEncapsStateTerminates_iff_vec_of_pointsTo hpre.1.1 hpre.2

theorem kemEncapsStateTerminates_iff_of_preservedAtSpec_pre {stk : Nat} {Q : PqxdhPrims}
    {x : KemEncapsCall} {R : SepProp} {u : State}
    (hpre : u.mem ⊨ (kemEncapsPreservedAtSpec stk Q).pre x u ∗ R) :
    KemEncapsStateTerminates u ↔ KemEncapsCallTerminates x := by
  rcases x with ⟨pkA, pk, rA, rnd, ret⟩
  dsimp only [kemEncapsPreservedAtSpec, withStack] at hpre
  simp only [sepConj_assoc] at hpre
  rw [satisfies_pure_sepConj] at hpre
  exact kemEncapsStateTerminates_iff_vec_of_pointsTo hpre.1.1 hpre.2

theorem kemDecapsStateTerminates_iff_of_atSpec_pre {stk : Nat} {Q : PqxdhPrims}
    {x : KemDecapsCall} {R : SepProp} {u : State}
    (hpre : u.mem ⊨ (kemDecapsAtSpec stk Q).pre x u ∗ R) :
    KemDecapsStateTerminates u ↔ KemDecapsCallTerminates x := by
  rcases x with ⟨skA, sk, ctA, ct, ret⟩
  dsimp only [kemDecapsAtSpec, withStack] at hpre
  simp only [sepConj_assoc] at hpre
  rw [satisfies_pure_sepConj] at hpre
  exact kemDecapsStateTerminates_iff_vec_of_pointsTo hpre.1.1 hpre.2

theorem mlkemFromSeedStateTerminates_iff_of_atSpec_pre {stk : Nat} {K : MlKem}
    {x : MlkemFromSeedCall} {R : SepProp} {u : State}
    (hpre : u.mem ⊨ (mlkemFromSeedAtSpec stk K).pre x u ∗ R) :
    MlkemFromSeedStateTerminates u ↔ MlkemFromSeedCallTerminates x := by
  dsimp only [mlkemFromSeedAtSpec] at hpre
  simp only [sepConj_assoc] at hpre
  rw [satisfies_pure_sepConj] at hpre
  exact mlkemFromSeedStateTerminates_iff_of_pointsTo hpre.1.1 hpre.2

theorem mlkemEncaps1StateTerminates_iff_of_atSpec_pre {stk : Nat} {K : MlKem}
    {x : MlkemEncaps1Call} {R : SepProp} {u : State}
    (hpre : u.mem ⊨ (mlkemEncaps1AtSpec stk K).pre x u ∗ R) :
    MlkemEncaps1StateTerminates u ↔ MlkemEncaps1CallTerminates x := by
  dsimp only [mlkemEncaps1AtSpec] at hpre
  simp only [sepConj_assoc] at hpre
  rw [satisfies_pure_sepConj] at hpre
  exact mlkemEncaps1StateTerminates_iff_of_pointsTo hpre.1.2.1 hpre.1.2.2.1 hpre.2

theorem mlkemDecapsStateTerminates_iff_of_atSpec_pre {stk : Nat} {K : MlKem}
    {x : MlkemDecapsCall} {R : SepProp} {u : State}
    (hpre : u.mem ⊨ (mlkemDecapsAtSpec stk K).pre x u ∗ R) :
    MlkemDecapsStateTerminates u ↔ MlkemDecapsCallTerminates x := by
  dsimp only [mlkemDecapsAtSpec] at hpre
  simp only [sepConj_assoc] at hpre
  rw [satisfies_pure_sepConj] at hpre
  exact mlkemDecapsStateTerminates_iff_of_pointsTo hpre.1.2.1 hpre.2

/-! ## 3. Real-Run Return & Contrapositive Non-Return Bridges on `0d6227d2…` -/

private theorem externAt?_mlkemBlockProgram_none_local (mpl : MultiPlacement) (j : Nat)
    (pc : BitVec 64) :
    (mlkemMultiLib.blockProgram mpl j).externAt? pc = none := by
  have h0 : ∀ L : List (String × Nat),
      L.findSome? (fun _ => (none : Option (State → State))) = none := by
    intro L; induction L <;> simp [*]
  dsimp only [MultiPlacedLib.blockProgram, PlacedLib.program,
    Program.externAt?, Program.hookAtOff?]
  simp only [ite_self, h0, Option.or_none]

private theorem mlkemKeep_eq_c2MlkemKeep (mpl : MultiPlacement) :
    mlkemKeep mpl = c2MlkemKeep mpl := rfl

private theorem perm_eq_of_stripExecOutside_keepsFrozen_local {keepR : BitVec 64 → Bool}
    {m0 mf : Memory} (hfr0 : ExecFrozen m0) (hfrf : ExecFrozen mf) (hkf : m0.KeepsFrozen mf)
    (hstrip : ∀ a : BitVec 64,
      (stripExecOutside keepR mf).perm a = (stripExecOutside keepR m0).perm a) :
    ∀ a : BitVec 64, mf.perm a = m0.perm a := fun a => by
  have hst := hstrip a; rw [ProofLib.strip_perm, ProofLib.strip_perm] at hst
  have hfr0_a := hfr0 a; have hfrf_a := hfrf a
  by_cases hfrozen0 : m0.Frozen a
  · exact (hkf a hfrozen0).2.1
  · unfold Memory.Frozen Option.frozen Perm.frozen at hfrozen0
    cases hp0 : m0.perm a <;> cases hpf : mf.perm a
    · rfl
    · rw [hp0, hpf] at hst; simp [Option.map] at hst
    · rw [hp0, hpf] at hst; simp [Option.map] at hst
    · rename_i p0 pf; rw [hp0] at hfr0_a hfrozen0 hst; rw [hpf] at hfrf_a hst
      rcases p0 with ⟨r0, w0, x0, _, _⟩; rcases pf with ⟨rf, wf, xf, _, _⟩
      unfold ProofLib.stripPerm at hst
      cases hk : keepR a <;> cases r0 <;> cases w0 <;> cases x0 <;>
        cases rf <;> cases wf <;> cases xf <;> simp_all [Option.map, Option.x, Option.r, Option.w]

/-- Generic `0d6227d2…` block-to-real-ELF runner for any `mlkemMultiLib` export `(j, sym)`:
    when `StateTerm u` holds at entry `u`, the call terminates normally (`Returned u sf`) on
    `mlkemMultiLib.blockProgram c2MlkemMpl j`, `cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W`,
    AND `cliProgPlacedSig mpl mmpl W`. -/
theorem c2_mlkem_real_returns_of_stateTerminates
    {j : Nat} {sym lsSym : String} {α : Type}
    {master : Spec α} {CallTerm : α → Prop} {StateTerm : State → Prop}
    (hj : j < mlkemMultiLib.blocks.length)
    (hsym : lookupBlockSym sym mlkemMultiLib.blocks = some (j, 0))
    (hmok : mlkemMultiLib.subroutineOk sym
      (fun mpl => withMlKemRoOk mpl (withPremise CallTerm (keepsFs (withVmPreserved master))))
      (fun _ => none))
    (hStateImpCall : ∀ (x : α) (R : SepProp) (s : State),
      StateTerm s → s.mem ⊨ master.pre x s ∗ R → CallTerm x)
    (hm_pan : master.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hm_ex : master.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hm_oom : master.onOom = fun _ _ _ => ⌜False⌝ := by rfl)
    (hm_pre_mem : ∀ x (s : State) (m : Memory),
      master.pre x (s.setMem m) = master.pre x s := by intro _ s _; cases s; rfl)
    (hm_post_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      master.post x (s0.setMem m0) (sf.setMem mf) = master.post x s0 sf := by
        intro _ s0 sf _ _; cases s0; cases sf; rfl)
    {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    (hRes : libsignalSessionLib.resolve mpl lsSym = c2MlkemMpl.base j)
    (W : CliHooks)
    {x : α} {R : SepProp} {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsSym)
    (hrun : u.status = .Running)
    (hsp : u.spAligned = true)
    (hInv : F3CodeInv mpl mmpl u.mem)
    (hFr : ExecFrozen u.mem)
    (hlr_keep : c2MlkemKeep c2MlkemMpl (u.readReg64 .lr) = false)
    (hpre : u.mem ⊨ (keepsFs master).pre x u ∗ R)
    (hTerm : StateTerm u) :
    ∃ sf : State,
      StepsUntil (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (SubroutineStop u) u sf ∧
      Steps (cliProgPlacedSig mpl mmpl W) u sf ∧
      Returned u sf ∧
      CallingConventionPreserved u sf ∧
      VmPreserved u sf ∧
      ExecFrozen sf.mem ∧
      (sf.mem ⊨ (keepsFs master).post x u sf ∗ R) := by
  obtain ⟨hpl, hcl, hro⟩ := c2_mlkem_invMem_of_f3CodeInv hLs hInv
  have hCall : CallTerm x := hStateImpCall x R u hTerm (by simpa only [keepsFs] using hpre)
  obtain ⟨_, i, off, hsym', hsub⟩ := hmok
  have hij : i = j ∧ off = 0 := by
    rw [hsym] at hsym'
    simp only [Option.some.injEq, Prod.mk.injEq] at hsym'
    exact ⟨hsym'.1.symm, hsym'.2.symm⟩
  have hfn : mlkemMultiLib.fnAddr c2MlkemMpl sym = c2MlkemMpl.base j := by
    simp [MultiPlacedLib.fnAddr, hsym]
  have hok_j := hij.1 ▸ hsub c2MlkemMpl hpl
  rw [hfn] at hok_j
  let keep := mlkemKeep c2MlkemMpl
  let u' := stripS keep u
  have hpc_base : u.pc = c2MlkemMpl.base j := hpc.trans hRes
  have hcl' : mlkemMultiLib.CodeLoaded c2MlkemMpl u'.mem := strip_codeLoaded_mlkem hcl
  have hro' : LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables.MlKemRoOk c2MlkemMpl u'.mem := by
    simpa [u', stripS_mem] using mlkemRoOk_stripExecOutside keep hro
  have hpre_strip : u'.mem ⊨ (keepsFs master).pre x u' ∗ R := by
    have hsat := satisfies_stripExecOutside keep hpre
    have hu'_set : u' = u.setMem (stripExecOutside keep u.mem) := by cases u; rfl
    dsimp only [keepsFs] at hsat ⊢
    rw [hu'_set, hm_pre_mem]
    exact hsat
  have hpre_full : u'.mem ⊨
      (mlkemMultiLib.withCodeLoaded c2MlkemMpl
        (withMlKemRoOk c2MlkemMpl
          (withPremise CallTerm (keepsFs (withVmPreserved master))))).pre x u' ∗ R := by
    dsimp only [MultiPlacedLib.withCodeLoaded, withMlKemRoOk, withPremise, keepsFs, withVmPreserved]
    rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, pure_sepConj_of_true hcl',
      sepConj_assoc, pure_sepConj_of_true hro',
      sepConj_assoc, pure_sepConj_of_true hCall]
    exact hpre_strip
  obtain ⟨sf', hsteps', hout'⟩ :=
    reaches_outcome_iff.1
      (subroutine_ok_iff.1 hok_j x R u'
        (by simpa [u', stripS_pc] using hpc_base)
        (by simpa [u', stripS_status] using hrun)
        hpre_full
        (by simpa [u', stripS_spAligned] using hsp))
      (hcl' j hj)
  rcases hout' with ⟨hret', hcc', hpost'⟩ | ⟨_, hp'⟩ | ⟨_, _, he'⟩ | ⟨_, ho'⟩
  · have hlr_out : keep (u.readReg64 .lr) = false := by
      simpa [keep, mlkemKeep_eq_c2MlkemKeep] using hlr_keep
    have hext1_no : ∀ pc, keep pc = true →
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none := by
      intro pc hk
      dsimp only [keep] at hk
      rw [mlkemKeep_eq_c2MlkemKeep] at hk
      exact f3RxSeg_realProg617_externAt_none hExt W (c2_mlkemKeep_sub_rxProg hk)
        (c2_mlkemKeep_noPanic hk)
    obtain ⟨sf, huntil, _, hsf_eq, hfr_sf, hvis⟩ :=
      h2fsgen_stepsVisitedIn_of_stripS_standard (s0 := u) (s1 := u)
        (P1 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (P_sub := mlkemMultiLib.blockProgram c2MlkemMpl j)
        rfl rfl hext1_no (externAt?_mlkemBlockProgram_none_local c2MlkemMpl j)
        hlr_out hsteps' (Or.inl hret') (by rw [hret'.2.2]; decide) hFr
    have hret : Returned u sf := by
      rw [hsf_eq] at hret'
      exact ⟨by simpa [u', stripS_pc, stripS_readReg64] using hret'.1,
        by simpa [u', stripS_sp] using hret'.2.1,
        by simpa [stripS_status] using hret'.2.2⟩
    have hcc : CallingConventionPreserved u sf := by
      rw [hsf_eq] at hcc'
      dsimp only [u'] at hcc'
      cases u; cases sf; exact hcc'
    rw [hsf_eq] at hpost'
    dsimp only [MultiPlacedLib.withCodeLoaded, withMlKemRoOk, withPremise, keepsFs,
      withVmPreserved] at hpost'
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost'
    obtain ⟨hfs', hvm_post'⟩ := hpost'
    rw [sepConj_assoc, satisfies_pure_sepConj] at hvm_post'
    obtain ⟨hvm', hpost_m'⟩ := hvm_post'
    have hfs : sf.fs = u.fs := by
      dsimp only [u'] at hfs'
      cases u; cases sf; exact hfs'
    have hperm : ∀ a : BitVec 64, sf.mem.perm a = u.mem.perm a :=
      perm_eq_of_stripExecOutside_keepsFrozen_local hFr hfr_sf huntil.toSteps.keepsFrozen hvm'.2.2.1
    have hpool : PoolPreserved u sf := by
      rcases hvm'.1 with ⟨h1, h2, h3⟩
      dsimp only [u'] at h1 h2 h3
      exact ⟨by cases u; cases sf; exact h1,
        by cases u; cases sf; exact h2,
        by cases u; cases sf; exact h3⟩
    have hphys : sf.physMemAvail = u.physMemAvail := by
      have hp := hvm'.2.1
      dsimp only [u'] at hp
      cases u; cases sf; exact hp
    have hvm : VmPreserved u sf := ⟨hpool, hphys, hperm, FdsHiFrame.of_fs_eq hfs⟩
    have hpost_sf : sf.mem ⊨ (keepsFs master).post x u sf ∗ R := by
      have hu'_set : u' = u.setMem (stripExecOutside keep u.mem) := by cases u; rfl
      have hsf_set : stripS keep sf = sf.setMem (stripExecOutside keep sf.mem) := by cases sf; rfl
      rw [hu'_set, hsf_set, hm_post_mem] at hpost_m'
      have hpost_m : sf.mem ⊨ master.post x u sf ∗ R :=
        satisfies_of_stripExecOutside hfr_sf (by simpa [State.setMem] using hpost_m')
      dsimp only [keepsFs]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hfs, hpost_m⟩
    have hsig0 : Steps (cliProgPlacedSig mpl mmpl W) u sf :=
      h2fsgen_steps_lift_of_visitedIn_noExtern
        (by rw [← cliProgExtPlacedSigAt_cliExternsPlaced_eq]; rfl)
        hext1_no
        (fun pc hk => by
          rw [← cliProgExtPlacedSigAt_cliExternsPlaced_eq]
          exact externAt?_cliProgExtPlacedSigAt_eq_none.mpr (hext1_no pc hk))
        hvis
    exact ⟨sf, huntil, hsig0, hret, hcc, hvm, hfr_sf, hpost_sf⟩
  · dsimp only [MultiPlacedLib.withCodeLoaded, withMlKemRoOk, withPremise, keepsFs,
      withVmPreserved] at hp'
    rw [hm_pan] at hp'
    exact False.elim (not_satisfies_false_sepConj hp')
  · dsimp only [MultiPlacedLib.withCodeLoaded, withMlKemRoOk, withPremise, keepsFs,
      withVmPreserved] at he'
    rw [hm_ex] at he'
    exact False.elim (not_satisfies_false_sepConj he')
  · dsimp only [MultiPlacedLib.withCodeLoaded, withMlKemRoOk, withPremise, keepsFs,
      withVmPreserved] at ho'
    rw [hm_oom] at ho'
    exact False.elim (not_satisfies_false_sepConj ho')

/-- Contrapositive on `cliProgExtPlacedAt`: if the real 0-hook run from `u` never returns, then
    `¬ StateTerm u`. -/
theorem c2_mlkem_not_stateTerminates_of_real_never_returns
    {j : Nat} {sym lsSym : String} {α : Type}
    {master : Spec α} {CallTerm : α → Prop} {StateTerm : State → Prop}
    (hj : j < mlkemMultiLib.blocks.length)
    (hsym : lookupBlockSym sym mlkemMultiLib.blocks = some (j, 0))
    (hmok : mlkemMultiLib.subroutineOk sym
      (fun mpl => withMlKemRoOk mpl (withPremise CallTerm (keepsFs (withVmPreserved master))))
      (fun _ => none))
    (hStateImpCall : ∀ (x : α) (R : SepProp) (s : State),
      StateTerm s → s.mem ⊨ master.pre x s ∗ R → CallTerm x)
    (hm_pan : master.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hm_ex : master.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hm_oom : master.onOom = fun _ _ _ => ⌜False⌝ := by rfl)
    (hm_pre_mem : ∀ x (s : State) (m : Memory),
      master.pre x (s.setMem m) = master.pre x s := by intro _ s _; cases s; rfl)
    (hm_post_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      master.post x (s0.setMem m0) (sf.setMem mf) = master.post x s0 sf := by
        intro _ s0 sf _ _; cases s0; cases sf; rfl)
    {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    (hRes : libsignalSessionLib.resolve mpl lsSym = c2MlkemMpl.base j)
    (W : CliHooks)
    {x : α} {R : SepProp} {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsSym)
    (hrun : u.status = .Running)
    (hsp : u.spAligned = true)
    (hInv : F3CodeInv mpl mmpl u.mem)
    (hFr : ExecFrozen u.mem)
    (hlr_keep : c2MlkemKeep c2MlkemMpl (u.readReg64 .lr) = false)
    (hpre : u.mem ⊨ (keepsFs master).pre x u ∗ R)
    (hNeverRet : ∀ sf : State,
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u sf → ¬ Returned u sf) :
    ¬ StateTerm u := by
  intro hTerm
  obtain ⟨sf, huntil, _, hret, _⟩ :=
    c2_mlkem_real_returns_of_stateTerminates hj hsym hmok hStateImpCall
      hm_pan hm_ex hm_oom hm_pre_mem hm_post_mem
      hLs hExt hRes W hpc hrun hsp hInv hFr hlr_keep hpre hTerm
  exact hNeverRet sf huntil.toSteps hret

/-- Contrapositive on `cliProgPlacedSig`: if the `cliProgPlacedSig` run from `u` never returns,
    then `¬ StateTerm u`. -/
theorem c2_mlkem_not_stateTerminates_of_sig_never_returns
    {j : Nat} {sym lsSym : String} {α : Type}
    {master : Spec α} {CallTerm : α → Prop} {StateTerm : State → Prop}
    (hj : j < mlkemMultiLib.blocks.length)
    (hsym : lookupBlockSym sym mlkemMultiLib.blocks = some (j, 0))
    (hmok : mlkemMultiLib.subroutineOk sym
      (fun mpl => withMlKemRoOk mpl (withPremise CallTerm (keepsFs (withVmPreserved master))))
      (fun _ => none))
    (hStateImpCall : ∀ (x : α) (R : SepProp) (s : State),
      StateTerm s → s.mem ⊨ master.pre x s ∗ R → CallTerm x)
    (hm_pan : master.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hm_ex : master.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hm_oom : master.onOom = fun _ _ _ => ⌜False⌝ := by rfl)
    (hm_pre_mem : ∀ x (s : State) (m : Memory),
      master.pre x (s.setMem m) = master.pre x s := by intro _ s _; cases s; rfl)
    (hm_post_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      master.post x (s0.setMem m0) (sf.setMem mf) = master.post x s0 sf := by
        intro _ s0 sf _ _; cases s0; cases sf; rfl)
    {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    (hRes : libsignalSessionLib.resolve mpl lsSym = c2MlkemMpl.base j)
    (W : CliHooks)
    {x : α} {R : SepProp} {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsSym)
    (hrun : u.status = .Running)
    (hsp : u.spAligned = true)
    (hInv : F3CodeInv mpl mmpl u.mem)
    (hFr : ExecFrozen u.mem)
    (hlr_keep : c2MlkemKeep c2MlkemMpl (u.readReg64 .lr) = false)
    (hpre : u.mem ⊨ (keepsFs master).pre x u ∗ R)
    (hNeverRet : ∀ sf : State,
      Steps (cliProgPlacedSig mpl mmpl W) u sf → ¬ Returned u sf) :
    ¬ StateTerm u := by
  intro hTerm
  obtain ⟨sf, _, hsig, hret, _⟩ :=
    c2_mlkem_real_returns_of_stateTerminates hj hsym hmok hStateImpCall
      hm_pan hm_ex hm_oom hm_pre_mem hm_post_mem
      hLs hExt hRes W hpc hrun hsp hInv hFr hlr_keep hpre hTerm
  exact hNeverRet sf hsig hret

/-! ### Per-Row Specializations for All 5 `SampleNTT` Entry Points -/

private theorem kyber1024Prims₀_encaps_eq
    (pk : List.Vector (BitVec 8) 1568) (rand : List.Vector (BitVec 8) 32) :
    (kyber1024Prims₀.encaps pk rand).1.toList = (kyber1024Encaps pk.toList rand.toList).1 ∧
    (kyber1024Prims₀.encaps pk rand).2.toList = (kyber1024Encaps pk.toList rand.toList).2 :=
  ⟨kyber1024EncapsVec_fst_toList pk rand, kyber1024EncapsVec_snd_toList pk rand⟩

private theorem kyber1024Prims₀_decaps_eq
    (sk : List.Vector (BitVec 8) 3168) (ct : List.Vector (BitVec 8) 1568) :
    (kyber1024Prims₀.decaps sk ct).toList = kyber1024Decaps sk.toList ct.toList :=
  kyber1024DecapsVec_toList sk ct

private theorem mlkem768Incremental_decaps_eq_local
    (d : List.Vector (BitVec 8) 2400) (c1 : List.Vector (BitVec 8) 960)
    (c2 : List.Vector (BitVec 8) 128) :
    mlkem768Incremental.decaps d c1 c2 =
      toByteVec 32 (mlkem768DecapsWith sampleNtt d.toList c1.toList c2.toList) := rfl

/-- **Row 1 (`B24` `kyber1024::encapsulate`)**: `KemEncapsStateTerminates u` → real run returns. -/
theorem kemEncaps_real_returns_of_stateTerminates
    {stk : Nat} (hstk : kemEncapsTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    (W : CliHooks) {x : KemEncapsCall} {R : SepProp} {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsKyber1024EncapsSym)
    (hrun : u.status = .Running) (hsp : u.spAligned = true)
    (hInv : F3CodeInv mpl mmpl u.mem) (hFr : ExecFrozen u.mem)
    (hlr_keep : c2MlkemKeep c2MlkemMpl (u.readReg64 .lr) = false)
    (hpre : u.mem ⊨ (keepsFs (kemEncapsPreservedAtSpec stk kyber1024Prims₀)).pre x u ∗ R)
    (hTerm : KemEncapsStateTerminates u) :
    ∃ sf : State,
      StepsUntil (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (SubroutineStop u) u sf ∧
      Steps (cliProgPlacedSig mpl mmpl W) u sf ∧
      Returned u sf ∧
      CallingConventionPreserved u sf ∧
      VmPreserved u sf ∧
      ExecFrozen sf.mem ∧
      (sf.mem ⊨ (keepsFs (kemEncapsPreservedAtSpec stk kyber1024Prims₀)).post x u sf ∗ R) :=
  c2_mlkem_real_returns_of_stateTerminates (j := 24) (sym := kemEncapsName) (by decide)
    (by rfl_kernel)
    (kemEncapsPreserved_at_keepsFs_vm_premise_subroutineOk kyber1024Prims₀
      kyber1024Prims₀_encaps_eq stk hstk hfit (fun _ => none))
    (fun _ _ _ hT hp => (kemEncapsStateTerminates_iff_of_preservedAtSpec_pre hp).mp hT)
    rfl rfl rfl (by intro _ s _; cases s; rfl) (by intro _ s0 sf _ _; cases s0; cases sf; rfl)
    hLs hExt (c2_resolve_kyber1024Encaps_eq hLs) W hpc hrun hsp hInv hFr hlr_keep hpre hTerm

theorem not_kemEncapsStateTerminates_of_real_never_returns
    {stk : Nat} (hstk : kemEncapsTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    (W : CliHooks) {x : KemEncapsCall} {R : SepProp} {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsKyber1024EncapsSym)
    (hrun : u.status = .Running) (hsp : u.spAligned = true)
    (hInv : F3CodeInv mpl mmpl u.mem) (hFr : ExecFrozen u.mem)
    (hlr_keep : c2MlkemKeep c2MlkemMpl (u.readReg64 .lr) = false)
    (hpre : u.mem ⊨ (keepsFs (kemEncapsPreservedAtSpec stk kyber1024Prims₀)).pre x u ∗ R)
    (hNeverRet : ∀ sf : State,
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u sf → ¬ Returned u sf) :
    ¬ KemEncapsStateTerminates u := by
  intro hTerm
  obtain ⟨sf, huntil, _, hret, _⟩ :=
    kemEncaps_real_returns_of_stateTerminates hstk hfit hLs hExt W
      hpc hrun hsp hInv hFr hlr_keep hpre hTerm
  exact hNeverRet sf huntil.toSteps hret

theorem not_kemEncapsStateTerminates_of_sig_never_returns
    {stk : Nat} (hstk : kemEncapsTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    (W : CliHooks) {x : KemEncapsCall} {R : SepProp} {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsKyber1024EncapsSym)
    (hrun : u.status = .Running) (hsp : u.spAligned = true)
    (hInv : F3CodeInv mpl mmpl u.mem) (hFr : ExecFrozen u.mem)
    (hlr_keep : c2MlkemKeep c2MlkemMpl (u.readReg64 .lr) = false)
    (hpre : u.mem ⊨ (keepsFs (kemEncapsPreservedAtSpec stk kyber1024Prims₀)).pre x u ∗ R)
    (hNeverRet : ∀ sf : State, Steps (cliProgPlacedSig mpl mmpl W) u sf → ¬ Returned u sf) :
    ¬ KemEncapsStateTerminates u := by
  intro hTerm
  obtain ⟨sf, _, hsig, hret, _⟩ :=
    kemEncaps_real_returns_of_stateTerminates hstk hfit hLs hExt W
      hpc hrun hsp hInv hFr hlr_keep hpre hTerm
  exact hNeverRet sf hsig hret

/-- **Row 2 (`B23` `kyber1024::decapsulate`)**: `KemDecapsStateTerminates u` → real run returns. -/
theorem kemDecaps_real_returns_of_stateTerminates
    {stk : Nat} (hstk : kemDecapsTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    (W : CliHooks) {x : KemDecapsCall} {R : SepProp} {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsKyber1024DecapsSym)
    (hrun : u.status = .Running) (hsp : u.spAligned = true)
    (hInv : F3CodeInv mpl mmpl u.mem) (hFr : ExecFrozen u.mem)
    (hlr_keep : c2MlkemKeep c2MlkemMpl (u.readReg64 .lr) = false)
    (hpre : u.mem ⊨ (keepsFs (kemDecapsAtSpec stk kyber1024Prims₀)).pre x u ∗ R)
    (hTerm : KemDecapsStateTerminates u) :
    ∃ sf : State,
      StepsUntil (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (SubroutineStop u) u sf ∧
      Steps (cliProgPlacedSig mpl mmpl W) u sf ∧
      Returned u sf ∧
      CallingConventionPreserved u sf ∧
      VmPreserved u sf ∧
      ExecFrozen sf.mem ∧
      (sf.mem ⊨ (keepsFs (kemDecapsAtSpec stk kyber1024Prims₀)).post x u sf ∗ R) :=
  c2_mlkem_real_returns_of_stateTerminates (j := 23) (sym := kemDecapsName) (by decide)
    (by rfl_kernel)
    (kemDecaps_at_keepsFs_vm_premise_subroutineOk kyber1024Prims₀
      kyber1024Prims₀_decaps_eq stk hstk hfit (fun _ => none))
    (fun _ _ _ hT hp => (kemDecapsStateTerminates_iff_of_atSpec_pre hp).mp hT)
    rfl rfl rfl (by intro _ s _; cases s; rfl) (by intro _ s0 sf _ _; cases s0; cases sf; rfl)
    hLs hExt (c2_resolve_kyber1024Decaps_eq hLs) W hpc hrun hsp hInv hFr hlr_keep hpre hTerm

theorem not_kemDecapsStateTerminates_of_real_never_returns
    {stk : Nat} (hstk : kemDecapsTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    (W : CliHooks) {x : KemDecapsCall} {R : SepProp} {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsKyber1024DecapsSym)
    (hrun : u.status = .Running) (hsp : u.spAligned = true)
    (hInv : F3CodeInv mpl mmpl u.mem) (hFr : ExecFrozen u.mem)
    (hlr_keep : c2MlkemKeep c2MlkemMpl (u.readReg64 .lr) = false)
    (hpre : u.mem ⊨ (keepsFs (kemDecapsAtSpec stk kyber1024Prims₀)).pre x u ∗ R)
    (hNeverRet : ∀ sf : State,
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u sf → ¬ Returned u sf) :
    ¬ KemDecapsStateTerminates u := by
  intro hTerm
  obtain ⟨sf, huntil, _, hret, _⟩ :=
    kemDecaps_real_returns_of_stateTerminates hstk hfit hLs hExt W
      hpc hrun hsp hInv hFr hlr_keep hpre hTerm
  exact hNeverRet sf huntil.toSteps hret

theorem not_kemDecapsStateTerminates_of_sig_never_returns
    {stk : Nat} (hstk : kemDecapsTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    (W : CliHooks) {x : KemDecapsCall} {R : SepProp} {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsKyber1024DecapsSym)
    (hrun : u.status = .Running) (hsp : u.spAligned = true)
    (hInv : F3CodeInv mpl mmpl u.mem) (hFr : ExecFrozen u.mem)
    (hlr_keep : c2MlkemKeep c2MlkemMpl (u.readReg64 .lr) = false)
    (hpre : u.mem ⊨ (keepsFs (kemDecapsAtSpec stk kyber1024Prims₀)).pre x u ∗ R)
    (hNeverRet : ∀ sf : State, Steps (cliProgPlacedSig mpl mmpl W) u sf → ¬ Returned u sf) :
    ¬ KemDecapsStateTerminates u := by
  intro hTerm
  obtain ⟨sf, _, hsig, hret, _⟩ :=
    kemDecaps_real_returns_of_stateTerminates hstk hfit hLs hExt W
      hpc hrun hsp hInv hFr hlr_keep hpre hTerm
  exact hNeverRet sf hsig hret

/-- **Row 3 (`B10` `mlkem768::from_seed`)**: `MlkemFromSeedStateTerminates u` → real run returns. -/
theorem mlkemFromSeed_real_returns_of_stateTerminates
    {stk : Nat} (hstk : mlkemFromSeedTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    (W : CliHooks) {x : MlkemFromSeedCall} {R : SepProp} {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsMlkem768FromSeedSym)
    (hrun : u.status = .Running) (hsp : u.spAligned = true)
    (hInv : F3CodeInv mpl mmpl u.mem) (hFr : ExecFrozen u.mem)
    (hlr_keep : c2MlkemKeep c2MlkemMpl (u.readReg64 .lr) = false)
    (hpre : u.mem ⊨ (keepsFs (mlkemFromSeedAtSpec stk mlkem768Incremental)).pre x u ∗ R)
    (hTerm : MlkemFromSeedStateTerminates u) :
    ∃ sf : State,
      StepsUntil (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (SubroutineStop u) u sf ∧
      Steps (cliProgPlacedSig mpl mmpl W) u sf ∧
      Returned u sf ∧
      CallingConventionPreserved u sf ∧
      VmPreserved u sf ∧
      ExecFrozen sf.mem ∧
      (sf.mem ⊨ (keepsFs (mlkemFromSeedAtSpec stk mlkem768Incremental)).post x u sf ∗ R) :=
  c2_mlkem_real_returns_of_stateTerminates (j := 10) (sym := mlkemFromSeedName) (by decide)
    (by rfl_kernel)
    (mlkemFromSeed_at_keepsFs_vm_premise_subroutineOk mlkem768Incremental
      mlkem768Incremental_fromSeed_dk_toList stk hstk hfit (fun _ => none))
    (fun _ _ _ hT hp => (mlkemFromSeedStateTerminates_iff_of_atSpec_pre hp).mp hT)
    rfl rfl rfl (by intro _ s _; cases s; rfl) (by intro _ s0 sf _ _; cases s0; cases sf; rfl)
    hLs hExt (c2_resolve_mlkem768FromSeed_eq hLs) W hpc hrun hsp hInv hFr hlr_keep hpre hTerm

theorem not_mlkemFromSeedStateTerminates_of_real_never_returns
    {stk : Nat} (hstk : mlkemFromSeedTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    (W : CliHooks) {x : MlkemFromSeedCall} {R : SepProp} {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsMlkem768FromSeedSym)
    (hrun : u.status = .Running) (hsp : u.spAligned = true)
    (hInv : F3CodeInv mpl mmpl u.mem) (hFr : ExecFrozen u.mem)
    (hlr_keep : c2MlkemKeep c2MlkemMpl (u.readReg64 .lr) = false)
    (hpre : u.mem ⊨ (keepsFs (mlkemFromSeedAtSpec stk mlkem768Incremental)).pre x u ∗ R)
    (hNeverRet : ∀ sf : State,
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u sf → ¬ Returned u sf) :
    ¬ MlkemFromSeedStateTerminates u := by
  intro hTerm
  obtain ⟨sf, huntil, _, hret, _⟩ :=
    mlkemFromSeed_real_returns_of_stateTerminates hstk hfit hLs hExt W
      hpc hrun hsp hInv hFr hlr_keep hpre hTerm
  exact hNeverRet sf huntil.toSteps hret

theorem not_mlkemFromSeedStateTerminates_of_sig_never_returns
    {stk : Nat} (hstk : mlkemFromSeedTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    (W : CliHooks) {x : MlkemFromSeedCall} {R : SepProp} {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsMlkem768FromSeedSym)
    (hrun : u.status = .Running) (hsp : u.spAligned = true)
    (hInv : F3CodeInv mpl mmpl u.mem) (hFr : ExecFrozen u.mem)
    (hlr_keep : c2MlkemKeep c2MlkemMpl (u.readReg64 .lr) = false)
    (hpre : u.mem ⊨ (keepsFs (mlkemFromSeedAtSpec stk mlkem768Incremental)).pre x u ∗ R)
    (hNeverRet : ∀ sf : State, Steps (cliProgPlacedSig mpl mmpl W) u sf → ¬ Returned u sf) :
    ¬ MlkemFromSeedStateTerminates u := by
  intro hTerm
  obtain ⟨sf, _, hsig, hret, _⟩ :=
    mlkemFromSeed_real_returns_of_stateTerminates hstk hfit hLs hExt W
      hpc hrun hsp hInv hFr hlr_keep hpre hTerm
  exact hNeverRet sf hsig hret

/-- **Row 4 (`B19` `mlkem768::encapsulate1`)**: `MlkemEncaps1StateTerminates u` → real run returns. -/
theorem mlkemEncaps1_real_returns_of_stateTerminates
    {stk : Nat} (hstk : mlkemEncaps1TightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    (W : CliHooks) {x : MlkemEncaps1Call} {R : SepProp} {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsMlkem768Encaps1Sym)
    (hrun : u.status = .Running) (hsp : u.spAligned = true)
    (hInv : F3CodeInv mpl mmpl u.mem) (hFr : ExecFrozen u.mem)
    (hlr_keep : c2MlkemKeep c2MlkemMpl (u.readReg64 .lr) = false)
    (hpre : u.mem ⊨ (keepsFs (mlkemEncaps1AtSpec stk mlkem768Incremental)).pre x u ∗ R)
    (hTerm : MlkemEncaps1StateTerminates u) :
    ∃ sf : State,
      StepsUntil (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (SubroutineStop u) u sf ∧
      Steps (cliProgPlacedSig mpl mmpl W) u sf ∧
      Returned u sf ∧
      CallingConventionPreserved u sf ∧
      VmPreserved u sf ∧
      ExecFrozen sf.mem ∧
      (sf.mem ⊨ (keepsFs (mlkemEncaps1AtSpec stk mlkem768Incremental)).post x u sf ∗ R) :=
  c2_mlkem_real_returns_of_stateTerminates (j := 19) (sym := mlkemEncaps1Name) (by decide)
    (by rfl_kernel)
    (mlkemEncaps1_at_keepsFs_vm_premise_subroutineOk mlkem768Incremental
      (fun _ _ => rfl) stk hstk hfit (fun _ => none))
    (fun _ _ _ hT hp => (mlkemEncaps1StateTerminates_iff_of_atSpec_pre hp).mp hT)
    rfl rfl rfl (by intro _ s _; cases s; rfl) (by intro _ s0 sf _ _; cases s0; cases sf; rfl)
    hLs hExt (c2_resolve_mlkem768Encaps1_eq hLs) W hpc hrun hsp hInv hFr hlr_keep hpre hTerm

theorem not_mlkemEncaps1StateTerminates_of_real_never_returns
    {stk : Nat} (hstk : mlkemEncaps1TightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    (W : CliHooks) {x : MlkemEncaps1Call} {R : SepProp} {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsMlkem768Encaps1Sym)
    (hrun : u.status = .Running) (hsp : u.spAligned = true)
    (hInv : F3CodeInv mpl mmpl u.mem) (hFr : ExecFrozen u.mem)
    (hlr_keep : c2MlkemKeep c2MlkemMpl (u.readReg64 .lr) = false)
    (hpre : u.mem ⊨ (keepsFs (mlkemEncaps1AtSpec stk mlkem768Incremental)).pre x u ∗ R)
    (hNeverRet : ∀ sf : State,
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u sf → ¬ Returned u sf) :
    ¬ MlkemEncaps1StateTerminates u := by
  intro hTerm
  obtain ⟨sf, huntil, _, hret, _⟩ :=
    mlkemEncaps1_real_returns_of_stateTerminates hstk hfit hLs hExt W
      hpc hrun hsp hInv hFr hlr_keep hpre hTerm
  exact hNeverRet sf huntil.toSteps hret

theorem not_mlkemEncaps1StateTerminates_of_sig_never_returns
    {stk : Nat} (hstk : mlkemEncaps1TightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    (W : CliHooks) {x : MlkemEncaps1Call} {R : SepProp} {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsMlkem768Encaps1Sym)
    (hrun : u.status = .Running) (hsp : u.spAligned = true)
    (hInv : F3CodeInv mpl mmpl u.mem) (hFr : ExecFrozen u.mem)
    (hlr_keep : c2MlkemKeep c2MlkemMpl (u.readReg64 .lr) = false)
    (hpre : u.mem ⊨ (keepsFs (mlkemEncaps1AtSpec stk mlkem768Incremental)).pre x u ∗ R)
    (hNeverRet : ∀ sf : State, Steps (cliProgPlacedSig mpl mmpl W) u sf → ¬ Returned u sf) :
    ¬ MlkemEncaps1StateTerminates u := by
  intro hTerm
  obtain ⟨sf, _, hsig, hret, _⟩ :=
    mlkemEncaps1_real_returns_of_stateTerminates hstk hfit hLs hExt W
      hpc hrun hsp hInv hFr hlr_keep hpre hTerm
  exact hNeverRet sf hsig hret

/-- **Row 5 (`B22` `mlkem768::decapsulate_compressed_key`)**: `MlkemDecapsStateTerminates u` → real run returns. -/
theorem mlkemDecaps_real_returns_of_stateTerminates
    {stk : Nat} (hstk : mlkemDecapsTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    (W : CliHooks) {x : MlkemDecapsCall} {R : SepProp} {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsMlkem768DecapsSym)
    (hrun : u.status = .Running) (hsp : u.spAligned = true)
    (hInv : F3CodeInv mpl mmpl u.mem) (hFr : ExecFrozen u.mem)
    (hlr_keep : c2MlkemKeep c2MlkemMpl (u.readReg64 .lr) = false)
    (hpre : u.mem ⊨ (keepsFs (mlkemDecapsAtSpec stk mlkem768Incremental)).pre x u ∗ R)
    (hTerm : MlkemDecapsStateTerminates u) :
    ∃ sf : State,
      StepsUntil (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (SubroutineStop u) u sf ∧
      Steps (cliProgPlacedSig mpl mmpl W) u sf ∧
      Returned u sf ∧
      CallingConventionPreserved u sf ∧
      VmPreserved u sf ∧
      ExecFrozen sf.mem ∧
      (sf.mem ⊨ (keepsFs (mlkemDecapsAtSpec stk mlkem768Incremental)).post x u sf ∗ R) :=
  c2_mlkem_real_returns_of_stateTerminates (j := 22) (sym := mlkemDecapsName) (by decide)
    (by rfl_kernel)
    (mlkemDecaps_at_keepsFs_vm_premise_subroutineOk mlkem768Incremental
      mlkem768Incremental_decaps_eq_local stk hstk hfit (fun _ => none))
    (fun _ _ _ hT hp => (mlkemDecapsStateTerminates_iff_of_atSpec_pre hp).mp hT)
    rfl rfl rfl (by intro _ s _; cases s; rfl) (by intro _ s0 sf _ _; cases s0; cases sf; rfl)
    hLs hExt (c2_resolve_mlkem768Decaps_eq hLs) W hpc hrun hsp hInv hFr hlr_keep hpre hTerm

theorem not_mlkemDecapsStateTerminates_of_real_never_returns
    {stk : Nat} (hstk : mlkemDecapsTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    (W : CliHooks) {x : MlkemDecapsCall} {R : SepProp} {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsMlkem768DecapsSym)
    (hrun : u.status = .Running) (hsp : u.spAligned = true)
    (hInv : F3CodeInv mpl mmpl u.mem) (hFr : ExecFrozen u.mem)
    (hlr_keep : c2MlkemKeep c2MlkemMpl (u.readReg64 .lr) = false)
    (hpre : u.mem ⊨ (keepsFs (mlkemDecapsAtSpec stk mlkem768Incremental)).pre x u ∗ R)
    (hNeverRet : ∀ sf : State,
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u sf → ¬ Returned u sf) :
    ¬ MlkemDecapsStateTerminates u := by
  intro hTerm
  obtain ⟨sf, huntil, _, hret, _⟩ :=
    mlkemDecaps_real_returns_of_stateTerminates hstk hfit hLs hExt W
      hpc hrun hsp hInv hFr hlr_keep hpre hTerm
  exact hNeverRet sf huntil.toSteps hret

theorem not_mlkemDecapsStateTerminates_of_sig_never_returns
    {stk : Nat} (hstk : mlkemDecapsTightStack ≤ stk) (hfit : stk ≤ 2 ^ 64 := by decide)
    {mpl mmpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hExt : C2ExternTableFacts mpl)
    (W : CliHooks) {x : MlkemDecapsCall} {R : SepProp} {u : State}
    (hpc : u.pc = libsignalSessionLib.resolve mpl lsMlkem768DecapsSym)
    (hrun : u.status = .Running) (hsp : u.spAligned = true)
    (hInv : F3CodeInv mpl mmpl u.mem) (hFr : ExecFrozen u.mem)
    (hlr_keep : c2MlkemKeep c2MlkemMpl (u.readReg64 .lr) = false)
    (hpre : u.mem ⊨ (keepsFs (mlkemDecapsAtSpec stk mlkem768Incremental)).pre x u ∗ R)
    (hNeverRet : ∀ sf : State, Steps (cliProgPlacedSig mpl mmpl W) u sf → ¬ Returned u sf) :
    ¬ MlkemDecapsStateTerminates u := by
  intro hTerm
  obtain ⟨sf, _, hsig, hret, _⟩ :=
    mlkemDecaps_real_returns_of_stateTerminates hstk hfit hLs hExt W
      hpc hrun hsp hInv hFr hlr_keep hpre hTerm
  exact hNeverRet sf hsig hret

/-! ### `LsRetAddr624` Convenience Corollaries -/

theorem c2_mlkemKeep_lr_false_of_lsRetAddr624 [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {u : State} (hlr : LsRetAddr624 (u.readReg64 .lr)) :
    c2MlkemKeep c2MlkemMpl (u.readReg64 .lr) = false :=
  c2_mlkemKeep_lr_false hLs hlr

/-! ## 4. Generic `SampleNTT` Loop Divergence Combinators (`¬ Shake128SeedTerminates → SafeSepWP … False`) -/

/-- If some lane `i < N` has `¬ Shake128SeedTerminates (seeds i)`, `allLanesDone N seeds extra`
    remains `false` for every `extra : Nat`. -/
theorem allLanesDone_eq_false_of_exists_not_terminates {N : Nat} {seeds : Nat → List (BitVec 8)}
    (hbad : ∃ i, i < N ∧ ¬ Shake128SeedTerminates (seeds i)) (extra : Nat) :
    allLanesDone N seeds extra = false := by
  obtain ⟨i, hi, hnt⟩ := hbad
  cases hd : allLanesDone N seeds extra
  · rfl
  · exact False.elim (hnt ⟨extra, allLanesDone_eq_true_iff.mp hd i hi⟩)

/-- If `¬ Shake128MatrixTerminates rho k`, some matrix entry `(i, j) ∈ [0, k)²` has a non-terminating
    34-byte XOF seed `rho.take 32 ++ [i, j]`. -/
theorem exists_bad_matrix_entry_of_not_matrixTerminates {rho : List (BitVec 8)} {k : Nat}
    (h : ¬ Shake128MatrixTerminates rho k) :
    ∃ i j : Nat, i < k ∧ j < k ∧
      ¬ Shake128SeedTerminates (rho.take 32 ++ [BitVec.ofNat 8 i, BitVec.ofNat 8 j]) := by
  classical
  by_contra hall
  apply h
  intro i j hi hj
  by_contra hnt
  exact hall ⟨i, j, hi, hj, hnt⟩

/-- Divergence counterpart to `LoopFramework.sampleNttWhile_safeSepWP`: when
    `∀ extra, allLanesDone N seeds (extra + 1) = false`, the `SampleNTT` `while !done` loop satisfies
    `SafeSepWP prog s0 P0 (fun _ _ => False)` (never exits, never faults). -/
theorem sampleNttWhile_diverge_safeSepWP {prog : Program} {N : Nat}
    {seeds : Nat → List (BitVec 8)} {loopHead midPC exitPC : BitVec 64}
    {Inv Mid : Nat → State → SepProp → Prop}
    (hne : loopHead ≠ midPC) (hInvPC : ∀ extra st P, Inv extra st P → st.pc = loopHead)
    (hNever : ∀ extra : Nat, allLanesDone N seeds (extra + 1) = false)
    (hBodyA : ∀ extra st P, Inv extra st P → SepWP prog midPC st P (Mid extra))
    (hBodyB : ∀ extra sm Pm, sm.pc = midPC → sm.status = .Running → Mid extra sm Pm →
      SepWP prog (if allLanesDone N seeds (extra + 1) then exitPC else loopHead) sm Pm
        (fun sf Pf => if allLanesDone N seeds (extra + 1) then False else Inv (extra + 1) sf Pf))
    {extra0 : Nat} {s0 : State} {P0 : SepProp} (h0 : Inv extra0 s0 P0) :
    SafeSepWP prog s0 P0 (fun _ _ => False) := by
  refine sampleNttWhile_safeSepWP1 (fun extra st P hInv => ?_) h0
  refine SafeSepWP1.of_sepWP (by rw [hInvPC extra st P hInv]; exact hne) ?_
  refine (hBodyA extra st P hInv).mono fun sm Pm hmpc hmrun hMid => ?_
  refine SafeSepWP.of_total ((hBodyB extra sm Pm hmpc hmrun hMid).mono fun _ _ _ _ hPost => ?_)
  rw [hNever extra] at hPost
  exact Or.inl hPost

/-- Divergence counterpart to `LoopFramework.sampleNttRow_safeSepWP`: when
    `∀ extra, allLanesDone N seeds extra = false`, the 3-block init + `while !done` row site
    satisfies `SafeSepWP prog sEntry PEntry (fun _ _ => False)`. -/
theorem sampleNttRow_diverge_safeSepWP {prog : Program} {N : Nat}
    {seeds : Nat → List (BitVec 8)} {loopHead midPC exitPC : BitVec 64}
    {Inv Mid : Nat → State → SepProp → Prop}
    {sEntry : State} {PEntry : SepProp}
    (hne : loopHead ≠ midPC) (hInvPC : ∀ extra st P, Inv extra st P → st.pc = loopHead)
    (hNever : ∀ extra : Nat, allLanesDone N seeds extra = false)
    (hInit : SepWP prog (if allLanesDone N seeds 0 then exitPC else loopHead) sEntry PEntry
      (fun sf Pf => if allLanesDone N seeds 0 then False else Inv 0 sf Pf))
    (hBodyA : ∀ extra st P, Inv extra st P → SepWP prog midPC st P (Mid extra))
    (hBodyB : ∀ extra sm Pm, sm.pc = midPC → sm.status = .Running → Mid extra sm Pm →
      SepWP prog (if allLanesDone N seeds (extra + 1) then exitPC else loopHead) sm Pm
        (fun sf Pf => if allLanesDone N seeds (extra + 1) then False else Inv (extra + 1) sf Pf)) :
    SafeSepWP prog sEntry PEntry (fun _ _ => False) := by
  refine SafeSepWP.of_sepWP (hInit.mono fun _ _ _ _ hPost => ?_)
  rw [hNever 0] at hPost
  exact sampleNttWhile_diverge_safeSepWP hne hInvPC (fun extra => hNever (extra + 1))
    hBodyA hBodyB hPost

/-- Eliminate `SafeSepWP prog s0 P0 (fun _ _ => False)` into concrete operational divergence:
    every state reachable from `s0` is `.Running` and has a `Step prog` successor. -/
theorem diverge_of_safeSepWP_false {prog : Program} {s0 : State} {P0 R : SepProp}
    (hw : SafeSepWP prog s0 P0 (fun _ _ => False))
    (hm : s0.mem ⊨ P0 ∗ R) (hcl : prog.CodeLoaded s0.mem) :
    ∀ u : State, Steps prog s0 u → u.status = .Running ∧ ∃ v : State, Step prog u v := by
  rcases hw R hm hcl with ⟨_, _, _, _, hf⟩ | hdiv
  · exact False.elim hf
  · exact hdiv

/-- Under `CallerLrUnmapped prog s0`, an infinite `.Running` execution from `s0.setPC entry`
    can never reach a `Returned s0 sf` state (`sf.pc = s0.readReg64 .lr`), because any step at
    `s0.readReg64 .lr` would halt with `.Halted` (`≠ .Running`). -/
theorem never_returns_of_diverge_at_lr_unmapped {prog : Program} {s0 : State} {entry : BitVec 64}
    (hLr : CallerLrUnmapped prog s0)
    (hdiv : ∀ u : State, Steps prog (s0.setPC entry) u →
      u.status = .Running ∧ ∃ v : State, Step prog u v) :
    ∀ sf : State, Steps prog (s0.setPC entry) sf → ¬ Returned s0 sf := by
  intro sf hsteps hret
  have hkf : s0.mem.KeepsFrozen sf.mem := by
    have hm : (s0.setPC entry).mem = s0.mem := by cases s0; rfl
    exact hm ▸ hsteps.keepsFrozen
  obtain ⟨hfetch_none, hext_none⟩ := hLr sf.mem hkf
  rw [← hret.1] at hfetch_none hext_none
  obtain ⟨_, v, hstep_v⟩ := hdiv sf hsteps
  obtain ⟨hrun_v, _⟩ := hdiv v (hsteps.trans (Steps.step hstep_v (Steps.refl v)))
  cases hstep_v with
  | exec _ hfm => rw [hfetch_none] at hfm; cases hfm
  | halt_unmapped _ _ _ => cases hrun_v
  | extern _ he _ _ => rw [hext_none] at he; cases he
  | extern_fault _ he _ => rw [hext_none] at he; cases he

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemSampleNttHelpers
