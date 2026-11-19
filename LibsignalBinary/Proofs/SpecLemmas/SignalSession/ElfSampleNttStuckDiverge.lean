/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.Bridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Placed.CliPlainPanPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3G -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeBase -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDomainArms -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import VerifiedLibraries.Mallocng.Spec
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTight
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraWideTable
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeMlKemAvoid
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Branch2
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2ExecFrozenWire
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMemcpy
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMemset
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KNarrowR1

/-!
# Top-Level Stuck-`SampleNTT` Divergence & OOM-Freedom (`ElfSampleNttStuckDiverge`)

Instantiates `ElfSampleNttStuckDivergeBase` at `ghFixed := h2k_ghFixedK mpl mmpl` and
`GhostMainArmsFor` (`H2KGhostArmsType`), discharging all 38 `c2LinkedExtraGhosts` rows via:
- `ElfSampleNttStuckDivergeExtraTight` (23 tight-keep / sentinel-`lr` rows),
- `ElfSampleNttStuckDivergeMlKemAvoid` (2 non-`SampleNTT` + 5 `SampleNTT` ML-KEM rows),
- `ElfSampleNttStuckDivergeExtraWideTable` (8 wide-keep rows),
while keeping `ElfSlicesPqOomH2Asm`, `ElfSlicesPqOomH2KAssembly`, and
`ElfSlicesPqOomH2KGhostArms` out of the import cone so any of them (as well as
`ElfNoOomPlacedInstK` and `ProgressElfPlacedG`) can import this module without an import cycle.
-/

public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDiverge

open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalSpqrV1 (sha256Compress)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhInputs Inputs cliElfBytes cliElfImage cliElf_parse cliExternsPlaced
   libsignalSessionLib)
open CryptoVerification.SignalSession.Cli.RunGlue
  (cliGhostExterns cliGhostExterns_eq_withExtra)
open LibsignalBinary.Proofs.Placed.CliPlainPanPlaced
  (CliReachesOOMPlainPanPlaced CliReachesSampleNttStuckPlainPanPlaced cliRunPlainPanPlacedSig)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3G (V2F3StuckDomain)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay
  (GhostSymActive_iff_named_or_extra)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer
  (mlkemSampleNttSyms)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs
  (kemDecapsTightStack kemEncapsTightStack mlkemDecapsTightStack mlkemEncaps1TightStack
   mlkemFromSeedTightStack)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeBase
  (cliRunPlacedSig_none_and_not_oom_of_v2F3StuckDomain_of_ghFixed h2kSnttExtraFacts_of_subtables
   namedGhostSteps_of_ghFixed_eq)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeCore
  (GhostFixedFacts H2KSnttExtraFacts NamedGhostStepsBelow4b0000)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTight
  (c2ExtraTightSyms c2ExtraTightTable isExtraTightSym)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraWideTable
  (c2ExtraWideSyms c2ExtraWideTable extraWide_nonSnttAvoidS5_of_subtable isExtraWideSym)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeMlKemAvoid
  (c2MlKemNonSnttSyms c2MlKemNonSnttTable c2MlKemSnttTable isMlKemNonSnttSym
   mlkem_nonSnttAvoidS5_of_subtable mlkem_snttStrictAvoid_of_subtable)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDomainArms
  (GhostMainArmsFor)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Branch2
  (h2b2_realW_externAt_none_of_ghostSymActive)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2ExecFrozenWire
  (h2ef_h2k_ghFixedK_preserves_execFrozen)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks
  (c2LinkedExtraGhosts c2_atCallSntt_h2k c2_extraReplaysNonSntt_h2k h2k_extra_lookup_kemDecaps
   h2k_extra_lookup_kemEncaps h2k_extra_lookup_mlkemDecaps h2k_extra_lookup_mlkemEncaps1
   h2k_extra_lookup_mlkemFromSeed h2k_fds_of_noException h2k_ghFixedK
   h2k_keepSubLr_false_of_noException)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMemcpy
  (h2k_ghFixedK_blk20TrapHook)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMemset
  (h2k_ghFixedK_blk21TrapHook)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KNarrowR1
  (h2k_ghFixedK_blk20_ext_trap h2k_ghFixedK_blk21_ext_trap)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_hblk hole2_hext_nodup hole2_keepSub)
open VerifiedLibraries (mallocngLib)

/-- Global 6-arm ghost witness type at `h2k_ghFixedK` (defined via `GhostMainArmsFor` without
    importing `ElfSlicesPqOomH2Asm` or `ElfSlicesPqOomH2KGhostArms` so any downstream module can
    import this module without an import cycle). -/
@[expose] def H2KGhostArmsType : Prop :=
  ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl),
    mallocngLib.LinkedAt cliElfBytes mmpl →
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    GhostMainArmsFor mpl mmpl
      (fun W => cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))

/-- Discharges all 8 fields of `GhostFixedFacts` at `keepSub := hole2_keepSub`,
    `ghFixed := h2k_ghFixedK mpl mmpl`. -/
theorem ghostFixedFacts_h2k [LibsignalPlacement] {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    GhostFixedFacts mpl mmpl hole2_keepSub (h2k_ghFixedK mpl mmpl) where
  realNone W sym f hsym_ext hAct :=
    h2b2_realW_externAt_none_of_ghostSymActive hLs (h2k_ghFixedK mpl mmpl) W hsym_ext
      ((GhostSymActive_iff_named_or_extra (h2k_ghFixedK mpl mmpl) sym f).mpr (Or.inl hAct))
  noExLr hext hnoShim hnoex hnoMs hnoMc :=
    h2k_keepSubLr_false_of_noException mpl mmpl hext hnoShim hnoex hnoMs hnoMc
  noExFds hext hnoex :=
    h2k_fds_of_noException mpl mmpl hext hnoex
  trap21 hext hnoShim :=
    h2k_ghFixedK_blk21TrapHook mpl hMm hext hnoShim
  trap20 hext hnoShim :=
    h2k_ghFixedK_blk20TrapHook mpl hMm hext hnoShim
  blk21Ext := h2k_ghFixedK_blk21_ext_trap hLs hMm
  blk20Ext := h2k_ghFixedK_blk20_ext_trap hLs hMm
  preservesExecFrozen hAct u hfr :=
    h2ef_h2k_ghFixedK_preserves_execFrozen mpl mmpl hAct u hfr

/-- Discharges `NamedGhostStepsBelow4b0000` at `keepSub := hole2_keepSub`,
    `ghFixed := h2k_ghFixedK mpl mmpl`. -/
theorem namedGhostSteps_h2k [LibsignalPlacement] {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    NamedGhostStepsBelow4b0000 mpl mmpl hole2_keepSub (h2k_ghFixedK mpl mmpl) :=
  namedGhostSteps_of_ghFixed_eq hLs hMm (h2k_ghFixedK mpl mmpl)
    rfl rfl rfl rfl rfl
    (fun _ _ h => (congrArg Subtype.val (Option.some.inj h)).symm)
    (fun _ _ h => (congrArg Subtype.val (Option.some.inj h)).symm)
    rfl rfl

/-! ## Subtable Lookup Agreements & Concrete `h2kSnttExtraFacts` -/

private theorem lookup_here {V : Type} (k : String) (v : V) (tl : List (String × V)) :
    ((k, v) :: tl).lookup k = some v := by
  simp [List.lookup]

private theorem lookup_there {V : Type} {k sym : String} (v : V) (tl : List (String × V))
    (hne : (sym == k) = false := by decide) :
    ((k, v) :: tl).lookup sym = tl.lookup sym := by
  simp [List.lookup, hne]

private theorem subtable_lookup_eq {V : Type} {s : String} {l1 l2 : List (String × V)}
    {v : V} (h1 : l1.lookup s = some v) (h2 : l2.lookup s = some v) :
    l1.lookup s = l2.lookup s :=
  h1.trans h2.symm

set_option maxRecDepth 2000000 in
private theorem h2k_extra_subtable_tight [LibsignalPlacement] (mpl mmpl : MultiPlacement) :
    ∀ s : String, isExtraTightSym s = true →
      (h2k_ghFixedK mpl mmpl).extra.lookup s = (c2ExtraTightTable mmpl).lookup s := by
  intro s hs
  have hmem := List.contains_iff_mem.mp hs
  simp only [c2ExtraTightSyms, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · apply subtable_lookup_eq
    · dsimp only [h2k_ghFixedK, c2LinkedExtraGhosts]
      repeat' first | exact lookup_here _ _ _ | refine (lookup_there _ _).trans ?_
    · dsimp only [c2ExtraTightTable]
      repeat' first | exact lookup_here _ _ _ | refine (lookup_there _ _).trans ?_

set_option maxRecDepth 2000000 in
private theorem h2k_extra_subtable_mlkemNonSntt [LibsignalPlacement] (mpl mmpl : MultiPlacement) :
    ∀ s : String, isMlKemNonSnttSym s = true →
      (h2k_ghFixedK mpl mmpl).extra.lookup s = c2MlKemNonSnttTable.lookup s := by
  intro s hs
  have hmem := List.contains_iff_mem.mp hs
  simp only [c2MlKemNonSnttSyms, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl <;>
  · apply subtable_lookup_eq
    · dsimp only [h2k_ghFixedK, c2LinkedExtraGhosts]
      repeat' first | exact lookup_here _ _ _ | refine (lookup_there _ _).trans ?_
    · dsimp only [c2MlKemNonSnttTable]
      repeat' first | exact lookup_here _ _ _ | refine (lookup_there _ _).trans ?_

set_option maxRecDepth 2000000 in
private theorem h2k_extra_subtable_extraWide [LibsignalPlacement] (mpl mmpl : MultiPlacement) :
    ∀ s : String, isExtraWideSym s = true →
      (h2k_ghFixedK mpl mmpl).extra.lookup s = (c2ExtraWideTable mmpl).lookup s := by
  intro s hs
  have hmem := List.contains_iff_mem.mp hs
  simp only [c2ExtraWideSyms, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · apply subtable_lookup_eq
    · dsimp only [h2k_ghFixedK, c2LinkedExtraGhosts]
      repeat' first | exact lookup_here _ _ _ | refine (lookup_there _ _).trans ?_
    · dsimp only [c2ExtraWideTable]
      repeat' first | exact lookup_here _ _ _ | refine (lookup_there _ _).trans ?_

set_option maxRecDepth 2000000 in
private theorem h2k_extra_subtable_mlkemSntt [LibsignalPlacement] (mpl mmpl : MultiPlacement) :
    ∀ s : String, s ∈ mlkemSampleNttSyms →
      (h2k_ghFixedK mpl mmpl).extra.lookup s = c2MlKemSnttTable.lookup s := by
  intro s hs
  simp only [mlkemSampleNttSyms, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl <;>
  · apply subtable_lookup_eq
    · dsimp only [h2k_ghFixedK, c2LinkedExtraGhosts]
      repeat' first | exact lookup_here _ _ _ | refine (lookup_there _ _).trans ?_
    · dsimp only [c2MlKemSnttTable]
      repeat' first | exact lookup_here _ _ _ | refine (lookup_there _ _).trans ?_

/-- Concrete `H2KSnttExtraFacts` bundle across all 38 `c2LinkedExtraGhosts` rows of
    `h2k_ghFixedK mpl mmpl`. -/
theorem h2kSnttExtraFacts
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    H2KSnttExtraFacts mpl mmpl (h2k_ghFixedK mpl mmpl) (h2k_ghFixedK mpl mmpl).extra := by
  letI : LibsignalPlacement :=
    libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  change H2KSnttExtraFacts lsmpl mmpl (h2k_ghFixedK lsmpl mmpl) (h2k_ghFixedK lsmpl mmpl).extra
  exact h2kSnttExtraFacts_of_subtables hLs
    (Or.inr rfl)
    (Or.inr rfl)
    (h2k_extra_subtable_tight lsmpl mmpl)
    ⟨kemEncapsTightStack, Nat.le_refl _, by decide, h2k_extra_lookup_kemEncaps lsmpl mmpl⟩
    ⟨kemDecapsTightStack, Nat.le_refl _, by decide, h2k_extra_lookup_kemDecaps lsmpl mmpl⟩
    ⟨mlkemFromSeedTightStack, Nat.le_refl _, by decide, h2k_extra_lookup_mlkemFromSeed lsmpl mmpl⟩
    ⟨mlkemEncaps1TightStack, Nat.le_refl _, by decide, h2k_extra_lookup_mlkemEncaps1 lsmpl mmpl⟩
    ⟨mlkemDecapsTightStack, Nat.le_refl _, by decide, h2k_extra_lookup_mlkemDecaps lsmpl mmpl⟩
    (c2_atCallSntt_h2k lsmpl mmpl hLs rfl)
    (fun sym f hDom hNotSntt hLook => by
      have hNotMem : sym ∉ mlkemSampleNttSyms :=
        fun hmem => Bool.false_ne_true (hNotSntt.symm.trans (List.contains_iff_mem.mpr hmem))
      simpa only [cliGhostExterns_eq_withExtra (h2k_ghFixedK lsmpl mmpl)] using
        c2_extraReplaysNonSntt_h2k lsmpl mmpl hLs hMm rfl sym f hDom hNotMem hLook)
    (mlkem_nonSnttAvoidS5_of_subtable hLs (h2k_extra_subtable_mlkemNonSntt lsmpl mmpl))
    (extraWide_nonSnttAvoidS5_of_subtable hLs hMm (h2k_extra_subtable_extraWide lsmpl mmpl))
    (mlkem_snttStrictAvoid_of_subtable hLs (h2k_extra_subtable_mlkemSntt lsmpl mmpl))

/-! ## Top-Level Divergence & OOM-Freedom Theorems -/

/-- Full `V2F3StuckDomain` divergence and OOM-freedom theorem parameterized over `H2KSnttExtraFacts`
    at `h2k_ghFixedK mpl mmpl`. -/
theorem cliRunPlacedSig_none_and_not_oom_of_v2F3StuckDomain_of_extraFacts
    (hG : H2KGhostArmsType)
    (hExtra : ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl),
      mallocngLib.LinkedAt cliElfBytes mmpl →
      letI : LibsignalPlacement :=
        libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      H2KSnttExtraFacts mpl mmpl (h2k_ghFixedK mpl mmpl) (h2k_ghFixedK mpl mmpl).extra)
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (i : Inputs)
    (hDom : V2F3StuckDomain ⟨W.C, W.Q⟩ i)
    (hStuck : CliReachesSampleNttStuckPlainPanPlaced mpl mmpl cliElfImage W i) :
    cliRunPlainPanPlacedSig mpl mmpl cliElfImage W i = none ∧
      ¬ CliReachesOOMPlainPanPlaced mpl mmpl cliElfImage W i :=
  letI : LibsignalPlacement :=
     libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  cliRunPlacedSig_none_and_not_oom_of_v2F3StuckDomain_of_ghFixed
    mpl mmpl hLs hMm (h2k_ghFixedK mpl mmpl)
    (hG mpl mmpl hLs hMm)
    (ghostFixedFacts_h2k hLs hMm)
    (namedGhostSteps_h2k hLs hMm)
    (hExtra mpl mmpl hLs hMm)
    W hF hE hD hX hPub hF512 hEnc hDec hK i hDom hStuck

/-- Unconditional `V2F3StuckDomain` divergence and OOM-freedom theorem at `h2k_ghFixedK`. -/
theorem cliRunPlacedSig_none_and_not_oom_of_v2F3StuckDomain_cliElfK
    (hG : H2KGhostArmsType)
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (i : Inputs)
    (hDom : V2F3StuckDomain ⟨W.C, W.Q⟩ i)
    (hStuck : CliReachesSampleNttStuckPlainPanPlaced mpl mmpl cliElfImage W i) :
    cliRunPlainPanPlacedSig mpl mmpl cliElfImage W i = none ∧
      ¬ CliReachesOOMPlainPanPlaced mpl mmpl cliElfImage W i :=
  cliRunPlacedSig_none_and_not_oom_of_v2F3StuckDomain_of_extraFacts
    hG h2kSnttExtraFacts mpl mmpl hLs hMm W hF hE hD hX hPub hF512 hEnc hDec hK i hDom hStuck

/-- `cliRunPlainPanPlacedSig = none` projection for `ElfSlicesPqOomH2KGhostArms` (`hStuckDiv`). -/
theorem cliRunPlacedSig_eq_none_of_v2F3StuckDomain_cliElfK
    (hG : H2KGhostArmsType) :
    ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      mallocngLib.LinkedAt cliElfBytes mmpl →
      ∀ (W : CliHooks),
        W.C.F = sha256Compress →
        W.C.E = CryptoGames.AES256.aes256Enc →
        W.C.D = CryptoGames.AES256.aes256Dec →
        W.C.X = CryptoGames.RFC7748.x25519Ref →
        W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
        W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
        W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
        W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
        W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
        ∀ (i : Inputs), V2F3StuckDomain ⟨W.C, W.Q⟩ i →
          CliReachesSampleNttStuckPlainPanPlaced mpl mmpl cliElfImage W i →
          cliRunPlainPanPlacedSig mpl mmpl cliElfImage W i = none :=
  fun mpl mmpl hLs hMm W hF hE hD hX hPub hF512 hEnc hDec hK i hDom hStuck =>
    (cliRunPlacedSig_none_and_not_oom_of_v2F3StuckDomain_cliElfK
      hG mpl mmpl hLs hMm W hF hE hD hX hPub hF512 hEnc hDec hK i hDom hStuck).1

/-- `¬ CliReachesOOMPlainPanPlaced` projection across `V2F3StuckDomain`. -/
theorem not_cliReachesOOMPlaced_of_v2F3StuckDomain_cliElfK
    (hG : H2KGhostArmsType) :
    ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      mallocngLib.LinkedAt cliElfBytes mmpl →
      ∀ (W : CliHooks),
        W.C.F = sha256Compress →
        W.C.E = CryptoGames.AES256.aes256Enc →
        W.C.D = CryptoGames.AES256.aes256Dec →
        W.C.X = CryptoGames.RFC7748.x25519Ref →
        W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
        W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
        W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
        W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
        W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
        ∀ (i : Inputs), V2F3StuckDomain ⟨W.C, W.Q⟩ i →
          CliReachesSampleNttStuckPlainPanPlaced mpl mmpl cliElfImage W i →
          ¬ CliReachesOOMPlainPanPlaced mpl mmpl cliElfImage W i :=
  fun mpl mmpl hLs hMm W hF hE hD hX hPub hF512 hEnc hDec hK i hDom hStuck =>
    (cliRunPlacedSig_none_and_not_oom_of_v2F3StuckDomain_cliElfK
      hG mpl mmpl hLs hMm W hF hE hD hX hPub hF512 hEnc hDec hK i hDom hStuck).2

/-- `ElfImage.parse` corollary of `cliRunPlacedSig_none_and_not_oom_of_v2F3StuckDomain_cliElfK`. -/
theorem cliRunPlacedSig_none_and_not_oom_of_v2F3StuckDomain_cliElfK_parsed
    (hG : H2KGhostArmsType)
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (elf : ElfImage) (hParse : ElfImage.parse cliElfBytes = .ok elf)
    (W : CliHooks)
    (hF : W.C.F = sha256Compress)
    (hE : W.C.E = CryptoGames.AES256.aes256Enc)
    (hD : W.C.D = CryptoGames.AES256.aes256Dec)
    (hX : W.C.X = CryptoGames.RFC7748.x25519Ref)
    (hPub : W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef)
    (hF512 : W.Q.F512 = CryptoGames.SHA512.sha512CompressState)
    (hEnc : W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec)
    (hDec : W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec)
    (hK : W.Q.K = CryptoGames.MLKEM.mlkem768Incremental)
    (i : Inputs)
    (hDom : V2F3StuckDomain ⟨W.C, W.Q⟩ i)
    (hStuck : CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W i) :
    cliRunPlainPanPlacedSig mpl mmpl elf W i = none ∧
      ¬ CliReachesOOMPlainPanPlaced mpl mmpl elf W i := by
  have heq : cliElfImage = elf := Except.ok.inj (cliElf_parse.symm.trans hParse)
  subst heq
  exact cliRunPlacedSig_none_and_not_oom_of_v2F3StuckDomain_cliElfK
    hG mpl mmpl hLs hMm W hF hE hD hX hPub hF512 hEnc hDec hK i hDom hStuck

/-- `CliPqxdhInputs` specialization (`Or.inl`) of
    `cliRunPlacedSig_eq_none_of_v2F3StuckDomain_cliElfK` for `ElfNoOomPlacedInstK`. -/
theorem cliRunPlacedSig_eq_none_of_cliPqxdhInputs_cliElfK
    (hG : H2KGhostArmsType) :
    ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      mallocngLib.LinkedAt cliElfBytes mmpl →
      ∀ (W : CliHooks),
        W.C.F = sha256Compress →
        W.C.E = CryptoGames.AES256.aes256Enc →
        W.C.D = CryptoGames.AES256.aes256Dec →
        W.C.X = CryptoGames.RFC7748.x25519Ref →
        W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
        W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
        W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
        W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
        W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
        ∀ (i : Inputs), CliPqxdhInputs ⟨W.C, W.Q⟩ i →
          CliReachesSampleNttStuckPlainPanPlaced mpl mmpl cliElfImage W i →
          cliRunPlainPanPlacedSig mpl mmpl cliElfImage W i = none :=
  fun mpl mmpl hLs hMm W hF hE hD hX hPub hF512 hEnc hDec hK i hi hStuck =>
    cliRunPlacedSig_eq_none_of_v2F3StuckDomain_cliElfK
      hG mpl mmpl hLs hMm W hF hE hD hX hPub hF512 hEnc hDec hK i (Or.inl hi) hStuck

/-- `CliPqxdhInputs` specialization (`Or.inl`) of
    `not_cliReachesOOMPlaced_of_v2F3StuckDomain_cliElfK` for `ElfNoOomPlacedInstK`. -/
theorem not_cliReachesOOMPlaced_of_cliPqxdhInputs_cliElfK
    (hG : H2KGhostArmsType) :
    ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      mallocngLib.LinkedAt cliElfBytes mmpl →
      ∀ (W : CliHooks),
        W.C.F = sha256Compress →
        W.C.E = CryptoGames.AES256.aes256Enc →
        W.C.D = CryptoGames.AES256.aes256Dec →
        W.C.X = CryptoGames.RFC7748.x25519Ref →
        W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
        W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
        W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
        W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
        W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
        ∀ (i : Inputs), CliPqxdhInputs ⟨W.C, W.Q⟩ i →
          CliReachesSampleNttStuckPlainPanPlaced mpl mmpl cliElfImage W i →
          ¬ CliReachesOOMPlainPanPlaced mpl mmpl cliElfImage W i :=
  fun mpl mmpl hLs hMm W hF hE hD hX hPub hF512 hEnc hDec hK i hi hStuck =>
    not_cliReachesOOMPlaced_of_v2F3StuckDomain_cliElfK
      hG mpl mmpl hLs hMm W hF hE hD hX hPub hF512 hEnc hDec hK i (Or.inl hi) hStuck

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDiverge
