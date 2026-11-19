/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Phase4GhostHooks -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4GhostHooks -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2EntryGuard -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress256 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress512 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Time -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.X25519 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Compress512GhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTightCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTightCrypto -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTightDalek -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTightRows -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTightSentinel -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen -- proof-setup: allow-public-import

/-!
# `c2ExtraTightTable` & Unified 23-Row `SampleNTT` Non-Visitation Dispatcher (`ElfSampleNttStuckDivergeExtraTight`)

Packages the 23 tight-keep / sentinel-`lr` `ExtraGhostTable` rows into
`c2ExtraTightTable` (`c2ExtraTightSyms`, `isExtraTightSym`) and proves the unified
`extraTight_nonSnttAvoidS5` (plus `extraTight_nonSnttAvoidS5_of_subtable`) dispatcher
discharging `StepsStrictAvoid` against `mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl)`
for `H2KSnttExtraFacts.nonSnttAvoidS5`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTight

open Arm64
open Arm64.Obj (MultiPlacement)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliExternsPlaced libsignalSessionLib
   lsBlackBoxSym lsCompress256Sym lsCompressSym lsDiffieHellmanSym lsDsmbSym
   lsDurationSinceSym lsEdNegSym lsFromUtf8Sym lsMemrchrSym lsMlkemPk1Sym lsMlkemPk2Sym
   lsPubFromSecretSym lsScalarModSym lsScalarWideSym lsSharedSecretDropSym
   lsStaticSecretDropSym lsTimeAddSym lsToEdwardsSym lsTorsionFreeSym)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks ExtraGhostTable cliExtraGhostSyms cliGhostExternsWithExtra)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.Phase4GhostHooks
  (x25519DiffieHellmanGhost x25519PubFromSecretGhost)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4GhostHooks
  (dalekCompressGhostLs dalekDsmbGhostLs dalekMontToEdGhostLs
   dalekScalarModGhostLs dalekScalarWideGhostLs dalekTorsionFreeGhostLs)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpGhostReplays
  (bcmpEntryGuard bcmpGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxGhostReplays
  (blackBoxEntryGuard blackBoxGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2EntryGuard (c2GuardOf)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress256
  (c2Compress256Pl)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress512
  (c2Compress512Addr c2Compress512K64Addr lsCompress512Sym)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Time (c2TimeMpl)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.X25519 (c2X25519Mpl)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Compress256GhostReplays
  (compress256Ghost)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Compress512GhostReplays
  (compress512Ghost compress512Placement)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DalekHooksDehook
  (c2DalekMpl c2EdNegAddr c2SharedSecretDropSentinelGhost edNegSentinelGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceGhostReplays
  (durationSinceGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.FromUtf8GhostReplays
  (fromUtf8EntryGuard fromUtf8MplGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveExtraReplays
  (memmoveEntryGuard memmoveGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrExtraReplays (memrchrGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemFirstStopTransfer
  (mlkemSampleNttSyms)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.NarrowF3R1Witness
  (f3EmptyMemcpyGhostHookNarrow f3EmptyMemsetGhostHookNarrow)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StaticSecretDropGhostReplays
  (staticSecretDropEntryGuard staticSecretDropGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhostReplays
  (strlenEntryGuard strlenGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TimeAddGhostReplays (timeAddGhost)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeCore
  (StepsStrictAvoid)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTightCrypto
  (compress256_avoidS5 compress512_avoidS5 x25519DiffieHellman_avoidS5 x25519PubFromSecret_avoidS5)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTightDalek
  (dalekCompress_avoidS5 dalekDsmb_avoidS5 dalekScalarMod_avoidS5 dalekScalarWide_avoidS5
   dalekToEdwards_avoidS5 dalekTorsionFree_avoidS5 mlkemPk1_avoidS5 mlkemPk2_avoidS5)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTightRows
  (bcmp_avoidS5 blackBox_avoidS5 durationSince_avoidS5 fromUtf8_avoidS5 memmove_avoidS5
   memrchr_avoidS5 staticSecretDrop_avoidS5 strlen_avoidS5 timeAdd_avoidS5)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTightSentinel
  (edNeg_avoidS5 sharedSecretDrop_avoidS5)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy (mlkemPk1Hook mlkemPk2Hook)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen (c2FromUtf8TableAddr)

/-! ## 1. The 23 Tight-Keep Symbols & `c2ExtraTightTable` -/

/-- Ordered list of the 23 tight-keep / sentinel-`lr` `ExtraGhostTable` symbols. -/
@[expose] def c2ExtraTightSyms : List String :=
  [ "memmove",
    "bcmp",
    "strlen",
    lsMemrchrSym,
    lsFromUtf8Sym,
    lsDurationSinceSym,
    lsTimeAddSym,
    lsBlackBoxSym,
    lsStaticSecretDropSym,
    lsSharedSecretDropSym,
    lsToEdwardsSym,
    lsCompressSym,
    lsEdNegSym,
    lsTorsionFreeSym,
    lsDsmbSym,
    lsScalarModSym,
    lsScalarWideSym,
    lsMlkemPk1Sym,
    lsMlkemPk2Sym,
    lsCompress256Sym,
    lsCompress512Sym,
    lsPubFromSecretSym,
    lsDiffieHellmanSym ]

/-- Membership predicate for the 23 tight-keep `ExtraGhostTable` symbols. -/
@[expose] def isExtraTightSym (sym : String) : Bool :=
  c2ExtraTightSyms.contains sym

/-- Canonical 23-row tight-keep / sentinel-`lr` `ExtraGhostTable` slice at `lsmpl`. -/
@[expose] noncomputable def c2ExtraTightTable [LibsignalPlacement] (mmpl : MultiPlacement) :
    ExtraGhostTable :=
  [ ("memmove", memmoveGhost lsmpl mmpl),
    ("bcmp", bcmpGhost lsmpl mmpl),
    ("strlen", strlenGhost lsmpl mmpl),
    (lsMemrchrSym, memrchrGhost lsmpl mmpl),
    (lsFromUtf8Sym, fromUtf8MplGhost lsmpl mmpl c2FromUtf8TableAddr),
    (lsDurationSinceSym, durationSinceGhost c2TimeMpl),
    (lsTimeAddSym, timeAddGhost c2TimeMpl),
    (lsBlackBoxSym, blackBoxGhost lsmpl mmpl),
    (lsStaticSecretDropSym, staticSecretDropGhost lsmpl mmpl),
    (lsSharedSecretDropSym, c2SharedSecretDropSentinelGhost),
    (lsToEdwardsSym, dalekMontToEdGhostLs c2DalekMpl),
    (lsCompressSym, dalekCompressGhostLs c2DalekMpl),
    (lsEdNegSym, edNegSentinelGhost c2EdNegAddr),
    (lsTorsionFreeSym, dalekTorsionFreeGhostLs c2DalekMpl),
    (lsDsmbSym, dalekDsmbGhostLs c2DalekMpl),
    (lsScalarModSym, dalekScalarModGhostLs c2DalekMpl),
    (lsScalarWideSym, dalekScalarWideGhostLs c2DalekMpl),
    (lsMlkemPk1Sym, mlkemPk1Hook),
    (lsMlkemPk2Sym, mlkemPk2Hook),
    (lsCompress256Sym, compress256Ghost c2Compress256Pl),
    (lsCompress512Sym,
      compress512Ghost (compress512Placement c2Compress512Addr c2Compress512K64Addr)),
    (lsPubFromSecretSym, x25519PubFromSecretGhost c2X25519Mpl),
    (lsDiffieHellmanSym, x25519DiffieHellmanGhost c2X25519Mpl) ]

/-! ## 2. Domain, Disjointness, & Table-Composition Helpers -/

theorem c2ExtraTightTable_keys [LibsignalPlacement] (mmpl : MultiPlacement) :
    (c2ExtraTightTable mmpl).map Prod.fst = c2ExtraTightSyms :=
  rfl

set_option maxRecDepth 400000 in
theorem c2ExtraTightSyms_nodup : c2ExtraTightSyms.Nodup := by
  decide

set_option maxRecDepth 400000 in
private theorem c2ExtraTightSyms_all_extra_and_nonSntt :
    (c2ExtraTightSyms.all fun s =>
      cliExtraGhostSyms.contains s && !(mlkemSampleNttSyms.contains s)) = true := by
  decide

theorem isExtraTightSym_imp_cliExtraGhostSyms {sym : String}
    (h : isExtraTightSym sym = true) :
    cliExtraGhostSyms.contains sym = true := by
  have hall := List.all_eq_true.mp c2ExtraTightSyms_all_extra_and_nonSntt sym
    (List.contains_iff_mem.mp h)
  simp only [Bool.and_eq_true] at hall
  exact hall.1

theorem isExtraTightSym_imp_not_sntt {sym : String}
    (h : isExtraTightSym sym = true) :
    mlkemSampleNttSyms.contains sym = false := by
  have hall := List.all_eq_true.mp c2ExtraTightSyms_all_extra_and_nonSntt sym
    (List.contains_iff_mem.mp h)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hall
  exact hall.2

private theorem lookup_isSome_eq_map_fst_contains {α : Type} (sym : String) :
    ∀ t : List (String × α), (t.lookup sym).isSome = (t.map Prod.fst).contains sym
  | [] => rfl
  | (k, _) :: rest => by
    simp only [List.lookup, List.map_cons, List.contains_cons]
    cases sym == k
    · exact lookup_isSome_eq_map_fst_contains sym rest
    · rfl

theorem c2ExtraTightTable_lookup_isSome [LibsignalPlacement] (mmpl : MultiPlacement)
    (sym : String) :
    ((c2ExtraTightTable mmpl).lookup sym).isSome = isExtraTightSym sym :=
  lookup_isSome_eq_map_fst_contains sym (c2ExtraTightTable mmpl)

private theorem lookup_append_of_isSome {α : Type} {sym : String} {t₁ t₂ : List (String × α)}
    (h : (t₁.lookup sym).isSome = true) :
    (t₁ ++ t₂).lookup sym = t₁.lookup sym := by
  induction t₁ with
  | nil => cases h
  | cons kv rest ih =>
    rcases kv with ⟨k, v⟩
    simp only [List.cons_append, List.lookup] at h ⊢
    cases hsk : sym == k
    · rw [hsk] at h
      exact ih h
    · rfl

private theorem lookup_append_of_isNone {α : Type} {sym : String} {t₁ t₂ : List (String × α)}
    (h : (t₁.lookup sym).isSome = false) :
    (t₁ ++ t₂).lookup sym = t₂.lookup sym := by
  induction t₁ with
  | nil => rfl
  | cons kv rest ih =>
    rcases kv with ⟨k, v⟩
    simp only [List.cons_append, List.lookup] at h ⊢
    cases hsk : sym == k
    · rw [hsk] at h
      exact ih h
    · rw [hsk] at h
      cases h

theorem c2ExtraTightTable_lookup_append_of_true [LibsignalPlacement]
    (mmpl : MultiPlacement) (rest : ExtraGhostTable) {sym : String}
    (h : isExtraTightSym sym = true) :
    (c2ExtraTightTable mmpl ++ rest).lookup sym = (c2ExtraTightTable mmpl).lookup sym :=
  lookup_append_of_isSome ((c2ExtraTightTable_lookup_isSome mmpl sym).trans h)

theorem c2ExtraTightTable_lookup_append_of_false [LibsignalPlacement]
    (mmpl : MultiPlacement) (rest : ExtraGhostTable) {sym : String}
    (h : isExtraTightSym sym = false) :
    (c2ExtraTightTable mmpl ++ rest).lookup sym = rest.lookup sym :=
  lookup_append_of_isNone ((c2ExtraTightTable_lookup_isSome mmpl sym).trans h)

/-! ## 3. `c2GuardOf` Per-Arm Projections & `List.lookup` Inversion -/

private theorem of_ite_true {c : Bool} {P Q : Prop} (hc : c = true) (h : if c then P else Q) :
    P := by
  rw [hc] at h
  simpa only [↓reduceIte] using h

private theorem of_ite_false {c : Bool} {P Q : Prop} (hc : c = false) (h : if c then P else Q) :
    Q := by
  rw [hc] at h
  simpa only [Bool.false_eq_true, ↓reduceIte] using h

private theorem c2GuardOf_memmove (mpl : MultiPlacement) (s0 : State)
    (h : c2GuardOf mpl "memmove" s0) : memmoveEntryGuard mpl s0 := by
  unfold c2GuardOf at h
  exact of_ite_true (by decide) h

private theorem c2GuardOf_bcmp (mpl : MultiPlacement) (s0 : State)
    (h : c2GuardOf mpl "bcmp" s0) : bcmpEntryGuard mpl s0 := by
  unfold c2GuardOf at h
  exact of_ite_true (by decide) (of_ite_false (by decide) h)

private theorem c2GuardOf_strlen (mpl : MultiPlacement) (s0 : State)
    (h : c2GuardOf mpl "strlen" s0) : strlenEntryGuard mpl s0 := by
  unfold c2GuardOf at h
  exact of_ite_true (by decide)
    (of_ite_false (by decide) (of_ite_false (by decide) h))

private theorem c2GuardOf_fromUtf8 (mpl : MultiPlacement) (s0 : State)
    (h : c2GuardOf mpl lsFromUtf8Sym s0) : fromUtf8EntryGuard mpl s0 := by
  unfold c2GuardOf at h
  exact of_ite_true (by decide)
    (of_ite_false (by decide) (of_ite_false (by decide)
      (of_ite_false (by decide) (of_ite_false (by decide) h))))

private theorem c2GuardOf_blackBox (mpl : MultiPlacement) (s0 : State)
    (h : c2GuardOf mpl lsBlackBoxSym s0) : blackBoxEntryGuard mpl s0 := by
  unfold c2GuardOf at h
  exact of_ite_true (by decide)
    (of_ite_false (by decide) (of_ite_false (by decide)
      (of_ite_false (by decide) (of_ite_false (by decide)
        (of_ite_false (by decide) (of_ite_false (by decide)
          (of_ite_false (by decide) h)))))))

private theorem c2GuardOf_staticSecretDrop (mpl : MultiPlacement) (s0 : State)
    (h : c2GuardOf mpl lsStaticSecretDropSym s0) : staticSecretDropEntryGuard mpl s0 := by
  unfold c2GuardOf at h
  exact of_ite_true (by decide)
    (of_ite_false (by decide) (of_ite_false (by decide)
      (of_ite_false (by decide) (of_ite_false (by decide)
        (of_ite_false (by decide) (of_ite_false (by decide)
          (of_ite_false (by decide) (of_ite_false (by decide) h))))))))

private theorem lookup_cons_some {α : Type} {s k : String} {v f : α} {rest : List (String × α)}
    (h : List.lookup s ((k, v) :: rest) = some f) :
    (s = k ∧ f = v) ∨ List.lookup s rest = some f := by
  unfold List.lookup at h
  cases hsk : (s == k)
  · rw [hsk] at h
    exact Or.inr h
  · rw [hsk] at h
    exact Or.inl ⟨beq_iff_eq.mp hsk, (Option.some.inj h).symm⟩

/-! ## 4. Unified 23-Row `StepsStrictAvoid` Dispatcher -/

/-- Unified `StepsStrictAvoid` dispatcher across all 23 rows of `c2ExtraTightTable`, matching
    `H2KSnttExtraFacts.nonSnttAvoidS5` at `mpl := lsmpl`. -/
theorem extraTight_nonSnttAvoidS5 [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {ghFixed : CliGhostHooks} {extra : ExtraGhostTable}
    (hGMemcpy : ghFixed.memcpy = none ∨ ghFixed.memcpy = some (f3EmptyMemcpyGhostHookNarrow mmpl))
    (hGMemset : ghFixed.memset = none ∨ ghFixed.memset = some (f3EmptyMemsetGhostHookNarrow mmpl))
    (W : CliHooks) (s0 sf : State) (sym : String) (f : State → State)
    (hGuard : c2GuardOf lsmpl sym s0)
    (hRetPc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hNoExSf : ∀ msg, sf.status ≠ .Exception msg)
    (hNotHaltSf : sf.status ≠ .Halted)
    (hTight : isExtraTightSym sym = true)
    (hLookTbl : (c2ExtraTightTable mmpl).lookup sym = some f)
    (hLookExtra : extra.lookup sym = some f)
    (u : State)
    (hStepsBefore :
      Steps
        (cliProgExtPlacedAt lsmpl
          (fun W' => cliGhostExternsWithExtra ghFixed extra (cliExternsPlaced mmpl W')) 617 W)
        s0 u)
    (hStepsAfter :
      Steps
        (cliProgExtPlacedAt lsmpl
          (fun W' => cliGhostExternsWithExtra ghFixed extra (cliExternsPlaced mmpl W')) 617 W)
        (f u) sf)
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl sym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (f u).status ≠ .Exception msg)
    (hkf : u.mem.KeepsFrozen (f u).mem)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u (f u) := by
  have _ := hTight
  have _ := hStepsBefore
  dsimp only [c2ExtraTightTable] at hLookTbl
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact memmove_avoidS5 hLs hGMemcpy hGMemset hLookExtra W
      (c2GuardOf_memmove lsmpl s0 hGuard) hRetPc hNoExSf hNotHaltSf hStepsAfter
      hpc hrun hnoex hkf hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact bcmp_avoidS5 hLs hLookExtra W
      (c2GuardOf_bcmp lsmpl s0 hGuard) hRetPc hNoExSf hNotHaltSf hStepsAfter
      hpc hrun hnoex hkf hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact strlen_avoidS5 hLs hLookExtra W
      (c2GuardOf_strlen lsmpl s0 hGuard) hRetPc hNoExSf hNotHaltSf hStepsAfter
      hpc hrun hnoex hkf hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact memrchr_avoidS5 hLs W hpc hrun hnoex hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact fromUtf8_avoidS5 hLs hLookExtra W
      (c2GuardOf_fromUtf8 lsmpl s0 hGuard) hRetPc hNoExSf hNotHaltSf hStepsAfter
      hpc hrun hnoex hkf hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact durationSince_avoidS5 hLs W hpc hnoex hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact timeAdd_avoidS5 hLs W hpc hrun hnoex hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact blackBox_avoidS5 hLs hLookExtra W
      (c2GuardOf_blackBox lsmpl s0 hGuard) hRetPc hNoExSf hNotHaltSf hStepsAfter
      hpc hrun hnoex hkf hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact staticSecretDrop_avoidS5 hLs hLookExtra W
      (c2GuardOf_staticSecretDrop lsmpl s0 hGuard) hRetPc hNoExSf hNotHaltSf hStepsAfter
      hpc hrun hnoex hkf hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact sharedSecretDrop_avoidS5 hLs W hpc hrun hnoex hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact dalekToEdwards_avoidS5 hLs W hpc hnoex hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact dalekCompress_avoidS5 hLs W hpc hnoex hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact edNeg_avoidS5 hLs W hpc hrun hnoex hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact dalekTorsionFree_avoidS5 hLs W hpc hnoex hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact dalekDsmb_avoidS5 hLs W hpc hnoex hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact dalekScalarMod_avoidS5 hLs W hpc hnoex hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact dalekScalarWide_avoidS5 hLs W hpc hnoex hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact mlkemPk1_avoidS5 hLs W hpc hrun hnoex hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact mlkemPk2_avoidS5 hLs W hpc hrun hnoex hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact compress256_avoidS5 hLs W hpc hrun hnoex hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact compress512_avoidS5 hLs W hpc hrun hnoex hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact x25519PubFromSecret_avoidS5 hLs W hpc hrun hnoex hfr hinv
  rcases lookup_cons_some hLookTbl with ⟨rfl, rfl⟩ | hLookTbl
  · exact x25519DiffieHellman_avoidS5 hLs W hpc hrun hnoex hfr hinv
  cases hLookTbl

/-- Subtable wrapper around `extraTight_nonSnttAvoidS5` for any composite `extra : ExtraGhostTable`
    that agrees with `c2ExtraTightTable mmpl` on `isExtraTightSym`. -/
theorem extraTight_nonSnttAvoidS5_of_subtable [LibsignalPlacement] {mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {ghFixed : CliGhostHooks} {extra : ExtraGhostTable}
    (hSub : ∀ s : String, isExtraTightSym s = true →
      extra.lookup s = (c2ExtraTightTable mmpl).lookup s)
    (hGMemcpy : ghFixed.memcpy = none ∨ ghFixed.memcpy = some (f3EmptyMemcpyGhostHookNarrow mmpl))
    (hGMemset : ghFixed.memset = none ∨ ghFixed.memset = some (f3EmptyMemsetGhostHookNarrow mmpl))
    (W : CliHooks) (s0 sf : State) (sym : String) (f : State → State)
    (hGuard : c2GuardOf lsmpl sym s0)
    (hRetPc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hNoExSf : ∀ msg, sf.status ≠ .Exception msg)
    (hNotHaltSf : sf.status ≠ .Halted)
    (hTight : isExtraTightSym sym = true)
    (hLookExtra : extra.lookup sym = some f)
    (u : State)
    (hStepsBefore :
      Steps
        (cliProgExtPlacedAt lsmpl
          (fun W' => cliGhostExternsWithExtra ghFixed extra (cliExternsPlaced mmpl W')) 617 W)
        s0 u)
    (hStepsAfter :
      Steps
        (cliProgExtPlacedAt lsmpl
          (fun W' => cliGhostExternsWithExtra ghFixed extra (cliExternsPlaced mmpl W')) 617 W)
        (f u) sf)
    (hpc : u.pc = libsignalSessionLib.resolve lsmpl sym)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg, (f u).status ≠ .Exception msg)
    (hkf : u.mem.KeepsFrozen (f u).mem)
    (hfr : ExecFrozen u.mem)
    (hinv : F3CodeInv lsmpl mmpl u.mem) :
    StepsStrictAvoid
      (fun z => z.pc ∈ mlkemSampleNttSyms.map (libsignalSessionLib.resolve lsmpl))
      (cliProgExtPlacedAt lsmpl (cliExternsPlaced mmpl) 617 W)
      u (f u) :=
  extraTight_nonSnttAvoidS5 hLs hGMemcpy hGMemset W s0 sf sym f hGuard hRetPc hNoExSf hNotHaltSf
    hTight ((hSub sym hTight).symm.trans hLookExtra) hLookExtra u hStepsBefore hStepsAfter
    hpc hrun hnoex hkf hfr hinv

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDivergeExtraTight
