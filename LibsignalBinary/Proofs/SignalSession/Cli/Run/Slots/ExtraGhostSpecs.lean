/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEq -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.HooksE.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Libc.Memmove -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Libc.Strlen -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHookPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.AesDecRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.AesEncRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.BcmpRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.BlackBoxRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.Compress256RowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.Compress512RowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoDalekRowSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoX25519RowSpecsBase -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.DurationSinceRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.FmtWriteRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.FormatInnerRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.FromUtf8RowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.LibcruxHmacRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.MemmoveRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.MemrchrRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.SharedSecretDropRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.SpqrOnceCallRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.StaticSecretDropRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.StrlenRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.TimeAddRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.WriteFileRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.WriteStdoutRowSpec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalPublicApi -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpecLemmas.RoLiterals

/-!
# Generic `extra` Ghost Table Consumer Contracts (`Cli.Run.Slots.ExtraGhostSpecs`)

Consumer-contract (`HookOk` / `HookSat` / `VmPreserved` / `withAlloc` / `HookFsTraced`) layer for
`CliGhostHooks.extra : List (String × (State → State))`:

1. Symbol partition and key freshness (`cliNamedGhostSyms`, `cliExtraGhostSyms`,
   `FreshExtraKeysList`): partitions the 10 named ghost slots (allocator, `String::clone`,
   `read_file`, `read_stdin`, `memset`, `memcpy`) from the 38 `cliExtraGhostSyms` symbols, with
   kernel-decidable disjointness (`cliExtraGhostSyms_disjoint_named`).
2. Domain-guarded `extra` dispatch (`cliGhostExternsWithExtra`): checks the 10 named slots first,
   then dispatches `extra.lookup sym` only when `cliExtraGhostSyms.contains sym = true`. Symbols
   outside both lists pass through to `baseExt sym` unconditionally (`by left; decide`).
   `cliGhostExterns g baseExt sym` equals `cliGhostExternsWithExtra g g.extra baseExt sym`.
3. Per-row consumer `HookOk` table (`ExtraRowSpec`, `GhostRowSpecOk`, `WriteFileRowOk`,
   `ExtraRowOk`, `ExtraListSpecOk`, `ExtraSpecOk`): imports the row-owned `ExtraRowSpecs.*RowSpec`
   modules and bundles `FreshExtraKeysList` with per-row obligations into `ExtraSpecOk g` for
   `CliGhostA0Hooks`, `CliGhostAllocHooks`, and `CliGhostSpqrAllocHooks`.
-/

set_option autoImplicit false
set_option maxRecDepth 200000

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (PEParams PqxdhPrims UnreachedPqxdhPrimitives modelPrims u8Vec vecU8)
open CryptoVerification.E2E.HooksE (bcmpVregsSpec e2eBcmpSpec hookOk_bcmpSpec_of_vregs)
open CryptoVerification.E2E.Pqxdh.Shared
  (compressInPlaceStubSpecPlaced cryptoLeafStubSpec sha512CompressOutBytes)
open CryptoVerification.LibsignalPublicApi.StoreKit (extract_withLsRoCl withLsRoCl)
open CryptoVerification.LibsignalSpqrV1
  (MlKem mlkemDecapsSpec mlkemEncaps1Spec mlkemEncaps2Spec mlkemFromSeedSpec mlkemPk1Spec
   mlkemPk2Spec mlkemValidatePkSpec sha256Compress)
open CryptoVerification.LibsignalTripleRatchet
  (blackBoxSpec compress256Spec derivePublicKeyBytesStackSpec diffieHellmanSpec extHookStack
   pubFromSecretSpec withStack zeroizeSecretSpec)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SignalSession
  (lsAesDecSym lsAesEncSym lsBlackBoxSym lsCompress256Sym lsCompress512Sym lsCompressSym
   lsDiffieHellmanSym lsDsmbSym lsDurationSinceSym lsEdNegSym lsFmtWriteSym lsFormatInnerSym
   lsFromUtf8Sym lsKemDecapsSym lsKemEncapsSym lsLibcruxHmacSym lsMemcpySym lsMemrchrSym
   lsMemsetSym lsMlkemDecapsSym lsMlkemEncaps1Sym lsMlkemEncaps2Sym lsMlkemFromSeedSym
   lsMlkemPk1Sym lsMlkemPk2Sym lsMlkemValidatePkSym lsPubFromSecretSym lsReadFileSym
   lsReadStdinSym lsRustAllocSymCli lsRustAllocZeroedSymCli lsRustDeallocSymCli
   lsRustNoAllocShimSymCli lsRustReallocSymCli lsScalarModSym lsScalarWideSym
   lsSharedSecretDropSym lsSpqrOnceCallSym lsStaticSecretDropSym lsStringCloneSym lsTimeAddSym
   lsToEdwardsSym lsTorsionFreeSym lsWriteFileSym lsWriteStdoutSym)
open CryptoVerification.SignalSession.Cli (cliBcmpSpec)
open CryptoVerification.SignalSession.CliExt (dhSpec pureByteFunctionSpec)
open CryptoVerification.SignalSession.Cli.MainHops
  (fromUtf8AsciiSpec memrchrSpec strlenSpec)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks ExtraGhostTable IsFsC cliExtraGhostSyms cliExtraGhostSyms_disjoint_named
   cliExtraGhostSyms_not_named cliGhostExterns cliGhostExternsNamed cliGhostExternsWithExtra
   cliGhostExternsWithExtra_extra_some cliGhostExternsWithExtra_other cliNamedGhostSyms
   named_eq_false_of_extra_contains)
open CryptoVerification.SignalSession.Cli.Slots
  (durationSinceEpochAllocSpec durationSinceEpochAtSpec)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget
  (durationSinceEpochBudgetSpec timeAddBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridgesBase
  (kemDecapsAtSpec kemEncapsAtSpec kemEncapsPreservedAtSpec mlkemDecapsAtSpec mlkemEncaps1AtSpec
   mlkemEncaps2AtSpec mlkemFromSeedAtSpec mlkemValidatePkAtSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.MlKemCorrectProofs
  (kyber1024DecapsVec kyber1024EncapsVec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (mlkem768Incremental)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512 (compress512StackedMasterSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Ref (sha512CompressState)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref
  (x25519PubFromSecretRef x25519Ref)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.ConsumerBridges (dalekEdNegVec)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.DalekPureFallbacks (dalekHookStack)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4Block202
  (dalekMontToEdExtSpec dalekTorsionFreeExtSpec)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4Block204
  (dalekCompressExtSpec dalekDsmbExtSpec dalekEdNegExtSpec dalekScalarModExtSpec
   dalekScalarWideExtSpec edwardsPointNegUnstackedSpec)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.Libc.Memmove
  (libcMemmoveBoundedSpec sessionMemmoveBoundedBudgetSpec sessionMemmoveBoundedSpec)
open LibsignalBinary.Proofs.HookDischarge.Libc.Strlen (withStrlenPadRO)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.EdNegCode (masterEdNegSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc (withAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO
  (fromUtf8AsciiSpecRO memrchrSpecRO strlenSpecRO)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.AesDecRowSpec (AesDecRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.AesEncRowSpec (AesEncRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.BcmpRowSpec (BcmpRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.BlackBoxRowSpec
  (BlackBoxRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.Compress256RowSpec
  (Compress256RowSpec compress256RowSingleSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.Compress512RowSpec
  (Compress512RowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoDalekRowSpecs
  (DalekCompressRowSpec DalekDsmbRowSpec DalekLsRowTuple DalekMontToEdRowSpec DalekScalarModRowSpec
   DalekScalarWideRowSpec DalekTorsionFreeRowSpec EdNegRowSpec MlkemPk1RowSpec MlkemPk2RowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs
  (KemDecapsRowSpec KemDecapsRowSpecAt KemEncapsRowSpec KemEncapsRowSpecAt MlkemDecapsRowSpec
   MlkemDecapsRowSpecAt MlkemEncaps1RowSpec MlkemEncaps1RowSpecAt MlkemEncaps2RowSpec
   MlkemEncaps2RowSpecAt MlkemFromSeedRowSpec MlkemFromSeedRowSpecAt MlkemValidatePkRowSpec
   MlkemValidatePkRowSpecAt kemDecapsTightStack kemEncapsTightStack mlkemDecapsTightStack
   mlkemEncaps1TightStack mlkemEncaps2TightStack mlkemFromSeedTightStack mlkemHookStack
   mlkemValidatePkTightStack)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoX25519RowSpecsBase
  (X25519DiffieHellmanRowSpec X25519PubFromSecretRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.SpqrOnceCallRowSpec
  (SpqrOnceCallRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.DurationSinceRowSpec
  (DurationSinceRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.FmtWriteRowSpec
  (FmtWriteRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.FormatInnerRowSpec
  (FormatInnerRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.FromUtf8RowSpec
  (FromUtf8RowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.LibcruxHmacRowSpec
  (LibcruxHmacRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.MemmoveRowSpec
  (MemmoveRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.MemrchrRowSpec
  (MemrchrRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.SharedSecretDropRowSpec
  (SharedSecretDropRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.StaticSecretDropRowSpec
  (StaticSecretDropRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.StrlenRowSpec (StrlenRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.TimeAddRowSpec
  (TimeAddRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.WriteFileRowSpec
  (WriteFileRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.WriteStdoutRowSpec
  (WriteStdoutRowSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (derivePublicKeyBytesStackBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
  (HookOkCompress256 HookSatCompress256)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionCompress256ROBudgetSpec)

export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.AesDecRowSpec
  (AesDecRowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.AesEncRowSpec
  (AesEncRowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.BcmpRowSpec (BcmpRowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.BlackBoxRowSpec
  (BlackBoxRowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.Compress256RowSpec
  (Compress256RowSpec compress256RowSingleSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.Compress512RowSpec
  (Compress512RowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoDalekRowSpecs
  (DalekCompressRowSpec DalekDsmbRowSpec DalekLsRowTuple DalekMontToEdRowSpec DalekScalarModRowSpec
   DalekScalarWideRowSpec DalekTorsionFreeRowSpec EdNegRowSpec MlkemPk1RowSpec MlkemPk2RowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs
  (KemDecapsRowSpec KemDecapsRowSpecAt KemEncapsRowSpec KemEncapsRowSpecAt MlkemDecapsRowSpec
   MlkemDecapsRowSpecAt MlkemEncaps1RowSpec MlkemEncaps1RowSpecAt MlkemEncaps2RowSpec
   MlkemEncaps2RowSpecAt MlkemFromSeedRowSpec MlkemFromSeedRowSpecAt MlkemValidatePkRowSpec
   MlkemValidatePkRowSpecAt kemDecapsTightStack kemEncapsTightStack mlkemDecapsTightStack
   mlkemEncaps1TightStack mlkemEncaps2TightStack mlkemFromSeedTightStack mlkemHookStack
   mlkemValidatePkTightStack)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoX25519RowSpecsBase
  (X25519DiffieHellmanRowSpec X25519PubFromSecretRowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.SpqrOnceCallRowSpec
  (SpqrOnceCallRowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.DurationSinceRowSpec
  (DurationSinceRowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.FmtWriteRowSpec
  (FmtWriteRowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.FormatInnerRowSpec
  (FormatInnerRowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.FromUtf8RowSpec
  (FromUtf8RowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.LibcruxHmacRowSpec
  (LibcruxHmacRowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.MemmoveRowSpec
  (MemmoveRowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.MemrchrRowSpec
  (MemrchrRowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.SharedSecretDropRowSpec
  (SharedSecretDropRowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.StaticSecretDropRowSpec
  (StaticSecretDropRowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.StrlenRowSpec (StrlenRowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.TimeAddRowSpec
  (TimeAddRowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.WriteFileRowSpec
  (WriteFileRowSpec)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.WriteStdoutRowSpec
  (WriteStdoutRowSpec)

attribute [local irreducible] x25519PubFromSecretRef x25519Ref

/-! ## 1. Named vs. Extra Ghost Symbol Lists & Key Freshness -/

export CryptoVerification.SignalSession.Cli.RunGlue
  (ExtraGhostTable cliNamedGhostSyms cliExtraGhostSyms cliExtraGhostSyms_disjoint_named
   cliExtraGhostSyms_not_named)
export CryptoVerification.SignalSession.Cli.RunGlue
  (named_eq_false_of_extra_contains cliGhostExternsNamed cliGhostExternsWithExtra
   cliGhostExternsWithExtra_extra_some cliGhostExternsWithExtra_other)

/-- At `extra = []`, `cliGhostExternsWithExtra` collapses to the 10-way `cliGhostExternsNamed`
    (using `named_eq_false_of_extra_contains` on the `cliExtraGhostSyms.contains sym = true` branch,
    where `[].lookup sym = none` falls back to `b sym`). -/
theorem cliGhostExternsWithExtra_nil (gh : CliGhostHooks)
    (b : String → Option (State → State)) :
    cliGhostExternsWithExtra gh [] b = cliGhostExternsNamed gh b := by
  funext sym
  unfold cliGhostExternsWithExtra cliGhostExternsNamed
  cases hc : cliExtraGhostSyms.contains sym with
  | false => simp only [Bool.false_eq_true, ↓reduceIte]
  | true =>
    rcases named_eq_false_of_extra_contains hc with
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    simp only [List.lookup, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, Bool.false_eq_true, ↓reduceIte]

/-- Key-only projection that never inspects (potentially `noncomputable`) `State → State` values. -/
@[expose] def cliGhostExtraKeys {V : Type} : List (String × V) → List String
  | [] => []
  | (k, _) :: tl => k :: cliGhostExtraKeys tl

@[simp] theorem cliGhostExtraKeys_eq_map_fst {V : Type} (l : List (String × V)) :
    cliGhostExtraKeys l = l.map Prod.fst := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp [cliGhostExtraKeys, ih]

/-- Kernel-`rfl`-reducible key freshness check: keys are pairwise distinct (`Nodup`), drawn from
    `cliExtraGhostSyms`, and disjoint from `cliNamedGhostSyms`. -/
@[expose] def freshExtraKeysListB {V : Type} (extra : List (String × V)) : Bool :=
  let ks := cliGhostExtraKeys extra
  ks.Pairwise (· != ·) &&
    ks.all (fun k => cliExtraGhostSyms.contains k && !(cliNamedGhostSyms.contains k))

/-- Propositional key freshness side condition (`Nodup` + inside `cliExtraGhostSyms` + disjoint
    from `cliNamedGhostSyms`). Decidable even when paired `State → State` values are noncomputable. -/
abbrev FreshExtraKeysList {V : Type} (extra : List (String × V)) : Prop :=
  (extra.map Prod.fst).Nodup ∧
    ∀ k ∈ extra.map Prod.fst, k ∈ cliExtraGhostSyms ∧ k ∉ cliNamedGhostSyms

abbrev FreshExtraKeys (g : CliGhostHooks) : Prop :=
  FreshExtraKeysList g.extra

theorem FreshExtraKeysList.nil {V : Type} : FreshExtraKeysList ([] : List (String × V)) :=
  ⟨List.nodup_nil, fun _ h => nomatch h⟩

/-- Key-completeness predicate: every symbol in `cliExtraGhostSyms` is bound in `extra`.
    Uses `extra.map Prod.fst` so `by decide` closes concrete tables without inspecting
    noncomputable `State → State` functions. -/
abbrev CompleteExtraKeysList {V : Type} (extra : List (String × V)) : Prop :=
  ∀ sym ∈ cliExtraGhostSyms, sym ∈ extra.map Prod.fst

private theorem lookup_isSome_of_mem_map_fst {V : Type} {l : List (String × V)} {sym : String}
    (hmem : sym ∈ l.map Prod.fst) :
    (l.lookup sym).isSome = true := by
  induction l with
  | nil => cases hmem
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    by_cases hsk : sym = k
    · subst hsk
      simp [List.lookup]
    · simp only [List.map_cons, List.mem_cons] at hmem
      rcases hmem with hsk' | htl
      · exact absurd hsk' hsk
      · have hbeq : (sym == k) = false := beq_eq_false_iff_ne.mpr hsk
        simp [List.lookup, hbeq, ih htl]

/-- Extract `(extra.lookup sym).isSome = true` from `CompleteExtraKeysList extra` and
    `cliExtraGhostSyms.contains sym = true`. -/
theorem CompleteExtraKeysList.lookup_isSome {V : Type} {extra : List (String × V)}
    (hComp : CompleteExtraKeysList extra) {sym : String}
    (hDom : cliExtraGhostSyms.contains sym = true) :
    (extra.lookup sym).isSome = true :=
  lookup_isSome_of_mem_map_fst (hComp sym (List.contains_iff_mem.mp hDom))

/-! ## 3. `ExtraRowSpec`, `GhostRowSpecOk`, `ExtraListSpecOk` & `ExtraSpecOk` -/

/-- Row-specific `HookOk` dispatcher routing each symbol in `cliExtraGhostSyms` to its
    row-owned `*RowSpec` leaf predicate. -/
@[expose] def ExtraRowSpec [LibsignalPlacement] (sym : String) (f : State → State) : Prop :=
  if sym == "bcmp" then BcmpRowSpec f
  else if sym == "strlen" then StrlenRowSpec f
  else if sym == "memmove" then MemmoveRowSpec f
  else if sym == lsFromUtf8Sym then FromUtf8RowSpec f
  else if sym == lsMemrchrSym then MemrchrRowSpec f
  else if sym == lsDurationSinceSym then DurationSinceRowSpec f
  else if sym == lsTimeAddSym then TimeAddRowSpec f
  else if sym == lsBlackBoxSym then BlackBoxRowSpec f
  else if sym == lsStaticSecretDropSym then StaticSecretDropRowSpec f
  else if sym == lsSharedSecretDropSym then SharedSecretDropRowSpec f
  else if sym == lsToEdwardsSym then DalekMontToEdRowSpec f
  else if sym == lsCompressSym then DalekCompressRowSpec f
  else if sym == lsEdNegSym then EdNegRowSpec f
  else if sym == lsTorsionFreeSym then DalekTorsionFreeRowSpec f
  else if sym == lsDsmbSym then DalekDsmbRowSpec f
  else if sym == lsScalarModSym then DalekScalarModRowSpec f
  else if sym == lsScalarWideSym then DalekScalarWideRowSpec f
  else if sym == lsMlkemPk1Sym then MlkemPk1RowSpec f
  else if sym == lsMlkemPk2Sym then MlkemPk2RowSpec f
  else if sym == lsCompress256Sym then Compress256RowSpec f
  else if sym == lsLibcruxHmacSym then LibcruxHmacRowSpec f
  else if sym == lsAesEncSym then AesEncRowSpec f
  else if sym == lsAesDecSym then AesDecRowSpec f
  else if sym == lsCompress512Sym then Compress512RowSpec f
  else if sym == lsKemEncapsSym then KemEncapsRowSpecAt kemEncapsTightStack f
  else if sym == lsKemDecapsSym then KemDecapsRowSpecAt kemDecapsTightStack f
  else if sym == lsMlkemFromSeedSym then MlkemFromSeedRowSpecAt mlkemFromSeedTightStack f
  else if sym == lsMlkemEncaps1Sym then MlkemEncaps1RowSpecAt mlkemEncaps1TightStack f
  else if sym == lsMlkemEncaps2Sym then MlkemEncaps2RowSpecAt mlkemEncaps2TightStack f
  else if sym == lsMlkemDecapsSym then MlkemDecapsRowSpecAt mlkemDecapsTightStack f
  else if sym == lsMlkemValidatePkSym then MlkemValidatePkRowSpecAt mlkemValidatePkTightStack f
  else if sym == lsWriteFileSym then WriteFileRowSpec f
  else if sym == lsWriteStdoutSym then WriteStdoutRowSpec f
  else if sym == lsFmtWriteSym then FmtWriteRowSpec f
  else if sym == lsFormatInnerSym then FormatInnerRowSpec f
  else if sym == lsPubFromSecretSym then X25519PubFromSecretRowSpec f
  else if sym == lsDiffieHellmanSym then X25519DiffieHellmanRowSpec f
  else if sym == lsSpqrOnceCallSym then SpqrOnceCallRowSpec f
  else False

/-- Complete consumer-side obligation for an `fs`-preserving ghost hook `(sym, f)`:
    1. `fs_eq` (`(f s).fs = s.fs`),
    2. `fsT` (`HookFsTraced IsFsC f`),
    3. `rowSpec` (`ExtraRowSpec sym f` — covers plain, RO, `withVmPreserved`, and `withAlloc`
       consumer specs; `withLsRoCl` follows generically via `hookOk_withLsRoCl`). -/
structure GhostRowSpecOk [LibsignalPlacement] (sym : String) (f : State → State) : Prop where
  fs_eq   : ∀ s : State, (f s).fs = s.fs
  fsT     : HookFsTraced IsFsC f
  rowSpec : ExtraRowSpec sym f

/-- Consumer-side row obligation for `lsWriteFileSym` (`write_file`), which updates `.fs.files`
    via `cliIo.wr` while satisfying `HookFsTraced IsFsC f` and `WriteFileRowSpec f`. -/
structure WriteFileRowOk (f : State → State) : Prop where
  fsT     : HookFsTraced IsFsC f
  rowSpec : WriteFileRowSpec f := WriteFileRowSpec.intro f

/-- Per-row `ExtraListSpecOk` entry predicate: identical to `GhostRowSpecOk sym f` on all
    `fs`-preserving `cliExtraGhostSyms`, and `WriteFileRowOk f` on `lsWriteFileSym`. -/
structure ExtraRowOk [LibsignalPlacement] (sym : String) (f : State → State) : Prop where
  fs_eq_ne : (sym == lsWriteFileSym) = false → ∀ s : State, (f s).fs = s.fs
  fsT      : HookFsTraced IsFsC f
  rowSpec  : ExtraRowSpec sym f

theorem ExtraRowOk.fs_eq [LibsignalPlacement] {sym : String} {f : State → State}
    (h : ExtraRowOk sym f) (hne : (sym == lsWriteFileSym) = false := by decide) :
    ∀ s : State, (f s).fs = s.fs :=
  h.fs_eq_ne hne

theorem ExtraRowOk.toGhostRowSpecOk [LibsignalPlacement] {sym : String} {f : State → State}
    (h : ExtraRowOk sym f) (hne : (sym == lsWriteFileSym) = false := by decide) :
    GhostRowSpecOk sym f :=
  ⟨h.fs_eq_ne hne, h.fsT, h.rowSpec⟩

theorem GhostRowSpecOk.toExtraRowOk [LibsignalPlacement] {sym : String} {f : State → State}
    (h : GhostRowSpecOk sym f) : ExtraRowOk sym f :=
  ⟨fun _ => h.fs_eq, h.fsT, h.rowSpec⟩

theorem WriteFileRowOk.toExtraRowOk [LibsignalPlacement] {f : State → State}
    (h : WriteFileRowOk f) : ExtraRowOk lsWriteFileSym f where
  fs_eq_ne hne := absurd (by decide : (lsWriteFileSym == lsWriteFileSym) = true)
    (by rw [hne]; decide)
  fsT := h.fsT
  rowSpec := by
    unfold ExtraRowSpec
    repeat rw [ite_eq_right (by decide)]
    rw [ite_eq_left (by decide)]
    exact h.rowSpec

theorem ExtraRowOk.toWriteFileRowOk [LibsignalPlacement] {f : State → State}
    (h : ExtraRowOk lsWriteFileSym f) : WriteFileRowOk f where
  fsT := h.fsT
  rowSpec := by
    have hp := h.rowSpec
    unfold ExtraRowSpec at hp
    repeat rw [ite_eq_right (by decide)] at hp
    rw [ite_eq_left (by decide)] at hp
    exact hp

/-- Bundle predicate over an `extra` table: key freshness plus `ExtraRowOk` for every entry. -/
structure ExtraListSpecOk [LibsignalPlacement] (extra : ExtraGhostTable) : Prop where
  fresh : FreshExtraKeysList extra := by decide
  rowOk : ∀ sym f, extra.lookup sym = some f → ExtraRowOk sym f := by
    intro _ _ h; cases h

theorem ExtraListSpecOk.nil [LibsignalPlacement] : ExtraListSpecOk [] :=
  ⟨FreshExtraKeysList.nil, fun _ _ h => by cases h⟩

theorem ExtraListSpecOk.ghostRowOk [LibsignalPlacement] {extra : ExtraGhostTable}
    (hOk : ExtraListSpecOk extra) (sym : String) (f : State → State)
    (hLook : extra.lookup sym = some f)
    (hne : (sym == lsWriteFileSym) = false := by decide) :
    GhostRowSpecOk sym f :=
  (hOk.rowOk sym f hLook).toGhostRowSpecOk hne

theorem ExtraListSpecOk.fsT [LibsignalPlacement] {extra : ExtraGhostTable}
    (hOk : ExtraListSpecOk extra) :
    ∀ sym f, cliExtraGhostSyms.contains sym = true →
      extra.lookup sym = some f → HookFsTraced IsFsC f :=
  fun sym f _ hLook => (hOk.rowOk sym f hLook).fsT

/-- Complete consumer spec bundle over a populated `extra` table
    (`ExtraListSpecOk` + `CompleteExtraKeysList`). -/
structure ExtraFullListSpecOk [LibsignalPlacement] (extra : ExtraGhostTable) : Prop
    extends ExtraListSpecOk extra where
  complete : CompleteExtraKeysList extra := by decide

/-- Bundle field predicate (`extraOk : ExtraSpecOk g`) on `CliGhostHooks`: guarantees key
    freshness, `ExtraRowOk` on every row, and completeness across all `cliExtraGhostSyms`. -/
abbrev ExtraSpecOk [LibsignalPlacement] (g : CliGhostHooks) : Prop :=
  ExtraFullListSpecOk g.extra

/-- Direct `(extra.lookup sym).isSome = true` projection on `ExtraFullListSpecOk` / `ExtraSpecOk`
    so callers of `hookSat_withExtra_of_isSome` can pass `(hSome := hG.extraOk.lookup_isSome)`. -/
theorem ExtraFullListSpecOk.lookup_isSome [LibsignalPlacement] {extra : ExtraGhostTable}
    (hOk : ExtraFullListSpecOk extra) {sym : String}
    (hDom : cliExtraGhostSyms.contains sym = true := by decide) :
    (extra.lookup sym).isSome = true :=
  hOk.complete.lookup_isSome hDom

theorem ExtraFullListSpecOk.ghostRowOk [LibsignalPlacement] {extra : ExtraGhostTable}
    (hOk : ExtraFullListSpecOk extra) (sym : String) (f : State → State)
    (hLook : extra.lookup sym = some f)
    (hne : (sym == lsWriteFileSym) = false := by decide) :
    GhostRowSpecOk sym f :=
  hOk.toExtraListSpecOk.ghostRowOk sym f hLook hne

/-- `HookFsTraced` projection on `ExtraFullListSpecOk` / `ExtraSpecOk`. -/
theorem ExtraFullListSpecOk.fsT [LibsignalPlacement] {extra : ExtraGhostTable}
    (hOk : ExtraFullListSpecOk extra) :
    ∀ sym f, cliExtraGhostSyms.contains sym = true →
      extra.lookup sym = some f → HookFsTraced IsFsC f :=
  hOk.toExtraListSpecOk.fsT

/-! ## 4. Generic Framing (`withLsRoCl`, Twin Congruence) & `HookSat` Lift Combinators -/

/-- Congruence transfer between duplicate `Spec α` definitions with identical fields (e.g.
    `LibsignalTripleRatchet.blackBoxSpec` ↔ `FindReceiverChainIndex.blackBoxSpec`, or
    `withVmPreserved LibsignalPublicApi.timeAddSpec` ↔ `timeAddBudgetSpec`). -/
theorem hookOk_congr {α : Type} {f : State → State} {spec₁ spec₂ : Spec α}
    (h : HookOk f spec₁)
    (hpre  : spec₁.pre = spec₂.pre := by rfl)
    (hpost : spec₁.post = spec₂.post := by rfl)
    (hpan  : spec₁.onPanic = spec₂.onPanic := by rfl)
    (hexit : spec₁.onExit = spec₂.onExit := by rfl)
    (hoom  : spec₁.onOom = spec₂.onOom := by rfl) :
    HookOk f spec₂ := by
  cases spec₁; cases spec₂
  dsimp at hpre hpost hpan hexit hoom
  subst hpre hpost hpan hexit hoom
  exact h

/-- Any `HookOk f spec` automatically satisfies `StoreKit.withLsRoCl pl spec` via `KeepsFrozen`. -/
theorem hookOk_withLsRoCl {α : Type} {f : State → State} (pl : MultiPlacement) {spec : Spec α}
    (h : HookOk f spec) :
    HookOk f (withLsRoCl pl spec) := by
  intro x R s0 hrun hpre hsp
  have ⟨hcrl0, hpre'⟩ := extract_withLsRoCl hpre
  rcases h x R s0 hrun hpre' hsp with ⟨hkeep, hsym, hout⟩
  have hcrlf := hcrl0.of_keepsFrozen hkeep
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsRoCl]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcrlf, hpost⟩
  · exact Or.inr hrest

/-- Lift `HookSat hooks sym spec` to `HookSat hooks sym (StoreKit.withLsRoCl pl spec)`. -/
theorem hookSat_withLsRoCl {α : Type} {hooks : String → Option (State → State)}
    (pl : MultiPlacement) {sym : String} {spec : Spec α}
    (h : HookSat hooks sym spec) :
    HookSat hooks sym (withLsRoCl pl spec) := by
  rcases h with ⟨f, hf, hok⟩
  exact ⟨f, hf, hookOk_withLsRoCl pl hok⟩

/-- Generic `HookSat` lift from a concrete `g.extra.lookup sym = some f` witness and `HookOk f spec`
    (works for all `cliExtraGhostSyms`, including `lsWriteFileSym`, `lsWriteStdoutSym`,
    `lsFmtWriteSym`, and `lsFormatInnerSym`, without requiring `ExtraSpecOk g`). -/
theorem hookSat_cliGhostExterns_of_extra_lookup {α : Type}
    (g : CliGhostHooks) (baseExt : String → Option (State → State))
    {sym : String} {f : State → State} {spec : Spec α}
    (hLook : g.extra.lookup sym = some f)
    (hOk : HookOk f spec)
    (hDom : cliExtraGhostSyms.contains sym = true := by decide) :
    HookSat (cliGhostExterns g baseExt) sym spec :=
  ⟨f, cliGhostExternsWithExtra_extra_some g g.extra baseExt hLook hDom, hOk⟩

/-- Transport any `extra`-row `HookSat` across two `CliGhostHooks` sharing `.extra`
    (e.g. `gh` and `gh.withFds fs0`). -/
theorem hookSat_cliGhostExterns_congr_extra {α : Type}
    (g₁ g₂ : CliGhostHooks) (baseExt : String → Option (State → State))
    {sym : String} {spec : Spec α}
    (hsat : HookSat (cliGhostExterns g₁ baseExt) sym spec)
    (hextra : g₂.extra = g₁.extra := by rfl)
    (hDom : cliExtraGhostSyms.contains sym = true := by decide) :
    HookSat (cliGhostExterns g₂ baseExt) sym spec := by
  rcases hsat with ⟨f, hf, hok⟩
  exact ⟨f,
    (CryptoVerification.SignalSession.Cli.RunGlue.cliGhostExterns_congr_extra
      g₂ g₁ baseExt hextra hDom).trans hf,
    hok⟩

/-- Generic `HookSat` lift over `cliGhostExterns g baseExt` using `ExtraRowOk` directly (covers all
    `cliExtraGhostSyms`, including `lsWriteFileSym`). -/
theorem hookSat_cliGhostExterns_of_extraRowOk [LibsignalPlacement] {α : Type}
    (g : CliGhostHooks) (baseExt : String → Option (State → State))
    {sym : String} {spec : Spec α}
    (hOk : ExtraSpecOk g)
    (hRow : ∀ f, g.extra.lookup sym = some f → ExtraRowOk sym f → HookOk f spec)
    (hDom : cliExtraGhostSyms.contains sym = true := by decide) :
    HookSat (cliGhostExterns g baseExt) sym spec := by
  have hSome := hOk.lookup_isSome hDom
  cases hLook : g.extra.lookup sym with
  | none => rw [hLook] at hSome; cases hSome
  | some f =>
    exact ⟨f, cliGhostExternsWithExtra_extra_some g g.extra baseExt hLook hDom,
      hRow f hLook (hOk.rowOk sym f hLook)⟩

/-- Generic `HookSat` lift over `cliGhostExternsWithExtra`: handles both `lookup = none`
    (delegating to `hBase`) and `lookup = some f` (extracting from `hOk`). -/
theorem hookSat_withExtra_of_base [LibsignalPlacement] {α : Type}
    (g : CliGhostHooks) {extra : ExtraGhostTable}
    (baseExt : String → Option (State → State))
    {sym : String} {spec : Spec α}
    (hDom : cliExtraGhostSyms.contains sym = true)
    (hRow : ∀ f, extra.lookup sym = some f → GhostRowSpecOk sym f → HookOk f spec)
    (hOk : ExtraListSpecOk extra)
    (hBase : HookSat baseExt sym spec)
    (hne : (sym == lsWriteFileSym) = false := by decide) :
    HookSat (cliGhostExternsWithExtra g extra baseExt) sym spec := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := named_eq_false_of_extra_contains hDom
  cases hLook : extra.lookup sym with
  | some f =>
    exact ⟨f, cliGhostExternsWithExtra_extra_some g extra baseExt hLook hDom,
      hRow f hLook (hOk.ghostRowOk sym f hLook hne)⟩
  | none =>
    have heq : cliGhostExternsWithExtra g extra baseExt sym = baseExt sym := by
      unfold cliGhostExternsWithExtra
      simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hDom, hLook, Bool.false_eq_true,
        ↓reduceIte]
    rcases hBase with ⟨fb, hfb, hokb⟩
    exact ⟨fb, heq.trans hfb, hokb⟩

/-- `cliGhostExterns`-targeted companion to `hookSat_withExtra_of_base`. -/
theorem hookSat_cliGhostExterns_of_base [LibsignalPlacement] {α : Type}
    (g : CliGhostHooks)
    (baseExt : String → Option (State → State))
    {sym : String} {spec : Spec α}
    (hDom : cliExtraGhostSyms.contains sym = true)
    (hRow : ∀ f, g.extra.lookup sym = some f → GhostRowSpecOk sym f → HookOk f spec)
    (hOk : ExtraSpecOk g)
    (hBase : HookSat baseExt sym spec)
    (hne : (sym == lsWriteFileSym) = false := by decide) :
    HookSat (cliGhostExterns g baseExt) sym spec :=
  hookSat_withExtra_of_base g baseExt hDom hRow hOk.toExtraListSpecOk hBase hne

/-- `HookSat` lift requiring no `baseExt` hypothesis when `sym` is populated in `extra`
    (`(extra.lookup sym).isSome = true`, closed by `rfl`/`decide` on concrete tables). -/
theorem hookSat_withExtra_of_isSome [LibsignalPlacement] {α : Type}
    (g : CliGhostHooks) {extra : ExtraGhostTable}
    (baseExt : String → Option (State → State))
    {sym : String} {spec : Spec α}
    (hRow : ∀ f, extra.lookup sym = some f → GhostRowSpecOk sym f → HookOk f spec)
    (hOk : ExtraListSpecOk extra)
    (hDom : cliExtraGhostSyms.contains sym = true := by decide)
    (hSome : (extra.lookup sym).isSome = true := by decide)
    (hne : (sym == lsWriteFileSym) = false := by decide) :
    HookSat (cliGhostExternsWithExtra g extra baseExt) sym spec := by
  cases hLook : extra.lookup sym with
  | none => rw [hLook] at hSome; cases hSome
  | some f =>
    exact ⟨f, cliGhostExternsWithExtra_extra_some g extra baseExt hLook hDom,
      hRow f hLook (hOk.ghostRowOk sym f hLook hne)⟩

/-- Table-parametric companion to `hookSat_cliGhostExterns_of_extraOk` on
    `cliGhostExternsWithExtra g extra baseExt`. -/
theorem hookSat_withExtra_of_fullOk [LibsignalPlacement] {α : Type}
    (g : CliGhostHooks) {extra : ExtraGhostTable}
    (baseExt : String → Option (State → State))
    {sym : String} {spec : Spec α}
    (hOk : ExtraFullListSpecOk extra)
    (hRow : ∀ f, extra.lookup sym = some f → GhostRowSpecOk sym f → HookOk f spec)
    (hDom : cliExtraGhostSyms.contains sym = true := by decide)
    (hne : (sym == lsWriteFileSym) = false := by decide) :
    HookSat (cliGhostExternsWithExtra g extra baseExt) sym spec :=
  hookSat_withExtra_of_isSome g baseExt hRow hOk.toExtraListSpecOk hDom (hOk.lookup_isSome hDom) hne

/-- Base-map-free consumer lift: derive `HookSat (cliGhostExterns g baseExt) sym spec` for any
    `fs`-preserving `sym ∈ cliExtraGhostSyms` directly from `hOk : ExtraSpecOk g` (`hG.extraOk`)
    without a `baseExt` hypothesis. -/
theorem hookSat_cliGhostExterns_of_extraOk [LibsignalPlacement] {α : Type}
    (g : CliGhostHooks) (baseExt : String → Option (State → State))
    {sym : String} {spec : Spec α}
    (hOk : ExtraSpecOk g)
    (hRow : ∀ f, g.extra.lookup sym = some f → GhostRowSpecOk sym f → HookOk f spec)
    (hDom : cliExtraGhostSyms.contains sym = true := by decide)
    (hne : (sym == lsWriteFileSym) = false := by decide) :
    HookSat (cliGhostExterns g baseExt) sym spec :=
  hookSat_withExtra_of_fullOk g baseExt hOk hRow hDom hne

/-! ## 5. Per-Row Plain, RO, `withVmPreserved`, & `withAlloc` Extractors from `GhostRowSpecOk` -/

theorem GhostRowSpecOk.bcmp_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "bcmp" f) : BcmpRowSpec f := by
  have hp := h.rowSpec; dsimp only [ExtraRowSpec] at hp; exact hp

theorem GhostRowSpecOk.bcmp_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "bcmp" f) : HookOk f cliBcmpSpec :=
  h.bcmp_row.1

theorem GhostRowSpecOk.bcmp_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "bcmp" f) : HookOk f (withVmPreserved cliBcmpSpec) :=
  h.bcmp_row.2.1

theorem GhostRowSpecOk.bcmp_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "bcmp" f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk f (withAlloc A lim cliBcmpSpec) :=
  h.bcmp_row.2.2.1 A lim

theorem GhostRowSpecOk.bcmpVregs_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "bcmp" f) : HookOk f bcmpVregsSpec :=
  h.bcmp_row.2.2.2.1

theorem GhostRowSpecOk.bcmpVregs_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "bcmp" f) : HookOk f (withVmPreserved bcmpVregsSpec) :=
  h.bcmp_row.2.2.2.2.1

theorem GhostRowSpecOk.bcmpVregs_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "bcmp" f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk f (withAlloc A lim bcmpVregsSpec) :=
  h.bcmp_row.2.2.2.2.2 A lim

theorem GhostRowSpecOk.e2eBcmp_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "bcmp" f) : HookOk f e2eBcmpSpec :=
  hookOk_bcmpSpec_of_vregs h.bcmpVregs_ok

theorem GhostRowSpecOk.strlen_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "strlen" f) : StrlenRowSpec f := by
  have hp := h.rowSpec; dsimp only [ExtraRowSpec] at hp; exact hp

theorem GhostRowSpecOk.strlen_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "strlen" f) (stk : Nat) :
    HookOk f (withStrlenPadRO (strlenSpec stk)) :=
  h.strlen_row.1 stk

theorem GhostRowSpecOk.strlen_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "strlen" f) (stk : Nat) :
    HookOk f (withVmPreserved (withStrlenPadRO (strlenSpec stk))) :=
  h.strlen_row.2.1 stk

theorem GhostRowSpecOk.strlen_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "strlen" f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    HookOk f (withAlloc A lim (withStrlenPadRO (strlenSpec stk))) :=
  h.strlen_row.2.2.1 A lim stk

theorem GhostRowSpecOk.strlenRO_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "strlen" f) (stk : Nat) :
    HookOk f (withStrlenPadRO (strlenSpecRO stk)) :=
  h.strlen_row.2.2.2.1 stk

theorem GhostRowSpecOk.strlenRO_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "strlen" f) (stk : Nat) :
    HookOk f (withVmPreserved (withStrlenPadRO (strlenSpecRO stk))) :=
  h.strlen_row.2.2.2.2.1 stk

theorem GhostRowSpecOk.strlenRO_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "strlen" f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    HookOk f (withAlloc A lim (withStrlenPadRO (strlenSpecRO stk))) :=
  h.strlen_row.2.2.2.2.2.1 A lim stk

theorem GhostRowSpecOk.strlenROSat_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "strlen" f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    HookOk f (withAlloc A lim (withVmPreserved (withStrlenPadRO (strlenSpecRO stk)))) :=
  h.strlen_row.2.2.2.2.2.2 A lim stk

theorem GhostRowSpecOk.memmove_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "memmove" f) : MemmoveRowSpec f := by
  have hp := h.rowSpec; dsimp only [ExtraRowSpec] at hp; exact hp

theorem GhostRowSpecOk.memmove_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "memmove" f) (stk : Nat) :
    HookOk f (libcMemmoveBoundedSpec stk) :=
  h.memmove_row.1 stk

theorem GhostRowSpecOk.memmove_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "memmove" f) (stk : Nat) :
    HookOk f (withVmPreserved (libcMemmoveBoundedSpec stk)) :=
  h.memmove_row.2.1 stk

theorem GhostRowSpecOk.memmove_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "memmove" f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    HookOk f (withAlloc A lim (libcMemmoveBoundedSpec stk)) :=
  h.memmove_row.2.2.1 A lim stk

theorem GhostRowSpecOk.sessionMemmove_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "memmove" f) (stk : Nat) :
    HookOk f (sessionMemmoveBoundedSpec stk) :=
  h.memmove_row.2.2.2.1 stk

theorem GhostRowSpecOk.sessionMemmove_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "memmove" f) (stk : Nat) :
    HookOk f (sessionMemmoveBoundedBudgetSpec stk) :=
  h.memmove_row.2.2.2.2.1 stk

theorem GhostRowSpecOk.sessionMemmove_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "memmove" f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    HookOk f (withAlloc A lim (sessionMemmoveBoundedSpec stk)) :=
  h.memmove_row.2.2.2.2.2.1 A lim stk

theorem GhostRowSpecOk.memmove_allocCallPreserved [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk "memmove" f) :
    ∀ s : State, AllocCallPreserved s (f s) :=
  h.memmove_row.2.2.2.2.2.2

theorem GhostRowSpecOk.fromUtf8_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsFromUtf8Sym f) : FromUtf8RowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  have hd1 : (lsFromUtf8Sym == "bcmp") = false := by decide
  have hd2 : (lsFromUtf8Sym == "strlen") = false := by decide
  have hd3 : (lsFromUtf8Sym == "memmove") = false := by decide
  have hd4 : (lsFromUtf8Sym == lsFromUtf8Sym) = true := by decide
  simp only [hd1, hd2, hd3, hd4, Bool.false_eq_true, ↓reduceIte] at hp
  exact hp

theorem GhostRowSpecOk.fromUtf8_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsFromUtf8Sym f) (stk : Nat) :
    HookOk f (fromUtf8AsciiSpec stk) :=
  h.fromUtf8_row.1 stk

theorem GhostRowSpecOk.fromUtf8_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsFromUtf8Sym f) (stk : Nat) :
    HookOk f (withVmPreserved (fromUtf8AsciiSpec stk)) :=
  h.fromUtf8_row.2.1 stk

theorem GhostRowSpecOk.fromUtf8_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsFromUtf8Sym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    HookOk f (withAlloc A lim (fromUtf8AsciiSpec stk)) :=
  h.fromUtf8_row.2.2.1 A lim stk

theorem GhostRowSpecOk.fromUtf8RO_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsFromUtf8Sym f) (stk : Nat) :
    HookOk f (fromUtf8AsciiSpecRO stk) :=
  h.fromUtf8_row.2.2.2.1 stk

theorem GhostRowSpecOk.fromUtf8RO_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsFromUtf8Sym f) (stk : Nat) :
    HookOk f (withVmPreserved (fromUtf8AsciiSpecRO stk)) :=
  h.fromUtf8_row.2.2.2.2.1 stk

theorem GhostRowSpecOk.fromUtf8RO_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsFromUtf8Sym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat) :
    HookOk f (withAlloc A lim (fromUtf8AsciiSpecRO stk)) :=
  h.fromUtf8_row.2.2.2.2.2 A lim stk

theorem GhostRowSpecOk.memrchr_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMemrchrSym f) : MemrchrRowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  have hd1 : (lsMemrchrSym == "bcmp") = false := by decide
  have hd2 : (lsMemrchrSym == "strlen") = false := by decide
  have hd3 : (lsMemrchrSym == "memmove") = false := by decide
  have hd4 : (lsMemrchrSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsMemrchrSym == lsMemrchrSym) = true := by decide
  simp only [hd1, hd2, hd3, hd4, hd5, Bool.false_eq_true, ↓reduceIte] at hp
  exact hp

theorem GhostRowSpecOk.memrchr_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMemrchrSym f) {stk : Nat}
    (hstk : extHookStack ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (memrchrSpec stk)) :=
  h.memrchr_row.1 stk hstk hstk_ub

theorem GhostRowSpecOk.memrchr_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMemrchrSym f) {stk : Nat}
    (hstk : extHookStack ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withVmPreserved (memrchrSpec stk))) :=
  h.memrchr_row.2.1 stk hstk hstk_ub

theorem GhostRowSpecOk.memrchr_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMemrchrSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) {stk : Nat}
    (hstk : extHookStack ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withAlloc A lim (memrchrSpec stk))) :=
  h.memrchr_row.2.2.1 A lim stk hstk hstk_ub

theorem GhostRowSpecOk.memrchrRO_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMemrchrSym f) {stk : Nat}
    (hstk : extHookStack ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (memrchrSpecRO stk)) :=
  h.memrchr_row.2.2.2.1 stk hstk hstk_ub

theorem GhostRowSpecOk.memrchrRO_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMemrchrSym f) {stk : Nat}
    (hstk : extHookStack ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withVmPreserved (memrchrSpecRO stk))) :=
  h.memrchr_row.2.2.2.2.1 stk hstk hstk_ub

theorem GhostRowSpecOk.memrchrRO_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMemrchrSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) {stk : Nat}
    (hstk : extHookStack ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withAlloc A lim (memrchrSpecRO stk))) :=
  h.memrchr_row.2.2.2.2.2 A lim stk hstk hstk_ub

theorem GhostRowSpecOk.durationSince_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDurationSinceSym f) : DurationSinceRowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  have hd1 : (lsDurationSinceSym == "bcmp") = false := by decide
  have hd2 : (lsDurationSinceSym == "strlen") = false := by decide
  have hd3 : (lsDurationSinceSym == "memmove") = false := by decide
  have hd4 : (lsDurationSinceSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsDurationSinceSym == lsMemrchrSym) = false := by decide
  have hd6 : (lsDurationSinceSym == lsDurationSinceSym) = true := by decide
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, Bool.false_eq_true, ↓reduceIte] at hp
  exact hp

theorem GhostRowSpecOk.durationSinceBounded_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDurationSinceSym f) :
    HookOk f (withLsRet CryptoVerification.SignalSession.Cli.Slots.durationSinceBoundedSpec) :=
  h.durationSince_row.1

theorem GhostRowSpecOk.durationSinceBounded_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDurationSinceSym f) :
    HookOk f (withLsRet (withVmPreserved
      CryptoVerification.SignalSession.Cli.Slots.durationSinceBoundedSpec)) :=
  h.durationSince_row.2.1

theorem GhostRowSpecOk.durationSinceBounded_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDurationSinceSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk f (withLsRet (withAlloc A lim
      CryptoVerification.SignalSession.Cli.Slots.durationSinceBoundedSpec)) :=
  h.durationSince_row.2.2.1 A lim

theorem GhostRowSpecOk.durationSinceEpochAt_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDurationSinceSym f) {stk : Nat}
    (hstk : 208 ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (durationSinceEpochAtSpec stk)) :=
  h.durationSince_row.2.2.2.1 stk hstk hstk_ub

theorem GhostRowSpecOk.durationSinceEpochAt_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDurationSinceSym f) {stk : Nat}
    (hstk : 208 ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withVmPreserved (durationSinceEpochAtSpec stk))) :=
  h.durationSince_row.2.2.2.2.1 stk hstk hstk_ub

theorem GhostRowSpecOk.durationSinceEpochAt_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDurationSinceSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) {stk : Nat}
    (hstk : 208 ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withAlloc A lim (durationSinceEpochAtSpec stk))) :=
  h.durationSince_row.2.2.2.2.2 A lim stk hstk hstk_ub

theorem GhostRowSpecOk.durationSinceEpoch_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDurationSinceSym f) :
    HookOk f (withLsRet durationSinceEpochBudgetSpec) :=
  h.durationSinceEpochAt_budget_ok (by decide : 208 ≤ extHookStack) (by decide)

theorem GhostRowSpecOk.durationSinceEpochAlloc_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDurationSinceSym f) :
    HookOk f (withLsRet (withVmPreserved durationSinceEpochAllocSpec)) :=
  h.durationSinceEpochAt_budget_ok (by decide : 208 ≤ allocHookStack) (by decide)

theorem GhostRowSpecOk.timeAdd_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsTimeAddSym f) : TimeAddRowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  have hd1 : (lsTimeAddSym == "bcmp") = false := by decide
  have hd2 : (lsTimeAddSym == "strlen") = false := by decide
  have hd3 : (lsTimeAddSym == "memmove") = false := by decide
  have hd4 : (lsTimeAddSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsTimeAddSym == lsMemrchrSym) = false := by decide
  have hd6 : (lsTimeAddSym == lsDurationSinceSym) = false := by decide
  have hd7 : (lsTimeAddSym == lsTimeAddSym) = true := by decide
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, Bool.false_eq_true, ↓reduceIte] at hp
  exact hp

theorem GhostRowSpecOk.publicApiTimeAdd_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsTimeAddSym f) :
    HookOk f (withLsRet CryptoVerification.LibsignalPublicApi.timeAddSpec) :=
  h.timeAdd_row.1

theorem GhostRowSpecOk.e2eTimeAdd_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsTimeAddSym f) :
    HookOk f (withLsRet CryptoVerification.E2E.HooksE.timeAddSpec) :=
  hookOk_congr h.publicApiTimeAdd_ok

theorem GhostRowSpecOk.publicApiTimeAdd_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsTimeAddSym f) :
    HookOk f (withLsRet (withVmPreserved CryptoVerification.LibsignalPublicApi.timeAddSpec)) :=
  h.timeAdd_row.2.1

theorem GhostRowSpecOk.timeAdd_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsTimeAddSym f) :
    HookOk f (withLsRet timeAddBudgetSpec) :=
  hookOk_congr h.publicApiTimeAdd_budget_ok

theorem GhostRowSpecOk.publicApiTimeAdd_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsTimeAddSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk f (withLsRet (withAlloc A lim CryptoVerification.LibsignalPublicApi.timeAddSpec)) :=
  h.timeAdd_row.2.2 A lim

theorem GhostRowSpecOk.blackBox_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsBlackBoxSym f) : BlackBoxRowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  have hd1 : (lsBlackBoxSym == "bcmp") = false := by decide
  have hd2 : (lsBlackBoxSym == "strlen") = false := by decide
  have hd3 : (lsBlackBoxSym == "memmove") = false := by decide
  have hd4 : (lsBlackBoxSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsBlackBoxSym == lsMemrchrSym) = false := by decide
  have hd6 : (lsBlackBoxSym == lsDurationSinceSym) = false := by decide
  have hd7 : (lsBlackBoxSym == lsTimeAddSym) = false := by decide
  have hd8 : (lsBlackBoxSym == lsBlackBoxSym) = true := by decide
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, Bool.false_eq_true, ↓reduceIte] at hp
  exact hp

theorem GhostRowSpecOk.blackBox_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsBlackBoxSym f) {stk : Nat}
    (hstk : 16 ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withStack blackBoxSpec stk) :=
  h.blackBox_row.1 stk hstk hstk_ub

theorem GhostRowSpecOk.blackBox_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsBlackBoxSym f) {stk : Nat}
    (hstk : 16 ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withVmPreserved (withStack blackBoxSpec stk)) :=
  h.blackBox_row.2.1 stk hstk hstk_ub

theorem GhostRowSpecOk.blackBox_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsBlackBoxSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) {stk : Nat}
    (hstk : 16 ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withAlloc A lim (withStack blackBoxSpec stk)) :=
  h.blackBox_row.2.2 A lim stk hstk hstk_ub

theorem GhostRowSpecOk.findReceiverBlackBox_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsBlackBoxSym f) {stk : Nat}
    (hstk : 16 ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withStack CryptoVerification.LibsignalSession.FindReceiverChainIndex.blackBoxSpec stk) :=
  hookOk_congr (h.blackBox_ok hstk hstk_ub)

theorem GhostRowSpecOk.findReceiverBlackBox_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsBlackBoxSym f) {stk : Nat}
    (hstk : 16 ≤ stk) (hstk_ub : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withVmPreserved
      (withStack CryptoVerification.LibsignalSession.FindReceiverChainIndex.blackBoxSpec stk)) :=
  hookOk_congr (h.blackBox_budget_ok hstk hstk_ub)

theorem GhostRowSpecOk.staticSecretDrop_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsStaticSecretDropSym f) : StaticSecretDropRowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  have hd1 : (lsStaticSecretDropSym == "bcmp") = false := by decide
  have hd2 : (lsStaticSecretDropSym == "strlen") = false := by decide
  have hd3 : (lsStaticSecretDropSym == "memmove") = false := by decide
  have hd4 : (lsStaticSecretDropSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsStaticSecretDropSym == lsMemrchrSym) = false := by decide
  have hd6 : (lsStaticSecretDropSym == lsDurationSinceSym) = false := by decide
  have hd7 : (lsStaticSecretDropSym == lsTimeAddSym) = false := by decide
  have hd8 : (lsStaticSecretDropSym == lsBlackBoxSym) = false := by decide
  have hd9 : (lsStaticSecretDropSym == lsStaticSecretDropSym) = true := by decide
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, Bool.false_eq_true, ↓reduceIte] at hp
  exact hp

theorem GhostRowSpecOk.staticSecretDrop_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsStaticSecretDropSym f) :
    HookOk f zeroizeSecretSpec :=
  h.staticSecretDrop_row.1

theorem GhostRowSpecOk.staticSecretDrop_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsStaticSecretDropSym f) :
    HookOk f (withVmPreserved zeroizeSecretSpec) :=
  h.staticSecretDrop_row.2.1

theorem GhostRowSpecOk.staticSecretDrop_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsStaticSecretDropSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk f (withAlloc A lim zeroizeSecretSpec) :=
  h.staticSecretDrop_row.2.2 A lim

theorem GhostRowSpecOk.sharedSecretDrop_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsSharedSecretDropSym f) : SharedSecretDropRowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  have hd1 : (lsSharedSecretDropSym == "bcmp") = false := by decide
  have hd2 : (lsSharedSecretDropSym == "strlen") = false := by decide
  have hd3 : (lsSharedSecretDropSym == "memmove") = false := by decide
  have hd4 : (lsSharedSecretDropSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsSharedSecretDropSym == lsMemrchrSym) = false := by decide
  have hd6 : (lsSharedSecretDropSym == lsDurationSinceSym) = false := by decide
  have hd7 : (lsSharedSecretDropSym == lsTimeAddSym) = false := by decide
  have hd8 : (lsSharedSecretDropSym == lsBlackBoxSym) = false := by decide
  have hd9 : (lsSharedSecretDropSym == lsStaticSecretDropSym) = false := by decide
  have hd10 : (lsSharedSecretDropSym == lsSharedSecretDropSym) = true := by decide
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, Bool.false_eq_true,
    ↓reduceIte] at hp
  exact hp

theorem GhostRowSpecOk.sharedSecretDrop_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsSharedSecretDropSym f) :
    HookOk f zeroizeSecretSpec :=
  h.sharedSecretDrop_row.1

theorem GhostRowSpecOk.sharedSecretDrop_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsSharedSecretDropSym f) :
    HookOk f (withVmPreserved zeroizeSecretSpec) :=
  h.sharedSecretDrop_row.2.1

theorem GhostRowSpecOk.sharedSecretDrop_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsSharedSecretDropSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk f (withAlloc A lim zeroizeSecretSpec) :=
  h.sharedSecretDrop_row.2.2 A lim

theorem GhostRowSpecOk.toEdwards_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsToEdwardsSym f) : DalekMontToEdRowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  have hd1 : (lsToEdwardsSym == "bcmp") = false := by decide
  have hd2 : (lsToEdwardsSym == "strlen") = false := by decide
  have hd3 : (lsToEdwardsSym == "memmove") = false := by decide
  have hd4 : (lsToEdwardsSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsToEdwardsSym == lsMemrchrSym) = false := by decide
  have hd6 : (lsToEdwardsSym == lsDurationSinceSym) = false := by decide
  have hd7 : (lsToEdwardsSym == lsTimeAddSym) = false := by decide
  have hd8 : (lsToEdwardsSym == lsBlackBoxSym) = false := by decide
  have hd9 : (lsToEdwardsSym == lsStaticSecretDropSym) = false := by decide
  have hd10 : (lsToEdwardsSym == lsSharedSecretDropSym) = false := by decide
  have hd11 : (lsToEdwardsSym == lsToEdwardsSym) = true := by decide
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, Bool.false_eq_true,
    ↓reduceIte] at hp
  exact hp

theorem GhostRowSpecOk.toEdwards_at_stk [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsToEdwardsSym f) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    DalekLsRowTuple f (dalekMontToEdExtSpec stk) :=
  h.toEdwards_row.at_stk stk hlo hhi

theorem GhostRowSpecOk.toEdwards_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsToEdwardsSym f) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (dalekMontToEdExtSpec stk)) :=
  (h.toEdwards_at_stk stk hlo hhi).plain

theorem GhostRowSpecOk.toEdwards_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsToEdwardsSym f) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withVmPreserved (dalekMontToEdExtSpec stk))) :=
  (h.toEdwards_at_stk stk hlo hhi).vm

theorem GhostRowSpecOk.toEdwards_keepsFs_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsToEdwardsSym f) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withVmPreserved (keepsFs (dalekMontToEdExtSpec stk)))) :=
  (h.toEdwards_at_stk stk hlo hhi).keepsFsVm

theorem GhostRowSpecOk.toEdwards_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsToEdwardsSym f) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withAlloc A lim (withLsRet (dalekMontToEdExtSpec stk))) :=
  (h.toEdwards_at_stk stk hlo hhi).alloc A lim

theorem GhostRowSpecOk.toEdwards_withLsRet_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsToEdwardsSym f) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withAlloc A lim (dalekMontToEdExtSpec stk))) :=
  (h.toEdwards_at_stk stk hlo hhi).withLsRetAlloc A lim

theorem GhostRowSpecOk.compress_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsCompressSym f) : DalekCompressRowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  have hd1 : (lsCompressSym == "bcmp") = false := by decide
  have hd2 : (lsCompressSym == "strlen") = false := by decide
  have hd3 : (lsCompressSym == "memmove") = false := by decide
  have hd4 : (lsCompressSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsCompressSym == lsMemrchrSym) = false := by decide
  have hd6 : (lsCompressSym == lsDurationSinceSym) = false := by decide
  have hd7 : (lsCompressSym == lsTimeAddSym) = false := by decide
  have hd8 : (lsCompressSym == lsBlackBoxSym) = false := by decide
  have hd9 : (lsCompressSym == lsStaticSecretDropSym) = false := by decide
  have hd10 : (lsCompressSym == lsSharedSecretDropSym) = false := by decide
  have hd11 : (lsCompressSym == lsToEdwardsSym) = false := by decide
  have hd12 : (lsCompressSym == lsCompressSym) = true := by decide
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, Bool.false_eq_true,
    ↓reduceIte] at hp
  exact hp

theorem GhostRowSpecOk.compress_at_stk [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsCompressSym f) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    DalekLsRowTuple f (dalekCompressExtSpec stk) :=
  h.compress_row.at_stk stk hlo hhi

theorem GhostRowSpecOk.compress_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsCompressSym f) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (dalekCompressExtSpec stk)) :=
  (h.compress_at_stk stk hlo hhi).plain

theorem GhostRowSpecOk.compress_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsCompressSym f) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withVmPreserved (dalekCompressExtSpec stk))) :=
  (h.compress_at_stk stk hlo hhi).vm

theorem GhostRowSpecOk.compress_keepsFs_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsCompressSym f) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withVmPreserved (keepsFs (dalekCompressExtSpec stk)))) :=
  (h.compress_at_stk stk hlo hhi).keepsFsVm

theorem GhostRowSpecOk.compress_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsCompressSym f) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withAlloc A lim (withLsRet (dalekCompressExtSpec stk))) :=
  (h.compress_at_stk stk hlo hhi).alloc A lim

theorem GhostRowSpecOk.compress_withLsRet_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsCompressSym f) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withAlloc A lim (dalekCompressExtSpec stk))) :=
  (h.compress_at_stk stk hlo hhi).withLsRetAlloc A lim

theorem GhostRowSpecOk.edNeg_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsEdNegSym f) : EdNegRowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  have hd1 : (lsEdNegSym == "bcmp") = false := by decide
  have hd2 : (lsEdNegSym == "strlen") = false := by decide
  have hd3 : (lsEdNegSym == "memmove") = false := by decide
  have hd4 : (lsEdNegSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsEdNegSym == lsMemrchrSym) = false := by decide
  have hd6 : (lsEdNegSym == lsDurationSinceSym) = false := by decide
  have hd7 : (lsEdNegSym == lsTimeAddSym) = false := by decide
  have hd8 : (lsEdNegSym == lsBlackBoxSym) = false := by decide
  have hd9 : (lsEdNegSym == lsStaticSecretDropSym) = false := by decide
  have hd10 : (lsEdNegSym == lsSharedSecretDropSym) = false := by decide
  have hd11 : (lsEdNegSym == lsToEdwardsSym) = false := by decide
  have hd12 : (lsEdNegSym == lsCompressSym) = false := by decide
  have hd13 : (lsEdNegSym == lsEdNegSym) = true := by decide
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13,
    Bool.false_eq_true, ↓reduceIte] at hp
  exact hp

theorem GhostRowSpecOk.edNeg_master_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsEdNegSym f) : HookOk f masterEdNegSpec :=
  h.edNeg_row.master

theorem GhostRowSpecOk.edNeg_vmPreserved [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsEdNegSym f) (s : State) : VmPreserved s (f s) :=
  h.edNeg_row.vmPreserved s

theorem GhostRowSpecOk.edNeg_master_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsEdNegSym f) : HookOk f (withVmPreserved masterEdNegSpec) :=
  h.edNeg_row.masterVm

theorem GhostRowSpecOk.edNeg_unstacked_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsEdNegSym f) (byVal : Bool := false) :
    HookOk f (edwardsPointNegUnstackedSpec byVal) :=
  h.edNeg_row.unstacked byVal

theorem GhostRowSpecOk.edNeg_unstacked_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsEdNegSym f) (byVal : Bool := false) :
    HookOk f (withVmPreserved (edwardsPointNegUnstackedSpec byVal)) :=
  h.edNeg_row.unstackedVm byVal

theorem GhostRowSpecOk.edNeg_unstacked_keepsFs_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsEdNegSym f) (byVal : Bool := false) :
    HookOk f (keepsFs (edwardsPointNegUnstackedSpec byVal)) :=
  h.edNeg_row.unstackedKeepsFs byVal

theorem GhostRowSpecOk.edNeg_pureByteFunction_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsEdNegSym f) (byVal : Bool := false) :
    HookOk f (pureByteFunctionSpec dalekEdNegVec byVal) :=
  h.edNeg_row.pureByteFunction byVal

theorem GhostRowSpecOk.edNeg_pureByteFunction_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsEdNegSym f) (byVal : Bool := false) :
    HookOk f (withVmPreserved (pureByteFunctionSpec dalekEdNegVec byVal)) :=
  h.edNeg_row.pureByteFunctionVm byVal

theorem GhostRowSpecOk.edNeg_pureByteFunction_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsEdNegSym f) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (byVal : Bool := false) :
    HookOk f (withAlloc A lim (pureByteFunctionSpec dalekEdNegVec byVal)) :=
  h.edNeg_row.pureByteFunctionAlloc A lim byVal

theorem GhostRowSpecOk.edNeg_cryptoLeafStub_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsEdNegSym f) :
    HookOk f (cryptoLeafStubSpec (fun bs => vecU8 (dalekEdNegVec (u8Vec 160 bs))) 160 160) :=
  h.edNeg_row.cryptoLeafStub

theorem GhostRowSpecOk.edNeg_cryptoLeafStub_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsEdNegSym f) :
    HookOk f (withVmPreserved
      (cryptoLeafStubSpec (fun bs => vecU8 (dalekEdNegVec (u8Vec 160 bs))) 160 160)) :=
  h.edNeg_row.cryptoLeafStubVm

theorem GhostRowSpecOk.edNeg_cryptoLeafStub_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsEdNegSym f) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk f (withAlloc A lim
      (cryptoLeafStubSpec (fun bs => vecU8 (dalekEdNegVec (u8Vec 160 bs))) 160 160)) :=
  h.edNeg_row.cryptoLeafStubAlloc A lim

theorem GhostRowSpecOk.edNeg_at_stk [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsEdNegSym f) (stk : Nat := dalekHookStack) :
    DalekLsRowTuple f (dalekEdNegExtSpec stk) :=
  h.edNeg_row.at_stk stk

theorem GhostRowSpecOk.edNeg_ext_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsEdNegSym f) (stk : Nat := dalekHookStack) :
    HookOk f (withLsRet (dalekEdNegExtSpec stk)) :=
  (h.edNeg_at_stk stk).plain

theorem GhostRowSpecOk.edNeg_ext_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsEdNegSym f) (stk : Nat := dalekHookStack) :
    HookOk f (withLsRet (withVmPreserved (dalekEdNegExtSpec stk))) :=
  (h.edNeg_at_stk stk).vm

theorem GhostRowSpecOk.edNeg_ext_keepsFs_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsEdNegSym f) (stk : Nat := dalekHookStack) :
    HookOk f (withLsRet (withVmPreserved (keepsFs (dalekEdNegExtSpec stk)))) :=
  (h.edNeg_at_stk stk).keepsFsVm

theorem GhostRowSpecOk.edNeg_ext_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsEdNegSym f) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := dalekHookStack) :
    HookOk f (withAlloc A lim (withLsRet (dalekEdNegExtSpec stk))) :=
  (h.edNeg_at_stk stk).alloc A lim

theorem GhostRowSpecOk.edNeg_ext_withLsRet_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsEdNegSym f) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := dalekHookStack) :
    HookOk f (withLsRet (withAlloc A lim (dalekEdNegExtSpec stk))) :=
  (h.edNeg_at_stk stk).withLsRetAlloc A lim

theorem GhostRowSpecOk.torsionFree_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsTorsionFreeSym f) : DalekTorsionFreeRowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  have hd1 : (lsTorsionFreeSym == "bcmp") = false := by decide
  have hd2 : (lsTorsionFreeSym == "strlen") = false := by decide
  have hd3 : (lsTorsionFreeSym == "memmove") = false := by decide
  have hd4 : (lsTorsionFreeSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsTorsionFreeSym == lsMemrchrSym) = false := by decide
  have hd6 : (lsTorsionFreeSym == lsDurationSinceSym) = false := by decide
  have hd7 : (lsTorsionFreeSym == lsTimeAddSym) = false := by decide
  have hd8 : (lsTorsionFreeSym == lsBlackBoxSym) = false := by decide
  have hd9 : (lsTorsionFreeSym == lsStaticSecretDropSym) = false := by decide
  have hd10 : (lsTorsionFreeSym == lsSharedSecretDropSym) = false := by decide
  have hd11 : (lsTorsionFreeSym == lsToEdwardsSym) = false := by decide
  have hd12 : (lsTorsionFreeSym == lsCompressSym) = false := by decide
  have hd13 : (lsTorsionFreeSym == lsEdNegSym) = false := by decide
  have hd14 : (lsTorsionFreeSym == lsTorsionFreeSym) = true := by decide
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14,
    Bool.false_eq_true, ↓reduceIte] at hp
  exact hp

theorem GhostRowSpecOk.torsionFree_at_stk [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsTorsionFreeSym f) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    DalekLsRowTuple f (dalekTorsionFreeExtSpec stk) :=
  h.torsionFree_row.at_stk stk hlo hhi

theorem GhostRowSpecOk.torsionFree_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsTorsionFreeSym f) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (dalekTorsionFreeExtSpec stk)) :=
  (h.torsionFree_at_stk stk hlo hhi).plain

theorem GhostRowSpecOk.torsionFree_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsTorsionFreeSym f) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withVmPreserved (dalekTorsionFreeExtSpec stk))) :=
  (h.torsionFree_at_stk stk hlo hhi).vm

theorem GhostRowSpecOk.torsionFree_keepsFs_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsTorsionFreeSym f) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withVmPreserved (keepsFs (dalekTorsionFreeExtSpec stk)))) :=
  (h.torsionFree_at_stk stk hlo hhi).keepsFsVm

theorem GhostRowSpecOk.torsionFree_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsTorsionFreeSym f) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withAlloc A lim (withLsRet (dalekTorsionFreeExtSpec stk))) :=
  (h.torsionFree_at_stk stk hlo hhi).alloc A lim

theorem GhostRowSpecOk.torsionFree_withLsRet_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsTorsionFreeSym f) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withAlloc A lim (dalekTorsionFreeExtSpec stk))) :=
  (h.torsionFree_at_stk stk hlo hhi).withLsRetAlloc A lim

theorem GhostRowSpecOk.dsmb_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDsmbSym f) : DalekDsmbRowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  have hd1 : (lsDsmbSym == "bcmp") = false := by decide
  have hd2 : (lsDsmbSym == "strlen") = false := by decide
  have hd3 : (lsDsmbSym == "memmove") = false := by decide
  have hd4 : (lsDsmbSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsDsmbSym == lsMemrchrSym) = false := by decide
  have hd6 : (lsDsmbSym == lsDurationSinceSym) = false := by decide
  have hd7 : (lsDsmbSym == lsTimeAddSym) = false := by decide
  have hd8 : (lsDsmbSym == lsBlackBoxSym) = false := by decide
  have hd9 : (lsDsmbSym == lsStaticSecretDropSym) = false := by decide
  have hd10 : (lsDsmbSym == lsSharedSecretDropSym) = false := by decide
  have hd11 : (lsDsmbSym == lsToEdwardsSym) = false := by decide
  have hd12 : (lsDsmbSym == lsCompressSym) = false := by decide
  have hd13 : (lsDsmbSym == lsEdNegSym) = false := by decide
  have hd14 : (lsDsmbSym == lsTorsionFreeSym) = false := by decide
  have hd15 : (lsDsmbSym == lsDsmbSym) = true := by decide
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14, hd15,
    Bool.false_eq_true, ↓reduceIte] at hp
  exact hp

theorem GhostRowSpecOk.dsmb_at_stk [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDsmbSym f) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    DalekLsRowTuple f (dalekDsmbExtSpec stk) :=
  h.dsmb_row.at_stk stk hlo hhi

theorem GhostRowSpecOk.dsmb_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDsmbSym f) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (dalekDsmbExtSpec stk)) :=
  (h.dsmb_at_stk stk hlo hhi).plain

theorem GhostRowSpecOk.dsmb_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDsmbSym f) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withVmPreserved (dalekDsmbExtSpec stk))) :=
  (h.dsmb_at_stk stk hlo hhi).vm

theorem GhostRowSpecOk.dsmb_keepsFs_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDsmbSym f) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withVmPreserved (keepsFs (dalekDsmbExtSpec stk)))) :=
  (h.dsmb_at_stk stk hlo hhi).keepsFsVm

theorem GhostRowSpecOk.dsmb_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDsmbSym f) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withAlloc A lim (withLsRet (dalekDsmbExtSpec stk))) :=
  (h.dsmb_at_stk stk hlo hhi).alloc A lim

theorem GhostRowSpecOk.dsmb_withLsRet_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDsmbSym f) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withAlloc A lim (dalekDsmbExtSpec stk))) :=
  (h.dsmb_at_stk stk hlo hhi).withLsRetAlloc A lim

theorem GhostRowSpecOk.scalarMod_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsScalarModSym f) : DalekScalarModRowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  have hd1 : (lsScalarModSym == "bcmp") = false := by decide
  have hd2 : (lsScalarModSym == "strlen") = false := by decide
  have hd3 : (lsScalarModSym == "memmove") = false := by decide
  have hd4 : (lsScalarModSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsScalarModSym == lsMemrchrSym) = false := by decide
  have hd6 : (lsScalarModSym == lsDurationSinceSym) = false := by decide
  have hd7 : (lsScalarModSym == lsTimeAddSym) = false := by decide
  have hd8 : (lsScalarModSym == lsBlackBoxSym) = false := by decide
  have hd9 : (lsScalarModSym == lsStaticSecretDropSym) = false := by decide
  have hd10 : (lsScalarModSym == lsSharedSecretDropSym) = false := by decide
  have hd11 : (lsScalarModSym == lsToEdwardsSym) = false := by decide
  have hd12 : (lsScalarModSym == lsCompressSym) = false := by decide
  have hd13 : (lsScalarModSym == lsEdNegSym) = false := by decide
  have hd14 : (lsScalarModSym == lsTorsionFreeSym) = false := by decide
  have hd15 : (lsScalarModSym == lsDsmbSym) = false := by decide
  have hd16 : (lsScalarModSym == lsScalarModSym) = true := by decide
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14, hd15,
    hd16, Bool.false_eq_true, ↓reduceIte] at hp
  exact hp

theorem GhostRowSpecOk.scalarMod_at_stk [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsScalarModSym f) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    DalekLsRowTuple f (dalekScalarModExtSpec stk) :=
  h.scalarMod_row.at_stk stk hlo hhi

theorem GhostRowSpecOk.scalarMod_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsScalarModSym f) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (dalekScalarModExtSpec stk)) :=
  (h.scalarMod_at_stk stk hlo hhi).plain

theorem GhostRowSpecOk.scalarMod_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsScalarModSym f) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withVmPreserved (dalekScalarModExtSpec stk))) :=
  (h.scalarMod_at_stk stk hlo hhi).vm

theorem GhostRowSpecOk.scalarMod_keepsFs_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsScalarModSym f) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withVmPreserved (keepsFs (dalekScalarModExtSpec stk)))) :=
  (h.scalarMod_at_stk stk hlo hhi).keepsFsVm

theorem GhostRowSpecOk.scalarMod_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsScalarModSym f) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withAlloc A lim (withLsRet (dalekScalarModExtSpec stk))) :=
  (h.scalarMod_at_stk stk hlo hhi).alloc A lim

theorem GhostRowSpecOk.scalarMod_withLsRet_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsScalarModSym f) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withAlloc A lim (dalekScalarModExtSpec stk))) :=
  (h.scalarMod_at_stk stk hlo hhi).withLsRetAlloc A lim

theorem GhostRowSpecOk.scalarWide_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsScalarWideSym f) : DalekScalarWideRowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  have hd1 : (lsScalarWideSym == "bcmp") = false := by decide
  have hd2 : (lsScalarWideSym == "strlen") = false := by decide
  have hd3 : (lsScalarWideSym == "memmove") = false := by decide
  have hd4 : (lsScalarWideSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsScalarWideSym == lsMemrchrSym) = false := by decide
  have hd6 : (lsScalarWideSym == lsDurationSinceSym) = false := by decide
  have hd7 : (lsScalarWideSym == lsTimeAddSym) = false := by decide
  have hd8 : (lsScalarWideSym == lsBlackBoxSym) = false := by decide
  have hd9 : (lsScalarWideSym == lsStaticSecretDropSym) = false := by decide
  have hd10 : (lsScalarWideSym == lsSharedSecretDropSym) = false := by decide
  have hd11 : (lsScalarWideSym == lsToEdwardsSym) = false := by decide
  have hd12 : (lsScalarWideSym == lsCompressSym) = false := by decide
  have hd13 : (lsScalarWideSym == lsEdNegSym) = false := by decide
  have hd14 : (lsScalarWideSym == lsTorsionFreeSym) = false := by decide
  have hd15 : (lsScalarWideSym == lsDsmbSym) = false := by decide
  have hd16 : (lsScalarWideSym == lsScalarModSym) = false := by decide
  have hd17 : (lsScalarWideSym == lsScalarWideSym) = true := by decide
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14, hd15,
    hd16, hd17, Bool.false_eq_true, ↓reduceIte] at hp
  exact hp

theorem GhostRowSpecOk.scalarWide_at_stk [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsScalarWideSym f) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    DalekLsRowTuple f (dalekScalarWideExtSpec stk) :=
  h.scalarWide_row.at_stk stk hlo hhi

theorem GhostRowSpecOk.scalarWide_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsScalarWideSym f) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (dalekScalarWideExtSpec stk)) :=
  (h.scalarWide_at_stk stk hlo hhi).plain

theorem GhostRowSpecOk.scalarWide_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsScalarWideSym f) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withVmPreserved (dalekScalarWideExtSpec stk))) :=
  (h.scalarWide_at_stk stk hlo hhi).vm

theorem GhostRowSpecOk.scalarWide_keepsFs_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsScalarWideSym f) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withVmPreserved (keepsFs (dalekScalarWideExtSpec stk)))) :=
  (h.scalarWide_at_stk stk hlo hhi).keepsFsVm

theorem GhostRowSpecOk.scalarWide_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsScalarWideSym f) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withAlloc A lim (withLsRet (dalekScalarWideExtSpec stk))) :=
  (h.scalarWide_at_stk stk hlo hhi).alloc A lim

theorem GhostRowSpecOk.scalarWide_withLsRet_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsScalarWideSym f) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := dalekHookStack)
    (hlo : dalekHookStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withAlloc A lim (dalekScalarWideExtSpec stk))) :=
  (h.scalarWide_at_stk stk hlo hhi).withLsRetAlloc A lim

theorem GhostRowSpecOk.mlkemPk1_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemPk1Sym f) : MlkemPk1RowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  have hd1 : (lsMlkemPk1Sym == "bcmp") = false := by decide
  have hd2 : (lsMlkemPk1Sym == "strlen") = false := by decide
  have hd3 : (lsMlkemPk1Sym == "memmove") = false := by decide
  have hd4 : (lsMlkemPk1Sym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsMlkemPk1Sym == lsMemrchrSym) = false := by decide
  have hd6 : (lsMlkemPk1Sym == lsDurationSinceSym) = false := by decide
  have hd7 : (lsMlkemPk1Sym == lsTimeAddSym) = false := by decide
  have hd8 : (lsMlkemPk1Sym == lsBlackBoxSym) = false := by decide
  have hd9 : (lsMlkemPk1Sym == lsStaticSecretDropSym) = false := by decide
  have hd10 : (lsMlkemPk1Sym == lsSharedSecretDropSym) = false := by decide
  have hd11 : (lsMlkemPk1Sym == lsToEdwardsSym) = false := by decide
  have hd12 : (lsMlkemPk1Sym == lsCompressSym) = false := by decide
  have hd13 : (lsMlkemPk1Sym == lsEdNegSym) = false := by decide
  have hd14 : (lsMlkemPk1Sym == lsTorsionFreeSym) = false := by decide
  have hd15 : (lsMlkemPk1Sym == lsDsmbSym) = false := by decide
  have hd16 : (lsMlkemPk1Sym == lsScalarModSym) = false := by decide
  have hd17 : (lsMlkemPk1Sym == lsScalarWideSym) = false := by decide
  have hd18 : (lsMlkemPk1Sym == lsMlkemPk1Sym) = true := by decide
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14, hd15,
    hd16, hd17, hd18, Bool.false_eq_true, ↓reduceIte] at hp
  exact hp

theorem GhostRowSpecOk.mlkemPk1_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemPk1Sym f) : HookOk f mlkemPk1Spec :=
  h.mlkemPk1_row.plain

theorem GhostRowSpecOk.mlkemPk1_vmPreserved [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemPk1Sym f) (s : State) : VmPreserved s (f s) :=
  h.mlkemPk1_row.vmPreserved s

theorem GhostRowSpecOk.mlkemPk1_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemPk1Sym f) : HookOk f (withVmPreserved mlkemPk1Spec) :=
  h.mlkemPk1_row.vm

theorem GhostRowSpecOk.mlkemPk1_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemPk1Sym f) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk f (withAlloc A lim mlkemPk1Spec) :=
  h.mlkemPk1_row.alloc A lim

theorem GhostRowSpecOk.mlkemPk1_ls_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemPk1Sym f) : HookOk f (withLsRet mlkemPk1Spec) :=
  h.mlkemPk1_row.ls

theorem GhostRowSpecOk.mlkemPk1_ls_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemPk1Sym f) : HookOk f (withLsRet (withVmPreserved mlkemPk1Spec)) :=
  h.mlkemPk1_row.lsVm

theorem GhostRowSpecOk.mlkemPk1_ls_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemPk1Sym f) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk f (withLsRet (withAlloc A lim mlkemPk1Spec)) :=
  h.mlkemPk1_row.lsAlloc A lim

theorem GhostRowSpecOk.mlkemPk2_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemPk2Sym f) : MlkemPk2RowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  have hd1 : (lsMlkemPk2Sym == "bcmp") = false := by decide
  have hd2 : (lsMlkemPk2Sym == "strlen") = false := by decide
  have hd3 : (lsMlkemPk2Sym == "memmove") = false := by decide
  have hd4 : (lsMlkemPk2Sym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsMlkemPk2Sym == lsMemrchrSym) = false := by decide
  have hd6 : (lsMlkemPk2Sym == lsDurationSinceSym) = false := by decide
  have hd7 : (lsMlkemPk2Sym == lsTimeAddSym) = false := by decide
  have hd8 : (lsMlkemPk2Sym == lsBlackBoxSym) = false := by decide
  have hd9 : (lsMlkemPk2Sym == lsStaticSecretDropSym) = false := by decide
  have hd10 : (lsMlkemPk2Sym == lsSharedSecretDropSym) = false := by decide
  have hd11 : (lsMlkemPk2Sym == lsToEdwardsSym) = false := by decide
  have hd12 : (lsMlkemPk2Sym == lsCompressSym) = false := by decide
  have hd13 : (lsMlkemPk2Sym == lsEdNegSym) = false := by decide
  have hd14 : (lsMlkemPk2Sym == lsTorsionFreeSym) = false := by decide
  have hd15 : (lsMlkemPk2Sym == lsDsmbSym) = false := by decide
  have hd16 : (lsMlkemPk2Sym == lsScalarModSym) = false := by decide
  have hd17 : (lsMlkemPk2Sym == lsScalarWideSym) = false := by decide
  have hd18 : (lsMlkemPk2Sym == lsMlkemPk1Sym) = false := by decide
  have hd19 : (lsMlkemPk2Sym == lsMlkemPk2Sym) = true := by decide
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14, hd15,
    hd16, hd17, hd18, hd19, Bool.false_eq_true, ↓reduceIte] at hp
  exact hp

theorem GhostRowSpecOk.mlkemPk2_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemPk2Sym f) : HookOk f mlkemPk2Spec :=
  h.mlkemPk2_row.plain

theorem GhostRowSpecOk.mlkemPk2_vmPreserved [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemPk2Sym f) (s : State) : VmPreserved s (f s) :=
  h.mlkemPk2_row.vmPreserved s

theorem GhostRowSpecOk.mlkemPk2_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemPk2Sym f) : HookOk f (withVmPreserved mlkemPk2Spec) :=
  h.mlkemPk2_row.vm

theorem GhostRowSpecOk.mlkemPk2_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemPk2Sym f) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk f (withAlloc A lim mlkemPk2Spec) :=
  h.mlkemPk2_row.alloc A lim

theorem GhostRowSpecOk.mlkemPk2_ls_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemPk2Sym f) : HookOk f (withLsRet mlkemPk2Spec) :=
  h.mlkemPk2_row.ls

theorem GhostRowSpecOk.mlkemPk2_ls_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemPk2Sym f) : HookOk f (withLsRet (withVmPreserved mlkemPk2Spec)) :=
  h.mlkemPk2_row.lsVm

theorem GhostRowSpecOk.mlkemPk2_ls_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemPk2Sym f) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk f (withLsRet (withAlloc A lim mlkemPk2Spec)) :=
  h.mlkemPk2_row.lsAlloc A lim

theorem GhostRowSpecOk.compress256_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsCompress256Sym f) : Compress256RowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  have hd1 : (lsCompress256Sym == "bcmp") = false := by decide
  have hd2 : (lsCompress256Sym == "strlen") = false := by decide
  have hd3 : (lsCompress256Sym == "memmove") = false := by decide
  have hd4 : (lsCompress256Sym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsCompress256Sym == lsMemrchrSym) = false := by decide
  have hd6 : (lsCompress256Sym == lsDurationSinceSym) = false := by decide
  have hd7 : (lsCompress256Sym == lsTimeAddSym) = false := by decide
  have hd8 : (lsCompress256Sym == lsBlackBoxSym) = false := by decide
  have hd9 : (lsCompress256Sym == lsStaticSecretDropSym) = false := by decide
  have hd10 : (lsCompress256Sym == lsSharedSecretDropSym) = false := by decide
  have hd11 : (lsCompress256Sym == lsToEdwardsSym) = false := by decide
  have hd12 : (lsCompress256Sym == lsCompressSym) = false := by decide
  have hd13 : (lsCompress256Sym == lsEdNegSym) = false := by decide
  have hd14 : (lsCompress256Sym == lsTorsionFreeSym) = false := by decide
  have hd15 : (lsCompress256Sym == lsDsmbSym) = false := by decide
  have hd16 : (lsCompress256Sym == lsScalarModSym) = false := by decide
  have hd17 : (lsCompress256Sym == lsScalarWideSym) = false := by decide
  have hd18 : (lsCompress256Sym == lsMlkemPk1Sym) = false := by decide
  have hd19 : (lsCompress256Sym == lsMlkemPk2Sym) = false := by decide
  have hd20 : (lsCompress256Sym == lsCompress256Sym) = true := by decide
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14, hd15,
    hd16, hd17, hd18, hd19, hd20, Bool.false_eq_true, ↓reduceIte] at hp
  exact hp

theorem GhostRowSpecOk.compress256_exact_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsCompress256Sym f) :
    HookOkCompress256 f sha256Compress :=
  h.compress256_row.exact

theorem GhostRowSpecOk.compress256_roBudget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsCompress256Sym f) {stk : Nat}
    (hstk : 176 ≤ stk := by decide) :
    HookOk f (withLsRet (sessionCompress256ROBudgetSpec sha256Compress stk)) :=
  h.compress256_row.roBudget stk hstk

theorem GhostRowSpecOk.compress256_roBudget_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsCompress256Sym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) {stk : Nat}
    (hstk : 176 ≤ stk := by decide) :
    HookOk f (withLsRet (withAlloc A lim (sessionCompress256ROBudgetSpec sha256Compress stk))) :=
  h.compress256_row.roBudget_alloc A lim stk hstk

theorem GhostRowSpecOk.compress256_multi_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsCompress256Sym f) {stk : Nat}
    (hstk : 176 ≤ stk := by decide) :
    HookOk f (withLsRet (withStack (compress256Spec sha256Compress) stk)) :=
  h.compress256_row.multi stk hstk

theorem GhostRowSpecOk.compress256_multi_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsCompress256Sym f) {stk : Nat}
    (hstk : 176 ≤ stk := by decide) :
    HookOk f (withLsRet (withVmPreserved (withStack (compress256Spec sha256Compress) stk))) :=
  h.compress256_row.multi_vm stk hstk

theorem GhostRowSpecOk.compress256_multi_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsCompress256Sym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) {stk : Nat}
    (hstk : 176 ≤ stk := by decide) :
    HookOk f (withLsRet (withAlloc A lim (withStack (compress256Spec sha256Compress) stk))) :=
  h.compress256_row.multi_alloc A lim stk hstk

theorem GhostRowSpecOk.compress256_single_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsCompress256Sym f) {stk : Nat}
    (hstk : 176 ≤ stk := by decide) :
    HookOk f (withLsRet (withStack (compress256RowSingleSpec sha256Compress) stk)) :=
  h.compress256_row.single stk hstk

theorem GhostRowSpecOk.compress256_single_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsCompress256Sym f) {stk : Nat}
    (hstk : 176 ≤ stk := by decide) :
    HookOk f (withLsRet (withVmPreserved (withStack (compress256RowSingleSpec sha256Compress) stk))) :=
  h.compress256_row.single_vm stk hstk

theorem GhostRowSpecOk.compress256_single_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsCompress256Sym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) {stk : Nat}
    (hstk : 176 ≤ stk := by decide) :
    HookOk f (withLsRet (withAlloc A lim (withStack (compress256RowSingleSpec sha256Compress) stk))) :=
  h.compress256_row.single_alloc A lim stk hstk

theorem hookSatCompress256_cliGhostExterns_of_extraOk [LibsignalPlacement]
    (g : CliGhostHooks) (baseExt : String → Option (State → State))
    (hOk : ExtraSpecOk g) :
    HookSatCompress256 (cliGhostExterns g baseExt) lsCompress256Sym sha256Compress := by
  have hDom : cliExtraGhostSyms.contains lsCompress256Sym = true := by decide
  have hSome := hOk.lookup_isSome hDom
  cases hLook : g.extra.lookup lsCompress256Sym with
  | none => rw [hLook] at hSome; cases hSome
  | some f =>
    exact ⟨f, cliGhostExternsWithExtra_extra_some g g.extra baseExt hLook hDom,
      (hOk.ghostRowOk lsCompress256Sym f hLook).compress256_exact_ok⟩

theorem hookSatCompress256_cliGhostExterns_of_extraOk_eq [LibsignalPlacement]
    {F : CryptoGames.HMAC.ShaState → List (BitVec 8) → CryptoGames.HMAC.ShaState}
    (g : CliGhostHooks) (baseExt : String → Option (State → State))
    (hOk : ExtraSpecOk g) (hF : F = sha256Compress) :
    HookSatCompress256 (cliGhostExterns g baseExt) lsCompress256Sym F :=
  hF ▸ hookSatCompress256_cliGhostExterns_of_extraOk g baseExt hOk

theorem GhostRowSpecOk.libcruxHmac_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsLibcruxHmacSym f) : LibcruxHmacRowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  have hd1 : (lsLibcruxHmacSym == "bcmp") = false := by decide
  have hd2 : (lsLibcruxHmacSym == "strlen") = false := by decide
  have hd3 : (lsLibcruxHmacSym == "memmove") = false := by decide
  have hd4 : (lsLibcruxHmacSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsLibcruxHmacSym == lsMemrchrSym) = false := by decide
  have hd6 : (lsLibcruxHmacSym == lsDurationSinceSym) = false := by decide
  have hd7 : (lsLibcruxHmacSym == lsTimeAddSym) = false := by decide
  have hd8 : (lsLibcruxHmacSym == lsBlackBoxSym) = false := by decide
  have hd9 : (lsLibcruxHmacSym == lsStaticSecretDropSym) = false := by decide
  have hd10 : (lsLibcruxHmacSym == lsSharedSecretDropSym) = false := by decide
  have hd11 : (lsLibcruxHmacSym == lsToEdwardsSym) = false := by decide
  have hd12 : (lsLibcruxHmacSym == lsCompressSym) = false := by decide
  have hd13 : (lsLibcruxHmacSym == lsEdNegSym) = false := by decide
  have hd14 : (lsLibcruxHmacSym == lsTorsionFreeSym) = false := by decide
  have hd15 : (lsLibcruxHmacSym == lsDsmbSym) = false := by decide
  have hd16 : (lsLibcruxHmacSym == lsScalarModSym) = false := by decide
  have hd17 : (lsLibcruxHmacSym == lsScalarWideSym) = false := by decide
  have hd18 : (lsLibcruxHmacSym == lsMlkemPk1Sym) = false := by decide
  have hd19 : (lsLibcruxHmacSym == lsMlkemPk2Sym) = false := by decide
  have hd20 : (lsLibcruxHmacSym == lsCompress256Sym) = false := by decide
  have hd21 : (lsLibcruxHmacSym == lsLibcruxHmacSym) = true := by decide
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14, hd15,
    hd16, hd17, hd18, hd19, hd20, hd21, Bool.false_eq_true, ↓reduceIte] at hp
  exact hp

theorem GhostRowSpecOk.aesEnc_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsAesEncSym f) : AesEncRowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  have hd1 : (lsAesEncSym == "bcmp") = false := by decide
  have hd2 : (lsAesEncSym == "strlen") = false := by decide
  have hd3 : (lsAesEncSym == "memmove") = false := by decide
  have hd4 : (lsAesEncSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsAesEncSym == lsMemrchrSym) = false := by decide
  have hd6 : (lsAesEncSym == lsDurationSinceSym) = false := by decide
  have hd7 : (lsAesEncSym == lsTimeAddSym) = false := by decide
  have hd8 : (lsAesEncSym == lsBlackBoxSym) = false := by decide
  have hd9 : (lsAesEncSym == lsStaticSecretDropSym) = false := by decide
  have hd10 : (lsAesEncSym == lsSharedSecretDropSym) = false := by decide
  have hd11 : (lsAesEncSym == lsToEdwardsSym) = false := by decide
  have hd12 : (lsAesEncSym == lsCompressSym) = false := by decide
  have hd13 : (lsAesEncSym == lsEdNegSym) = false := by decide
  have hd14 : (lsAesEncSym == lsTorsionFreeSym) = false := by decide
  have hd15 : (lsAesEncSym == lsDsmbSym) = false := by decide
  have hd16 : (lsAesEncSym == lsScalarModSym) = false := by decide
  have hd17 : (lsAesEncSym == lsScalarWideSym) = false := by decide
  have hd18 : (lsAesEncSym == lsMlkemPk1Sym) = false := by decide
  have hd19 : (lsAesEncSym == lsMlkemPk2Sym) = false := by decide
  have hd20 : (lsAesEncSym == lsCompress256Sym) = false := by decide
  have hd21 : (lsAesEncSym == lsLibcruxHmacSym) = false := by decide
  have hd22 : (lsAesEncSym == lsAesEncSym) = true := by decide
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14, hd15,
    hd16, hd17, hd18, hd19, hd20, hd21, hd22, Bool.false_eq_true, ↓reduceIte] at hp
  exact hp

theorem GhostRowSpecOk.aesDec_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsAesDecSym f) : AesDecRowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  have hd1 : (lsAesDecSym == "bcmp") = false := by decide
  have hd2 : (lsAesDecSym == "strlen") = false := by decide
  have hd3 : (lsAesDecSym == "memmove") = false := by decide
  have hd4 : (lsAesDecSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsAesDecSym == lsMemrchrSym) = false := by decide
  have hd6 : (lsAesDecSym == lsDurationSinceSym) = false := by decide
  have hd7 : (lsAesDecSym == lsTimeAddSym) = false := by decide
  have hd8 : (lsAesDecSym == lsBlackBoxSym) = false := by decide
  have hd9 : (lsAesDecSym == lsStaticSecretDropSym) = false := by decide
  have hd10 : (lsAesDecSym == lsSharedSecretDropSym) = false := by decide
  have hd11 : (lsAesDecSym == lsToEdwardsSym) = false := by decide
  have hd12 : (lsAesDecSym == lsCompressSym) = false := by decide
  have hd13 : (lsAesDecSym == lsEdNegSym) = false := by decide
  have hd14 : (lsAesDecSym == lsTorsionFreeSym) = false := by decide
  have hd15 : (lsAesDecSym == lsDsmbSym) = false := by decide
  have hd16 : (lsAesDecSym == lsScalarModSym) = false := by decide
  have hd17 : (lsAesDecSym == lsScalarWideSym) = false := by decide
  have hd18 : (lsAesDecSym == lsMlkemPk1Sym) = false := by decide
  have hd19 : (lsAesDecSym == lsMlkemPk2Sym) = false := by decide
  have hd20 : (lsAesDecSym == lsCompress256Sym) = false := by decide
  have hd21 : (lsAesDecSym == lsLibcruxHmacSym) = false := by decide
  have hd22 : (lsAesDecSym == lsAesEncSym) = false := by decide
  have hd23 : (lsAesDecSym == lsAesDecSym) = true := by decide
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14, hd15,
    hd16, hd17, hd18, hd19, hd20, hd21, hd22, hd23, Bool.false_eq_true, ↓reduceIte] at hp
  exact hp

/-! ### Row Projections for `compress512`, `libcrux_ml_kem`, `write_*`, `fmt`, and `X25519` -/

theorem GhostRowSpecOk.compress512_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsCompress512Sym f) : Compress512RowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  repeat rw [ite_eq_right (by decide)] at hp
  rw [ite_eq_left (by decide)] at hp
  exact hp

theorem GhostRowSpecOk.compress512_stackedMaster_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsCompress512Sym f) {stk : Nat} (hstk : 256 ≤ stk := by decide) :
    HookOk f (withLsRet (compress512StackedMasterSpec stk)) :=
  h.compress512_row.stackedMaster stk hstk

theorem GhostRowSpecOk.compress512_stackedMaster_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsCompress512Sym f) {stk : Nat} (hstk : 256 ≤ stk := by decide) :
    HookOk f (withLsRet (withVmPreserved (compress512StackedMasterSpec stk))) :=
  h.compress512_row.stackedMaster_vm stk hstk

theorem GhostRowSpecOk.compress512_stackedMaster_ls_withAlloc_ok [LibsignalPlacement]
    {f : State → State} (h : GhostRowSpecOk lsCompress512Sym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) {stk : Nat}
    (hstk : 256 ≤ stk := by decide) :
    HookOk f (withLsRet (withAlloc A lim (compress512StackedMasterSpec stk))) :=
  h.compress512_row.stackedMaster_alloc A lim stk hstk

theorem GhostRowSpecOk.compress512_stackedMaster_withAlloc_ok [LibsignalPlacement]
    {f : State → State} (h : GhostRowSpecOk lsCompress512Sym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) {stk : Nat}
    (hstk : 256 ≤ stk := by decide) :
    HookOk f (withAlloc A lim (withLsRet (compress512StackedMasterSpec stk))) :=
  h.compress512_row.stackedMaster_alloc_ls A lim stk hstk

theorem GhostRowSpecOk.compress512_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsCompress512Sym f) {Q : PqxdhPrims}
    (hF : Q.F512 = sha512CompressState) :
    HookOk f (withLsRet (CryptoVerification.SignalSession.CliExt.compress512Spec Q)) :=
  h.compress512_row.cliExt_ls hF

theorem GhostRowSpecOk.compress512_keepsFs_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsCompress512Sym f) {Q : PqxdhPrims}
    (hF : Q.F512 = sha512CompressState) :
    HookOk f (withLsRet (keepsFs (CryptoVerification.SignalSession.CliExt.compress512Spec Q))) :=
  h.compress512_row.cliExt_keepsFs hF

theorem GhostRowSpecOk.compress512_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsCompress512Sym f) {Q : PqxdhPrims}
    (hF : Q.F512 = sha512CompressState) :
    HookOk f
      (withLsRet (withVmPreserved (CryptoVerification.SignalSession.CliExt.compress512Spec Q))) :=
  h.compress512_row.cliExt_vm hF

theorem GhostRowSpecOk.compress512_ls_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsCompress512Sym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) {Q : PqxdhPrims}
    (hF : Q.F512 = sha512CompressState) :
    HookOk f
      (withLsRet (withAlloc A lim (CryptoVerification.SignalSession.CliExt.compress512Spec Q))) :=
  h.compress512_row.cliExt_alloc A lim hF

theorem GhostRowSpecOk.compress512_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsCompress512Sym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) {Q : PqxdhPrims}
    (hF : Q.F512 = sha512CompressState) :
    HookOk f
      (withAlloc A lim (withLsRet (CryptoVerification.SignalSession.CliExt.compress512Spec Q))) :=
  h.compress512_row.cliExt_alloc_ls A lim hF

theorem GhostRowSpecOk.compress512_pqxdhStubPlaced_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsCompress512Sym f) (X : UnreachedPqxdhPrimitives) {P0 : PEParams}
    (hF : P0.Q.F512 = sha512CompressState) :
    HookOk f
      (withLsRet (compressInPlaceStubSpecPlaced (sha512CompressOutBytes (modelPrims X P0)) 64 128)) :=
  h.compress512_row.pqxdhStubPlaced_ls X hF

theorem GhostRowSpecOk.compress512_pqxdhStubPlaced_keepsFs_ok [LibsignalPlacement]
    {f : State → State} (h : GhostRowSpecOk lsCompress512Sym f)
    (X : UnreachedPqxdhPrimitives) {P0 : PEParams} (hF : P0.Q.F512 = sha512CompressState) :
    HookOk f (withLsRet (keepsFs
      (compressInPlaceStubSpecPlaced (sha512CompressOutBytes (modelPrims X P0)) 64 128))) :=
  h.compress512_row.pqxdhStubPlaced_keepsFs X hF

theorem GhostRowSpecOk.compress512_pqxdhStubPlaced_budget_ok [LibsignalPlacement]
    {f : State → State} (h : GhostRowSpecOk lsCompress512Sym f)
    (X : UnreachedPqxdhPrimitives) {P0 : PEParams} (hF : P0.Q.F512 = sha512CompressState) :
    HookOk f (withLsRet (withVmPreserved
      (compressInPlaceStubSpecPlaced (sha512CompressOutBytes (modelPrims X P0)) 64 128))) :=
  h.compress512_row.pqxdhStubPlaced_vm X hF

theorem GhostRowSpecOk.compress512_pqxdhStubPlaced_ls_withAlloc_ok [LibsignalPlacement]
    {f : State → State} (h : GhostRowSpecOk lsCompress512Sym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (X : UnreachedPqxdhPrimitives) {P0 : PEParams} (hF : P0.Q.F512 = sha512CompressState) :
    HookOk f (withLsRet (withAlloc A lim
      (compressInPlaceStubSpecPlaced (sha512CompressOutBytes (modelPrims X P0)) 64 128))) :=
  h.compress512_row.pqxdhStubPlaced_alloc A lim X hF

theorem GhostRowSpecOk.compress512_pqxdhStubPlaced_withAlloc_ok [LibsignalPlacement]
    {f : State → State} (h : GhostRowSpecOk lsCompress512Sym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (X : UnreachedPqxdhPrimitives) {P0 : PEParams} (hF : P0.Q.F512 = sha512CompressState) :
    HookOk f (withAlloc A lim (withLsRet
      (compressInPlaceStubSpecPlaced (sha512CompressOutBytes (modelPrims X P0)) 64 128))) :=
  h.compress512_row.pqxdhStubPlaced_alloc_ls A lim X hF

-- `lsKemEncapsSym` (`KemEncapsRowSpecAt kemEncapsTightStack`):
theorem GhostRowSpecOk.kemEncaps_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsKemEncapsSym f) : KemEncapsRowSpecAt kemEncapsTightStack f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  repeat rw [ite_eq_right (by decide)] at hp
  rw [ite_eq_left (by decide)] at hp
  exact hp

theorem GhostRowSpecOk.kemEncapsPreserved_tuple [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsKemEncapsSym f) (stk : Nat := mlkemHookStack)
    (hlo : kemEncapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} (hQ : Q.encaps = kyber1024EncapsVec) :
    DalekLsRowTuple f (kemEncapsPreservedAtSpec stk Q) :=
  (h.kemEncaps_row.mono hlo hhi).for_Q_preserved hQ

theorem GhostRowSpecOk.kemEncaps_tuple [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsKemEncapsSym f) (stk : Nat := mlkemHookStack)
    (hlo : kemEncapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} (hQ : Q.encaps = kyber1024EncapsVec) :
    DalekLsRowTuple f (kemEncapsAtSpec stk Q) :=
  (h.kemEncaps_row.mono hlo hhi).for_Q hQ

theorem GhostRowSpecOk.kemEncapsPreserved_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsKemEncapsSym f) (stk : Nat := mlkemHookStack)
    (hlo : kemEncapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} (hQ : Q.encaps = kyber1024EncapsVec) :
    HookOk f (withLsRet (kemEncapsPreservedAtSpec stk Q)) :=
  (h.kemEncapsPreserved_tuple stk hlo hhi hQ).plain

theorem GhostRowSpecOk.kemEncapsPreserved_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsKemEncapsSym f) (stk : Nat := mlkemHookStack)
    (hlo : kemEncapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} (hQ : Q.encaps = kyber1024EncapsVec) :
    HookOk f (withLsRet (withVmPreserved (kemEncapsPreservedAtSpec stk Q))) :=
  (h.kemEncapsPreserved_tuple stk hlo hhi hQ).vm

theorem GhostRowSpecOk.kemEncapsPreserved_keepsFs_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsKemEncapsSym f) (stk : Nat := mlkemHookStack)
    (hlo : kemEncapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} (hQ : Q.encaps = kyber1024EncapsVec) :
    HookOk f (withLsRet (withVmPreserved (keepsFs (kemEncapsPreservedAtSpec stk Q)))) :=
  (h.kemEncapsPreserved_tuple stk hlo hhi hQ).keepsFsVm

theorem GhostRowSpecOk.kemEncapsPreserved_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsKemEncapsSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := mlkemHookStack)
    (hlo : kemEncapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} (hQ : Q.encaps = kyber1024EncapsVec) :
    HookOk f (withAlloc A lim (withLsRet (kemEncapsPreservedAtSpec stk Q))) :=
  (h.kemEncapsPreserved_tuple stk hlo hhi hQ).alloc A lim

theorem GhostRowSpecOk.kemEncapsPreserved_ls_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsKemEncapsSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := mlkemHookStack)
    (hlo : kemEncapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} (hQ : Q.encaps = kyber1024EncapsVec) :
    HookOk f (withLsRet (withAlloc A lim (kemEncapsPreservedAtSpec stk Q))) :=
  (h.kemEncapsPreserved_tuple stk hlo hhi hQ).withLsRetAlloc A lim

theorem GhostRowSpecOk.kemEncaps_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsKemEncapsSym f) (stk : Nat := mlkemHookStack)
    (hlo : kemEncapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} (hQ : Q.encaps = kyber1024EncapsVec) :
    HookOk f (withLsRet (kemEncapsAtSpec stk Q)) :=
  (h.kemEncaps_tuple stk hlo hhi hQ).plain

theorem GhostRowSpecOk.kemEncaps_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsKemEncapsSym f) (stk : Nat := mlkemHookStack)
    (hlo : kemEncapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} (hQ : Q.encaps = kyber1024EncapsVec) :
    HookOk f (withLsRet (withVmPreserved (kemEncapsAtSpec stk Q))) :=
  (h.kemEncaps_tuple stk hlo hhi hQ).vm

theorem GhostRowSpecOk.kemEncaps_keepsFs_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsKemEncapsSym f) (stk : Nat := mlkemHookStack)
    (hlo : kemEncapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} (hQ : Q.encaps = kyber1024EncapsVec) :
    HookOk f (withLsRet (withVmPreserved (keepsFs (kemEncapsAtSpec stk Q)))) :=
  (h.kemEncaps_tuple stk hlo hhi hQ).keepsFsVm

theorem GhostRowSpecOk.kemEncaps_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsKemEncapsSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := mlkemHookStack)
    (hlo : kemEncapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} (hQ : Q.encaps = kyber1024EncapsVec) :
    HookOk f (withAlloc A lim (withLsRet (kemEncapsAtSpec stk Q))) :=
  (h.kemEncaps_tuple stk hlo hhi hQ).alloc A lim

theorem GhostRowSpecOk.kemEncaps_ls_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsKemEncapsSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := mlkemHookStack)
    (hlo : kemEncapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} (hQ : Q.encaps = kyber1024EncapsVec) :
    HookOk f (withLsRet (withAlloc A lim (kemEncapsAtSpec stk Q))) :=
  (h.kemEncaps_tuple stk hlo hhi hQ).withLsRetAlloc A lim

-- `lsKemDecapsSym` (`KemDecapsRowSpecAt kemDecapsTightStack`):
theorem GhostRowSpecOk.kemDecaps_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsKemDecapsSym f) : KemDecapsRowSpecAt kemDecapsTightStack f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  repeat rw [ite_eq_right (by decide)] at hp
  rw [ite_eq_left (by decide)] at hp
  exact hp

theorem GhostRowSpecOk.kemDecaps_tuple [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsKemDecapsSym f) (stk : Nat := mlkemHookStack)
    (hlo : kemDecapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} (hQ : Q.decaps = kyber1024DecapsVec) :
    DalekLsRowTuple f (kemDecapsAtSpec stk Q) :=
  (h.kemDecaps_row.mono hlo hhi).for_Q hQ

theorem GhostRowSpecOk.kemDecaps_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsKemDecapsSym f) (stk : Nat := mlkemHookStack)
    (hlo : kemDecapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} (hQ : Q.decaps = kyber1024DecapsVec) :
    HookOk f (withLsRet (kemDecapsAtSpec stk Q)) :=
  (h.kemDecaps_tuple stk hlo hhi hQ).plain

theorem GhostRowSpecOk.kemDecaps_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsKemDecapsSym f) (stk : Nat := mlkemHookStack)
    (hlo : kemDecapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} (hQ : Q.decaps = kyber1024DecapsVec) :
    HookOk f (withLsRet (withVmPreserved (kemDecapsAtSpec stk Q))) :=
  (h.kemDecaps_tuple stk hlo hhi hQ).vm

theorem GhostRowSpecOk.kemDecaps_keepsFs_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsKemDecapsSym f) (stk : Nat := mlkemHookStack)
    (hlo : kemDecapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} (hQ : Q.decaps = kyber1024DecapsVec) :
    HookOk f (withLsRet (withVmPreserved (keepsFs (kemDecapsAtSpec stk Q)))) :=
  (h.kemDecaps_tuple stk hlo hhi hQ).keepsFsVm

theorem GhostRowSpecOk.kemDecaps_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsKemDecapsSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := mlkemHookStack)
    (hlo : kemDecapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} (hQ : Q.decaps = kyber1024DecapsVec) :
    HookOk f (withAlloc A lim (withLsRet (kemDecapsAtSpec stk Q))) :=
  (h.kemDecaps_tuple stk hlo hhi hQ).alloc A lim

theorem GhostRowSpecOk.kemDecaps_ls_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsKemDecapsSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := mlkemHookStack)
    (hlo : kemDecapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {Q : PqxdhPrims} (hQ : Q.decaps = kyber1024DecapsVec) :
    HookOk f (withLsRet (withAlloc A lim (kemDecapsAtSpec stk Q))) :=
  (h.kemDecaps_tuple stk hlo hhi hQ).withLsRetAlloc A lim

-- `lsMlkemFromSeedSym` (`MlkemFromSeedRowSpecAt mlkemFromSeedTightStack`):
theorem GhostRowSpecOk.mlkemFromSeed_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemFromSeedSym f) : MlkemFromSeedRowSpecAt mlkemFromSeedTightStack f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  repeat rw [ite_eq_right (by decide)] at hp
  rw [ite_eq_left (by decide)] at hp
  exact hp

theorem GhostRowSpecOk.mlkemFromSeed_tuple [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemFromSeedSym f) (stk : Nat := mlkemHookStack)
    (hlo : mlkemFromSeedTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    DalekLsRowTuple f (mlkemFromSeedAtSpec stk K) :=
  (h.mlkemFromSeed_row.mono hlo hhi).for_K hK

theorem GhostRowSpecOk.mlkemFromSeed_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemFromSeedSym f) (stk : Nat := mlkemHookStack)
    (hlo : mlkemFromSeedTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withLsRet (mlkemFromSeedAtSpec stk K)) :=
  (h.mlkemFromSeed_tuple stk hlo hhi hK).plain

theorem GhostRowSpecOk.mlkemFromSeed_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemFromSeedSym f) (stk : Nat := mlkemHookStack)
    (hlo : mlkemFromSeedTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withLsRet (withVmPreserved (mlkemFromSeedAtSpec stk K))) :=
  (h.mlkemFromSeed_tuple stk hlo hhi hK).vm

theorem GhostRowSpecOk.mlkemFromSeed_keepsFs_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemFromSeedSym f) (stk : Nat := mlkemHookStack)
    (hlo : mlkemFromSeedTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withLsRet (withVmPreserved (keepsFs (mlkemFromSeedAtSpec stk K)))) :=
  (h.mlkemFromSeed_tuple stk hlo hhi hK).keepsFsVm

theorem GhostRowSpecOk.mlkemFromSeed_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemFromSeedSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemFromSeedTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withAlloc A lim (withLsRet (mlkemFromSeedAtSpec stk K))) :=
  (h.mlkemFromSeed_tuple stk hlo hhi hK).alloc A lim

theorem GhostRowSpecOk.mlkemFromSeed_ls_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemFromSeedSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemFromSeedTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withLsRet (withAlloc A lim (mlkemFromSeedAtSpec stk K))) :=
  (h.mlkemFromSeed_tuple stk hlo hhi hK).withLsRetAlloc A lim

-- `lsMlkemEncaps1Sym` (`MlkemEncaps1RowSpecAt mlkemEncaps1TightStack`):
theorem GhostRowSpecOk.mlkemEncaps1_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemEncaps1Sym f) : MlkemEncaps1RowSpecAt mlkemEncaps1TightStack f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  repeat rw [ite_eq_right (by decide)] at hp
  rw [ite_eq_left (by decide)] at hp
  exact hp

theorem GhostRowSpecOk.mlkemEncaps1_tuple [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemEncaps1Sym f) (stk : Nat := mlkemHookStack)
    (hlo : mlkemEncaps1TightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    DalekLsRowTuple f (mlkemEncaps1AtSpec stk K) :=
  (h.mlkemEncaps1_row.mono hlo hhi).for_K hK

theorem GhostRowSpecOk.mlkemEncaps1_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemEncaps1Sym f) (stk : Nat := mlkemHookStack)
    (hlo : mlkemEncaps1TightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withLsRet (mlkemEncaps1AtSpec stk K)) :=
  (h.mlkemEncaps1_tuple stk hlo hhi hK).plain

theorem GhostRowSpecOk.mlkemEncaps1_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemEncaps1Sym f) (stk : Nat := mlkemHookStack)
    (hlo : mlkemEncaps1TightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withLsRet (withVmPreserved (mlkemEncaps1AtSpec stk K))) :=
  (h.mlkemEncaps1_tuple stk hlo hhi hK).vm

theorem GhostRowSpecOk.mlkemEncaps1_keepsFs_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemEncaps1Sym f) (stk : Nat := mlkemHookStack)
    (hlo : mlkemEncaps1TightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withLsRet (withVmPreserved (keepsFs (mlkemEncaps1AtSpec stk K)))) :=
  (h.mlkemEncaps1_tuple stk hlo hhi hK).keepsFsVm

theorem GhostRowSpecOk.mlkemEncaps1_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemEncaps1Sym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemEncaps1TightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withAlloc A lim (withLsRet (mlkemEncaps1AtSpec stk K))) :=
  (h.mlkemEncaps1_tuple stk hlo hhi hK).alloc A lim

theorem GhostRowSpecOk.mlkemEncaps1_ls_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemEncaps1Sym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemEncaps1TightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withLsRet (withAlloc A lim (mlkemEncaps1AtSpec stk K))) :=
  (h.mlkemEncaps1_tuple stk hlo hhi hK).withLsRetAlloc A lim

-- `lsMlkemEncaps2Sym` (`MlkemEncaps2RowSpecAt mlkemEncaps2TightStack`):
theorem GhostRowSpecOk.mlkemEncaps2_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemEncaps2Sym f) : MlkemEncaps2RowSpecAt mlkemEncaps2TightStack f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  repeat rw [ite_eq_right (by decide)] at hp
  rw [ite_eq_left (by decide)] at hp
  exact hp

theorem GhostRowSpecOk.mlkemEncaps2_extTuple [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemEncaps2Sym f) {K : MlKem} (hK : K = mlkem768Incremental) :
    DalekLsRowTuple f (mlkemEncaps2Spec K) :=
  h.mlkemEncaps2_row.at_extHookStack hK

theorem GhostRowSpecOk.mlkemEncaps2_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemEncaps2Sym f) {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withLsRet (mlkemEncaps2Spec K)) :=
  (h.mlkemEncaps2_extTuple hK).plain

theorem GhostRowSpecOk.mlkemEncaps2_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemEncaps2Sym f) {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withLsRet (withVmPreserved (mlkemEncaps2Spec K))) :=
  (h.mlkemEncaps2_extTuple hK).vm

theorem GhostRowSpecOk.mlkemEncaps2_keepsFs_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemEncaps2Sym f) {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withLsRet (withVmPreserved (keepsFs (mlkemEncaps2Spec K)))) :=
  (h.mlkemEncaps2_extTuple hK).keepsFsVm

theorem GhostRowSpecOk.mlkemEncaps2_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemEncaps2Sym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withAlloc A lim (withLsRet (mlkemEncaps2Spec K))) :=
  (h.mlkemEncaps2_extTuple hK).alloc A lim

theorem GhostRowSpecOk.mlkemEncaps2_ls_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemEncaps2Sym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withLsRet (withAlloc A lim (mlkemEncaps2Spec K))) :=
  (h.mlkemEncaps2_extTuple hK).withLsRetAlloc A lim

theorem GhostRowSpecOk.mlkemEncaps2At_tuple [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemEncaps2Sym f) (stk : Nat := mlkemHookStack)
    (hlo : mlkemEncaps2TightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    DalekLsRowTuple f (mlkemEncaps2AtSpec stk K) :=
  (h.mlkemEncaps2_row.mono hlo hhi).for_K hK

theorem GhostRowSpecOk.mlkemEncaps2At_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemEncaps2Sym f) (stk : Nat := mlkemHookStack)
    (hlo : mlkemEncaps2TightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withLsRet (mlkemEncaps2AtSpec stk K)) :=
  (h.mlkemEncaps2At_tuple stk hlo hhi hK).plain

theorem GhostRowSpecOk.mlkemEncaps2At_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemEncaps2Sym f) (stk : Nat := mlkemHookStack)
    (hlo : mlkemEncaps2TightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withLsRet (withVmPreserved (mlkemEncaps2AtSpec stk K))) :=
  (h.mlkemEncaps2At_tuple stk hlo hhi hK).vm

theorem GhostRowSpecOk.mlkemEncaps2At_keepsFs_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemEncaps2Sym f) (stk : Nat := mlkemHookStack)
    (hlo : mlkemEncaps2TightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withLsRet (withVmPreserved (keepsFs (mlkemEncaps2AtSpec stk K)))) :=
  (h.mlkemEncaps2At_tuple stk hlo hhi hK).keepsFsVm

theorem GhostRowSpecOk.mlkemEncaps2At_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemEncaps2Sym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemEncaps2TightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withAlloc A lim (withLsRet (mlkemEncaps2AtSpec stk K))) :=
  (h.mlkemEncaps2At_tuple stk hlo hhi hK).alloc A lim

theorem GhostRowSpecOk.mlkemEncaps2At_ls_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemEncaps2Sym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemEncaps2TightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withLsRet (withAlloc A lim (mlkemEncaps2AtSpec stk K))) :=
  (h.mlkemEncaps2At_tuple stk hlo hhi hK).withLsRetAlloc A lim

-- `lsMlkemDecapsSym` (`MlkemDecapsRowSpecAt mlkemDecapsTightStack`):
theorem GhostRowSpecOk.mlkemDecaps_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemDecapsSym f) : MlkemDecapsRowSpecAt mlkemDecapsTightStack f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  repeat rw [ite_eq_right (by decide)] at hp
  rw [ite_eq_left (by decide)] at hp
  exact hp

theorem GhostRowSpecOk.mlkemDecapsAt_tuple [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemDecapsSym f) (stk : Nat := mlkemHookStack)
    (hlo : mlkemDecapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    DalekLsRowTuple f (mlkemDecapsAtSpec stk K) :=
  (h.mlkemDecaps_row.mono hlo hhi).for_K hK

theorem GhostRowSpecOk.mlkemDecapsAt_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemDecapsSym f) (stk : Nat := mlkemHookStack)
    (hlo : mlkemDecapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withLsRet (mlkemDecapsAtSpec stk K)) :=
  (h.mlkemDecapsAt_tuple stk hlo hhi hK).plain

theorem GhostRowSpecOk.mlkemDecapsAt_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemDecapsSym f) (stk : Nat := mlkemHookStack)
    (hlo : mlkemDecapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withLsRet (withVmPreserved (mlkemDecapsAtSpec stk K))) :=
  (h.mlkemDecapsAt_tuple stk hlo hhi hK).vm

theorem GhostRowSpecOk.mlkemDecapsAt_keepsFs_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemDecapsSym f) (stk : Nat := mlkemHookStack)
    (hlo : mlkemDecapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withLsRet (withVmPreserved (keepsFs (mlkemDecapsAtSpec stk K)))) :=
  (h.mlkemDecapsAt_tuple stk hlo hhi hK).keepsFsVm

theorem GhostRowSpecOk.mlkemDecapsAt_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemDecapsSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemDecapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withAlloc A lim (withLsRet (mlkemDecapsAtSpec stk K))) :=
  (h.mlkemDecapsAt_tuple stk hlo hhi hK).alloc A lim

theorem GhostRowSpecOk.mlkemDecapsAt_ls_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemDecapsSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemDecapsTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withLsRet (withAlloc A lim (mlkemDecapsAtSpec stk K))) :=
  (h.mlkemDecapsAt_tuple stk hlo hhi hK).withLsRetAlloc A lim

-- `lsMlkemValidatePkSym` (`MlkemValidatePkRowSpecAt mlkemValidatePkTightStack`):
theorem GhostRowSpecOk.mlkemValidatePk_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemValidatePkSym f) :
    MlkemValidatePkRowSpecAt mlkemValidatePkTightStack f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  repeat rw [ite_eq_right (by decide)] at hp
  rw [ite_eq_left (by decide)] at hp
  exact hp

theorem GhostRowSpecOk.mlkemValidatePk_extTuple [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemValidatePkSym f) {K : MlKem} (hK : K = mlkem768Incremental) :
    DalekLsRowTuple f (mlkemValidatePkSpec K) :=
  h.mlkemValidatePk_row.at_extHookStack hK

theorem GhostRowSpecOk.mlkemValidatePk_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemValidatePkSym f) {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withLsRet (mlkemValidatePkSpec K)) :=
  (h.mlkemValidatePk_extTuple hK).plain

theorem GhostRowSpecOk.mlkemValidatePk_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemValidatePkSym f) {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withLsRet (withVmPreserved (mlkemValidatePkSpec K))) :=
  (h.mlkemValidatePk_extTuple hK).vm

theorem GhostRowSpecOk.mlkemValidatePk_keepsFs_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemValidatePkSym f) {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withLsRet (withVmPreserved (keepsFs (mlkemValidatePkSpec K)))) :=
  (h.mlkemValidatePk_extTuple hK).keepsFsVm

theorem GhostRowSpecOk.mlkemValidatePk_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemValidatePkSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withAlloc A lim (withLsRet (mlkemValidatePkSpec K))) :=
  (h.mlkemValidatePk_extTuple hK).alloc A lim

theorem GhostRowSpecOk.mlkemValidatePk_ls_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemValidatePkSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withLsRet (withAlloc A lim (mlkemValidatePkSpec K))) :=
  (h.mlkemValidatePk_extTuple hK).withLsRetAlloc A lim

theorem GhostRowSpecOk.mlkemValidatePkAt_tuple [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemValidatePkSym f) (stk : Nat := mlkemHookStack)
    (hlo : mlkemValidatePkTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    DalekLsRowTuple f (mlkemValidatePkAtSpec stk K) :=
  (h.mlkemValidatePk_row.mono hlo hhi).for_K hK

theorem GhostRowSpecOk.mlkemValidatePkAt_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemValidatePkSym f) (stk : Nat := mlkemHookStack)
    (hlo : mlkemValidatePkTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withLsRet (mlkemValidatePkAtSpec stk K)) :=
  (h.mlkemValidatePkAt_tuple stk hlo hhi hK).plain

theorem GhostRowSpecOk.mlkemValidatePkAt_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemValidatePkSym f) (stk : Nat := mlkemHookStack)
    (hlo : mlkemValidatePkTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withLsRet (withVmPreserved (mlkemValidatePkAtSpec stk K))) :=
  (h.mlkemValidatePkAt_tuple stk hlo hhi hK).vm

theorem GhostRowSpecOk.mlkemValidatePkAt_keepsFs_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemValidatePkSym f) (stk : Nat := mlkemHookStack)
    (hlo : mlkemValidatePkTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withLsRet (withVmPreserved (keepsFs (mlkemValidatePkAtSpec stk K)))) :=
  (h.mlkemValidatePkAt_tuple stk hlo hhi hK).keepsFsVm

theorem GhostRowSpecOk.mlkemValidatePkAt_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemValidatePkSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemValidatePkTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withAlloc A lim (withLsRet (mlkemValidatePkAtSpec stk K))) :=
  (h.mlkemValidatePkAt_tuple stk hlo hhi hK).alloc A lim

theorem GhostRowSpecOk.mlkemValidatePkAt_ls_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsMlkemValidatePkSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := mlkemHookStack)
    (hlo : mlkemValidatePkTightStack ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide)
    {K : MlKem} (hK : K = mlkem768Incremental) :
    HookOk f (withLsRet (withAlloc A lim (mlkemValidatePkAtSpec stk K))) :=
  (h.mlkemValidatePkAt_tuple stk hlo hhi hK).withLsRetAlloc A lim

-- `lsWriteFileSym`, `lsWriteStdoutSym`, `lsFmtWriteSym`, `lsFormatInnerSym`:
theorem ExtraRowOk.writeFile_row [LibsignalPlacement] {f : State → State}
    (h : ExtraRowOk lsWriteFileSym f) : WriteFileRowSpec f :=
  h.toWriteFileRowOk.rowSpec

theorem GhostRowSpecOk.writeFile_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsWriteFileSym f) : WriteFileRowSpec f :=
  h.toExtraRowOk.writeFile_row

theorem GhostRowSpecOk.writeStdout_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsWriteStdoutSym f) : WriteStdoutRowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  iterate 20 rw [ite_eq_right (by decide)] at hp
  repeat rw [ite_eq_right (by decide)] at hp
  rw [ite_eq_left (by decide)] at hp
  exact hp

theorem GhostRowSpecOk.fmtWrite_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsFmtWriteSym f) : FmtWriteRowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  iterate 20 rw [ite_eq_right (by decide)] at hp
  repeat rw [ite_eq_right (by decide)] at hp
  rw [ite_eq_left (by decide)] at hp
  exact hp

theorem GhostRowSpecOk.formatInner_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsFormatInnerSym f) : FormatInnerRowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  iterate 20 rw [ite_eq_right (by decide)] at hp
  repeat rw [ite_eq_right (by decide)] at hp
  rw [ite_eq_left (by decide)] at hp
  exact hp

-- `lsPubFromSecretSym` (`X25519PubFromSecretRowSpec`):
theorem GhostRowSpecOk.pubFromSecret_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsPubFromSecretSym f) : X25519PubFromSecretRowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  iterate 35 rw [ite_eq_right (by decide)] at hp
  rw [ite_eq_left (by decide)] at hp
  exact hp

theorem GhostRowSpecOk.pubFromSecretWithStack_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsPubFromSecretSym f) (stk : Nat := extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (CryptoVerification.SignalSession.CliExt.withStack
      (pubFromSecretSpec x25519PubFromSecretRef) stk)) :=
  h.pubFromSecret_row.withStack_ls stk hlo hhi

theorem GhostRowSpecOk.pubFromSecretWithStack_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsPubFromSecretSym f) (stk : Nat := extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withVmPreserved (CryptoVerification.SignalSession.CliExt.withStack
      (pubFromSecretSpec x25519PubFromSecretRef) stk))) :=
  h.pubFromSecret_row.withStack_vm stk hlo hhi

theorem GhostRowSpecOk.pubFromSecretWithStack_keepsFs_budget_ok [LibsignalPlacement]
    {f : State → State} (h : GhostRowSpecOk lsPubFromSecretSym f) (stk : Nat := extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withVmPreserved (keepsFs
      (CryptoVerification.SignalSession.CliExt.withStack
        (pubFromSecretSpec x25519PubFromSecretRef) stk)))) :=
  h.pubFromSecret_row.withStack_keepsFs stk hlo hhi

theorem GhostRowSpecOk.pubFromSecretWithStack_ls_withAlloc_ok [LibsignalPlacement]
    {f : State → State} (h : GhostRowSpecOk lsPubFromSecretSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := extHookStack) (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withAlloc A lim (CryptoVerification.SignalSession.CliExt.withStack
      (pubFromSecretSpec x25519PubFromSecretRef) stk))) :=
  h.pubFromSecret_row.withStack_alloc A lim stk hlo hhi

theorem GhostRowSpecOk.pubFromSecretWithStack_withAlloc_ok [LibsignalPlacement]
    {f : State → State} (h : GhostRowSpecOk lsPubFromSecretSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := extHookStack) (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withAlloc A lim (withLsRet (CryptoVerification.SignalSession.CliExt.withStack
      (pubFromSecretSpec x25519PubFromSecretRef) stk))) :=
  h.pubFromSecret_row.withStack_alloc_ls A lim stk hlo hhi

theorem GhostRowSpecOk.pubFromSecret_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsPubFromSecretSym f) {C : Crypto}
    (hC : C.pubKey = x25519PubFromSecretRef) :
    HookOk f (withLsRet (CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C)) :=
  h.pubFromSecret_row.cliExt_ls hC

theorem GhostRowSpecOk.pubFromSecret_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsPubFromSecretSym f) {C : Crypto}
    (hC : C.pubKey = x25519PubFromSecretRef) :
    HookOk f
      (withLsRet (withVmPreserved (CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C))) :=
  h.pubFromSecret_row.cliExt_vm hC

theorem GhostRowSpecOk.pubFromSecret_keepsFs_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsPubFromSecretSym f) {C : Crypto}
    (hC : C.pubKey = x25519PubFromSecretRef) :
    HookOk f (withLsRet (withVmPreserved
      (keepsFs (CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C)))) :=
  h.pubFromSecret_row.cliExt_keepsFs hC

theorem GhostRowSpecOk.pubFromSecret_ls_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsPubFromSecretSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {C : Crypto} (hC : C.pubKey = x25519PubFromSecretRef) :
    HookOk f
      (withLsRet (withAlloc A lim (CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C))) :=
  h.pubFromSecret_row.cliExt_alloc A lim hC

theorem GhostRowSpecOk.pubFromSecret_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsPubFromSecretSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {C : Crypto} (hC : C.pubKey = x25519PubFromSecretRef) :
    HookOk f
      (withAlloc A lim (withLsRet (CryptoVerification.SignalSession.CliExt.pubFromSecretSpec C))) :=
  h.pubFromSecret_row.cliExt_alloc_ls A lim hC

theorem GhostRowSpecOk.pubFromSecretPureByte_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsPubFromSecretSym f) (byVal : Bool := false) :
    HookOk f (withLsRet (pureByteFunctionSpec x25519PubFromSecretRef byVal)) :=
  h.pubFromSecret_row.pureByteFunction_ls byVal

theorem GhostRowSpecOk.pubFromSecretPureByte_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsPubFromSecretSym f) (byVal : Bool := false) :
    HookOk f (withLsRet (withVmPreserved (pureByteFunctionSpec x25519PubFromSecretRef byVal))) :=
  h.pubFromSecret_row.pureByteFunction_vm byVal

theorem GhostRowSpecOk.pubFromSecretPureByte_keepsFs_budget_ok [LibsignalPlacement]
    {f : State → State} (h : GhostRowSpecOk lsPubFromSecretSym f) (byVal : Bool := false) :
    HookOk f (withLsRet (withVmPreserved
      (keepsFs (pureByteFunctionSpec x25519PubFromSecretRef byVal)))) :=
  h.pubFromSecret_row.pureByteFunction_keepsFs byVal

theorem GhostRowSpecOk.pubFromSecretPureByte_ls_withAlloc_ok [LibsignalPlacement]
    {f : State → State} (h : GhostRowSpecOk lsPubFromSecretSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (byVal : Bool := false) :
    HookOk f (withLsRet (withAlloc A lim (pureByteFunctionSpec x25519PubFromSecretRef byVal))) :=
  h.pubFromSecret_row.pureByteFunction_alloc A lim byVal

theorem GhostRowSpecOk.pubFromSecretPureByte_withAlloc_ok [LibsignalPlacement]
    {f : State → State} (h : GhostRowSpecOk lsPubFromSecretSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (byVal : Bool := false) :
    HookOk f (withAlloc A lim (withLsRet (pureByteFunctionSpec x25519PubFromSecretRef byVal))) :=
  h.pubFromSecret_row.pureByteFunction_alloc_ls A lim byVal

theorem GhostRowSpecOk.derivePublicKeyBytesStack_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsPubFromSecretSym f) (stk : Nat := extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk)) :=
  h.pubFromSecret_row.derivePublicKeyBytesStack_ls stk hlo hhi

theorem GhostRowSpecOk.derivePublicKeyBytesStack_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsPubFromSecretSym f) (stk : Nat := extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f
      (withLsRet (withVmPreserved (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk))) :=
  h.pubFromSecret_row.derivePublicKeyBytesStack_vm stk hlo hhi

theorem GhostRowSpecOk.derivePublicKeyBytesStack_keepsFs_budget_ok [LibsignalPlacement]
    {f : State → State} (h : GhostRowSpecOk lsPubFromSecretSym f) (stk : Nat := extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withVmPreserved
      (keepsFs (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk)))) :=
  h.pubFromSecret_row.derivePublicKeyBytesStack_keepsFs stk hlo hhi

theorem GhostRowSpecOk.derivePublicKeyBytesStack_ls_withAlloc_ok [LibsignalPlacement]
    {f : State → State} (h : GhostRowSpecOk lsPubFromSecretSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := extHookStack) (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f
      (withLsRet (withAlloc A lim (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk))) :=
  h.pubFromSecret_row.derivePublicKeyBytesStack_alloc A lim stk hlo hhi

theorem GhostRowSpecOk.derivePublicKeyBytesStack_withAlloc_ok [LibsignalPlacement]
    {f : State → State} (h : GhostRowSpecOk lsPubFromSecretSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := extHookStack) (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f
      (withAlloc A lim (withLsRet (derivePublicKeyBytesStackSpec x25519PubFromSecretRef stk))) :=
  h.pubFromSecret_row.derivePublicKeyBytesStack_alloc_ls A lim stk hlo hhi

theorem GhostRowSpecOk.derivePublicKeyBytesStackBudget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsPubFromSecretSym f) (stk : Nat := extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (derivePublicKeyBytesStackBudgetSpec x25519PubFromSecretRef stk)) :=
  h.pubFromSecret_row.derivePublicKeyBytesStackBudget_ls stk hlo hhi

theorem GhostRowSpecOk.derivePublicKeyBytesStackBudget_budget_ok [LibsignalPlacement]
    {f : State → State} (h : GhostRowSpecOk lsPubFromSecretSym f) (stk : Nat := extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet
      (withVmPreserved (derivePublicKeyBytesStackBudgetSpec x25519PubFromSecretRef stk))) :=
  h.pubFromSecret_row.derivePublicKeyBytesStackBudget_vm stk hlo hhi

theorem GhostRowSpecOk.derivePublicKeyBytesStackBudget_keepsFs_budget_ok [LibsignalPlacement]
    {f : State → State} (h : GhostRowSpecOk lsPubFromSecretSym f) (stk : Nat := extHookStack)
    (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withVmPreserved
      (keepsFs (derivePublicKeyBytesStackBudgetSpec x25519PubFromSecretRef stk)))) :=
  h.pubFromSecret_row.derivePublicKeyBytesStackBudget_keepsFs stk hlo hhi

theorem GhostRowSpecOk.derivePublicKeyBytesStackBudget_ls_withAlloc_ok [LibsignalPlacement]
    {f : State → State} (h : GhostRowSpecOk lsPubFromSecretSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := extHookStack) (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet
      (withAlloc A lim (derivePublicKeyBytesStackBudgetSpec x25519PubFromSecretRef stk))) :=
  h.pubFromSecret_row.derivePublicKeyBytesStackBudget_alloc A lim stk hlo hhi

theorem GhostRowSpecOk.derivePublicKeyBytesStackBudget_withAlloc_ok [LibsignalPlacement]
    {f : State → State} (h : GhostRowSpecOk lsPubFromSecretSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := extHookStack) (hlo : 1904 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withAlloc A lim
      (withLsRet (derivePublicKeyBytesStackBudgetSpec x25519PubFromSecretRef stk))) :=
  h.pubFromSecret_row.derivePublicKeyBytesStackBudget_alloc_ls A lim stk hlo hhi

-- `lsDiffieHellmanSym` (`X25519DiffieHellmanRowSpec`):
theorem GhostRowSpecOk.diffieHellman_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDiffieHellmanSym f) : X25519DiffieHellmanRowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  iterate 36 rw [ite_eq_right (by decide)] at hp
  rw [ite_eq_left (by decide)] at hp
  exact hp

theorem GhostRowSpecOk.diffieHellmanWithStack_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDiffieHellmanSym f) (stk : Nat := extHookStack)
    (hlo : 1808 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (CryptoVerification.SignalSession.CliExt.withStack
      (diffieHellmanSpec x25519Ref) stk)) :=
  h.diffieHellman_row.withStack_ls stk hlo hhi

theorem GhostRowSpecOk.diffieHellmanWithStack_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDiffieHellmanSym f) (stk : Nat := extHookStack)
    (hlo : 1808 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withVmPreserved (CryptoVerification.SignalSession.CliExt.withStack
      (diffieHellmanSpec x25519Ref) stk))) :=
  h.diffieHellman_row.withStack_vm stk hlo hhi

theorem GhostRowSpecOk.diffieHellmanWithStack_keepsFs_budget_ok [LibsignalPlacement]
    {f : State → State} (h : GhostRowSpecOk lsDiffieHellmanSym f) (stk : Nat := extHookStack)
    (hlo : 1808 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withVmPreserved (keepsFs
      (CryptoVerification.SignalSession.CliExt.withStack (diffieHellmanSpec x25519Ref) stk)))) :=
  h.diffieHellman_row.withStack_keepsFs stk hlo hhi

theorem GhostRowSpecOk.diffieHellmanWithStack_ls_withAlloc_ok [LibsignalPlacement]
    {f : State → State} (h : GhostRowSpecOk lsDiffieHellmanSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := extHookStack) (hlo : 1808 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withLsRet (withAlloc A lim (CryptoVerification.SignalSession.CliExt.withStack
      (diffieHellmanSpec x25519Ref) stk))) :=
  h.diffieHellman_row.withStack_alloc A lim stk hlo hhi

theorem GhostRowSpecOk.diffieHellmanWithStack_withAlloc_ok [LibsignalPlacement]
    {f : State → State} (h : GhostRowSpecOk lsDiffieHellmanSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := extHookStack) (hlo : 1808 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    HookOk f (withAlloc A lim (withLsRet (CryptoVerification.SignalSession.CliExt.withStack
      (diffieHellmanSpec x25519Ref) stk))) :=
  h.diffieHellman_row.withStack_alloc_ls A lim stk hlo hhi

theorem GhostRowSpecOk.diffieHellman_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDiffieHellmanSym f) {C : Crypto} (hC : C.X = x25519Ref) :
    HookOk f (withLsRet (dhSpec C)) :=
  h.diffieHellman_row.cliExt_ls hC

theorem GhostRowSpecOk.diffieHellman_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDiffieHellmanSym f) {C : Crypto} (hC : C.X = x25519Ref) :
    HookOk f (withLsRet (withVmPreserved (dhSpec C))) :=
  h.diffieHellman_row.cliExt_vm hC

theorem GhostRowSpecOk.diffieHellman_keepsFs_budget_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDiffieHellmanSym f) {C : Crypto} (hC : C.X = x25519Ref) :
    HookOk f (withLsRet (withVmPreserved (keepsFs (dhSpec C)))) :=
  h.diffieHellman_row.cliExt_keepsFs hC

theorem GhostRowSpecOk.diffieHellman_ls_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDiffieHellmanSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {C : Crypto} (hC : C.X = x25519Ref) :
    HookOk f (withLsRet (withAlloc A lim (dhSpec C))) :=
  h.diffieHellman_row.cliExt_alloc A lim hC

theorem GhostRowSpecOk.diffieHellman_withAlloc_ok [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsDiffieHellmanSym f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {C : Crypto} (hC : C.X = x25519Ref) :
    HookOk f (withAlloc A lim (withLsRet (dhSpec C))) :=
  h.diffieHellman_row.cliExt_alloc_ls A lim hC

theorem GhostRowSpecOk.spqrOnceCall_row [LibsignalPlacement] {f : State → State}
    (h : GhostRowSpecOk lsSpqrOnceCallSym f) : SpqrOnceCallRowSpec f := by
  have hp := h.rowSpec
  unfold ExtraRowSpec at hp
  iterate 37 rw [ite_eq_right (by decide)] at hp
  rw [ite_eq_left (by decide)] at hp
  exact hp

/-! ## 6. Kernel Reduction Smoke Checks on `List.lookup` & `FreshExtraKeysList` -/

theorem extra_lookup_hit_smoke (f : State → State) :
    ({ alloc := id, dealloc := id, realloc := id, allocZeroed := id,
       extra := [("memmove", f)] } : CliGhostHooks).extra.lookup "memmove" = some f :=
  rfl

theorem extra_lookup_miss_smoke (f : State → State) :
    ({ alloc := id, dealloc := id, realloc := id, allocZeroed := id,
       extra := [("memmove", f)] } : CliGhostHooks).extra.lookup "memset" = none :=
  rfl

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
