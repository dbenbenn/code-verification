/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs -- proof-setup: allow-public-import
import LibsignalBinary.Heap.SpecBudget
import LibsignalBinary.Proofs.E2E.HooksE.WrapperHooksCommon
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.Defs
import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Ref
import LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref
import LibsignalBinary.Proofs.HookDischarge.Libc.Memmove
import LibsignalBinary.Proofs.HookDischarge.Libc.Strlen
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
import LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AddressA1
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StrlenUtf8A1
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHook
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTraced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.Compress512RowSpec
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoX25519RowSpecsBase
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.FmtWriteRowSpec
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.FormatInnerRowSpec
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.SpqrOnceCallRowSpec
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.WriteFileRowSpec
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.WriteStdoutRowSpec
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRun
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import ProofLib.SepLogic.WP.StateNorm
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget

/-!
# Pure / Unplaced 10-Row `extra` Ghost Witness (`Cli.Run.Slots.PureExtraGhosts`)

Constructs the `W`-free, placement-free 10-row `pureExtraGhosts : ExtraGhostTable` witness for
Cutover 2B's unplaced/pure ghost hook bundles (`a0Ghost`, `bumpGhost`, and `hole2_ghFixed`),
together with:
- `pureBcmpFn` / `pureBcmpFn_ok` and `pureUtf8Err`,
- `pureExtraGhosts_specOk : ExtraFullListSpecOk pureExtraGhosts`,
- `pureExtraGhosts_fsT` (`HookFsTraced IsFsC` for `CliGhostHooksFs.extra_fsT`),
- `pureExtraGhosts_trace_eq` and `pureExtraGhosts_noAllocFailed` (for `ExternNoAllocFailed`),
- `pureExtraGhosts_vmPreserved`, `pureExtraGhosts_perm_eq`, and
  `pureExtraGhosts_preserves_execFrozen` (for `h2ef_hole2_ghFixed_preserves_execFrozen`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.PureExtraGhosts

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (fmtWriteHook0 formatInnerHook0 timeAddHook writeVecHeader)
open CryptoVerification.E2E.HooksE (bcmpVregsSpec timeAddHook_ok)
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)
open CryptoVerification.LibsignalPublicApi (timeAddSpec)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalSession.CryptoHmacSha256 (compress256Hook_one_eq shaStateBytes_length)
open CryptoVerification.LibsignalSpqrV1 (sha256Compress)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.LibsignalTripleRatchet
  (blackBoxHook_ok blackBoxSpec compress256Hook_ok diffieHellmanHook extHookStack pubFromSecretHook
   withStack zeroizeSecretHook zeroizeSecretHook_ok zeroizeSecretSpec)
open CryptoVerification.RustHeap (allocFailedEvent)
open CryptoVerification.SignalSession
  (PathOk blockingAncestor? cliBcmpHook cliPathMaxBytes durationSinceExactHook fromUtf8Hook
   lsAesDecSym lsAesEncSym lsBlackBoxSym lsCompress256Sym lsCompress512Sym lsCompressSym
   lsDiffieHellmanSym lsDsmbSym lsDurationSinceSym lsEdNegSym lsFmtWriteSym lsFormatInnerSym
   lsFromUtf8Sym lsKemDecapsSym lsKemEncapsSym lsLibcruxHmacSym lsMemrchrSym lsMlkemDecapsSym
   lsMlkemEncaps1Sym lsMlkemEncaps2Sym lsMlkemFromSeedSym lsMlkemPk1Sym lsMlkemPk2Sym
   lsMlkemValidatePkSym lsPubFromSecretSym lsScalarModSym lsScalarWideSym lsSharedSecretDropSym
   lsSpqrOnceCallSym lsStaticSecretDropSym lsTimeAddSym lsToEdwardsSym lsTorsionFreeSym
   lsWriteFileSym lsWriteStdoutSym memrchrHook readPath strlenHook unitResult unmodelled
   writeFileHook writeStdoutHook)
open CryptoVerification.SignalSession.Cli (cliBcmpSpec)
open CryptoVerification.SignalSession.Cli.MainHops
  (fromUtf8AsciiSpec fromUtf8Hook_ok hookMemmove_fs hookOk_withStack memrchrHook_ok memrchrSpec
   strlenHook_ok strlenSpec)
open CryptoVerification.SignalSession.Cli.RunGlue
  (IsFsC blackBoxHook_fsT bytesAt_readBytes cliBcmpHook_fsT compress256Hook_fsT compress512Hook_fsT
   diffieHellmanHook_fsT durationSinceExactHook_fsT edNegHook_fsT fmtWriteHook0_fsT
   formatInnerHook0_fsT fromUtf8Hook_fsT hookMemmove_fsT hookNoop_fsT memrchrHook_fsT
   mlkemPk1Hook_fsT mlkemPk2Hook_fsT pubFromSecretHook_fsT strlenHook_fsT timeAddHook_fsT
   writeFileHook_fsT writeStdoutHook_fsT zeroizeSecretHook_fsT)
open CryptoVerification.SignalSession.Cli.Slots
  (durationSinceBoundedSpec durationSinceEpochAtSpec durationSinceExactHook_bounded_ok
   durationSinceExactHook_epoch_at_ok)
open LibsignalBinary.Heap (AllocCallPreserved VmPreserved)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (perm_write32_norm perm_write64_norm perm_writeBytes_norm)
open LibsignalBinary.Heap.SpecBudget (vmPreserved_writeFileHook vmPreserved_writeStdoutHook)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Ref (sha512CompressState)
open LibsignalBinary.Proofs.HookDischarge.CryptoX25519.X25519Ref
  (x25519PubFromSecretRef x25519Ref)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.ConsumerBridges (dalekEdNegVec)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.DalekPureFallbacks
  (dalekCompressFallback dalekCompressFallback_fsT dalekCompressFallback_preserved
   dalekDsmbFallback dalekDsmbFallback_fsT dalekDsmbFallback_preserved
   dalekMontToEdFallback dalekMontToEdFallback_fsT dalekMontToEdFallback_preserved
   dalekScalarModFallback dalekScalarModFallback_fsT dalekScalarModFallback_preserved
   dalekScalarWideFallback dalekScalarWideFallback_fsT dalekScalarWideFallback_preserved
   dalekTorsionFreeFallback dalekTorsionFreeFallback_fsT dalekTorsionFreeFallback_preserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Memmove
  (hookMemmove_bounded_ok hookMemmove_sessionBounded_ok)
open LibsignalBinary.Proofs.HookDischarge.Libc.Strlen (withStrlenPadRO)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO
  (fromUtf8Hook_ro_ok fromUtf8Hook_vmPreserved memrchrHook_ro_ok memrchrHook_vmPreserved
   strlenHook_ro_ok strlenHook_vmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (AesDecRowSpec AesEncRowSpec BcmpRowSpec BlackBoxRowSpec CompleteExtraKeysList Compress256RowSpec
   DalekCompressRowSpec DalekDsmbRowSpec DalekMontToEdRowSpec DalekScalarModRowSpec
   DalekScalarWideRowSpec DalekTorsionFreeRowSpec DurationSinceRowSpec EdNegRowSpec
   ExtraFullListSpecOk ExtraGhostTable ExtraListSpecOk ExtraRowOk ExtraRowSpec FreshExtraKeysList
   FromUtf8RowSpec GhostRowSpecOk LibcruxHmacRowSpec MemmoveRowSpec MemrchrRowSpec MlkemPk1RowSpec
   MlkemPk2RowSpec SharedSecretDropRowSpec StaticSecretDropRowSpec StrlenRowSpec TimeAddRowSpec
   WriteFileRowOk cliExtraGhostSyms compress256RowSingleSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.Compress512RowSpec
  (Compress512RowSpec compress512Fallback compress512Fallback_rowSpec
   compress512Fallback_vmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoDalekRowSpecs
  (dalekCompressFallback_rowSpec dalekDsmbFallback_rowSpec dalekMontToEdFallback_rowSpec
   dalekScalarModFallback_rowSpec dalekScalarWideFallback_rowSpec
   dalekTorsionFreeFallback_rowSpec edNegFallback_fsT edNegFallback_rowSpec
   mlkemPk1Fallback_fsT mlkemPk1Hook_rowSpec mlkemPk2Fallback_fsT mlkemPk2Hook_rowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs
  (KemDecapsRowSpecAt KemEncapsRowSpecAt MlkemDecapsRowSpecAt MlkemEncaps1RowSpecAt
   MlkemEncaps2RowSpecAt MlkemFromSeedRowSpecAt MlkemValidatePkRowSpecAt
   kemDecapsFallback kemDecapsFallback_fsT kemDecapsFallback_preserved kemDecapsFallback_rowSpecAt
   kemDecapsTightStack kemEncapsFallback kemEncapsFallback_fsT kemEncapsFallback_preserved
   kemEncapsFallback_rowSpecAt kemEncapsTightStack mlkemDecapsFallback mlkemDecapsFallback_fsT
   mlkemDecapsFallback_preserved mlkemDecapsFallback_rowSpecAt mlkemDecapsTightStack
   mlkemEncaps1Fallback mlkemEncaps1Fallback_fsT mlkemEncaps1Fallback_preserved
   mlkemEncaps1Fallback_rowSpecAt mlkemEncaps1TightStack mlkemEncaps2Fallback
   mlkemEncaps2Fallback_fsT mlkemEncaps2Fallback_preserved mlkemEncaps2Fallback_rowSpecAt
   mlkemEncaps2TightStack mlkemFromSeedFallback mlkemFromSeedFallback_fsT
   mlkemFromSeedFallback_preserved mlkemFromSeedFallback_rowSpecAt mlkemFromSeedTightStack
   mlkemValidatePkFallback mlkemValidatePkFallback_fsT mlkemValidatePkFallback_preserved
   mlkemValidatePkFallback_rowSpecAt mlkemValidatePkTightStack)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoX25519RowSpecsBase
  (X25519DiffieHellmanRowSpec X25519PubFromSecretRowSpec diffieHellmanFallback_rowSpec
   pubFromSecretFallback_rowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.FmtWriteRowSpec
  (FmtWriteRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.FormatInnerRowSpec
  (FormatInnerRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.WriteFileRowSpec
  (WriteFileRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.WriteStdoutRowSpec
  (WriteStdoutRowSpec)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy
  (edNegHook mlkemPk1Hook mlkemPk2Hook)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
  (compress256Hook_keepsExec compress256Hook_roBudget_ok)

attribute [local irreducible] x25519PubFromSecretRef x25519Ref

/-! ## 1. Pure `bcmp` & `from_utf8` Value Helpers and 23-Row `pureExtraGhosts` Table -/

/-- Pure `W`-free `bcmp` return-value function (`0` iff equal, `1` otherwise). -/
@[expose] def pureBcmpFn (a b : List (BitVec 8)) : BitVec 64 :=
  if a = b then 0#64 else 1#64

theorem pureBcmpFn_ok :
    ∀ a b : List (BitVec 8), a.length = b.length →
      ((pureBcmpFn a b).setWidth 32 = 0#32 ↔ a = b) := by
  intro a b _
  unfold pureBcmpFn
  by_cases hab : a = b <;> simp [hab]

/-- Pure `W`-free `from_utf8` error payload function. -/
@[expose] def pureUtf8Err (_ : List (BitVec 8)) : BitVec 64 × BitVec 16 :=
  (0#64, 0#16)

/-- 38-row `ExtraGhostTable` in canonical `cliExtraGhostSyms` key order parameterized by the
    `lsLibcruxHmacSym`, `lsAesEncSym`, `lsAesDecSym`, and `lsSpqrOnceCallSym` hooks
    (`fHmac`, `fEnc`, `fDec`, `fOnce`). -/
@[expose] noncomputable def pureExtraGhostsWithCryptoAndOnce
    (fHmac fEnc fDec fOnce : State → State) : ExtraGhostTable :=
  [ ("memmove", hookMemmove)
  , ("bcmp", cliBcmpHook pureBcmpFn)
  , ("strlen", strlenHook)
  , (lsMemrchrSym, memrchrHook)
  , (lsFromUtf8Sym, fromUtf8Hook pureUtf8Err)
  , (lsDurationSinceSym, durationSinceExactHook)
  , (lsTimeAddSym, timeAddHook)
  , (lsBlackBoxSym, blackBoxHook)
  , (lsStaticSecretDropSym, zeroizeSecretHook)
  , (lsSharedSecretDropSym, zeroizeSecretHook)
  , (lsToEdwardsSym, dalekMontToEdFallback)
  , (lsCompressSym, dalekCompressFallback)
  , (lsEdNegSym, edNegHook dalekEdNegVec)
  , (lsTorsionFreeSym, dalekTorsionFreeFallback)
  , (lsDsmbSym, dalekDsmbFallback)
  , (lsScalarModSym, dalekScalarModFallback)
  , (lsScalarWideSym, dalekScalarWideFallback)
  , (lsMlkemPk1Sym, mlkemPk1Hook)
  , (lsMlkemPk2Sym, mlkemPk2Hook)
  , (lsCompress256Sym, compress256Hook sha256Compress)
  , (lsLibcruxHmacSym, fHmac)
  , (lsAesEncSym, fEnc)
  , (lsAesDecSym, fDec)
  , (lsCompress512Sym, compress512Fallback)
  , (lsKemEncapsSym, kemEncapsFallback)
  , (lsKemDecapsSym, kemDecapsFallback)
  , (lsMlkemFromSeedSym, mlkemFromSeedFallback)
  , (lsMlkemEncaps1Sym, mlkemEncaps1Fallback)
  , (lsMlkemEncaps2Sym, mlkemEncaps2Fallback)
  , (lsMlkemDecapsSym, mlkemDecapsFallback)
  , (lsMlkemValidatePkSym, mlkemValidatePkFallback)
  , (lsWriteFileSym, writeFileHook)
  , (lsWriteStdoutSym, writeStdoutHook)
  , (lsFmtWriteSym, fmtWriteHook0)
  , (lsFormatInnerSym, formatInnerHook0)
  , (lsPubFromSecretSym, pubFromSecretHook x25519PubFromSecretRef)
  , (lsDiffieHellmanSym, diffieHellmanHook x25519Ref)
  , (lsSpqrOnceCallSym, fOnce)
  ]

/-- 38-row `ExtraGhostTable` specializing `lsSpqrOnceCallSym` to `hookNoop` and parameterized by
    `fHmac`, `fEnc`, `fDec`. -/
@[expose] noncomputable def pureExtraGhostsWithCrypto
    (fHmac fEnc fDec : State → State) : ExtraGhostTable :=
  pureExtraGhostsWithCryptoAndOnce fHmac fEnc fDec hookNoop

/-- 38-row `ExtraGhostTable` specializing `lsLibcruxHmacSym` / `lsAesEncSym` / `lsAesDecSym` to
    `hookNoop` and parameterized by `fOnce`. -/
@[expose] noncomputable def pureExtraGhostsWithOnce (fOnce : State → State) : ExtraGhostTable :=
  pureExtraGhostsWithCryptoAndOnce hookNoop hookNoop hookNoop fOnce

/-- 23-row `ExtraGhostTable` specializing `lsAesEncSym` / `lsAesDecSym` to `hookNoop` and
    parameterized by `fHmac`. -/
@[expose] noncomputable def pureExtraGhostsWithHmac (fHmac : State → State) : ExtraGhostTable :=
  pureExtraGhostsWithCrypto fHmac hookNoop hookNoop

/-- 23-row `ExtraGhostTable` specializing `lsLibcruxHmacSym` to `hookNoop` and parameterized by
    `fEnc` and `fDec`. -/
@[expose] noncomputable def pureExtraGhostsWithAes
    (fEnc fDec : State → State) : ExtraGhostTable :=
  pureExtraGhostsWithCrypto hookNoop fEnc fDec

/-- 23-row pure/unplaced `ExtraGhostTable` in canonical `cliExtraGhostSyms` key order, binding
    `"memmove"` at index `0` to `ProofLib.hookMemmove`, `lsCompress256Sym` to
    `compress256Hook sha256Compress`, and `lsLibcruxHmacSym` / `lsAesEncSym` / `lsAesDecSym` to
    `hookNoop`. -/
@[expose] noncomputable def pureExtraGhosts : ExtraGhostTable :=
  pureExtraGhostsWithCrypto hookNoop hookNoop hookNoop

theorem pureExtraGhostsWithCryptoAndOnce_lookup_memmove (fHmac fEnc fDec fOnce : State → State) :
    (pureExtraGhostsWithCryptoAndOnce fHmac fEnc fDec fOnce).lookup "memmove" = some hookMemmove :=
  rfl

theorem pureExtraGhostsWithCrypto_lookup_memmove (fHmac fEnc fDec : State → State) :
    (pureExtraGhostsWithCrypto fHmac fEnc fDec).lookup "memmove" = some hookMemmove :=
  rfl

theorem pureExtraGhostsWithHmac_lookup_memmove (fHmac : State → State) :
    (pureExtraGhostsWithHmac fHmac).lookup "memmove" = some hookMemmove :=
  rfl

theorem pureExtraGhostsWithAes_lookup_memmove (fEnc fDec : State → State) :
    (pureExtraGhostsWithAes fEnc fDec).lookup "memmove" = some hookMemmove :=
  rfl

/-- `pureExtraGhosts.lookup "memmove"` reduces definitionally to `some hookMemmove` by `rfl`. -/
theorem pureExtraGhosts_lookup_memmove :
    pureExtraGhosts.lookup "memmove" = some hookMemmove :=
  rfl

private theorem pureExtraGhostsWithCryptoAndOnce_map_fst (fHmac fEnc fDec fOnce : State → State) :
    (pureExtraGhostsWithCryptoAndOnce fHmac fEnc fDec fOnce).map Prod.fst = cliExtraGhostSyms :=
  rfl

theorem pureExtraGhostsWithCryptoAndOnce_fresh (fHmac fEnc fDec fOnce : State → State) :
    FreshExtraKeysList (pureExtraGhostsWithCryptoAndOnce fHmac fEnc fDec fOnce) := by
  dsimp only [FreshExtraKeysList]
  rw [pureExtraGhostsWithCryptoAndOnce_map_fst fHmac fEnc fDec fOnce]
  decide

theorem pureExtraGhostsWithCryptoAndOnce_complete (fHmac fEnc fDec fOnce : State → State) :
    CompleteExtraKeysList (pureExtraGhostsWithCryptoAndOnce fHmac fEnc fDec fOnce) := by
  dsimp only [CompleteExtraKeysList]
  rw [pureExtraGhostsWithCryptoAndOnce_map_fst fHmac fEnc fDec fOnce]
  decide

theorem pureExtraGhostsWithCrypto_fresh (fHmac fEnc fDec : State → State) :
    FreshExtraKeysList (pureExtraGhostsWithCrypto fHmac fEnc fDec) :=
  pureExtraGhostsWithCryptoAndOnce_fresh fHmac fEnc fDec hookNoop

theorem pureExtraGhostsWithCrypto_complete (fHmac fEnc fDec : State → State) :
    CompleteExtraKeysList (pureExtraGhostsWithCrypto fHmac fEnc fDec) :=
  pureExtraGhostsWithCryptoAndOnce_complete fHmac fEnc fDec hookNoop

theorem pureExtraGhostsWithHmac_fresh (fHmac : State → State) :
    FreshExtraKeysList (pureExtraGhostsWithHmac fHmac) :=
  pureExtraGhostsWithCrypto_fresh fHmac hookNoop hookNoop

theorem pureExtraGhostsWithHmac_complete (fHmac : State → State) :
    CompleteExtraKeysList (pureExtraGhostsWithHmac fHmac) :=
  pureExtraGhostsWithCrypto_complete fHmac hookNoop hookNoop

theorem pureExtraGhostsWithAes_fresh (fEnc fDec : State → State) :
    FreshExtraKeysList (pureExtraGhostsWithAes fEnc fDec) :=
  pureExtraGhostsWithCrypto_fresh hookNoop fEnc fDec

theorem pureExtraGhostsWithAes_complete (fEnc fDec : State → State) :
    CompleteExtraKeysList (pureExtraGhostsWithAes fEnc fDec) :=
  pureExtraGhostsWithCrypto_complete hookNoop fEnc fDec

theorem pureExtraGhosts_fresh : FreshExtraKeysList pureExtraGhosts :=
  pureExtraGhostsWithCrypto_fresh hookNoop hookNoop hookNoop

theorem pureExtraGhosts_complete : CompleteExtraKeysList pureExtraGhosts :=
  pureExtraGhostsWithCrypto_complete hookNoop hookNoop hookNoop

theorem pureExtraGhostsWithCryptoAndOnce_lookup_hmac (fHmac fEnc fDec fOnce : State → State) :
    (pureExtraGhostsWithCryptoAndOnce fHmac fEnc fDec fOnce).lookup lsLibcruxHmacSym = some fHmac := by
  have hd1 : (lsLibcruxHmacSym == "memmove") = false := by decide
  have hd2 : (lsLibcruxHmacSym == "bcmp") = false := by decide
  have hd3 : (lsLibcruxHmacSym == "strlen") = false := by decide
  have hd4 : (lsLibcruxHmacSym == lsMemrchrSym) = false := by decide
  have hd5 : (lsLibcruxHmacSym == lsFromUtf8Sym) = false := by decide
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
  simp only [pureExtraGhostsWithCryptoAndOnce, List.lookup, hd1, hd2, hd3, hd4, hd5, hd6, hd7,
    hd8, hd9, hd10, hd11, hd12, hd13, hd14, hd15, hd16, hd17, hd18, hd19, hd20, hd21]

theorem pureExtraGhostsWithCrypto_lookup_hmac (fHmac fEnc fDec : State → State) :
    (pureExtraGhostsWithCrypto fHmac fEnc fDec).lookup lsLibcruxHmacSym = some fHmac :=
  pureExtraGhostsWithCryptoAndOnce_lookup_hmac fHmac fEnc fDec hookNoop

theorem pureExtraGhostsWithCryptoAndOnce_lookup_aesEnc (fHmac fEnc fDec fOnce : State → State) :
    (pureExtraGhostsWithCryptoAndOnce fHmac fEnc fDec fOnce).lookup lsAesEncSym = some fEnc := by
  have hd1 : (lsAesEncSym == "memmove") = false := by decide
  have hd2 : (lsAesEncSym == "bcmp") = false := by decide
  have hd3 : (lsAesEncSym == "strlen") = false := by decide
  have hd4 : (lsAesEncSym == lsMemrchrSym) = false := by decide
  have hd5 : (lsAesEncSym == lsFromUtf8Sym) = false := by decide
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
  simp only [pureExtraGhostsWithCryptoAndOnce, List.lookup, hd1, hd2, hd3, hd4, hd5, hd6, hd7,
    hd8, hd9, hd10, hd11, hd12, hd13, hd14, hd15, hd16, hd17, hd18, hd19, hd20, hd21, hd22]

theorem pureExtraGhostsWithCrypto_lookup_aesEnc (fHmac fEnc fDec : State → State) :
    (pureExtraGhostsWithCrypto fHmac fEnc fDec).lookup lsAesEncSym = some fEnc :=
  pureExtraGhostsWithCryptoAndOnce_lookup_aesEnc fHmac fEnc fDec hookNoop

theorem pureExtraGhostsWithCryptoAndOnce_lookup_aesDec (fHmac fEnc fDec fOnce : State → State) :
    (pureExtraGhostsWithCryptoAndOnce fHmac fEnc fDec fOnce).lookup lsAesDecSym = some fDec := by
  have hd1 : (lsAesDecSym == "memmove") = false := by decide
  have hd2 : (lsAesDecSym == "bcmp") = false := by decide
  have hd3 : (lsAesDecSym == "strlen") = false := by decide
  have hd4 : (lsAesDecSym == lsMemrchrSym) = false := by decide
  have hd5 : (lsAesDecSym == lsFromUtf8Sym) = false := by decide
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
  simp only [pureExtraGhostsWithCryptoAndOnce, List.lookup, hd1, hd2, hd3, hd4, hd5, hd6, hd7,
    hd8, hd9, hd10, hd11, hd12, hd13, hd14, hd15, hd16, hd17, hd18, hd19, hd20, hd21, hd22, hd23]

theorem pureExtraGhostsWithCrypto_lookup_aesDec (fHmac fEnc fDec : State → State) :
    (pureExtraGhostsWithCrypto fHmac fEnc fDec).lookup lsAesDecSym = some fDec :=
  pureExtraGhostsWithCryptoAndOnce_lookup_aesDec fHmac fEnc fDec hookNoop

theorem pureExtraGhostsWithHmac_lookup_hmac (fHmac : State → State) :
    (pureExtraGhostsWithHmac fHmac).lookup lsLibcruxHmacSym = some fHmac :=
  pureExtraGhostsWithCrypto_lookup_hmac fHmac hookNoop hookNoop

theorem pureExtraGhostsWithAes_lookup_aesEnc (fEnc fDec : State → State) :
    (pureExtraGhostsWithAes fEnc fDec).lookup lsAesEncSym = some fEnc :=
  pureExtraGhostsWithCrypto_lookup_aesEnc hookNoop fEnc fDec

theorem pureExtraGhostsWithAes_lookup_aesDec (fEnc fDec : State → State) :
    (pureExtraGhostsWithAes fEnc fDec).lookup lsAesDecSym = some fDec :=
  pureExtraGhostsWithCrypto_lookup_aesDec hookNoop fEnc fDec

private theorem lookup_cons_ne {V : Type} {k sym : String} {v : V} {tl : List (String × V)}
    (hne : (sym == k) = false) :
    ((k, v) :: tl).lookup sym = tl.lookup sym := by
  simp [List.lookup, hne]

private theorem lookup_cons_eq {V : Type} {k sym : String} {v : V} {tl : List (String × V)}
    (heq : (sym == k) = true) :
    ((k, v) :: tl).lookup sym = some v := by
  simp [List.lookup, heq]

theorem pureExtraGhostsWithCryptoAndOnce_lookup_writeFile (fHmac fEnc fDec fOnce : State → State) :
    (pureExtraGhostsWithCryptoAndOnce fHmac fEnc fDec fOnce).lookup lsWriteFileSym =
      some writeFileHook := by
  unfold pureExtraGhostsWithCryptoAndOnce
  repeat rw [lookup_cons_ne (by decide)]
  exact lookup_cons_eq (by decide)

theorem pureExtraGhostsWithCrypto_lookup_writeFile (fHmac fEnc fDec : State → State) :
    (pureExtraGhostsWithCrypto fHmac fEnc fDec).lookup lsWriteFileSym = some writeFileHook :=
  pureExtraGhostsWithCryptoAndOnce_lookup_writeFile fHmac fEnc fDec hookNoop

theorem pureExtraGhostsWithCryptoAndOnce_lookup_writeStdout (fHmac fEnc fDec fOnce : State → State) :
    (pureExtraGhostsWithCryptoAndOnce fHmac fEnc fDec fOnce).lookup lsWriteStdoutSym =
      some writeStdoutHook := by
  unfold pureExtraGhostsWithCryptoAndOnce
  repeat rw [lookup_cons_ne (by decide)]
  exact lookup_cons_eq (by decide)

theorem pureExtraGhostsWithCrypto_lookup_writeStdout (fHmac fEnc fDec : State → State) :
    (pureExtraGhostsWithCrypto fHmac fEnc fDec).lookup lsWriteStdoutSym = some writeStdoutHook :=
  pureExtraGhostsWithCryptoAndOnce_lookup_writeStdout fHmac fEnc fDec hookNoop

theorem pureExtraGhostsWithCryptoAndOnce_lookup_fmtWrite (fHmac fEnc fDec fOnce : State → State) :
    (pureExtraGhostsWithCryptoAndOnce fHmac fEnc fDec fOnce).lookup lsFmtWriteSym =
      some fmtWriteHook0 := by
  unfold pureExtraGhostsWithCryptoAndOnce
  repeat rw [lookup_cons_ne (by decide)]
  exact lookup_cons_eq (by decide)

theorem pureExtraGhostsWithCrypto_lookup_fmtWrite (fHmac fEnc fDec : State → State) :
    (pureExtraGhostsWithCrypto fHmac fEnc fDec).lookup lsFmtWriteSym = some fmtWriteHook0 :=
  pureExtraGhostsWithCryptoAndOnce_lookup_fmtWrite fHmac fEnc fDec hookNoop

theorem pureExtraGhostsWithCryptoAndOnce_lookup_formatInner (fHmac fEnc fDec fOnce : State → State) :
    (pureExtraGhostsWithCryptoAndOnce fHmac fEnc fDec fOnce).lookup lsFormatInnerSym =
      some formatInnerHook0 := by
  unfold pureExtraGhostsWithCryptoAndOnce
  repeat rw [lookup_cons_ne (by decide)]
  exact lookup_cons_eq (by decide)

theorem pureExtraGhostsWithCrypto_lookup_formatInner (fHmac fEnc fDec : State → State) :
    (pureExtraGhostsWithCrypto fHmac fEnc fDec).lookup lsFormatInnerSym = some formatInnerHook0 :=
  pureExtraGhostsWithCryptoAndOnce_lookup_formatInner fHmac fEnc fDec hookNoop

theorem pureExtraGhostsWithCryptoAndOnce_lookup_spqrOnceCall (fHmac fEnc fDec fOnce : State → State) :
    (pureExtraGhostsWithCryptoAndOnce fHmac fEnc fDec fOnce).lookup lsSpqrOnceCallSym =
      some fOnce := by
  unfold pureExtraGhostsWithCryptoAndOnce
  repeat rw [lookup_cons_ne (by decide)]
  exact lookup_cons_eq (by decide)

theorem pureExtraGhostsWithOnce_lookup_spqrOnceCall (fOnce : State → State) :
    (pureExtraGhostsWithOnce fOnce).lookup lsSpqrOnceCallSym = some fOnce :=
  pureExtraGhostsWithCryptoAndOnce_lookup_spqrOnceCall hookNoop hookNoop hookNoop fOnce

theorem pureExtraGhosts_lookup_writeFile :
    pureExtraGhosts.lookup lsWriteFileSym = some writeFileHook :=
  pureExtraGhostsWithCrypto_lookup_writeFile hookNoop hookNoop hookNoop

theorem pureExtraGhosts_lookup_writeStdout :
    pureExtraGhosts.lookup lsWriteStdoutSym = some writeStdoutHook :=
  pureExtraGhostsWithCrypto_lookup_writeStdout hookNoop hookNoop hookNoop

theorem pureExtraGhosts_lookup_fmtWrite :
    pureExtraGhosts.lookup lsFmtWriteSym = some fmtWriteHook0 :=
  pureExtraGhostsWithCrypto_lookup_fmtWrite hookNoop hookNoop hookNoop

theorem pureExtraGhosts_lookup_formatInner :
    pureExtraGhosts.lookup lsFormatInnerSym = some formatInnerHook0 :=
  pureExtraGhostsWithCrypto_lookup_formatInner hookNoop hookNoop hookNoop

private theorem lookup_cons_cases {V : Type} {k sym : String} {v f : V} {tl : List (String × V)}
    (h : ((k, v) :: tl).lookup sym = some f) :
    (sym = k ∧ f = v) ∨ tl.lookup sym = some f := by
  dsimp only [List.lookup] at h
  cases hsk : (sym == k) with
  | true =>
    rw [hsk] at h
    injection h with hv
    exact Or.inl ⟨eq_of_beq hsk, hv.symm⟩
  | false =>
    rw [hsk] at h
    exact Or.inr h

private theorem pureExtraGhostsWithCryptoAndOnce_lookup_cases {fHmac fEnc fDec fOnce : State → State}
    {sym : String} {f : State → State}
    (hLook : (pureExtraGhostsWithCryptoAndOnce fHmac fEnc fDec fOnce).lookup sym = some f) :
    (sym = "memmove" ∧ f = hookMemmove) ∨
    (sym = "bcmp" ∧ f = cliBcmpHook pureBcmpFn) ∨
    (sym = "strlen" ∧ f = strlenHook) ∨
    (sym = lsMemrchrSym ∧ f = memrchrHook) ∨
    (sym = lsFromUtf8Sym ∧ f = fromUtf8Hook pureUtf8Err) ∨
    (sym = lsDurationSinceSym ∧ f = durationSinceExactHook) ∨
    (sym = lsTimeAddSym ∧ f = timeAddHook) ∨
    (sym = lsBlackBoxSym ∧ f = blackBoxHook) ∨
    (sym = lsStaticSecretDropSym ∧ f = zeroizeSecretHook) ∨
    (sym = lsSharedSecretDropSym ∧ f = zeroizeSecretHook) ∨
    (sym = lsToEdwardsSym ∧ f = dalekMontToEdFallback) ∨
    (sym = lsCompressSym ∧ f = dalekCompressFallback) ∨
    (sym = lsEdNegSym ∧ f = edNegHook dalekEdNegVec) ∨
    (sym = lsTorsionFreeSym ∧ f = dalekTorsionFreeFallback) ∨
    (sym = lsDsmbSym ∧ f = dalekDsmbFallback) ∨
    (sym = lsScalarModSym ∧ f = dalekScalarModFallback) ∨
    (sym = lsScalarWideSym ∧ f = dalekScalarWideFallback) ∨
    (sym = lsMlkemPk1Sym ∧ f = mlkemPk1Hook) ∨
    (sym = lsMlkemPk2Sym ∧ f = mlkemPk2Hook) ∨
    (sym = lsCompress256Sym ∧ f = compress256Hook sha256Compress) ∨
    (sym = lsLibcruxHmacSym ∧ f = fHmac) ∨
    (sym = lsAesEncSym ∧ f = fEnc) ∨
    (sym = lsAesDecSym ∧ f = fDec) ∨
    (sym = lsCompress512Sym ∧ f = compress512Fallback) ∨
    (sym = lsKemEncapsSym ∧ f = kemEncapsFallback) ∨
    (sym = lsKemDecapsSym ∧ f = kemDecapsFallback) ∨
    (sym = lsMlkemFromSeedSym ∧ f = mlkemFromSeedFallback) ∨
    (sym = lsMlkemEncaps1Sym ∧ f = mlkemEncaps1Fallback) ∨
    (sym = lsMlkemEncaps2Sym ∧ f = mlkemEncaps2Fallback) ∨
    (sym = lsMlkemDecapsSym ∧ f = mlkemDecapsFallback) ∨
    (sym = lsMlkemValidatePkSym ∧ f = mlkemValidatePkFallback) ∨
    (sym = lsWriteFileSym ∧ f = writeFileHook) ∨
    (sym = lsWriteStdoutSym ∧ f = writeStdoutHook) ∨
    (sym = lsFmtWriteSym ∧ f = fmtWriteHook0) ∨
    (sym = lsFormatInnerSym ∧ f = formatInnerHook0) ∨
    (sym = lsPubFromSecretSym ∧ f = pubFromSecretHook x25519PubFromSecretRef) ∨
    (sym = lsDiffieHellmanSym ∧ f = diffieHellmanHook x25519Ref) ∨
    (sym = lsSpqrOnceCallSym ∧ f = fOnce) := by
  dsimp only [pureExtraGhostsWithCryptoAndOnce] at hLook
  iterate 37 (
    rcases lookup_cons_cases hLook with h | hLook
    · exact Or.inl h
    refine Or.inr ?_)
  rcases lookup_cons_cases hLook with h | hLook
  · exact h
  · cases hLook

private theorem pureExtraGhosts_lookup_cases {sym : String} {f : State → State}
    (hLook : pureExtraGhosts.lookup sym = some f) :
    (sym = "memmove" ∧ f = hookMemmove) ∨
    (sym = "bcmp" ∧ f = cliBcmpHook pureBcmpFn) ∨
    (sym = "strlen" ∧ f = strlenHook) ∨
    (sym = lsMemrchrSym ∧ f = memrchrHook) ∨
    (sym = lsFromUtf8Sym ∧ f = fromUtf8Hook pureUtf8Err) ∨
    (sym = lsDurationSinceSym ∧ f = durationSinceExactHook) ∨
    (sym = lsTimeAddSym ∧ f = timeAddHook) ∨
    (sym = lsBlackBoxSym ∧ f = blackBoxHook) ∨
    (sym = lsStaticSecretDropSym ∧ f = zeroizeSecretHook) ∨
    (sym = lsSharedSecretDropSym ∧ f = zeroizeSecretHook) ∨
    (sym = lsToEdwardsSym ∧ f = dalekMontToEdFallback) ∨
    (sym = lsCompressSym ∧ f = dalekCompressFallback) ∨
    (sym = lsEdNegSym ∧ f = edNegHook dalekEdNegVec) ∨
    (sym = lsTorsionFreeSym ∧ f = dalekTorsionFreeFallback) ∨
    (sym = lsDsmbSym ∧ f = dalekDsmbFallback) ∨
    (sym = lsScalarModSym ∧ f = dalekScalarModFallback) ∨
    (sym = lsScalarWideSym ∧ f = dalekScalarWideFallback) ∨
    (sym = lsMlkemPk1Sym ∧ f = mlkemPk1Hook) ∨
    (sym = lsMlkemPk2Sym ∧ f = mlkemPk2Hook) ∨
    (sym = lsCompress256Sym ∧ f = compress256Hook sha256Compress) ∨
    (sym = lsLibcruxHmacSym ∧ f = hookNoop) ∨
    (sym = lsAesEncSym ∧ f = hookNoop) ∨
    (sym = lsAesDecSym ∧ f = hookNoop) ∨
    (sym = lsCompress512Sym ∧ f = compress512Fallback) ∨
    (sym = lsKemEncapsSym ∧ f = kemEncapsFallback) ∨
    (sym = lsKemDecapsSym ∧ f = kemDecapsFallback) ∨
    (sym = lsMlkemFromSeedSym ∧ f = mlkemFromSeedFallback) ∨
    (sym = lsMlkemEncaps1Sym ∧ f = mlkemEncaps1Fallback) ∨
    (sym = lsMlkemEncaps2Sym ∧ f = mlkemEncaps2Fallback) ∨
    (sym = lsMlkemDecapsSym ∧ f = mlkemDecapsFallback) ∨
    (sym = lsMlkemValidatePkSym ∧ f = mlkemValidatePkFallback) ∨
    (sym = lsWriteFileSym ∧ f = writeFileHook) ∨
    (sym = lsWriteStdoutSym ∧ f = writeStdoutHook) ∨
    (sym = lsFmtWriteSym ∧ f = fmtWriteHook0) ∨
    (sym = lsFormatInnerSym ∧ f = formatInnerHook0) ∨
    (sym = lsPubFromSecretSym ∧ f = pubFromSecretHook x25519PubFromSecretRef) ∨
    (sym = lsDiffieHellmanSym ∧ f = diffieHellmanHook x25519Ref) ∨
    (sym = lsSpqrOnceCallSym ∧ f = hookNoop) :=
  pureExtraGhostsWithCryptoAndOnce_lookup_cases hLook

/-! ## 2. Private Per-Row `HookOk`, `VmPreserved`, `fs_eq`, and `trace_eq` Lemmas -/

private theorem hookOk_withStrlenPadRO_of_hookOk {f : State → State}
    {spec : Spec (BitVec 64 × List (BitVec 8))}
    (hf : HookOk f spec) :
    HookOk f (withStrlenPadRO spec) := by
  intro ⟨p, s⟩ R s0 hrun hpre hsp
  dsimp only [withStrlenPadRO] at hpre
  rw [sepConj_assoc] at hpre
  exact hf (p, s) R s0 hrun (Satisfies.of_sep_right hpre) hsp

private theorem setMem_vm (s : State) {m' : Memory} (hp : ∀ a, m'.perm a = s.mem.perm a) :
    VmPreserved s (s.setMem m') :=
  ⟨⟨rfl, rfl, rfl⟩, rfl, hp, fun _ _ _ => rfl⟩

private theorem retHook_vm {g : State → State} {s : State} (hg : VmPreserved s (g s)) :
    VmPreserved s (retHook g s) := by
  unfold retHook
  exact hg

private theorem returnToLr_vm {s0 s : State} (hs : VmPreserved s0 s) :
    VmPreserved s0 (returnToLinkRegister s) := by
  unfold returnToLinkRegister
  exact hs

private theorem hookMemmove_vm (s : State) : VmPreserved s (hookMemmove s) := by
  unfold hookMemmove hookMemcpy
  exact retHook_vm (setMem_vm s fun a => congrFun (perm_writeBytes_norm _ _ _) a)

private theorem hookMemmove_acp (s : State) : AllocCallPreserved s (hookMemmove s) := by
  unfold hookMemmove hookMemcpy retHook
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem pureBcmpHook_ok : HookOk (cliBcmpHook pureBcmpFn) cliBcmpSpec := by
  refine retHook_ok fun x R s0 hrun hpre _hsp => ?_
  simp only [cliBcmpSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlen⟩, hmem⟩
  have hlenA : x.bsA.length ≤ 2 ^ 64 := by
    have := (s0.readReg64 .x2).isLt
    omega
  have hreadA := bytesAt_readBytes hmem hlenA
  have hmemB : s0.mem ⊨ bytesAt x.bRo x.b x.bsB ∗
      (bytesAt x.aRo x.a x.bsA ∗ (stackAt s0.sp extHookStack ∗ R)) := by
    rwa [← sepConj_assoc, sepConj_comm (bytesAt x.aRo x.a x.bsA), sepConj_assoc] at hmem
  have hreadB := bytesAt_readBytes hmemB (by omega)
  rw [hlen] at hreadB
  refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, hrun,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  dsimp only [cliBcmpSpec, cliBcmpHook, retHook]
  rw [hx0, hx1, hx2, hreadA, hreadB]
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨pureBcmpFn_ok x.bsA x.bsB hlen.symm, rfl⟩, hmem⟩

private theorem pureBcmpHook_vregs_ok : HookOk (cliBcmpHook pureBcmpFn) bcmpVregsSpec := by
  refine retHook_ok fun x R s0 hrun hpre _hsp => ?_
  simp only [bcmpVregsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlen⟩, hmem⟩
  have hreadA : s0.mem.readBytes x.a x.bsA.length = x.bsA :=
    ((IsBlock.pointsToBytes x.a x.bsA).read hmem).2
  have hmemB : s0.mem ⊨ (x.b ↦ₛ x.bsB) ∗ ((x.a ↦ₛ x.bsA) ∗ (stackAt s0.sp extHookStack ∗ R)) := by
    ac_nf at hmem ⊢
  have hreadB : s0.mem.readBytes x.b x.bsA.length = x.bsB := by
    rw [← hlen]; exact ((IsBlock.pointsToBytes x.b x.bsB).read hmemB).2
  refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, hrun,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  dsimp only [bcmpVregsSpec, cliBcmpHook, retHook]
  rw [hx0, hx1, hx2, hreadA, hreadB]
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨pureBcmpFn_ok x.bsA x.bsB hlen.symm, rfl, rfl⟩, hmem⟩

private theorem pureBcmpHook_vm (s : State) : VmPreserved s (cliBcmpHook pureBcmpFn s) :=
  VmPreserved.refl s

private theorem durationSinceExactHook_vm (s : State) :
    VmPreserved s (durationSinceExactHook s) := by
  unfold durationSinceExactHook; try dsimp only
  split
  · exact VmPreserved.refl s
  · try dsimp only
    split
    · refine retHook_vm (setMem_vm s fun a => ?_)
      simp only [perm_write32_norm, perm_write64_norm]
    · exact VmPreserved.refl s

private theorem timeAddHook_vm (s : State) : VmPreserved s (timeAddHook s) := by
  unfold timeAddHook
  try dsimp only
  split <;> (split <;> exact VmPreserved.refl s)

private theorem blackBoxHook_vm (s : State) : VmPreserved s (blackBoxHook s) :=
  VmPreserved.refl s

private theorem zeroizeSecretHook_vm (s : State) : VmPreserved s (zeroizeSecretHook s) := by
  unfold zeroizeSecretHook
  exact returnToLr_vm (setMem_vm s fun a => congrFun (perm_writeBytes_norm _ _ _) a)

private theorem compress256Hook_vm (s : State) :
    VmPreserved s (compress256Hook sha256Compress s) := by
  unfold compress256Hook
  exact returnToLr_vm (setMem_vm s fun a => congrFun (perm_writeBytes_norm _ _ _) a)

private theorem hookNoop_vm (s : State) : VmPreserved s (hookNoop s) :=
  VmPreserved.refl s

private theorem compress256Hook_rowSingle_ok :
    HookOk (compress256Hook sha256Compress) (compress256RowSingleSpec sha256Compress) := by
  intro ⟨stA, st, blkA, blk⟩ R s0 hrun hpre _
  simp only [compress256RowSingleSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hblk_len⟩, hmem⟩
  have hst_len : (shaStateBytes st).length = 32 := shaStateBytes_length st
  have hst_rd : s0.mem.readBytes stA 32 = shaStateBytes st := by
    have hrd := ((IsBlock.pointsToBytes stA (shaStateBytes st)).read hmem).2
    rwa [hst_len] at hrd
  have hmem_blk : s0.mem ⊨ (blkA ↦ₛ blk) ∗ ((stA ↦ₛ shaStateBytes st) ∗ R) := by
    ac_nf at hmem ⊢
  have hblk_rd : s0.mem.readBytes blkA 64 = blk := by
    have hrd := ((IsBlock.pointsToBytes blkA blk).read hmem_blk).2
    rwa [hblk_len] at hrd
  have heq := compress256Hook_one_eq sha256Compress hx0 hx1 hx2 rfl rfl hst_rd hblk_rd
  let outBytes := shaStateBytes (sha256Compress st blk)
  have hout_len : outBytes.length = 32 := shaStateBytes_length _
  have hmem_reg : s0.mem ⊨ memRegion stA outBytes.length ∗ ((blkA ↦ₛ blk) ∗ R) := by
    rw [hout_len]
    exact Satisfies.mono
      (sepConj_mono_left (Entails.trans (pointsToBytes_entails_memRegion stA _)
        (by rw [hst_len]; exact Entails.refl _)))
      hmem
  have hlen32 : outBytes.length ≤ 2 ^ 64 := by rw [hout_len]; decide
  rw [heq]
  refine ⟨keepsFrozen_writeBytes_of_memRegion outBytes hlen32 hmem_reg,
    rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
  have htr_eq :
      ((s0.setMem (s0.mem.writeBytes stA outBytes)).setPC (s0.readReg64 .lr)).trace = s0.trace :=
    rfl
  have hm_eq :
      ((s0.setMem (s0.mem.writeBytes stA outBytes)).setPC (s0.readReg64 .lr)).mem =
        s0.mem.writeBytes stA outBytes :=
    rfl
  dsimp only [compress256RowSingleSpec]
  rw [htr_eq, hm_eq]
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨trivial, satisfies_writeBytes outBytes hlen32 hmem_reg⟩

private theorem fromUtf8Hook_fs (s : State) : (fromUtf8Hook pureUtf8Err s).fs = s.fs := by
  unfold fromUtf8Hook; dsimp only
  split
  · rfl
  · split <;> rfl

private theorem durationSinceExactHook_fs (s : State) :
    (durationSinceExactHook s).fs = s.fs := by
  unfold durationSinceExactHook; dsimp only
  split
  · rfl
  · split <;> rfl

private theorem timeAddHook_fs (s : State) : (timeAddHook s).fs = s.fs := by
  unfold timeAddHook; dsimp only
  split <;> (split <;> rfl)

private theorem memrchrHook_fs (s : State) : (memrchrHook s).fs = s.fs := by
  unfold memrchrHook
  change (if (!s.mem.canRead (s.readReg64 .x1) (s.readReg64 .x2).toNat) = true then
      unmodelled "memrchr: unreadable bytes" s
    else
      match ((List.range (s.mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat).length).filter
        fun i => (s.mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat)[i]? ==
          some ((s.readReg64 .x0).setWidth 8)).getLast? with
      | some i => retHook (fun s => (s.writeReg64 .x0 1#64).writeReg64 .x1 (BitVec.ofNat 64 i)) s
      | none => retHook (fun s => s.writeReg64 .x0 0#64) s).fs = s.fs
  split
  · rfl
  · split <;> rfl

private theorem strlenHook_fs (s : State) : (strlenHook s).fs = s.fs := by
  unfold strlenHook; dsimp only
  split <;> rfl

private theorem hookMemmove_trace (s : State) : (hookMemmove s).trace = s.trace :=
  rfl

private theorem strlenHook_trace (s : State) : (strlenHook s).trace = s.trace := by
  unfold strlenHook; dsimp only
  split <;> rfl

private theorem memrchrHook_trace (s : State) : (memrchrHook s).trace = s.trace := by
  unfold memrchrHook
  change (if (!s.mem.canRead (s.readReg64 .x1) (s.readReg64 .x2).toNat) = true then
      unmodelled "memrchr: unreadable bytes" s
    else
      match ((List.range (s.mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat).length).filter
        fun i => (s.mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat)[i]? ==
          some ((s.readReg64 .x0).setWidth 8)).getLast? with
      | some i => retHook (fun s => (s.writeReg64 .x0 1#64).writeReg64 .x1 (BitVec.ofNat 64 i)) s
      | none => retHook (fun s => s.writeReg64 .x0 0#64) s).trace = s.trace
  split
  · rfl
  · split <;> rfl

private theorem fromUtf8Hook_trace (s : State) : (fromUtf8Hook pureUtf8Err s).trace = s.trace := by
  unfold fromUtf8Hook; dsimp only
  split
  · rfl
  · split <;> rfl

private theorem durationSinceExactHook_trace (s : State) :
    (durationSinceExactHook s).trace = s.trace := by
  unfold durationSinceExactHook; dsimp only
  split
  · rfl
  · split <;> rfl

private theorem timeAddHook_trace (s : State) : (timeAddHook s).trace = s.trace := by
  unfold timeAddHook; dsimp only
  split <;> (split <;> rfl)

private theorem writeStdoutHook_fs (s : State) : (writeStdoutHook s).fs = s.fs := by
  unfold writeStdoutHook; dsimp only
  split <;> rfl

private theorem writeStdoutHook_noAllocFailed (s : State) :
    ∃ d : List TraceEvent, (writeStdoutHook s).trace = s.trace ++ d ∧ allocFailedEvent ∉ d := by
  unfold writeStdoutHook; dsimp only
  split
  · exact ⟨[], by rw [List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · refine ⟨TraceEvent.ofBytes .stdout (s.mem.readBytes (s.readReg64 .x0) (s.readReg64 .x1).toNat),
      rfl, ?_⟩
    intro h
    simp only [TraceEvent.ofBytes, List.mem_map] at h
    rcases h with ⟨_, _, hb⟩
    nomatch hb

private theorem writeFileHook_noAllocFailed (s : State) :
    ∃ d : List TraceEvent, (writeFileHook s).trace = s.trace ++ d ∧ allocFailedEvent ∉ d := by
  unfold writeFileHook; dsimp only
  split
  · exact ⟨[], by rw [List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · split
    · exact ⟨[], by rw [List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
    · split
      · exact ⟨[], by rw [List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
      · have hnot :
            allocFailedEvent ∉ [.fileChanged (readPath s.mem (s.readReg64 .x0) (s.readReg64 .x1))] := by
          intro h
          simp only [List.mem_singleton] at h
          nomatch h
        split
        · exact ⟨_, rfl, hnot⟩
        · exact ⟨_, rfl, hnot⟩
        · exact ⟨_, rfl, hnot⟩

private theorem formatInnerHook0_vm (s : State) : VmPreserved s (formatInnerHook0 s) := by
  unfold formatInnerHook0 writeVecHeader
  refine retHook_vm (setMem_vm s fun a => ?_)
  simp only [perm_write64_norm]

private theorem pubFromSecretHook_vm (s : State) :
    VmPreserved s (pubFromSecretHook x25519PubFromSecretRef s) := by
  unfold pubFromSecretHook
  exact retHook_vm (setMem_vm s fun a => congrFun (perm_writeBytes_norm _ _ _) a)

private theorem diffieHellmanHook_vm (s : State) :
    VmPreserved s (diffieHellmanHook x25519Ref s) := by
  unfold diffieHellmanHook
  exact retHook_vm (setMem_vm s fun a => congrFun (perm_writeBytes_norm _ _ _) a)

/-! ## 3. Per-Row `GhostRowSpecOk` & Table-Level `ExtraFullListSpecOk` -/

private theorem memmove_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk "memmove" hookMemmove := by
  refine ⟨hookMemmove_fs, hookMemmove_fsT, ?_⟩
  change MemmoveRowSpec hookMemmove
  exact MemmoveRowSpec.of_vm (fun stk => hookMemmove_bounded_ok stk)
    (fun stk => hookMemmove_sessionBounded_ok stk) hookMemmove_vm hookMemmove_acp

private theorem bcmp_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk "bcmp" (cliBcmpHook pureBcmpFn) := by
  refine ⟨fun _ => rfl, cliBcmpHook_fsT pureBcmpFn, ?_⟩
  change BcmpRowSpec (cliBcmpHook pureBcmpFn)
  exact BcmpRowSpec.of_vm pureBcmpHook_ok pureBcmpHook_vregs_ok pureBcmpHook_vm

private theorem strlen_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk "strlen" strlenHook := by
  refine ⟨strlenHook_fs, strlenHook_fsT, ?_⟩
  change StrlenRowSpec strlenHook
  exact StrlenRowSpec.of_vm
    (fun stk => hookOk_withStrlenPadRO_of_hookOk (strlenHook_ok stk))
    (fun stk => hookOk_withStrlenPadRO_of_hookOk (strlenHook_ro_ok stk))
    strlenHook_vmPreserved

private theorem memrchr_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsMemrchrSym memrchrHook := by
  refine ⟨memrchrHook_fs, memrchrHook_fsT, ?_⟩
  have hd1 : (lsMemrchrSym == "bcmp") = false := by decide
  have hd2 : (lsMemrchrSym == "strlen") = false := by decide
  have hd3 : (lsMemrchrSym == "memmove") = false := by decide
  have hd4 : (lsMemrchrSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsMemrchrSym == lsMemrchrSym) = true := by decide
  unfold ExtraRowSpec
  simp only [hd1, hd2, hd3, hd4, hd5, Bool.false_eq_true, ↓reduceIte]
  exact MemrchrRowSpec.of_vm (fun stk _ _ => memrchrHook_ok stk)
    (fun stk _ _ => memrchrHook_ro_ok stk) memrchrHook_vmPreserved

private theorem fromUtf8_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsFromUtf8Sym (fromUtf8Hook pureUtf8Err) := by
  refine ⟨fromUtf8Hook_fs, fromUtf8Hook_fsT pureUtf8Err, ?_⟩
  have hd1 : (lsFromUtf8Sym == "bcmp") = false := by decide
  have hd2 : (lsFromUtf8Sym == "strlen") = false := by decide
  have hd3 : (lsFromUtf8Sym == "memmove") = false := by decide
  have hd4 : (lsFromUtf8Sym == lsFromUtf8Sym) = true := by decide
  unfold ExtraRowSpec
  simp only [hd1, hd2, hd3, hd4, Bool.false_eq_true, ↓reduceIte]
  exact FromUtf8RowSpec.of_vm (fun stk => fromUtf8Hook_ok stk pureUtf8Err)
    (fun stk => fromUtf8Hook_ro_ok stk pureUtf8Err) (fromUtf8Hook_vmPreserved pureUtf8Err)

private theorem durationSince_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsDurationSinceSym durationSinceExactHook := by
  refine ⟨durationSinceExactHook_fs, durationSinceExactHook_fsT, ?_⟩
  have hd1 : (lsDurationSinceSym == "bcmp") = false := by decide
  have hd2 : (lsDurationSinceSym == "strlen") = false := by decide
  have hd3 : (lsDurationSinceSym == "memmove") = false := by decide
  have hd4 : (lsDurationSinceSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsDurationSinceSym == lsMemrchrSym) = false := by decide
  have hd6 : (lsDurationSinceSym == lsDurationSinceSym) = true := by decide
  unfold ExtraRowSpec
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, Bool.false_eq_true, ↓reduceIte]
  exact DurationSinceRowSpec.of_vm durationSinceExactHook_bounded_ok
    (fun stk _ _ => durationSinceExactHook_epoch_at_ok stk) durationSinceExactHook_vm

private theorem timeAdd_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsTimeAddSym timeAddHook := by
  refine ⟨timeAddHook_fs, timeAddHook_fsT, ?_⟩
  have hd1 : (lsTimeAddSym == "bcmp") = false := by decide
  have hd2 : (lsTimeAddSym == "strlen") = false := by decide
  have hd3 : (lsTimeAddSym == "memmove") = false := by decide
  have hd4 : (lsTimeAddSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsTimeAddSym == lsMemrchrSym) = false := by decide
  have hd6 : (lsTimeAddSym == lsDurationSinceSym) = false := by decide
  have hd7 : (lsTimeAddSym == lsTimeAddSym) = true := by decide
  unfold ExtraRowSpec
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, Bool.false_eq_true, ↓reduceIte]
  exact TimeAddRowSpec.of_vm timeAddHook_ok timeAddHook_vm

private theorem blackBox_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsBlackBoxSym blackBoxHook := by
  refine ⟨fun _ => rfl, blackBoxHook_fsT, ?_⟩
  have hd1 : (lsBlackBoxSym == "bcmp") = false := by decide
  have hd2 : (lsBlackBoxSym == "strlen") = false := by decide
  have hd3 : (lsBlackBoxSym == "memmove") = false := by decide
  have hd4 : (lsBlackBoxSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsBlackBoxSym == lsMemrchrSym) = false := by decide
  have hd6 : (lsBlackBoxSym == lsDurationSinceSym) = false := by decide
  have hd7 : (lsBlackBoxSym == lsTimeAddSym) = false := by decide
  have hd8 : (lsBlackBoxSym == lsBlackBoxSym) = true := by decide
  unfold ExtraRowSpec
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, Bool.false_eq_true, ↓reduceIte]
  exact BlackBoxRowSpec.of_vm (fun stk _ _ => hookOk_withStack blackBoxHook_ok stk)
    blackBoxHook_vm

private theorem staticSecretDrop_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsStaticSecretDropSym zeroizeSecretHook := by
  refine ⟨fun _ => rfl, zeroizeSecretHook_fsT, ?_⟩
  have hd1 : (lsStaticSecretDropSym == "bcmp") = false := by decide
  have hd2 : (lsStaticSecretDropSym == "strlen") = false := by decide
  have hd3 : (lsStaticSecretDropSym == "memmove") = false := by decide
  have hd4 : (lsStaticSecretDropSym == lsFromUtf8Sym) = false := by decide
  have hd5 : (lsStaticSecretDropSym == lsMemrchrSym) = false := by decide
  have hd6 : (lsStaticSecretDropSym == lsDurationSinceSym) = false := by decide
  have hd7 : (lsStaticSecretDropSym == lsTimeAddSym) = false := by decide
  have hd8 : (lsStaticSecretDropSym == lsBlackBoxSym) = false := by decide
  have hd9 : (lsStaticSecretDropSym == lsStaticSecretDropSym) = true := by decide
  unfold ExtraRowSpec
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, Bool.false_eq_true, ↓reduceIte]
  exact StaticSecretDropRowSpec.of_vm zeroizeSecretHook_ok zeroizeSecretHook_vm

private theorem sharedSecretDrop_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsSharedSecretDropSym zeroizeSecretHook := by
  refine ⟨fun _ => rfl, zeroizeSecretHook_fsT, ?_⟩
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
  unfold ExtraRowSpec
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, Bool.false_eq_true, ↓reduceIte]
  exact SharedSecretDropRowSpec.of_vm zeroizeSecretHook_ok zeroizeSecretHook_vm

private theorem toEdwards_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsToEdwardsSym dalekMontToEdFallback := by
  refine ⟨fun s => (dalekMontToEdFallback_preserved s).2.1, dalekMontToEdFallback_fsT, ?_⟩
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
  unfold ExtraRowSpec
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, Bool.false_eq_true, ↓reduceIte]
  exact dalekMontToEdFallback_rowSpec

private theorem compress_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsCompressSym dalekCompressFallback := by
  refine ⟨fun s => (dalekCompressFallback_preserved s).2.1, dalekCompressFallback_fsT, ?_⟩
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
  unfold ExtraRowSpec
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, Bool.false_eq_true, ↓reduceIte]
  exact dalekCompressFallback_rowSpec

private theorem edNeg_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsEdNegSym (edNegHook dalekEdNegVec) := by
  refine ⟨fun _ => rfl, edNegFallback_fsT, ?_⟩
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
  unfold ExtraRowSpec
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, Bool.false_eq_true, ↓reduceIte]
  exact edNegFallback_rowSpec

private theorem torsionFree_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsTorsionFreeSym dalekTorsionFreeFallback := by
  refine ⟨fun s => (dalekTorsionFreeFallback_preserved s).2.1, dalekTorsionFreeFallback_fsT, ?_⟩
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
  unfold ExtraRowSpec
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14,
    Bool.false_eq_true, ↓reduceIte]
  exact dalekTorsionFreeFallback_rowSpec

private theorem dsmb_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsDsmbSym dalekDsmbFallback := by
  refine ⟨fun s => (dalekDsmbFallback_preserved s).2.1, dalekDsmbFallback_fsT, ?_⟩
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
  unfold ExtraRowSpec
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14, hd15,
    Bool.false_eq_true, ↓reduceIte]
  exact dalekDsmbFallback_rowSpec

private theorem scalarMod_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsScalarModSym dalekScalarModFallback := by
  refine ⟨fun s => (dalekScalarModFallback_preserved s).2.1, dalekScalarModFallback_fsT, ?_⟩
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
  unfold ExtraRowSpec
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14, hd15,
    hd16, Bool.false_eq_true, ↓reduceIte]
  exact dalekScalarModFallback_rowSpec

private theorem scalarWide_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsScalarWideSym dalekScalarWideFallback := by
  refine ⟨fun s => (dalekScalarWideFallback_preserved s).2.1, dalekScalarWideFallback_fsT, ?_⟩
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
  unfold ExtraRowSpec
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14, hd15,
    hd16, hd17, Bool.false_eq_true, ↓reduceIte]
  exact dalekScalarWideFallback_rowSpec

private theorem mlkemPk1_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsMlkemPk1Sym mlkemPk1Hook := by
  refine ⟨fun _ => rfl, mlkemPk1Fallback_fsT, ?_⟩
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
  unfold ExtraRowSpec
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14, hd15,
    hd16, hd17, hd18, Bool.false_eq_true, ↓reduceIte]
  exact mlkemPk1Hook_rowSpec

private theorem mlkemPk2_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsMlkemPk2Sym mlkemPk2Hook := by
  refine ⟨fun _ => rfl, mlkemPk2Fallback_fsT, ?_⟩
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
  unfold ExtraRowSpec
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14, hd15,
    hd16, hd17, hd18, hd19, Bool.false_eq_true, ↓reduceIte]
  exact mlkemPk2Hook_rowSpec

private theorem compress256_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsCompress256Sym (compress256Hook sha256Compress) := by
  refine ⟨fun _ => rfl, compress256Hook_fsT sha256Compress, ?_⟩
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
  unfold ExtraRowSpec
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14, hd15,
    hd16, hd17, hd18, hd19, hd20, Bool.false_eq_true, ↓reduceIte]
  exact Compress256RowSpec.of_vm
    (compress256Hook_keepsExec sha256Compress)
    (fun stk _ => compress256Hook_roBudget_ok sha256Compress stk)
    (fun stk _ => hookOk_withStack (compress256Hook_ok sha256Compress) stk)
    (fun stk _ => hookOk_withStack compress256Hook_rowSingle_ok stk)
    compress256Hook_vm

private theorem libcruxHmac_ghostRowSpecOk [LibsignalPlacement] {fHmac : State → State}
    (hFs : ∀ s : State, (fHmac s).fs = s.fs)
    (hFsT : HookFsTraced IsFsC fHmac) :
    GhostRowSpecOk lsLibcruxHmacSym fHmac := by
  refine ⟨hFs, hFsT, ?_⟩
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
  unfold ExtraRowSpec
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14, hd15,
    hd16, hd17, hd18, hd19, hd20, hd21, Bool.false_eq_true, ↓reduceIte]
  exact LibcruxHmacRowSpec.intro fHmac

private theorem aesEnc_ghostRowSpecOk [LibsignalPlacement] {fEnc : State → State}
    (hFs : ∀ s : State, (fEnc s).fs = s.fs)
    (hFsT : HookFsTraced IsFsC fEnc) :
    GhostRowSpecOk lsAesEncSym fEnc := by
  refine ⟨hFs, hFsT, ?_⟩
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
  unfold ExtraRowSpec
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14, hd15,
    hd16, hd17, hd18, hd19, hd20, hd21, hd22, Bool.false_eq_true, ↓reduceIte]
  exact AesEncRowSpec.intro fEnc

private theorem aesDec_ghostRowSpecOk [LibsignalPlacement] {fDec : State → State}
    (hFs : ∀ s : State, (fDec s).fs = s.fs)
    (hFsT : HookFsTraced IsFsC fDec) :
    GhostRowSpecOk lsAesDecSym fDec := by
  refine ⟨hFs, hFsT, ?_⟩
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
  unfold ExtraRowSpec
  simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14, hd15,
    hd16, hd17, hd18, hd19, hd20, hd21, hd22, hd23, Bool.false_eq_true, ↓reduceIte]
  exact AesDecRowSpec.intro fDec

private theorem compress512_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsCompress512Sym compress512Fallback := by
  refine ⟨fun _ => rfl, compress512Hook_fsT sha512CompressState, ?_⟩
  unfold ExtraRowSpec
  repeat rw [ite_eq_right (by decide)]
  rw [ite_eq_left (by decide)]
  exact compress512Fallback_rowSpec

private theorem kemEncaps_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsKemEncapsSym kemEncapsFallback := by
  refine ⟨fun s => (kemEncapsFallback_preserved s).2.1, kemEncapsFallback_fsT, ?_⟩
  unfold ExtraRowSpec
  repeat rw [ite_eq_right (by decide)]
  rw [ite_eq_left (by decide)]
  exact kemEncapsFallback_rowSpecAt kemEncapsTightStack

private theorem kemDecaps_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsKemDecapsSym kemDecapsFallback := by
  refine ⟨fun s => (kemDecapsFallback_preserved s).2.1, kemDecapsFallback_fsT, ?_⟩
  unfold ExtraRowSpec
  repeat rw [ite_eq_right (by decide)]
  rw [ite_eq_left (by decide)]
  exact kemDecapsFallback_rowSpecAt kemDecapsTightStack

private theorem mlkemFromSeed_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsMlkemFromSeedSym mlkemFromSeedFallback := by
  refine ⟨fun s => (mlkemFromSeedFallback_preserved s).2.1, mlkemFromSeedFallback_fsT, ?_⟩
  unfold ExtraRowSpec
  repeat rw [ite_eq_right (by decide)]
  rw [ite_eq_left (by decide)]
  exact mlkemFromSeedFallback_rowSpecAt mlkemFromSeedTightStack

private theorem mlkemEncaps1_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsMlkemEncaps1Sym mlkemEncaps1Fallback := by
  refine ⟨fun s => (mlkemEncaps1Fallback_preserved s).2.1, mlkemEncaps1Fallback_fsT, ?_⟩
  unfold ExtraRowSpec
  repeat rw [ite_eq_right (by decide)]
  rw [ite_eq_left (by decide)]
  exact mlkemEncaps1Fallback_rowSpecAt mlkemEncaps1TightStack

private theorem mlkemEncaps2_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsMlkemEncaps2Sym mlkemEncaps2Fallback := by
  refine ⟨fun s => (mlkemEncaps2Fallback_preserved s).2.1, mlkemEncaps2Fallback_fsT, ?_⟩
  unfold ExtraRowSpec
  repeat rw [ite_eq_right (by decide)]
  rw [ite_eq_left (by decide)]
  exact mlkemEncaps2Fallback_rowSpecAt mlkemEncaps2TightStack

private theorem mlkemDecaps_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsMlkemDecapsSym mlkemDecapsFallback := by
  refine ⟨fun s => (mlkemDecapsFallback_preserved s).2.1, mlkemDecapsFallback_fsT, ?_⟩
  unfold ExtraRowSpec
  repeat rw [ite_eq_right (by decide)]
  rw [ite_eq_left (by decide)]
  exact mlkemDecapsFallback_rowSpecAt mlkemDecapsTightStack

private theorem mlkemValidatePk_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsMlkemValidatePkSym mlkemValidatePkFallback := by
  refine ⟨fun s => (mlkemValidatePkFallback_preserved s).2.1, mlkemValidatePkFallback_fsT, ?_⟩
  unfold ExtraRowSpec
  repeat rw [ite_eq_right (by decide)]
  rw [ite_eq_left (by decide)]
  exact mlkemValidatePkFallback_rowSpecAt mlkemValidatePkTightStack

private theorem writeFile_extraRowOk [LibsignalPlacement] :
    ExtraRowOk lsWriteFileSym writeFileHook :=
  (WriteFileRowOk.mk writeFileHook_fsT (WriteFileRowSpec.intro writeFileHook)).toExtraRowOk

private theorem writeStdout_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsWriteStdoutSym writeStdoutHook := by
  refine ⟨writeStdoutHook_fs, writeStdoutHook_fsT, ?_⟩
  unfold ExtraRowSpec
  iterate 20 rw [ite_eq_right (by decide)]
  repeat rw [ite_eq_right (by decide)]
  rw [ite_eq_left (by decide)]
  exact WriteStdoutRowSpec.intro writeStdoutHook

private theorem fmtWrite_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsFmtWriteSym fmtWriteHook0 := by
  refine ⟨fun _ => rfl, fmtWriteHook0_fsT, ?_⟩
  unfold ExtraRowSpec
  iterate 20 rw [ite_eq_right (by decide)]
  repeat rw [ite_eq_right (by decide)]
  rw [ite_eq_left (by decide)]
  exact FmtWriteRowSpec.intro fmtWriteHook0

private theorem formatInner_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsFormatInnerSym formatInnerHook0 := by
  refine ⟨fun _ => rfl, formatInnerHook0_fsT, ?_⟩
  unfold ExtraRowSpec
  iterate 20 rw [ite_eq_right (by decide)]
  repeat rw [ite_eq_right (by decide)]
  rw [ite_eq_left (by decide)]
  exact FormatInnerRowSpec.intro formatInnerHook0

private theorem pubFromSecret_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsPubFromSecretSym (pubFromSecretHook x25519PubFromSecretRef) := by
  refine ⟨fun _ => rfl, pubFromSecretHook_fsT x25519PubFromSecretRef, ?_⟩
  unfold ExtraRowSpec
  iterate 35 rw [ite_eq_right (by decide)]
  rw [ite_eq_left (by decide)]
  exact pubFromSecretFallback_rowSpec

private theorem diffieHellman_ghostRowSpecOk [LibsignalPlacement] :
    GhostRowSpecOk lsDiffieHellmanSym (diffieHellmanHook x25519Ref) := by
  refine ⟨fun _ => rfl, diffieHellmanHook_fsT x25519Ref, ?_⟩
  unfold ExtraRowSpec
  iterate 36 rw [ite_eq_right (by decide)]
  rw [ite_eq_left (by decide)]
  exact diffieHellmanFallback_rowSpec

private theorem spqrOnceCall_ghostRowSpecOk [LibsignalPlacement] {fOnce : State → State}
    (hFs : ∀ s : State, (fOnce s).fs = s.fs)
    (hFsT : HookFsTraced IsFsC fOnce) :
    GhostRowSpecOk lsSpqrOnceCallSym fOnce := by
  refine ⟨hFs, hFsT, ?_⟩
  unfold ExtraRowSpec
  iterate 37 rw [ite_eq_right (by decide)]
  rw [ite_eq_left (by decide)]
  trivial

theorem pureExtraGhostsWithCryptoAndOnce_listSpecOk [LibsignalPlacement]
    {fHmac fEnc fDec fOnce : State → State}
    (hFsHmac : ∀ s : State, (fHmac s).fs = s.fs)
    (hFsTHmac : HookFsTraced IsFsC fHmac)
    (hFsEnc : ∀ s : State, (fEnc s).fs = s.fs)
    (hFsTEnc : HookFsTraced IsFsC fEnc)
    (hFsDec : ∀ s : State, (fDec s).fs = s.fs)
    (hFsTDec : HookFsTraced IsFsC fDec)
    (hFsOnce : ∀ s : State, (fOnce s).fs = s.fs)
    (hFsTOnce : HookFsTraced IsFsC fOnce) :
    ExtraListSpecOk (pureExtraGhostsWithCryptoAndOnce fHmac fEnc fDec fOnce) where
  fresh := pureExtraGhostsWithCryptoAndOnce_fresh fHmac fEnc fDec fOnce
  rowOk := by
    intro sym f hLook
    rcases pureExtraGhostsWithCryptoAndOnce_lookup_cases hLook with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact memmove_ghostRowSpecOk.toExtraRowOk
    · exact bcmp_ghostRowSpecOk.toExtraRowOk
    · exact strlen_ghostRowSpecOk.toExtraRowOk
    · exact memrchr_ghostRowSpecOk.toExtraRowOk
    · exact fromUtf8_ghostRowSpecOk.toExtraRowOk
    · exact durationSince_ghostRowSpecOk.toExtraRowOk
    · exact timeAdd_ghostRowSpecOk.toExtraRowOk
    · exact blackBox_ghostRowSpecOk.toExtraRowOk
    · exact staticSecretDrop_ghostRowSpecOk.toExtraRowOk
    · exact sharedSecretDrop_ghostRowSpecOk.toExtraRowOk
    · exact toEdwards_ghostRowSpecOk.toExtraRowOk
    · exact compress_ghostRowSpecOk.toExtraRowOk
    · exact edNeg_ghostRowSpecOk.toExtraRowOk
    · exact torsionFree_ghostRowSpecOk.toExtraRowOk
    · exact dsmb_ghostRowSpecOk.toExtraRowOk
    · exact scalarMod_ghostRowSpecOk.toExtraRowOk
    · exact scalarWide_ghostRowSpecOk.toExtraRowOk
    · exact mlkemPk1_ghostRowSpecOk.toExtraRowOk
    · exact mlkemPk2_ghostRowSpecOk.toExtraRowOk
    · exact compress256_ghostRowSpecOk.toExtraRowOk
    · exact (libcruxHmac_ghostRowSpecOk hFsHmac hFsTHmac).toExtraRowOk
    · exact (aesEnc_ghostRowSpecOk hFsEnc hFsTEnc).toExtraRowOk
    · exact (aesDec_ghostRowSpecOk hFsDec hFsTDec).toExtraRowOk
    · exact compress512_ghostRowSpecOk.toExtraRowOk
    · exact kemEncaps_ghostRowSpecOk.toExtraRowOk
    · exact kemDecaps_ghostRowSpecOk.toExtraRowOk
    · exact mlkemFromSeed_ghostRowSpecOk.toExtraRowOk
    · exact mlkemEncaps1_ghostRowSpecOk.toExtraRowOk
    · exact mlkemEncaps2_ghostRowSpecOk.toExtraRowOk
    · exact mlkemDecaps_ghostRowSpecOk.toExtraRowOk
    · exact mlkemValidatePk_ghostRowSpecOk.toExtraRowOk
    · exact writeFile_extraRowOk
    · exact writeStdout_ghostRowSpecOk.toExtraRowOk
    · exact fmtWrite_ghostRowSpecOk.toExtraRowOk
    · exact formatInner_ghostRowSpecOk.toExtraRowOk
    · exact pubFromSecret_ghostRowSpecOk.toExtraRowOk
    · exact diffieHellman_ghostRowSpecOk.toExtraRowOk
    · exact (spqrOnceCall_ghostRowSpecOk hFsOnce hFsTOnce).toExtraRowOk

theorem pureExtraGhostsWithCrypto_listSpecOk [LibsignalPlacement]
    {fHmac fEnc fDec : State → State}
    (hFsHmac : ∀ s : State, (fHmac s).fs = s.fs)
    (hFsTHmac : HookFsTraced IsFsC fHmac)
    (hFsEnc : ∀ s : State, (fEnc s).fs = s.fs)
    (hFsTEnc : HookFsTraced IsFsC fEnc)
    (hFsDec : ∀ s : State, (fDec s).fs = s.fs)
    (hFsTDec : HookFsTraced IsFsC fDec) :
    ExtraListSpecOk (pureExtraGhostsWithCrypto fHmac fEnc fDec) :=
  pureExtraGhostsWithCryptoAndOnce_listSpecOk hFsHmac hFsTHmac hFsEnc hFsTEnc hFsDec hFsTDec
    (fun _ => rfl) hookNoop_fsT

theorem pureExtraGhostsWithCryptoAndOnce_specOk [LibsignalPlacement]
    {fHmac fEnc fDec fOnce : State → State}
    (hFsHmac : ∀ s : State, (fHmac s).fs = s.fs)
    (hFsTHmac : HookFsTraced IsFsC fHmac)
    (hFsEnc : ∀ s : State, (fEnc s).fs = s.fs)
    (hFsTEnc : HookFsTraced IsFsC fEnc)
    (hFsDec : ∀ s : State, (fDec s).fs = s.fs)
    (hFsTDec : HookFsTraced IsFsC fDec)
    (hFsOnce : ∀ s : State, (fOnce s).fs = s.fs)
    (hFsTOnce : HookFsTraced IsFsC fOnce) :
    ExtraFullListSpecOk (pureExtraGhostsWithCryptoAndOnce fHmac fEnc fDec fOnce) where
  toExtraListSpecOk :=
    pureExtraGhostsWithCryptoAndOnce_listSpecOk hFsHmac hFsTHmac hFsEnc hFsTEnc hFsDec hFsTDec
      hFsOnce hFsTOnce
  complete := pureExtraGhostsWithCryptoAndOnce_complete fHmac fEnc fDec fOnce

theorem pureExtraGhostsWithCrypto_specOk [LibsignalPlacement]
    {fHmac fEnc fDec : State → State}
    (hFsHmac : ∀ s : State, (fHmac s).fs = s.fs)
    (hFsTHmac : HookFsTraced IsFsC fHmac)
    (hFsEnc : ∀ s : State, (fEnc s).fs = s.fs)
    (hFsTEnc : HookFsTraced IsFsC fEnc)
    (hFsDec : ∀ s : State, (fDec s).fs = s.fs)
    (hFsTDec : HookFsTraced IsFsC fDec) :
    ExtraFullListSpecOk (pureExtraGhostsWithCrypto fHmac fEnc fDec) :=
  pureExtraGhostsWithCryptoAndOnce_specOk hFsHmac hFsTHmac hFsEnc hFsTEnc hFsDec hFsTDec
    (fun _ => rfl) hookNoop_fsT

theorem pureExtraGhostsWithOnce_specOk [LibsignalPlacement] {fOnce : State → State}
    (hFsOnce : ∀ s : State, (fOnce s).fs = s.fs)
    (hFsTOnce : HookFsTraced IsFsC fOnce) :
    ExtraFullListSpecOk (pureExtraGhostsWithOnce fOnce) :=
  pureExtraGhostsWithCryptoAndOnce_specOk (fun _ => rfl) hookNoop_fsT (fun _ => rfl) hookNoop_fsT
    (fun _ => rfl) hookNoop_fsT hFsOnce hFsTOnce

theorem pureExtraGhostsWithHmac_listSpecOk [LibsignalPlacement] {fHmac : State → State}
    (hFs : ∀ s : State, (fHmac s).fs = s.fs)
    (hFsT : HookFsTraced IsFsC fHmac) :
    ExtraListSpecOk (pureExtraGhostsWithHmac fHmac) :=
  pureExtraGhostsWithCrypto_listSpecOk hFs hFsT (fun _ => rfl) hookNoop_fsT (fun _ => rfl)
    hookNoop_fsT

theorem pureExtraGhostsWithHmac_specOk [LibsignalPlacement] {fHmac : State → State}
    (hFs : ∀ s : State, (fHmac s).fs = s.fs)
    (hFsT : HookFsTraced IsFsC fHmac) :
    ExtraFullListSpecOk (pureExtraGhostsWithHmac fHmac) :=
  pureExtraGhostsWithCrypto_specOk hFs hFsT (fun _ => rfl) hookNoop_fsT (fun _ => rfl)
    hookNoop_fsT

theorem pureExtraGhostsWithAes_listSpecOk [LibsignalPlacement] {fEnc fDec : State → State}
    (hFsEnc : ∀ s : State, (fEnc s).fs = s.fs)
    (hFsTEnc : HookFsTraced IsFsC fEnc)
    (hFsDec : ∀ s : State, (fDec s).fs = s.fs)
    (hFsTDec : HookFsTraced IsFsC fDec) :
    ExtraListSpecOk (pureExtraGhostsWithAes fEnc fDec) :=
  pureExtraGhostsWithCrypto_listSpecOk (fun _ => rfl) hookNoop_fsT hFsEnc hFsTEnc hFsDec hFsTDec

theorem pureExtraGhostsWithAes_specOk [LibsignalPlacement] {fEnc fDec : State → State}
    (hFsEnc : ∀ s : State, (fEnc s).fs = s.fs)
    (hFsTEnc : HookFsTraced IsFsC fEnc)
    (hFsDec : ∀ s : State, (fDec s).fs = s.fs)
    (hFsTDec : HookFsTraced IsFsC fDec) :
    ExtraFullListSpecOk (pureExtraGhostsWithAes fEnc fDec) :=
  pureExtraGhostsWithCrypto_specOk (fun _ => rfl) hookNoop_fsT hFsEnc hFsTEnc hFsDec hFsTDec

theorem pureExtraGhosts_listSpecOk [LibsignalPlacement] :
    ExtraListSpecOk pureExtraGhosts :=
  pureExtraGhostsWithCrypto_listSpecOk (fun _ => rfl) hookNoop_fsT (fun _ => rfl) hookNoop_fsT
    (fun _ => rfl) hookNoop_fsT

/-- Complete 37-row consumer spec bundle (`ExtraFullListSpecOk`) for `pureExtraGhosts`
    (`0` `LinkedAt` / `MultiPlacement` hypotheses). -/
theorem pureExtraGhosts_specOk [LibsignalPlacement] :
    ExtraFullListSpecOk pureExtraGhosts :=
  pureExtraGhostsWithCrypto_specOk (fun _ => rfl) hookNoop_fsT (fun _ => rfl) hookNoop_fsT
    (fun _ => rfl) hookNoop_fsT

/-! ## 4. Placement-Free `fsT`, `noAllocFailed`, `VmPreserved`, and `ExecFrozen` Helpers -/

theorem pureExtraGhostsWithCryptoAndOnce_lookup_fsT {fHmac fEnc fDec fOnce : State → State}
    (hFsTHmac : HookFsTraced IsFsC fHmac)
    (hFsTEnc : HookFsTraced IsFsC fEnc)
    (hFsTDec : HookFsTraced IsFsC fDec)
    (hFsTOnce : HookFsTraced IsFsC fOnce)
    {sym : String} {f : State → State}
    (hLook : (pureExtraGhostsWithCryptoAndOnce fHmac fEnc fDec fOnce).lookup sym = some f) :
    HookFsTraced IsFsC f := by
  rcases pureExtraGhostsWithCryptoAndOnce_lookup_cases hLook with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hookMemmove_fsT
  · exact cliBcmpHook_fsT pureBcmpFn
  · exact strlenHook_fsT
  · exact memrchrHook_fsT
  · exact fromUtf8Hook_fsT pureUtf8Err
  · exact durationSinceExactHook_fsT
  · exact timeAddHook_fsT
  · exact blackBoxHook_fsT
  · exact zeroizeSecretHook_fsT
  · exact zeroizeSecretHook_fsT
  · exact dalekMontToEdFallback_fsT
  · exact dalekCompressFallback_fsT
  · exact edNegHook_fsT dalekEdNegVec
  · exact dalekTorsionFreeFallback_fsT
  · exact dalekDsmbFallback_fsT
  · exact dalekScalarModFallback_fsT
  · exact dalekScalarWideFallback_fsT
  · exact mlkemPk1Hook_fsT
  · exact mlkemPk2Hook_fsT
  · exact compress256Hook_fsT sha256Compress
  · exact hFsTHmac
  · exact hFsTEnc
  · exact hFsTDec
  · exact compress512Hook_fsT sha512CompressState
  · exact kemEncapsFallback_fsT
  · exact kemDecapsFallback_fsT
  · exact mlkemFromSeedFallback_fsT
  · exact mlkemEncaps1Fallback_fsT
  · exact mlkemEncaps2Fallback_fsT
  · exact mlkemDecapsFallback_fsT
  · exact mlkemValidatePkFallback_fsT
  · exact writeFileHook_fsT
  · exact writeStdoutHook_fsT
  · exact fmtWriteHook0_fsT
  · exact formatInnerHook0_fsT
  · exact pubFromSecretHook_fsT x25519PubFromSecretRef
  · exact diffieHellmanHook_fsT x25519Ref
  · exact hFsTOnce

theorem pureExtraGhostsWithCrypto_lookup_fsT {fHmac fEnc fDec : State → State}
    (hFsTHmac : HookFsTraced IsFsC fHmac)
    (hFsTEnc : HookFsTraced IsFsC fEnc)
    (hFsTDec : HookFsTraced IsFsC fDec)
    {sym : String} {f : State → State}
    (hLook : (pureExtraGhostsWithCrypto fHmac fEnc fDec).lookup sym = some f) :
    HookFsTraced IsFsC f :=
  pureExtraGhostsWithCryptoAndOnce_lookup_fsT hFsTHmac hFsTEnc hFsTDec hookNoop_fsT hLook

theorem pureExtraGhostsWithCryptoAndOnce_fsT {fHmac fEnc fDec fOnce : State → State}
    (hFsTHmac : HookFsTraced IsFsC fHmac)
    (hFsTEnc : HookFsTraced IsFsC fEnc)
    (hFsTDec : HookFsTraced IsFsC fDec)
    (hFsTOnce : HookFsTraced IsFsC fOnce) :
    ∀ sym f,
      cliExtraGhostSyms.contains sym = true →
      (pureExtraGhostsWithCryptoAndOnce fHmac fEnc fDec fOnce).lookup sym = some f →
      HookFsTraced IsFsC f :=
  fun _ _ _ hLook =>
    pureExtraGhostsWithCryptoAndOnce_lookup_fsT hFsTHmac hFsTEnc hFsTDec hFsTOnce hLook

theorem pureExtraGhostsWithCrypto_fsT {fHmac fEnc fDec : State → State}
    (hFsTHmac : HookFsTraced IsFsC fHmac)
    (hFsTEnc : HookFsTraced IsFsC fEnc)
    (hFsTDec : HookFsTraced IsFsC fDec) :
    ∀ sym f,
      cliExtraGhostSyms.contains sym = true →
      (pureExtraGhostsWithCrypto fHmac fEnc fDec).lookup sym = some f →
      HookFsTraced IsFsC f :=
  fun _ _ _ hLook => pureExtraGhostsWithCrypto_lookup_fsT hFsTHmac hFsTEnc hFsTDec hLook

theorem pureExtraGhostsWithOnce_fsT {fOnce : State → State}
    (hFsTOnce : HookFsTraced IsFsC fOnce) :
    ∀ sym f,
      cliExtraGhostSyms.contains sym = true →
      (pureExtraGhostsWithOnce fOnce).lookup sym = some f →
      HookFsTraced IsFsC f :=
  pureExtraGhostsWithCryptoAndOnce_fsT hookNoop_fsT hookNoop_fsT hookNoop_fsT hFsTOnce

theorem pureExtraGhostsWithHmac_lookup_fsT {fHmac : State → State}
    (hFsT : HookFsTraced IsFsC fHmac) {sym : String} {f : State → State}
    (hLook : (pureExtraGhostsWithHmac fHmac).lookup sym = some f) :
    HookFsTraced IsFsC f :=
  pureExtraGhostsWithCrypto_lookup_fsT hFsT hookNoop_fsT hookNoop_fsT hLook

theorem pureExtraGhostsWithHmac_fsT {fHmac : State → State}
    (hFsT : HookFsTraced IsFsC fHmac) :
    ∀ sym f,
      cliExtraGhostSyms.contains sym = true →
      (pureExtraGhostsWithHmac fHmac).lookup sym = some f →
      HookFsTraced IsFsC f :=
  fun _ _ _ hLook => pureExtraGhostsWithHmac_lookup_fsT hFsT hLook

theorem pureExtraGhostsWithAes_lookup_fsT {fEnc fDec : State → State}
    (hFsTEnc : HookFsTraced IsFsC fEnc)
    (hFsTDec : HookFsTraced IsFsC fDec) {sym : String} {f : State → State}
    (hLook : (pureExtraGhostsWithAes fEnc fDec).lookup sym = some f) :
    HookFsTraced IsFsC f :=
  pureExtraGhostsWithCrypto_lookup_fsT hookNoop_fsT hFsTEnc hFsTDec hLook

theorem pureExtraGhostsWithAes_fsT {fEnc fDec : State → State}
    (hFsTEnc : HookFsTraced IsFsC fEnc)
    (hFsTDec : HookFsTraced IsFsC fDec) :
    ∀ sym f,
      cliExtraGhostSyms.contains sym = true →
      (pureExtraGhostsWithAes fEnc fDec).lookup sym = some f →
      HookFsTraced IsFsC f :=
  fun _ _ _ hLook => pureExtraGhostsWithAes_lookup_fsT hFsTEnc hFsTDec hLook

theorem pureExtraGhosts_lookup_fsT {sym : String} {f : State → State}
    (hLook : pureExtraGhosts.lookup sym = some f) :
    HookFsTraced IsFsC f :=
  pureExtraGhostsWithCrypto_lookup_fsT hookNoop_fsT hookNoop_fsT hookNoop_fsT hLook

/-- `CliGhostHooksFs.extra_fsT` companion for `pureExtraGhosts` (placement-free). -/
theorem pureExtraGhosts_fsT :
    ∀ sym f,
      cliExtraGhostSyms.contains sym = true →
      pureExtraGhosts.lookup sym = some f →
      HookFsTraced IsFsC f :=
  fun _ _ _ hLook => pureExtraGhosts_lookup_fsT hLook

theorem pureExtraGhostsWithCryptoAndOnce_fs_eq {fHmac fEnc fDec fOnce : State → State}
    (hFsHmac : ∀ s : State, (fHmac s).fs = s.fs)
    (hFsEnc : ∀ s : State, (fEnc s).fs = s.fs)
    (hFsDec : ∀ s : State, (fDec s).fs = s.fs)
    (hFsOnce : ∀ s : State, (fOnce s).fs = s.fs)
    {sym : String} {f : State → State}
    (hLook : (pureExtraGhostsWithCryptoAndOnce fHmac fEnc fDec fOnce).lookup sym = some f)
    (s : State)
    (hne : (sym == lsWriteFileSym) = false := by decide) :
    (f s).fs = s.fs := by
  rcases pureExtraGhostsWithCryptoAndOnce_lookup_cases hLook with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hookMemmove_fs s
  · rfl
  · exact strlenHook_fs s
  · exact memrchrHook_fs s
  · exact fromUtf8Hook_fs s
  · exact durationSinceExactHook_fs s
  · exact timeAddHook_fs s
  · rfl
  · rfl
  · rfl
  · exact (dalekMontToEdFallback_preserved s).2.1
  · exact (dalekCompressFallback_preserved s).2.1
  · rfl
  · exact (dalekTorsionFreeFallback_preserved s).2.1
  · exact (dalekDsmbFallback_preserved s).2.1
  · exact (dalekScalarModFallback_preserved s).2.1
  · exact (dalekScalarWideFallback_preserved s).2.1
  · rfl
  · rfl
  · rfl
  · exact hFsHmac s
  · exact hFsEnc s
  · exact hFsDec s
  · rfl
  · exact (kemEncapsFallback_preserved s).2.1
  · exact (kemDecapsFallback_preserved s).2.1
  · exact (mlkemFromSeedFallback_preserved s).2.1
  · exact (mlkemEncaps1Fallback_preserved s).2.1
  · exact (mlkemEncaps2Fallback_preserved s).2.1
  · exact (mlkemDecapsFallback_preserved s).2.1
  · exact (mlkemValidatePkFallback_preserved s).2.1
  · simp at hne
  · exact writeStdoutHook_fs s
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hFsOnce s

theorem pureExtraGhostsWithCrypto_fs_eq {fHmac fEnc fDec : State → State}
    (hFsHmac : ∀ s : State, (fHmac s).fs = s.fs)
    (hFsEnc : ∀ s : State, (fEnc s).fs = s.fs)
    (hFsDec : ∀ s : State, (fDec s).fs = s.fs) {sym : String} {f : State → State}
    (hLook : (pureExtraGhostsWithCrypto fHmac fEnc fDec).lookup sym = some f) (s : State)
    (hne : (sym == lsWriteFileSym) = false := by decide) :
    (f s).fs = s.fs :=
  pureExtraGhostsWithCryptoAndOnce_fs_eq (fOnce := hookNoop)
    hFsHmac hFsEnc hFsDec (fun _ => rfl) hLook s hne

theorem pureExtraGhostsWithHmac_fs_eq {fHmac : State → State}
    (hFs : ∀ s : State, (fHmac s).fs = s.fs) {sym : String} {f : State → State}
    (hLook : (pureExtraGhostsWithHmac fHmac).lookup sym = some f) (s : State)
    (hne : (sym == lsWriteFileSym) = false := by decide) :
    (f s).fs = s.fs :=
  pureExtraGhostsWithCrypto_fs_eq (fEnc := hookNoop) (fDec := hookNoop)
    hFs (fun _ => rfl) (fun _ => rfl) hLook s hne

theorem pureExtraGhostsWithAes_fs_eq {fEnc fDec : State → State}
    (hFsEnc : ∀ s : State, (fEnc s).fs = s.fs)
    (hFsDec : ∀ s : State, (fDec s).fs = s.fs) {sym : String} {f : State → State}
    (hLook : (pureExtraGhostsWithAes fEnc fDec).lookup sym = some f) (s : State)
    (hne : (sym == lsWriteFileSym) = false := by decide) :
    (f s).fs = s.fs :=
  pureExtraGhostsWithCrypto_fs_eq (fHmac := hookNoop) (fun _ => rfl) hFsEnc hFsDec hLook s hne

theorem pureExtraGhosts_fs_eq {sym : String} {f : State → State}
    (hLook : pureExtraGhosts.lookup sym = some f) (s : State)
    (hne : (sym == lsWriteFileSym) = false := by decide) :
    (f s).fs = s.fs :=
  pureExtraGhostsWithCrypto_fs_eq (fHmac := hookNoop) (fEnc := hookNoop) (fDec := hookNoop)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hLook s hne

theorem pureExtraGhosts_trace_eq {sym : String} {f : State → State}
    (hLook : pureExtraGhosts.lookup sym = some f) (s : State)
    (hneWf : (sym == lsWriteFileSym) = false := by decide)
    (hneWs : (sym == lsWriteStdoutSym) = false := by decide) :
    (f s).trace = s.trace := by
  rcases pureExtraGhosts_lookup_cases hLook with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hookMemmove_trace s
  · rfl
  · exact strlenHook_trace s
  · exact memrchrHook_trace s
  · exact fromUtf8Hook_trace s
  · exact durationSinceExactHook_trace s
  · exact timeAddHook_trace s
  · rfl
  · rfl
  · rfl
  · exact (dalekMontToEdFallback_preserved s).2.2.1
  · exact (dalekCompressFallback_preserved s).2.2.1
  · rfl
  · exact (dalekTorsionFreeFallback_preserved s).2.2.1
  · exact (dalekDsmbFallback_preserved s).2.2.1
  · exact (dalekScalarModFallback_preserved s).2.2.1
  · exact (dalekScalarWideFallback_preserved s).2.2.1
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (kemEncapsFallback_preserved s).2.2.1
  · exact (kemDecapsFallback_preserved s).2.2.1
  · exact (mlkemFromSeedFallback_preserved s).2.2.1
  · exact (mlkemEncaps1Fallback_preserved s).2.2.1
  · exact (mlkemEncaps2Fallback_preserved s).2.2.1
  · exact (mlkemDecapsFallback_preserved s).2.2.1
  · exact (mlkemValidatePkFallback_preserved s).2.2.1
  · simp at hneWf
  · simp at hneWs
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem pureExtraGhostsWithCryptoAndOnce_noAllocFailed {fHmac fEnc fDec fOnce : State → State}
    (hNoFailHmac : ∀ s : State,
      ∃ d : List TraceEvent, (fHmac s).trace = s.trace ++ d ∧ allocFailedEvent ∉ d)
    (hNoFailEnc : ∀ s : State,
      ∃ d : List TraceEvent, (fEnc s).trace = s.trace ++ d ∧ allocFailedEvent ∉ d)
    (hNoFailDec : ∀ s : State,
      ∃ d : List TraceEvent, (fDec s).trace = s.trace ++ d ∧ allocFailedEvent ∉ d)
    (hNoFailOnce : ∀ s : State,
      ∃ d : List TraceEvent, (fOnce s).trace = s.trace ++ d ∧ allocFailedEvent ∉ d)
    {sym : String} {f : State → State}
    (hLook : (pureExtraGhostsWithCryptoAndOnce fHmac fEnc fDec fOnce).lookup sym = some f)
    (s : State) :
    ∃ d : List TraceEvent, (f s).trace = s.trace ++ d ∧ allocFailedEvent ∉ d := by
  rcases pureExtraGhostsWithCryptoAndOnce_lookup_cases hLook with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨[], by rw [hookMemmove_trace s, List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact ⟨[], by rw [List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact ⟨[], by rw [strlenHook_trace s, List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact ⟨[], by rw [memrchrHook_trace s, List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact ⟨[], by rw [fromUtf8Hook_trace s, List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact ⟨[], by rw [durationSinceExactHook_trace s, List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact ⟨[], by rw [timeAddHook_trace s, List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact ⟨[], by rw [List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact ⟨[], by rw [List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact ⟨[], by rw [List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact ⟨[], by rw [(dalekMontToEdFallback_preserved s).2.2.1, List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact ⟨[], by rw [(dalekCompressFallback_preserved s).2.2.1, List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact ⟨[], by rw [List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact ⟨[], by rw [(dalekTorsionFreeFallback_preserved s).2.2.1, List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact ⟨[], by rw [(dalekDsmbFallback_preserved s).2.2.1, List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact ⟨[], by rw [(dalekScalarModFallback_preserved s).2.2.1, List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact ⟨[], by rw [(dalekScalarWideFallback_preserved s).2.2.1, List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact ⟨[], by rw [List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact ⟨[], by rw [List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact ⟨[], by rw [List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact hNoFailHmac s
  · exact hNoFailEnc s
  · exact hNoFailDec s
  · exact ⟨[], by rw [List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact ⟨[], by rw [(kemEncapsFallback_preserved s).2.2.1, List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact ⟨[], by rw [(kemDecapsFallback_preserved s).2.2.1, List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact ⟨[], by rw [(mlkemFromSeedFallback_preserved s).2.2.1, List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact ⟨[], by rw [(mlkemEncaps1Fallback_preserved s).2.2.1, List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact ⟨[], by rw [(mlkemEncaps2Fallback_preserved s).2.2.1, List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact ⟨[], by rw [(mlkemDecapsFallback_preserved s).2.2.1, List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact ⟨[], by rw [(mlkemValidatePkFallback_preserved s).2.2.1, List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact writeFileHook_noAllocFailed s
  · exact writeStdoutHook_noAllocFailed s
  · exact ⟨[], by rw [List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact ⟨[], by rw [List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact ⟨[], by rw [List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact ⟨[], by rw [List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩
  · exact hNoFailOnce s

theorem pureExtraGhostsWithCrypto_noAllocFailed {fHmac fEnc fDec : State → State}
    (hNoFailHmac : ∀ s : State,
      ∃ d : List TraceEvent, (fHmac s).trace = s.trace ++ d ∧ allocFailedEvent ∉ d)
    (hNoFailEnc : ∀ s : State,
      ∃ d : List TraceEvent, (fEnc s).trace = s.trace ++ d ∧ allocFailedEvent ∉ d)
    (hNoFailDec : ∀ s : State,
      ∃ d : List TraceEvent, (fDec s).trace = s.trace ++ d ∧ allocFailedEvent ∉ d)
    {sym : String} {f : State → State}
    (hLook : (pureExtraGhostsWithCrypto fHmac fEnc fDec).lookup sym = some f) (s : State) :
    ∃ d : List TraceEvent, (f s).trace = s.trace ++ d ∧ allocFailedEvent ∉ d :=
  pureExtraGhostsWithCryptoAndOnce_noAllocFailed hNoFailHmac hNoFailEnc hNoFailDec
    (fun _ => ⟨[], by rw [List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩) hLook s

theorem pureExtraGhostsWithOnce_noAllocFailed {fOnce : State → State}
    (hNoFailOnce : ∀ s : State,
      ∃ d : List TraceEvent, (fOnce s).trace = s.trace ++ d ∧ allocFailedEvent ∉ d)
    {sym : String} {f : State → State}
    (hLook : (pureExtraGhostsWithOnce fOnce).lookup sym = some f) (s : State) :
    ∃ d : List TraceEvent, (f s).trace = s.trace ++ d ∧ allocFailedEvent ∉ d :=
  pureExtraGhostsWithCryptoAndOnce_noAllocFailed
    (fun _ => ⟨[], by rw [List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩)
    (fun _ => ⟨[], by rw [List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩)
    (fun _ => ⟨[], by rw [List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩)
    hNoFailOnce hLook s

/-- Every hook in `pureExtraGhosts` satisfies `CliInitSlotOkPlacedAt.HookNoAllocFailed f`. -/
theorem pureExtraGhosts_noAllocFailed {sym : String} {f : State → State}
    (hLook : pureExtraGhosts.lookup sym = some f) (s : State) :
    ∃ d : List TraceEvent, (f s).trace = s.trace ++ d ∧ allocFailedEvent ∉ d :=
  pureExtraGhostsWithCrypto_noAllocFailed
    (fun _ => ⟨[], by rw [List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩)
    (fun _ => ⟨[], by rw [List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩)
    (fun _ => ⟨[], by rw [List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩)
    hLook s

theorem pureExtraGhostsWithHmac_noAllocFailed {fHmac : State → State}
    (hNoFail : ∀ s : State,
      ∃ d : List TraceEvent, (fHmac s).trace = s.trace ++ d ∧ allocFailedEvent ∉ d)
    {sym : String} {f : State → State}
    (hLook : (pureExtraGhostsWithHmac fHmac).lookup sym = some f) (s : State) :
    ∃ d : List TraceEvent, (f s).trace = s.trace ++ d ∧ allocFailedEvent ∉ d :=
  pureExtraGhostsWithCrypto_noAllocFailed hNoFail
    (fun _ => ⟨[], by rw [List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩)
    (fun _ => ⟨[], by rw [List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩)
    hLook s

theorem pureExtraGhostsWithAes_noAllocFailed {fEnc fDec : State → State}
    (hNoFailEnc : ∀ s : State,
      ∃ d : List TraceEvent, (fEnc s).trace = s.trace ++ d ∧ allocFailedEvent ∉ d)
    (hNoFailDec : ∀ s : State,
      ∃ d : List TraceEvent, (fDec s).trace = s.trace ++ d ∧ allocFailedEvent ∉ d)
    {sym : String} {f : State → State}
    (hLook : (pureExtraGhostsWithAes fEnc fDec).lookup sym = some f) (s : State) :
    ∃ d : List TraceEvent, (f s).trace = s.trace ++ d ∧ allocFailedEvent ∉ d :=
  pureExtraGhostsWithCrypto_noAllocFailed
    (fun _ => ⟨[], by rw [List.append_nil]; exact ⟨rfl, fun h => nomatch h⟩⟩)
    hNoFailEnc hNoFailDec hLook s

theorem pureExtraGhosts_vmPreserved {sym : String} {f : State → State}
    (hLook : pureExtraGhosts.lookup sym = some f) (s : State) :
    VmPreserved s (f s) := by
  rcases pureExtraGhosts_lookup_cases hLook with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hookMemmove_vm s
  · exact pureBcmpHook_vm s
  · exact strlenHook_vmPreserved s
  · exact memrchrHook_vmPreserved s
  · exact fromUtf8Hook_vmPreserved pureUtf8Err s
  · exact durationSinceExactHook_vm s
  · exact timeAddHook_vm s
  · exact blackBoxHook_vm s
  · exact zeroizeSecretHook_vm s
  · exact zeroizeSecretHook_vm s
  · exact (dalekMontToEdFallback_preserved s).1
  · exact (dalekCompressFallback_preserved s).1
  · unfold edNegHook; exact returnToLr_vm (setMem_vm s fun a => congrFun (perm_writeBytes_norm _ _ _) a)
  · exact (dalekTorsionFreeFallback_preserved s).1
  · exact (dalekDsmbFallback_preserved s).1
  · exact (dalekScalarModFallback_preserved s).1
  · exact (dalekScalarWideFallback_preserved s).1
  · exact VmPreserved.refl s
  · exact VmPreserved.refl s
  · exact compress256Hook_vm s
  · exact hookNoop_vm s
  · exact hookNoop_vm s
  · exact hookNoop_vm s
  · exact compress512Fallback_vmPreserved s
  · exact (kemEncapsFallback_preserved s).1
  · exact (kemDecapsFallback_preserved s).1
  · exact (mlkemFromSeedFallback_preserved s).1
  · exact (mlkemEncaps1Fallback_preserved s).1
  · exact (mlkemEncaps2Fallback_preserved s).1
  · exact (mlkemDecapsFallback_preserved s).1
  · exact (mlkemValidatePkFallback_preserved s).1
  · exact vmPreserved_writeFileHook s
  · exact vmPreserved_writeStdoutHook s
  · exact VmPreserved.refl s
  · exact formatInnerHook0_vm s
  · exact pubFromSecretHook_vm s
  · exact diffieHellmanHook_vm s
  · exact hookNoop_vm s

theorem pureExtraGhosts_perm_eq {sym : String} {f : State → State}
    (hLook : pureExtraGhosts.lookup sym = some f) (u : State) (a : BitVec 64) :
    (f u).mem.perm a = u.mem.perm a :=
  (pureExtraGhosts_vmPreserved hLook u).2.2.1 a

/-- Every hook in `pureExtraGhosts` preserves `AllocGhostLinkTransfer.ExecFrozen`
    (`∀ a, (m.perm a).x = true → (m.perm a).r = true ∧ (m.perm a).w = false`), matching
    `ExecFrozen u.mem → ExecFrozen (f u).mem` definitionally. -/
theorem pureExtraGhosts_preserves_execFrozen {sym : String} {f : State → State}
    (hLook : pureExtraGhosts.lookup sym = some f) (u : State)
    (hfr : ∀ a : BitVec 64,
      (u.mem.perm a).x = true → (u.mem.perm a).r = true ∧ (u.mem.perm a).w = false) :
    ∀ a : BitVec 64,
      ((f u).mem.perm a).x = true → ((f u).mem.perm a).r = true ∧ ((f u).mem.perm a).w = false := by
  intro a hx
  rw [pureExtraGhosts_perm_eq hLook u a] at hx ⊢
  exact hfr a hx

theorem pureExtraGhostsWithCryptoAndOnce_preserves_execFrozen {fHmac fEnc fDec fOnce : State → State}
    (hHmacFr : ∀ u : State,
      (∀ a : BitVec 64,
        (u.mem.perm a).x = true → (u.mem.perm a).r = true ∧ (u.mem.perm a).w = false) →
      ∀ a : BitVec 64,
        ((fHmac u).mem.perm a).x = true →
          ((fHmac u).mem.perm a).r = true ∧ ((fHmac u).mem.perm a).w = false)
    (hEncFr : ∀ u : State,
      (∀ a : BitVec 64,
        (u.mem.perm a).x = true → (u.mem.perm a).r = true ∧ (u.mem.perm a).w = false) →
      ∀ a : BitVec 64,
        ((fEnc u).mem.perm a).x = true →
          ((fEnc u).mem.perm a).r = true ∧ ((fEnc u).mem.perm a).w = false)
    (hDecFr : ∀ u : State,
      (∀ a : BitVec 64,
        (u.mem.perm a).x = true → (u.mem.perm a).r = true ∧ (u.mem.perm a).w = false) →
      ∀ a : BitVec 64,
        ((fDec u).mem.perm a).x = true →
          ((fDec u).mem.perm a).r = true ∧ ((fDec u).mem.perm a).w = false)
    (hOnceFr : ∀ u : State,
      (∀ a : BitVec 64,
        (u.mem.perm a).x = true → (u.mem.perm a).r = true ∧ (u.mem.perm a).w = false) →
      ∀ a : BitVec 64,
        ((fOnce u).mem.perm a).x = true →
          ((fOnce u).mem.perm a).r = true ∧ ((fOnce u).mem.perm a).w = false)
    {sym : String} {f : State → State}
    (hLook : (pureExtraGhostsWithCryptoAndOnce fHmac fEnc fDec fOnce).lookup sym = some f)
    (u : State)
    (hfr : ∀ a : BitVec 64,
      (u.mem.perm a).x = true → (u.mem.perm a).r = true ∧ (u.mem.perm a).w = false) :
    ∀ a : BitVec 64,
      ((f u).mem.perm a).x = true → ((f u).mem.perm a).r = true ∧ ((f u).mem.perm a).w = false := by
  rcases pureExtraGhostsWithCryptoAndOnce_lookup_cases hLook with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · intro a hx; rw [(hookMemmove_vm u).2.2.1 a] at hx ⊢; exact hfr a hx
  · exact hfr
  · intro a hx; rw [(strlenHook_vmPreserved u).2.2.1 a] at hx ⊢; exact hfr a hx
  · intro a hx; rw [(memrchrHook_vmPreserved u).2.2.1 a] at hx ⊢; exact hfr a hx
  · intro a hx; rw [(fromUtf8Hook_vmPreserved pureUtf8Err u).2.2.1 a] at hx ⊢; exact hfr a hx
  · intro a hx; rw [(durationSinceExactHook_vm u).2.2.1 a] at hx ⊢; exact hfr a hx
  · intro a hx; rw [(timeAddHook_vm u).2.2.1 a] at hx ⊢; exact hfr a hx
  · exact hfr
  · intro a hx; rw [(zeroizeSecretHook_vm u).2.2.1 a] at hx ⊢; exact hfr a hx
  · intro a hx; rw [(zeroizeSecretHook_vm u).2.2.1 a] at hx ⊢; exact hfr a hx
  · intro a hx; rw [(dalekMontToEdFallback_preserved u).1.2.2.1 a] at hx ⊢; exact hfr a hx
  · intro a hx; rw [(dalekCompressFallback_preserved u).1.2.2.1 a] at hx ⊢; exact hfr a hx
  · intro a hx
    have hvm : VmPreserved u (edNegHook dalekEdNegVec u) := by
      unfold edNegHook
      exact returnToLr_vm (setMem_vm u fun b => congrFun (perm_writeBytes_norm _ _ _) b)
    rw [hvm.2.2.1 a] at hx ⊢; exact hfr a hx
  · intro a hx; rw [(dalekTorsionFreeFallback_preserved u).1.2.2.1 a] at hx ⊢; exact hfr a hx
  · intro a hx; rw [(dalekDsmbFallback_preserved u).1.2.2.1 a] at hx ⊢; exact hfr a hx
  · intro a hx; rw [(dalekScalarModFallback_preserved u).1.2.2.1 a] at hx ⊢; exact hfr a hx
  · intro a hx; rw [(dalekScalarWideFallback_preserved u).1.2.2.1 a] at hx ⊢; exact hfr a hx
  · exact hfr
  · exact hfr
  · intro a hx; rw [(compress256Hook_vm u).2.2.1 a] at hx ⊢; exact hfr a hx
  · exact hHmacFr u hfr
  · exact hEncFr u hfr
  · exact hDecFr u hfr
  · intro a hx; rw [(compress512Fallback_vmPreserved u).2.2.1 a] at hx ⊢; exact hfr a hx
  · intro a hx; rw [(kemEncapsFallback_preserved u).1.2.2.1 a] at hx ⊢; exact hfr a hx
  · intro a hx; rw [(kemDecapsFallback_preserved u).1.2.2.1 a] at hx ⊢; exact hfr a hx
  · intro a hx; rw [(mlkemFromSeedFallback_preserved u).1.2.2.1 a] at hx ⊢; exact hfr a hx
  · intro a hx; rw [(mlkemEncaps1Fallback_preserved u).1.2.2.1 a] at hx ⊢; exact hfr a hx
  · intro a hx; rw [(mlkemEncaps2Fallback_preserved u).1.2.2.1 a] at hx ⊢; exact hfr a hx
  · intro a hx; rw [(mlkemDecapsFallback_preserved u).1.2.2.1 a] at hx ⊢; exact hfr a hx
  · intro a hx; rw [(mlkemValidatePkFallback_preserved u).1.2.2.1 a] at hx ⊢; exact hfr a hx
  · intro a hx; rw [(vmPreserved_writeFileHook u).2.2.1 a] at hx ⊢; exact hfr a hx
  · intro a hx; rw [(vmPreserved_writeStdoutHook u).2.2.1 a] at hx ⊢; exact hfr a hx
  · exact hfr
  · intro a hx; rw [(formatInnerHook0_vm u).2.2.1 a] at hx ⊢; exact hfr a hx
  · intro a hx; rw [(pubFromSecretHook_vm u).2.2.1 a] at hx ⊢; exact hfr a hx
  · intro a hx; rw [(diffieHellmanHook_vm u).2.2.1 a] at hx ⊢; exact hfr a hx
  · exact hOnceFr u hfr

theorem pureExtraGhostsWithCrypto_preserves_execFrozen {fHmac fEnc fDec : State → State}
    (hHmacFr : ∀ u : State,
      (∀ a : BitVec 64,
        (u.mem.perm a).x = true → (u.mem.perm a).r = true ∧ (u.mem.perm a).w = false) →
      ∀ a : BitVec 64,
        ((fHmac u).mem.perm a).x = true →
          ((fHmac u).mem.perm a).r = true ∧ ((fHmac u).mem.perm a).w = false)
    (hEncFr : ∀ u : State,
      (∀ a : BitVec 64,
        (u.mem.perm a).x = true → (u.mem.perm a).r = true ∧ (u.mem.perm a).w = false) →
      ∀ a : BitVec 64,
        ((fEnc u).mem.perm a).x = true →
          ((fEnc u).mem.perm a).r = true ∧ ((fEnc u).mem.perm a).w = false)
    (hDecFr : ∀ u : State,
      (∀ a : BitVec 64,
        (u.mem.perm a).x = true → (u.mem.perm a).r = true ∧ (u.mem.perm a).w = false) →
      ∀ a : BitVec 64,
        ((fDec u).mem.perm a).x = true →
          ((fDec u).mem.perm a).r = true ∧ ((fDec u).mem.perm a).w = false)
    {sym : String} {f : State → State}
    (hLook : (pureExtraGhostsWithCrypto fHmac fEnc fDec).lookup sym = some f) (u : State)
    (hfr : ∀ a : BitVec 64,
      (u.mem.perm a).x = true → (u.mem.perm a).r = true ∧ (u.mem.perm a).w = false) :
    ∀ a : BitVec 64,
      ((f u).mem.perm a).x = true → ((f u).mem.perm a).r = true ∧ ((f u).mem.perm a).w = false :=
  pureExtraGhostsWithCryptoAndOnce_preserves_execFrozen (fOnce := hookNoop)
    hHmacFr hEncFr hDecFr (fun _ h => h) hLook u hfr

theorem pureExtraGhostsWithOnce_preserves_execFrozen {fOnce : State → State}
    (hOnceFr : ∀ u : State,
      (∀ a : BitVec 64,
        (u.mem.perm a).x = true → (u.mem.perm a).r = true ∧ (u.mem.perm a).w = false) →
      ∀ a : BitVec 64,
        ((fOnce u).mem.perm a).x = true →
          ((fOnce u).mem.perm a).r = true ∧ ((fOnce u).mem.perm a).w = false)
    {sym : String} {f : State → State}
    (hLook : (pureExtraGhostsWithOnce fOnce).lookup sym = some f) (u : State)
    (hfr : ∀ a : BitVec 64,
      (u.mem.perm a).x = true → (u.mem.perm a).r = true ∧ (u.mem.perm a).w = false) :
    ∀ a : BitVec 64,
      ((f u).mem.perm a).x = true → ((f u).mem.perm a).r = true ∧ ((f u).mem.perm a).w = false :=
  pureExtraGhostsWithCryptoAndOnce_preserves_execFrozen
    (fHmac := hookNoop) (fEnc := hookNoop) (fDec := hookNoop)
    (fun _ h => h) (fun _ h => h) (fun _ h => h) hOnceFr hLook u hfr

theorem pureExtraGhostsWithHmac_preserves_execFrozen {fHmac : State → State}
    (hHmacFr : ∀ u : State,
      (∀ a : BitVec 64,
        (u.mem.perm a).x = true → (u.mem.perm a).r = true ∧ (u.mem.perm a).w = false) →
      ∀ a : BitVec 64,
        ((fHmac u).mem.perm a).x = true →
          ((fHmac u).mem.perm a).r = true ∧ ((fHmac u).mem.perm a).w = false)
    {sym : String} {f : State → State}
    (hLook : (pureExtraGhostsWithHmac fHmac).lookup sym = some f) (u : State)
    (hfr : ∀ a : BitVec 64,
      (u.mem.perm a).x = true → (u.mem.perm a).r = true ∧ (u.mem.perm a).w = false) :
    ∀ a : BitVec 64,
      ((f u).mem.perm a).x = true → ((f u).mem.perm a).r = true ∧ ((f u).mem.perm a).w = false :=
  pureExtraGhostsWithCrypto_preserves_execFrozen (fEnc := hookNoop) (fDec := hookNoop) hHmacFr
    (fun _ h => h) (fun _ h => h) hLook u hfr

theorem pureExtraGhostsWithAes_preserves_execFrozen {fEnc fDec : State → State}
    (hEncFr : ∀ u : State,
      (∀ a : BitVec 64,
        (u.mem.perm a).x = true → (u.mem.perm a).r = true ∧ (u.mem.perm a).w = false) →
      ∀ a : BitVec 64,
        ((fEnc u).mem.perm a).x = true →
          ((fEnc u).mem.perm a).r = true ∧ ((fEnc u).mem.perm a).w = false)
    (hDecFr : ∀ u : State,
      (∀ a : BitVec 64,
        (u.mem.perm a).x = true → (u.mem.perm a).r = true ∧ (u.mem.perm a).w = false) →
      ∀ a : BitVec 64,
        ((fDec u).mem.perm a).x = true →
          ((fDec u).mem.perm a).r = true ∧ ((fDec u).mem.perm a).w = false)
    {sym : String} {f : State → State}
    (hLook : (pureExtraGhostsWithAes fEnc fDec).lookup sym = some f) (u : State)
    (hfr : ∀ a : BitVec 64,
      (u.mem.perm a).x = true → (u.mem.perm a).r = true ∧ (u.mem.perm a).w = false) :
    ∀ a : BitVec 64,
      ((f u).mem.perm a).x = true → ((f u).mem.perm a).r = true ∧ ((f u).mem.perm a).w = false :=
  pureExtraGhostsWithCrypto_preserves_execFrozen (fHmac := hookNoop)
    (fun _ h => h) hEncFr hDecFr hLook u hfr

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.PureExtraGhosts
